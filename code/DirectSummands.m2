---------------------------------------------------------------------------
-- PURPOSE : to compute direct summands of modules and coherent sheaves
--
-- UPDATE HISTORY : created Oct 2023
--
-- TODO :
-- 1. implement over Dmodules and other non-commutative rings
-- 2. implement diagonalize for matrices (and later, complexes)
-- 3. find a way to restrict and pass End to the summands
-- 4. make summands work over ZZ (currently rank fails)
-- 5. compute a general endomorphism without computing End
-- 6. speed up computing eigenvalues over ZZ/p and GF(q)
-- 7. once an indecomposable summand is found, call summands(N, M)
-- 8. add option to split over a field extension
-- 9. add Atlantic City, Las Vegas, or Monte Carlo style strategies?
---------------------------------------------------------------------------
newPackage(
    "DirectSummands",
    Version => "0.3",
    Date => "April 20th 2025",
    Headline => "decompositions of modules and coherent sheaves",
    Authors => {
	{ Name => "Devlin Mallory", Email => "malloryd@math.utah.edu", HomePage => "https://math.utah.edu/~malloryd/"},
	{ Name => "Mahrud Sayrafi", Email => "mahrud@umn.edu",         HomePage => "https://math.umn.edu/~mahrud/"}
	},
    Keywords => { "Commutative Algebra" },
    PackageImports => {
	"Polyhedra",       -- for coneFromVData and coneComp
	"Truncations",     -- for effGenerators
	--"LocalRings",      -- for the local examples
	"Varieties",       -- for the geometric examples
	},
    PackageExports => {
	"Isomorphism",     -- for isIsomorphic
	"PushForward",     -- only for frobenius.m2
	"RationalPoints2", -- for rationalPoints
	},
    AuxiliaryFiles => true,
    DebuggingMode => false
    )

export {
    -- methods
    "isIndecomposable",
    "directSummands", "summands" => "directSummands",
    "findProjectors",
    "findIdempotents", "findIdem" => "findIdempotents",
    "findSplitInclusion",
    "generalEndomorphism",
    "isomorphismTally",
    "tallySummands",
    -- frobenius methods
    "frobeniusMap",
    "frobeniusRing",
    "frobeniusPullback",
    "frobeniusPushforward",
    "frobeniusTwist",
    "potentialExtension",
    "extendGroundField" => "changeBaseField",
    "changeBaseField"
    -- symbols
    }

importFrom_Core {
    "raw", "rawReshape",
    "rawNumberOfColumns",
    "rawNumberOfRows",
    "localRandom",
    "tryHooks",
    "sortBy",
    }

LocalRing = new Type

-----------------------------------------------------------------------------
-* Code section *-
-----------------------------------------------------------------------------

-- defined here and used in idempotents.m2 and homogeneous.m2
DirectSummandsOptions = new OptionTable from {
    Limit             => null, -- used in directSummands(Module, Module)
    Strategy          => 3,    -- Strategy is a bitwise sum of the following:
    -- 1  => use degrees of generators as heuristic to peel off line bundles first
    -- 2  => check generators of End_0 as heuristic for finding idempotents
    -- 4  => use splitComponentsBasic, skips computing splitting maps
    -- 8  => precompute Homs before looking for idempotents
    -- 16 => use summandsFromIdempotents even in graded case
    "Splitting"       => null,
    Tries             => null, -- see defaultNumTries below
    Verbose           => false -- whether to print extra debugging info
}

-- the default number of attempts for randomized algorithms
-- e.g. 145 tries in char 2, 10 in char 32003, and 1 in char 0
defaultNumTries = p -> ceiling(0.1 + 100 / log p)
--apply({2, 32003, 0}, defaultNumTries)

-- helpers for computing Frobenius pushforwards of modules and sheaves
-- TODO: move to PushForward package?
load "./DirectSummands/pushforward2.m2"
load "./DirectSummands/linearalgebra.m2"
load "./DirectSummands/frobenius.m2"
-- helpers for finding random idempotents of a module for the local case
load "./DirectSummands/idempotents.m2"
-- helpers for finding random projectors of a module for the graded case
load "./DirectSummands/homogeneous.m2"

-----------------------------------------------------------------------------
-- Things to move to the Core
-----------------------------------------------------------------------------

-- return the submatrix with given degrees of target and source
submatrixByDegrees(Matrix, Sequence) := (m, degs) -> (
    (tar, src) := degs;
    col := if src =!= null then positions(degrees source m, deg -> member(deg, src));
    row := if tar =!= null then positions(degrees target m, deg -> member(deg, tar));
    submatrix(m, row, col))

-- rankWarn = true
-- rank' = M -> if groundField ring M =!= ZZ then rank M else try rank M else (
--     if rankWarn then ( rankWarn = false;
-- 	printerr "warning: rank over integers is not well-defined; returning zero");
--     0)

-- this defines sorting on modules and sheaves
CoherentSheaf ? CoherentSheaf :=
Module ? Module := (M, N) -> if rank M != rank N then rank M ? rank N else degrees M ? degrees N

position(ZZ, Function) := o -> (n, f) -> position(0..n-1, f)
-- TODO: this is different from position(List,List,Function)
position' = method()
position'(VisibleList, VisibleList, Function) := (B, C, f) -> for b in B do for c in C do if f(b, c) then return (b, c)
position'(ZZ,          ZZ,          Function) := (B, C, f) -> position'(0..B-1, 0..C-1, f)

partition(ZZ, Function) := HashTable => (n, f) -> partition(f, toList(0..n-1), {})

scan' = method()
scan'(VisibleList, VisibleList, Function) := (B, C, f) -> for b in B do for c in C do f(b,c)

char SheafOfRings := O -> char variety O

GF'ZZ'ZZ = memoize (lookup(GF, ZZ, ZZ)) (options GF)
GF'Ring  = memoize (lookup(GF, Ring))   (options GF)
GF(ZZ, ZZ) := GaloisField => opts -> GF'ZZ'ZZ
GF(Ring)   := GaloisField => opts -> GF'Ring

-- TODO: what generality should this be in?
-- WANT:
--   R ** ZZ/101 to change characteristic
--   R ** S to change coefficient ring
-- TODO: can you change the ground field but keep the tower structure?
QuotientRing   ** GaloisField :=
PolynomialRing ** GaloisField := (R, L) -> R.cache#(map, L, R) ??= (
    -- TODO: in general we may want to keep part of the ring tower
    A := first flattenRing(R, CoefficientRing => null);
    quotient sub(ideal A, L monoid A))

changeBaseMap = method()
changeBaseMap(Ring, Ring) := (L, S) -> S.cache#(map, L, S) ??= map(quotient sub(ideal S, L monoid S), S)

changeBaseField = method()
-- TODO: add more automated methods, e.g. where minors of the presentation factor
changeBaseField(ZZ, Module) :=
changeBaseField(ZZ, CoherentSheaf)   := (e, M) -> changeBaseField(GF(char ring M, e), M)
changeBaseField(GaloisField, Module) := (L, M) -> M.cache#(symbol changeBaseField, L) ??= (
    S := first flattenRing(ring M,
	CoefficientRing => null);
    K := coefficientRing S;
    if class K =!= GaloisField then return (
        R0 := quotient sub(ideal S, L monoid S);
	M' := directSum apply(cachedSummands M,
	    N -> coker sub(presentation N, R0));
        M.cache#(symbol changeBaseField, L) = M');
    -- don't needlessly create new rings:
    if K.order === L.order then return M;
    i0 := map(L, K);
    LS := L(monoid S);
    i1 := map(LS, ring ideal S, gens LS | { i0 K_0 });
    R := quotient i1 ideal S;
    i := map(R, S, i1);
    directSum apply(cachedSummands M, N -> i ** N))

changeBaseField(Ring, Module) := (L, M) -> M.cache#(symbol changeBaseField, L) ??= (
    S := first flattenRing(ring M,
	CoefficientRing => null);
    psi := changeBaseMap(L, S);
    directSum apply(cachedSummands M,
	N -> coker(psi ** presentation N)))

changeBaseField(Ring, Matrix) := (L, f) -> f.cache#(symbol changeBaseField, L) ??= (
    S := first flattenRing(ring f,
	CoefficientRing => null);
    psi := changeBaseMap(L, S);
    psi ** f)

-- TODO: come up with a better way to extend ground field of a variety
-- TODO: does this also need to be used for frobenius pushforward?
sheaf' = (X, M) -> try sheaf(X, M) else (
    if instance(X, ProjectiveVariety) then sheaf(Proj ring M, M) else
    if instance(X,     AffineVariety) then sheaf(Spec ring M, M) else
    error "extension of the coefficient field of the base variety is not implemented")

changeBaseField(GaloisField, CoherentSheaf) := (L, F) -> sheaf'(variety F, changeBaseField(L, module F))

importFrom_Varieties "flattenModule"
prune' = method()
prune' Module := M0 -> M0.cache.prune' ??= (
    M := prune M0;
    R := ring M;
    if isHomogeneous M0
    or instance(R, LocalRing) then return M;
    return M)
    -- S := ambient R;
    -- MS := flattenModule M;
    -- Sm := localRing(S, ideal gens S);
    -- MSm := prune(MS ** Sm);
    -- R ** liftUp MSm)

nonzero = x -> select(x, i -> i != 0)
nonnull = x -> select(x, i -> i =!= null)

checkRecursionDepth = () -> if recursionDepth() > recursionLimit - 20 then printerr(
    "Warning: the recursion depth limit may need to be extended; use `recursionLimit = N`")

-----------------------------------------------------------------------------
-- things to move to Isomorphism package
-----------------------------------------------------------------------------

module Module := identity

-- TODO: speed this up
-- TODO: implement isIsomorphic for sheaves
-- TODO: add strict option
tallySummands = method(Options => options isIsomorphic)
tallySummands List := Tally => opts -> L -> tally (
    L  = new MutableList from module \ L;
    b := new MutableList from #L : true;
    for i to #L-2 do if b#i then for j from i+1 to #L-1 do if b#j then (
	if isIsomorphic(L#i, L#j, opts)
	then ( b#j = false; L#j = L#i ));
    new List from L)

isomorphismTally = method(Options => options isIsomorphic)
isomorphismTally List := opts -> L -> (
    if not uniform L then error "expected list of elements of the same type";
    if not (class L_0 === Module or class L_0 === CoherentSheaf ) then error "expected list of modules or sheaves";
    --L = new MutableList from L;
    j := 0;
    while j < #L list (
	i := j + 1;
	c := 1;
	while i < #L do (
	    if isIsomorphic(L#j, L#i, opts)
	    then (
		L = drop(L, {i, i});
		c = c + 1)
	    else i = i + 1);
	j = j + 1;
	(L#(j-1), c)))

-----------------------------------------------------------------------------
-- methods for finding general endomorphisms of degree zero
-----------------------------------------------------------------------------

importFrom_Truncations { "effGenerators" }

coneComp = (C, u, v) -> (
    --if u == v                            then symbol== else
    if contains(C, matrix vector(v - u)) then symbol <= else
    if contains(C, matrix vector(u - v)) then symbol > else incomparable)

-- TODO: add this as a strategy to basis
smartBasis = (deg, M) -> (
    -- TODO: try splitting coker {{a, b^3}, {-b^3, a}} over ZZ/32003[a..b]/(a^2+b^6)
    if M == 0 then return map(M, 0, 0);
    if instance(deg, ZZ) then deg = {deg};
    degs := if #deg == 1 then select(unique degrees M, d -> d <= deg) else (
	-- FIXME: in the multigraded case sometimes just using basis is faster:
	return basis(deg, M);
        -- in the multigraded case, coneMin and coneComp can be slow
	-- but for sufficiently large modules they are still an improvement
        -- TODO: make them faster
        C := coneFromVData effGenerators ring M;
        --elapsedTime compMin(C, unique degrees M) -- TODO: this is not the right thing
        select(unique degrees M, d -> coneComp(C, d, deg) == symbol <=));
    if degs === {deg} then return map(M, , submatrixByDegrees(gens cover M, (, degs)));
    M' := subquotient(ambient M,
	if M.?generators then submatrixByDegrees(gens M, (, degs)),
	if M.?relations  then relations M);
    M'.cache.homomorphism = M.cache.homomorphism;
    basis(deg, M')) -- caching this globally causes issues!

-- matrix of (degree zero) generators of End M
-- TODO: rename this
-- also see gensHom0
gensEnd0 = M -> M.cache#"End0" ??= (
    -- TODO: need to pass options from Hom + choose the coefficient field
    zdeg := if isHomogeneous M then degree 0_M;
    if 0 < debugLevel then stderr << " -- computing End module ... " << flush;
    A := Hom(M, M,
	DegreeLimit       => zdeg,
	MinimalGenerators => false);
    if 0 < debugLevel then stderr << "done!" << endl;
    if isHomogeneous M
    then smartBasis(zdeg, A)
    else inducedMap(A, , gens A))

generalEndomorphism = method(Options => options random)
generalEndomorphism Module := Matrix => o -> M0 -> (
    -- FIXME: random with MaximalRank gives inhomogeneous results
    verify := o.MaximalRank;
    o = o ++ { MaximalRank => false };
    R := ring M0;
    -- TODO: avoid this hack for local rings
    M := M0; -- if instance(R, LocalRing) then liftUp M0 else M0;
    B := gensEnd0 M;
    r := if isHomogeneous M
    then random(source B, o)
    else localRandom(source B, o);
    -- TODO: this is a minor bottleneck
    h := R ** homomorphism(B * r);
    -- if MaximalRank is true verify that the map is an isomorphism
    if not verify or isSurjective sub(cover h, groundField R)
    then h else generalEndomorphism(M0, o))
-- the sheaf needs to be pruned to prevent missing endomorphisms
generalEndomorphism CoherentSheaf := SheafMap => o -> F -> (
    sheaf generalEndomorphism(module prune F, o))

-- left inverse of a split injection
-- TODO: figure out if we can ever do this without computing End source g
leftInverse = inverse' = method(Options => options Hom)
leftInverse Matrix := opts -> g -> g.cache.leftInverse ??= quotient'(id_(source g), g, opts)

-- right inverse of a split surjection
-- FIXME: inverse may fail for a general split surjection:
-- c.f. https://github.com/Macaulay2/M2/issues/3738
-- TODO: figure out if we can ever do this without computing End target g
rightInverse = method(Options => options Hom)
rightInverse Matrix := opts -> g -> g.cache.rightInverse ??= quotient(id_(target g), g, opts)

-- given N and a split injection inc:N -> M,
-- we use precomputed endomorphisms of M
-- to produce a general endomorphism of N
generalEndomorphism(Matrix, Nothing, Matrix) := Matrix => o -> (N, null, inc) -> (
    -- assert(N === source inc);
    inv := leftInverse(inc,
	DegreeLimit => degree 0_N,
	-- FIXME: setting this to false sometimes
	-- produces non-well-defined inverses
	MinimalGenerators => true);
    inc * generalEndomorphism(target inc, o) * inv)

-- given N and a split surjection pr:M -> N,
-- we use precomputed endomorphisms of M
-- to produce a general endomorphism of N
generalEndomorphism(Module, Matrix) := Matrix => o -> (N, pr) -> (
    -- assert(N === target pr);
    -- TODO: currently this still computes End_0(N)
    -- figure out a way to compute the inverse without doing so
    inv := rightInverse(pr,
	DegreeLimit => degree 0_N,
	-- FIXME: setting this to false sometimes
	-- produces non-well-defined inverses
	MinimalGenerators => true);
    pr * generalEndomorphism(source pr, o) * inv)

generalEndomorphism(Module, Matrix, Nothing) := Matrix => o -> (N, pr, null) -> generalEndomorphism(N, pr, o)
generalEndomorphism(Module, Matrix, Matrix)  := Matrix => o -> (N, pr, inc) -> (
    -- assert(N === target pr and source pr === target inc and N === source inc);
    pr * generalEndomorphism(source pr, o) * inc)

randomIsomorphism = method(Options => options random)
randomIsomorphism Module := Matrix => o -> M -> (
    -- FIXME: random with MaximalRank returns inhomogeneous matrices
    --if isFreeModule M then random(M, M, o, MaximalRank => true)
    generalEndomorphism(M, o, MaximalRank => true))

-----------------------------------------------------------------------------
-- helpers for splitting and caching projection maps
-----------------------------------------------------------------------------

findSplitInclusion = method(Options => { Tries => 50 })
--tests if M is a split summand of N
findSplitInclusion(Module, Module) := opts -> (M, N) -> (
    h := for i to opts.Tries - 1 do (
        b := homomorphism random Hom(M, N, MinimalGenerators => false);
        c := homomorphism random Hom(N, M, MinimalGenerators => false);
        if isIsomorphism(c * b) then break b);
    if h === null then return "not known" else return h)

-- helper for splitting a free module and setting the split surjections
splitFreeModule = (M, opts) -> components directSum apply(R := ring M; -degrees M, deg -> R^{deg})

-- helper for splitting free summands by observing the degrees of generators
splitFreeSummands = (M, opts) -> M.cache#"FreeSummands" ??= (
    directSummands(R := ring M; apply(-unique degrees M, d -> R^{d}), M, opts))

isDegreeSplit = M -> isHomogeneous M and 1 < #splitByDegrees M

-- helper for splitting a graded module M when Eff(R) is not smooth
-- in this case the degree support of M can split over Eff(R)
splitByDegrees = M -> M.cache#"DegreeSummands" ??= (
    degs := matrix transpose degrees M;
    eff := matrix transpose degrees ring M;
    if minors(rank eff, eff) == 1 then return {M};
    H := partition(numgens M, i -> flatten entries(degs_{i} % eff));
    apply(values H, ell -> image M_ell))

-- helper for splitting a module over a PID or field (e.g. ZZ, QQ, ZZ[x], etc.)
-- TODO: check if R is PID; currently this is only used if R has degree length zero.
-- TODO: get projection/inclusion maps working
splitPIDModule = M -> components directSum apply(numgens M, i -> prune image M_{i})

-- helper for splitting a module with known components
-- (in particular, the components may also have summands)
-- TODO: can we sort the summands here?
splitComponents = (M, comps, splitfunc) -> (
    n := #comps;
    c := -1; -- summand counter
    projs := if 1 < n then apply(n, i -> try M^[i]) else { id_M };
    flatten apply(comps, projs, (N, p) -> (
	L := splitfunc N;
	-- Projection maps to the summands
	try if #L > 1 then apply(#L, i ->
	    M.cache#(symbol ^, [c += 1]) = N^[i] * p)
	else M.cache#(symbol ^, [c += 1]) = p;
	-- Inclusion maps are computed on-demand
	L)))

splitComponentsBasic = (M, ends, opts) -> (
    -- the coker of each idempotent gives a summand, while
    L1 := prune' \ apply(ends, coker);
    -- the image of their composition is the complement.
    L2 := prune' \ { image product ends };
    -- TODO: call something like summands(L, M) here?
    flatten apply(nonzero join(L1, L2), summands_opts))

-- these are computed on-demand from the cached split surjection
oldinclusions = lookup(symbol_, Module, Array)
Module _ Array := Matrix => (M, w) -> M.cache#(symbol _, w) ??= (
    if not M.cache#?(symbol ^, w) then oldinclusions(M, w)
    else rightInverse(M.cache#(symbol ^, w),
	DegreeLimit       => degree 0_M,
	MinimalGenerators => true))

-- TODO: can we return cached summands from the closest subfield?
cachedSummands = M -> M.cache.summands ?? components M

-----------------------------------------------------------------------------
-- directSummands
-----------------------------------------------------------------------------

-- Note: M may need to be extended to a field extensions
directSummands = method(Options => DirectSummandsOptions)
directSummands Module := List => opts -> M -> M.cache.summands ??= (
    checkRecursionDepth();
    strategy := opts.Strategy;
    R := ring M;
    if prune' M == 0 then return { M };
    -- Note: End does not work for WeylAlgebras or AssociativeAlgebras yet, nor does basis
    if not isCommutative R and not isWeylAlgebra R then error "expected a commutative base ring";
    -- Note: rank does weird stuff if R is not a domain
    if opts.Verbose then printerr("splitting module of rank: ", toString rank M);
    if rank cover M <= 1 then return M.cache.summands = { M.cache.isIndecomposable = true; M };
    if isDirectSum  M    then return M.cache.summands = splitComponents(M, components M, directSummands_opts);
    if isDegreeSplit M   then return M.cache.summands = splitComponents(M, splitByDegrees M, directSummands_opts);
    if isFreeModule M    then return M.cache.summands = splitFreeModule(M, opts);
    if degrees R == {}   then return M.cache.summands = splitComponents(M, splitPIDModule M, N -> {N});
    if strategy & 1 == 1 then return M.cache.summands = (
	splitComponents(M, splitFreeSummands(M, opts),
	    directSummands_(opts, Strategy => strategy - 1)));
    -- TODO: where should indecomposability check happen?
    -- for now it's here, but once we figure out random endomorphisms
    -- without computing Hom, this would need to move.
    -- Note: this may return null if it is inconclusive
    if strategy & 2  == 2  and isIndecomposable M === true then { M } else
    if strategy & 16 != 16 and isHomogeneous M
    then summandsFromProjectors(M, opts)   -- see DirectSummands/homogeneous.m2
    else summandsFromIdempotents(M, opts)) -- see DirectSummands/idempotents.m2

directSummands CoherentSheaf := List => opts -> F -> apply(
    directSummands(module prune F, opts), N -> sheaf(variety F, N))

-----------------------------------------------------------------------------

-- tests whether L (perhaps a line bundle) is a summand of M
-- Limit => N _recommends_ stopping after peeling N summands of L
-- FIXME: it's not guaranteed to work, e.g. on X_4 over ZZ/2
-- TODO: cache projection/inclusion maps
-- TODO: cache this
directSummands(Module, Module) := List => opts -> (L, M) -> (
    checkRecursionDepth();
    if ring L =!= ring M then error "expected objects over the same ring";
    if rank L  >  rank M
    or rank L  >= rank M and isFreeModule M then return {M};
    limit := opts.Limit ?? numgens M;
    tries := opts.Tries ?? defaultNumTries char ring M;
    if 1 < #cachedSummands M then return flatten apply(cachedSummands M, N -> directSummands(L, N, opts));
    if 1 < limit then (
	N := M;
	M.cache#(symbol ^, [0]) = id_M;
	if opts.Verbose then stderr << " -- splitting summands of degree " << degrees L << ": " << flush;
	comps := new MutableList from {M};
	for i to limit - 1 do (
	    pr := M.cache#(symbol ^, [#comps-1]);
	    LL := directSummands(L, N, opts, Limit => 1);
	    if #LL == 1 then break;
	    M.cache#(symbol ^, [#comps])   = N^[1] * pr;
	    M.cache#(symbol ^, [#comps-1]) = N^[0] * pr;
	    comps#(#comps-1) = L; -- === LL#0
	    comps##comps = N = LL#1);
	if opts.Verbose then stderr << endl << flush;
	return toList comps
    );
    zdeg := degree 0_M;
    -- TODO: can we detect multiple summands of L at once?
    -- perhaps find a projector onto a summand with several copies?
    gensHom0 := (N, M) -> (
	H := Hom(N, M,
	    DegreeLimit => zdeg,
	    MinimalGenerators => false);
	smartBasis(zdeg, H));
    h := catch if isFreeModule L then (
	-- TODO: for the case of line bundle summands,
	-- is it faster if we compute all of Hom and check
	-- for line bundles of any degree all at once?
	C := gensHom0(M, L); if numcols C == 0 then return {M};
	-- Previous alternative:
	-- h := for i from 0 to numcols C - 1 do (
	--     isSurjective(c := homomorphism C_{i}) ...)
	for i to tries - 1 do (
	    c := homomorphism(C * random source C);
	    if isSurjective c then throw (c, rightInverse c)))
    else (
        -- we look for a composition L -> M -> L which is the identity
	B := gensHom0(L, M); if numcols B == 0 then return {M};
	C  = gensHom0(M, L); if numcols C == 0 then return {M};
        -- attempt to find a random isomorphism
        for i to tries - 1 do (
	    b := homomorphism(B * random source B);
	    c := homomorphism(C * random source C);
            --TODO: change isIsomorphism to isSurjective?
	    if isIsomorphism(c * b) then throw (c, b));
	-- TODO: is it worth doing the following lines? when does the random strategy above fail?
	printerr "summands got to this part, it's probably useful!";
	if opts.Strategy & 8 == 8 then (
	    -- precomputing the Homs can sometimes be a good strategy
	    -- TODO: confirm that this injectivity check is worthwhile and not slow
	    Bhoms := select(apply(numcols B, i -> homomorphism B_{i}), isInjective);
	    Choms := select(apply(numcols C, i -> homomorphism C_{i}), isSurjective);
	    scan'(Choms, Bhoms, (c, b) -> if isIsomorphism(c * b) then throw (c, b)))
	-- but sometimes too memory intensive
	else scan'(numcols C, numcols B, (ci, bi) ->
	    if isSurjective(c := homomorphism C_{ci})
	    and isInjective(b := homomorphism B_{bi})
	    and isIsomorphism(c * b) then throw (c, b))
    );
    (pr, inc) := if h =!= null then h else return {M};
    if opts.Verbose then stderr << concatenate(rank L : ".") << flush;
    N = prune' coker inc;
    iso := inverse N.cache.pruningMap;
    M.cache#(symbol ^, [0]) = pr;
    M.cache#(symbol ^, [1]) = iso * inducedMap(coker inc, M);
    {L, N})

directSummands(CoherentSheaf, CoherentSheaf) := List => opts -> (L, G) -> apply(
    directSummands(module prune L, module prune G, opts), N -> sheaf(variety L, N))

-- attempt to peel off summands from a given list of modules
directSummands(List, CoherentSheaf) :=
directSummands(List, Module) := List => opts -> (Ls, M) -> sort (
    if 1 < #cachedSummands M then flatten apply(cachedSummands M, N -> directSummands(Ls, N, opts))
    else fold(Ls, {M}, (L, LL) -> splitComponents(M, LL, directSummands_(opts, L))))

-----------------------------------------------------------------------------
-- isIndecomposable
-----------------------------------------------------------------------------

-- returns false if an easy decomposition can be found
-- (but does _not_ run the full directSummands algorithm)
-- returns true if the module is certifiably indecomposable
-- returns null for non-conclusive results
isIndecomposable = method(Options => { Strategy => null, Verbose => false })
isIndecomposable CoherentSheaf := o -> F -> isIndecomposable(module prune F, o)
isIndecomposable Module := o -> M -> M.cache.isIndecomposable ??= tryHooks(
    (isIndecomposable, Module), (o, M), (o, M) -> (
	if 1 < debugLevel then printerr("isIndecomposable was inconclusive. ",
	    "Try extending the field or pruning the sheaf.")))

-- this strategy checks if:
-- * M has only one degree zero endomorphism, namely identity, or
-- * all degree zero endomorphisms of M are zero mod maximal ideal
-- if a non-identity idempotent is found, it is cached in M
addHook((isIndecomposable, Module), Strategy => "IdempotentSearch", (opts, M) -> (
	(idemp, certified) := findBasicIdempotents(M, opts);
	if #idemp > 0 then ( if opts.Verbose then printerr "module is decomposable!";  false ) else
	if certified  then ( if opts.Verbose then printerr "module is indecomposable!"; true )
    ))

-- TODO
--addHook((isIndecomposable, Module), Strategy => TorsionFree, (opts, M) -> (
--	if isTorsionFree M and isDomain M
--	and degree M // degree R <= 1 then return true))

-----------------------------------------------------------------------------
-* Development section *-
-----------------------------------------------------------------------------

--directSummands Matrix  := List => opts -> f -> apply(directSummands(coker f,  opts), presentation)
-* TODO: not done yet
diagonalize = M -> (
    m := presentation M;
    elapsedTime A := End M; -- most time consuming step
    elapsedTime B := basis(degree 1_(ring M), A);
    h = generalEndomorphism M;
    N0 = image homomorphism B_{idem};
    N = prune N0;
    psi = inverse N.cache.pruningMap; -- map N0 --> N
    phi = map(N0, M, homomorphism B_{idem}); -- map M --> N0
    f = psi * phi; -- map M --> N
    h' = f * h * inverse f;
    source h' == N;
    target h' == N;
    h'
    )
*-

--directSummands Complex := List => opts -> C -> () -- TODO: should be functorial

-----------------------------------------------------------------------------
-* Test section *-
-----------------------------------------------------------------------------

load "./DirectSummands/tests.m2"

-----------------------------------------------------------------------------
-* Documentation section *-
-----------------------------------------------------------------------------

beginDocumentation()

load "./DirectSummands/docs.m2"

end--

restart
needsPackage "DirectSummands"
elapsedTime check "DirectSummands" -- ~135s

uninstallPackage "DirectSummands"
restart
viewHelp installPackage "DirectSummands"
viewHelp directSummands
viewHelp

end--
restart
debug needsPackage "DirectSummands"


R = kk[x,y,z];
n = 1000
d = {100}
elapsedTime smartBasis(0, Hom(R^n, R^d));
elapsedTime smartBasis(0, Hom(R^n, R^d, DegreeLimit => 0));
