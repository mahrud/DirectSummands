---------------------------------------------------------------------------
-- PURPOSE : to compute direct summands of modules and coherent sheaves
--
-- UPDATE HISTORY : created Oct 2023
--
-- TODO :
-- 1. implement over Dmodules and other non-commutative rings
-- 2. try to find all irreducible idempotents from End M using representation theory
-- 3. cache maps to the summands
-- 4. rewrite (isDirectSum, Module)
-- 5. implement diagonalize for matrices (and later, complexes)
-- 6. restrict and pass End to the summands
-- 7. check for isomorphic summands
-- 8. make summands work over ZZ (currently rank fails)
---------------------------------------------------------------------------
newPackage(
    "DirectSummands",
    Version => "0.1",
    Date => "25 Oct 2023",
    Headline => "decompositions of modules and coherent sheaves",
    Authors => {
	{ Name => "Devlin Mallory", Email => "malloryd@math.utah.edu", HomePage => "https://math.utah.edu/~malloryd/"},
	{ Name => "Mahrud Sayrafi", Email => "mahrud@umn.edu",         HomePage => "https://math.umn.edu/~mahrud/"}
	},
    Keywords => { "Commutative Algebra" },
    PackageImports => {
	"Isomorphism",     -- for isIsomorphic
	"Polyhedra",       -- for coneFromVData and coneComp
	"PushForward",     -- only for frobenius.m2
	"RationalPoints2", -- for rationalPoints in findIdempotent
	"Truncations",     -- for effGenerators
	"Varieties",
	},
    AuxiliaryFiles => true,
    DebuggingMode => true
    )

export {
    -- methods
    "directSummands", "summands" => "directSummands",
    "findIdempotent", "findIdem" => "findIdempotent",
    "findSplitInclusion",
    "isomorphismTally",
    -- symbols
    "ExtendGroundField",
    "Indecomposable",
    "Recursive",
    "Tries",
    -- frobenius methods
    "frobeniusMap",
    "frobeniusRing",
    "frobeniusPullback",
    "frobeniusPushforward",
    "frobeniusTwist",
    "potentialExtension",
    "changeBaseField"
    }

importFrom_Core {
    "raw", "rawReshape",
    "rawNumberOfColumns",
    "rawNumberOfRows",
    }

-----------------------------------------------------------------------------
-* Code section *-
-----------------------------------------------------------------------------

-- helpers for computing Frobenius pushforwards of modules and sheaves
-- TODO: move to PushForward package?
load "./DirectSummands/frobenius.m2"
-- helpers for finding random idempotents of a module
load "./DirectSummands/idempotents.m2"

-----------------------------------------------------------------------------
-- Things to move to the Core
-----------------------------------------------------------------------------

-- return the submatrix with given degrees of target and source
submatrixByDegrees(Matrix, Sequence) := (m, degs) -> (
    (tar, src) := degs;
    col := if src =!= null then positions(degrees source m, deg -> member(deg, src));
    row := if tar =!= null then positions(degrees target m, deg -> member(deg, tar));
    submatrix(m, row, col))

-- this defines sorting on modules and sheaves
CoherentSheaf ? CoherentSheaf :=
Module ? Module := (M, N) -> if rank M != rank N then rank M ? rank N else degrees M ? degrees N

-- TODO: move to Core
position(ZZ, Function) := o -> (n, f) -> position(0..n-1, f)
-- TODO: this is different from position(List,List,Function)
position' = method()
position'(VisibleList, VisibleList, Function) := (B, C, f) -> for b in B do for c in C do if f(b, c) then return (b, c)
position'(ZZ,          ZZ,          Function) := (B, C, f) -> position'(0..B-1, 0..C-1, f)

-- TODO: what generality should this be in?
-- WANT:
--   R ** ZZ/101 to change characteristic
--   R ** S to change coefficient ring
-- TODO: can you change the ground field but keep the tower structure?
QuotientRing   ** GaloisField :=
PolynomialRing ** GaloisField := (R, L) -> (
    -- TODO: in general we may want to keep part of the ring tower
    A := first flattenRing(R, CoefficientRing => null);
    quotient sub(ideal A, L monoid A))

changeBaseField = method()
changeBaseField(GaloisField, Module) := (L, M) -> (
    S := first flattenRing(ring M, CoefficientRing => null);
    K := coefficientRing S;
    if class K =!= GaloisField then (
        R0 := quotient sub(ideal S, L monoid S);
        return directSum apply(components M,
	    N -> coker sub(presentation N, R0)));
    -- don't needlessly create new rings:
    if K.order === L.order then return M;
    i0 := map(L, K);
    LS := L(monoid S);
    i1 := map(LS, ring ideal S, gens LS | { i0 K_0 });
    R := quotient i1 ideal S;
    i := map(R, S, i1);
    directSum apply(components M, N -> i ** N))

-- TODO: come up with a better way to extend ground field of a variety
-- TODO: does this also need to be used for frobenius pushforward?
sheaf' = (X, M) -> try sheaf(X, M) else (
    if instance(X, ProjectiveVariety) then sheaf(Proj ring M, M) else
    if instance(X,     AffineVariety) then sheaf(Spec ring M, M) else
    error "extension of the coefficient field of the base variety is not implemented")

changeBaseField(GaloisField, CoherentSheaf) := (L, F) -> sheaf'(variety F, changeBaseField(L, module F))

nonzero = x -> select(x, i -> i != 0)
nonnull = x -> select(x, i -> i =!= null)

checkRecursionDepth = () -> if recursionDepth() > recursionLimit - 20 then printerr(
    "Warning: the recursion depth limit may need to be extended; use `recursionLimit = N`")

module Module := identity

-- FIXME in the Core:
isiso = lookup(isIsomorphic, Module, Module)
isIsomorphic(Module, Module) := Sequence => o -> (M, N) -> (
    -- TODO: in the free case, handle the Strict => false option, too
    if isFreeModule M and isFreeModule N then (
	if set degrees M == set degrees N then return ( true, null )); -- FIXME: give the map
    (isiso o)(M, N))

isIsomorphic' = method(Options => options isIsomorphic ++ { Tries => 10 })
isIsomorphic'(Module, Module) := opts -> (M, N) -> (
    opts' := selectKeys(opts, k -> (options isIsomorphic)#?k);
    -- TODO: parallelize
    any(opts.Tries, i -> first isIsomorphic(M, N, opts')))

-- TODO: speed this up
-- TODO: implement isIsomorphic for sheaves
-- TODO: add strict option
tallySummands = L -> tally (
    opts := Homogeneous => all(L, isHomogeneous);
    L  = new MutableList from module \ L;
    b := new MutableList from #L : true;
    for i to #L-2 do if b#i then for j from i+1 to #L-1 do if b#j then (
	if isIsomorphic'(L#i, L#j, opts)
	then ( b#j = false; L#j = L#i ));
    new List from L)

isomorphismTally = method()
isomorphismTally List := L -> (
    if not uniform L then error "expected list of elements of the same type";
    if not (class L_0 === Module or class L_0 === CoherentSheaf ) then error "expected list of modules or sheaves";
    opts := Homogeneous => all(L, isHomogeneous);
    --L = new MutableList from L;
    j := 0;
    while j < #L list (
	i := j + 1;
	c := 1;
	while i < #L do (
	    if isIsomorphic'(L#j, L#i, opts)
	    then (
		L = drop(L, {i, i});
		c = c + 1)
	    else i = i + 1);
	j = j + 1;
	(L#(j-1), c)))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

importFrom_Truncations { "effGenerators" }

coneComp = (C, u, v) -> (
    --if u == v                            then symbol== else
    if contains(C, matrix vector(v - u)) then symbol <= else
    if contains(C, matrix vector(u - v)) then symbol > else incomparable)

-- TODO: add this as a strategy to basis
smartBasis = (deg, M) -> (
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

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-- same as flatten(Matrix), but doesn't bother homogenizing the result
flatten' = m -> map(R := ring m, rawReshape(m = raw m, raw R^1, raw R^(rawNumberOfColumns m * rawNumberOfRows m)))

-- not strictly speaking the "lead" coefficient
leadCoefficient Matrix := RingElement => m -> for c to numcols m - 1 do for r to numrows m - 1 do (
    if not zero m_(r,c) then return leadCoefficient m_(r,c))

-- hacky things for CC
-- TODO: move to Core, also add conjugate Matrix, realPart, imaginaryPart, etc.
conjugate RingElement := x -> sum(listForm x, (e, c) -> conjugate c * (ring x)_e)
magnitude = x -> x * conjugate x
isZero = x -> if not instance(F := ultimate(coefficientRing, ring x), InexactField) then x == 0 else (
    leadCoefficient magnitude x < 2^(-precision F))

-- borrowed from Varieties as hack to get around
-- https://github.com/Macaulay2/M2/issues/3407
flattenMorphism = f -> (
    g := presentation ring f;
    S := ring g;
    -- TODO: sometimes lifting to ring g is enough, how can we detect this?
    -- TODO: why doesn't lift(f, ring g) do this automatically?
    map(target f ** S, source f ** S, lift(cover f, S)) ** cokernel g)

leadCoefficient Number := identity

-- this is a kludge to handle the case when h^2 = ah
reduceScalar = m -> if m == 0 then m else map(target m, source m, cover m // leadCoefficient m)
isIdempotent = h -> reduceScalar(h^2) == reduceScalar h
isWeakIdempotent = h -> all(flatten entries flattenMorphism(reduceScalar(h^2) - reduceScalar h), isZero)
--isWeakIdempotent = h -> isZero det cover flattenMorphism(reduceScalar(h^2) - reduceScalar h)

-- TODO: can we return cached summands from the closest field extension?
-- all cached keys: select(keys M.cache, k -> instance(k, Option) and k#0 === symbol directSummands)
cachedSummands = { ExtendGroundField => null } >> o -> M -> (
    if  M.cache#?(symbol summands => o.ExtendGroundField)
    then M.cache#(symbol summands => o.ExtendGroundField) else components M)

-- Note: M may need to be extended to a field extensions
-- TODO: add option to provide a general endomorphism or idempotent
-- TODO: when splitting over a field extension, use cached splitting over summands
-- TODO: cache the inclusion maps
-- Strategies:
-- 1 => use degrees of generators as heuristic to peel off line bundles first
-- 2 => use Hom option DegreeLimit => 0
-- 4 => use Hom option MinimalGenerators => false
-- 8 => precompute Homs before looking for idempotents
directSummands = method(Options => { Recursive => true, Tries => 10, Verbose => true, Strategy => 7, ExtendGroundField => null })
directSummands Module := List => opts -> (cacheValue (symbol summands => opts.ExtendGroundField)) (M -> (
    checkRecursionDepth();
    -- Note: rank does weird stuff if R is not a domain
    -- Note: End does not work for WeylAlgebras or AssociativeAlgebras yet, nor does basis
    R := ring M;
    if not isCommutative R and not isWeylAlgebra R then error "expected a commutative base ring";
    if 0 < debugLevel then printerr("splitting module of rank: ", toString rank M);
    if isFreeModule M then return apply(-degrees M, d -> R^{d});
    --TODO: is there an easy way to check if rank = 1 and M torsionfree?
    if 1 < #components M then return flatten apply(components M, directSummands_opts); -- TODO: parallelize
    if opts.ExtendGroundField =!= null then (
	L := opts.ExtendGroundField;
	L  = if instance(L, ZZ)   then GF(char R, L)
	else if instance(L, Ring) then L else error "expected an integer or a ground field";
	M = changeBaseField(L, directSum cachedSummands M);
	R = ring M);
    -- Attempt to peel off line bundles by observing the degrees of generators
    if opts.Strategy & 1 == 1 then (
	opts = opts ++ { Strategy => opts.Strategy ^^ 1 }; -- so we only try this once
	if 0 < debugLevel then stderr << " -- peeling off rank 1 summands: " << flush;
	L = directSummands(apply(-unique degrees M, d -> R^{d}), M, opts);
	if 0 < debugLevel then stderr << endl << " -- split off " << #L - 1 << " summands!" << endl;
	if 1 < #L then return directSummands(directSum L, opts));
    --
    K := coker vars R;
    zdeg := degree 0_M;
    -- TODO: make "elapsedTime" contingent on verbosity
    elapsedTime A := Hom(M, M, -- most time consuming step
	DegreeLimit       => if opts.Strategy & 2 == 2 then zdeg,
	MinimalGenerators => if opts.Strategy & 4 == 4 then false);
    elapsedTime B := smartBasis(zdeg, A);
    --error 0;
    ///
      T := R(monoid[]);
      use source psi
      A=sub(cover sum for i to numcols B - 1 list a_i * homomorphism B_(i-1), Ra)
      J=trim ideal cover(A^2-A)
      degree eliminate(apply(gens R,i->sub(i,ambient Ra)),  sub(J,ambient Ra)+ideal(Ra))
      decompose J
    ///;
    -- FIXME: this currently does not find _all_ idempotents
    flag := true; -- whether all non-identity homomorphisms are zero mod m
    -- TODO: 10k columns for F_*(OO_X) on Gr(2,4) over ZZ/3 take a long time
    -- TODO: add option to skip this step
    idem := position(numcols B, c -> (
	    h := homomorphism B_{c};
	    if h == id_M or h == 0 then false else (
		if flag and K ** h != 0
		then flag = false;
                --TODO: is it worth asking if K**h is idempotent instead? (in graded/local case)
		isIdempotent h))
	);
    -- check if M is certifiably indecomposable
    if flag then (
	if 0 < debugLevel then printerr("\t... certified indecomposable!");
	M.cache.Indecomposable = true; return {M} );
    -- TODO: parallelize
    h := if idem =!= null then homomorphism B_{idem} else try findIdempotent M;
    -- TODO: add this when the maps M_[w] and M^[w] also work with subsets
    -- M.cache.components =
    if h === null then {M} else (
	-- TODO: restrict End M to each summand and pass it on
	-- TODO: could use 'compose' perhaps
	-- TODO: can we check if M has multiple copies of M0 or M1 quickly?
	M0 := prune image h;
	M1 := prune coker h;
	-- TODO: can we keep homomorphisms?
	--B0.cache.homomorphism = f -> map(M0, M0, adjoint'(p1 * f * inverse p0, M0, M0), Degree => first degrees source f + degree f);
	M0comps := directSummands(M0, opts);
	M1comps := directSummands(M1, opts);
	-- Projection maps to the summands
	c := -1;
	p0 := inverse M0.cache.pruningMap * inducedMap(image h, M, h);
	p1 := inverse M1.cache.pruningMap * inducedMap(coker h, M);
	if #M0comps > 1 then apply(#M0comps, i -> M.cache#(symbol ^, [c += 1]) = M0^[i] * p0) else M.cache#(symbol ^, [c += 1]) = p0;
	if #M1comps > 1 then apply(#M1comps, i -> M.cache#(symbol ^, [c += 1]) = M1^[i] * p1) else M.cache#(symbol ^, [c += 1]) = p1;
	-- Inclusion maps from the summands
	-- TODO: will this always work?
	scan(c + 1, i -> M.cache#(symbol _, [i]) = inverse M.cache#(symbol ^, [i]));
	-- return the lists
	-- TODO: why is this nonzero needed?
	-- TODO: sort these, along with the projections
	nonzero flatten join(M0comps, M1comps))
    ))

-- TODO: if ExtendGroundField is given, change variety
-- TODO: when ExtendGroundField is given, the variety will change!
directSummands CoherentSheaf := List => opts -> F -> apply(directSummands(module F, opts), N -> sheaf'(variety F, N))

-- tests whether L (perhaps a line bundle) is a summand of M
-- Recursive => true (default) attempts to peel as many copies of L as possible
-- FIXME: it's not guaranteed to work, e.g. on X_4 over ZZ/2
-- TODO: cache this
directSummands(Module, Module) := List => opts -> (L, M) -> (
    checkRecursionDepth();
    if ring L =!= ring M then error "expected objects over the same ring";
    if rank L  >= rank M then return {M};
    if 1 < #cachedSummands M then return sort flatten apply(cachedSummands M, N -> directSummands(L, N, opts));
    zdeg := degree 0_M;
    if isFreeModule L then(
        B := smartBasis(zdeg, Hom(M, L, DegreeLimit => zdeg, MinimalGenerators => false));
        --h := for i from 0 to numcols B - 1 do( if isSurjective(b := homomorphism B_{i}) then break matrix{L_0}//b);
        h := for i to opts.Tries - 1 do (
	    b := homomorphism(B * random source B);
            if isSurjective b then break matrix{L_0}//b);)
    else(
        -- we look for a composition L -> M -> L which is the identity
        B = smartBasis(zdeg, Hom(L, M, DegreeLimit => zdeg, MinimalGenerators => false));
        if numcols B == 0 then return {M};
        C := smartBasis(zdeg, Hom(M, L, DegreeLimit => zdeg, MinimalGenerators => false));
        if numcols C == 0 then return {M};
        -- attempt to find a random isomorphism
        h = for i to opts.Tries - 1 do (
	    b := homomorphism(B * random source B);
	    c := homomorphism(C * random source C);
            --TODO: change isIsomorphism to isSurjective?
	    if isIsomorphism(c * b) then break b);
        --is it worth doing the following lines? when does the random strategy above fail?
        if h === null then h = (
	    if opts.Strategy & 8 == 8 then (
	        -- precomputing the Homs can sometimes be a good strategy
	        Bhoms := apply(numcols B, i -> homomorphism B_{i});
	        Choms := select(apply(numcols C, i -> homomorphism C_{i}), j -> isSurjective j);
	        pos := position'(Choms, Bhoms,
		    (c, b) -> isIsomorphism(c * b));
	        if pos =!= null then last pos)
	    else (
	        -- and sometimes too memory intensive
	        ind := position'(numcols C, numcols B,
                    --how to skip c if homomorphism C_{c} is not surjective?
		    (c, b) -> isSurjective homomorphism C_{c} and isIsomorphism(homomorphism C_{c} * homomorphism B_{b}));
	        if ind =!= null then homomorphism B_{last ind})););
    if h === null then return {M};
    if 0 < debugLevel then stderr << concatenate(rank L : ".") << flush;
    -- TODO: can we detect multiple summands of L at once?
    sort flatten join({L}, if not opts.Recursive then {prune coker h}
	else directSummands(L, prune coker h, opts)))

directSummands(CoherentSheaf, CoherentSheaf) := List => opts -> (L, G) -> apply(
    directSummands(module L, module G, opts), N -> sheaf(variety L, N))

-- attempt to peel off summands from a given list of modules
directSummands(List, CoherentSheaf) :=
directSummands(List, Module) := List => opts -> (Ls, M) -> sort (
    if 1 < #cachedSummands M then flatten apply(cachedSummands M, N -> directSummands(Ls, N, opts))
    else fold(Ls, {M}, (L, LL) -> join(drop(LL, -1), directSummands(L, last LL, opts))))

--
isDefinitelyIndecomposable = method()
isDefinitelyIndecomposable Module := M -> M.cache.?Indecomposable
-- TODO: check that the sheaf is pruned also
isDefinitelyIndecomposable CoherentSheaf := M -> isDefinitelyIndecomposable module M

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

-----------------------------------------------------------------------------
-* Development section *-
-----------------------------------------------------------------------------

restart
check needsPackage "DirectSummands"

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


--------
-- summand of 4th syzygy of residue field of ring defined by
-- ideal(y*z,x*z,y^3,x*y^2+z^3,x^2*y,x^3) is indecomposable,
-- but the current method doesn't really show that definitively
