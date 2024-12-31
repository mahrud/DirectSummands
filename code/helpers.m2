needsPackage "NormalToricVarieties"
debug needsPackage "VirtualResolutions"
needsPackage "FourierMotzkin"
needsPackage "LinearTruncations"
debug needsPackage "Truncations"
needsPackage "Isomorphism" -- because TateOnProducts overwrites isIsomorphic

kk = ZZ/101

importFrom_Core {"nonnull"}

-- erase the symbols first
importFrom(Package, List) := (P, x) -> apply(nonnull x, s -> if not currentPackage#"private dictionary"#?s then currentPackage#"private dictionary"#s = P#"private dictionary"#s)

importFrom_"SpectralSequences" {"spots"}
spots GradedModule := lookup(spots, ChainComplex)
spots ChainComplexMap := f -> select(keys f, i -> class i === ZZ)
support GradedModule := lookup(support, ChainComplex)

- Sequence := Sequence => p -> apply(p, minus)

if instance(PP, Symbol) then PP = method()
PP ZZ   := NormalToricVariety => memoize(n -> toricProjectiveSpace(n, CoefficientRing => kk))
PP List := NormalToricVariety => memoize(w -> weightedProjectiveSpace(w, CoefficientRing => kk))

cartesianProduct List := lookup(cartesianProduct, Sequence)

importFrom_Core {"concatCols", "concatRows"}
concatMats = T -> concatRows for row in T list concatCols row
rows = m -> apply(numrows m, i -> m^{i})
cols = m -> apply(numcols m, j -> m_{j})
vecs = m -> entries transpose m
-- pads columns of M with n columns
pad(Matrix, ZZ) := (M, n) -> M | map(target M, (ring M)^(max(n - numcols M, 0)), 0)

ceiling Matrix := m -> matrix table(numrows m, numcols m, (i, j) -> ceiling m_(i,j))
floor   Matrix := m -> matrix table(numrows m, numcols m, (i, j) -> floor   m_(i,j))
graph = (L, f) -> apply(L, x -> (x, f(x)))

-- TODO: is this the best way?
-- TODO: move to Chambers?
gale = m -> gens ker (if coker m == 0 then identity else transpose) m
-- TODO: can we use this? galeDualMatrix := matrix (fromWDivToCl X)^torsionlessCoord;

-- return the submatrix with given degrees of target and source
submatrixByDegrees(Matrix, Sequence) := (m, degs) -> (
    (tar, src) := degs;
    col := if src =!= null then positions(degrees source m, deg -> member(deg, src));
    row := if tar =!= null then positions(degrees target m, deg -> member(deg, tar));
    submatrix(m, row, col))

intersect(Set, Set) := (S, T) -> select(keys S, k -> T#?k)

-- TODO: add to NormalToricVarieties
cotangentSheaf(List, NormalToricVariety) := CoherentSheaf => opts -> (a, X) -> (
    assert(#a == #(Xs := components X));
    if X#?(cotangentSheaf, a)
    then X#(cotangentSheaf, a) 
    else X#(cotangentSheaf, a) = tensor apply(#a, i -> pullback(X^[i], cotangentSheaf(a#i, Xs#i))))

-- returns K_X
canonicalDivisor = X -> toricDivisor X

-- redefining this from NormalToricVarieties/ToricVarieties.m2 to allow P(1,2)
weightedProjectiveSpace List := NormalToricVariety => opts -> q -> (
    if #q < 2 then error "-- expected a list with at least two elements";
    if not all (q, i -> i > 0) then error "-- expected positive integers";
    d := #q-1;
--    if not all (subsets (q,d), s -> gcd s === 1) then (
--    	error ("--  the " | toString d | "-elements have a common factor")
--	);
    rayList := entries kernelLLL matrix {q};
    coneList := subsets (d+1,d);
    normalToricVariety (rayList, coneList,
    	CoefficientRing => opts.CoefficientRing, 
	Variable        => opts.Variable))

-- redefining nefGenerators to be in class group instead of Picard group
-- TODO: why did I need this?
-*
nefGenerators NormalToricVariety := Matrix => X -> (
    if isDegenerate X then 
	error "-- not implemented for degenerate varieties";
    clX := classGroup X;
    if clX == 0 then return matrix {{}};
    if not isFreeModule clX then (
	smithMatrix := presentation clX;
	torsionlessCoord := select (rank target smithMatrix, 
	    i -> smithMatrix^{i} == 0
	    )
	)
    else torsionlessCoord = toList (0.. rank clX - 1);
    galeDualMatrix := matrix (fromWDivToCl X)^torsionlessCoord;
    innerNormals := matrix {for sigma in max X list (
	    sigma' := select(# rays X, i -> not member(i, sigma));
	    dualCone := fourierMotzkin galeDualMatrix_sigma';
	    dualCone#0 | dualCone#1 | -dualCone#1 
	    )
	};
    coneGens := fourierMotzkin innerNormals;
    coneGens = coneGens#0 | coneGens#1 | - coneGens#1;
    if not isFreeModule clX then (
    	rowCounter := 0;
	coneGens = matrix for i to rank target smithMatrix - 1 list (
    	    if member(i, torsionlessCoord) then (
		rowCounter = rowCounter+1;
		{coneGens^{rowCounter-1}}
		)
    	    else {0*coneGens^{0}}
	    )
	);
--    fromPic := matrix fromPicToCl X;
--    indexOfPic := abs lcm (minors( rank source fromPic, fromPic^torsionlessCoord))_*;
--    (indexOfPic * coneGens) // fromPic 
    coneGens
    );
*-

coh = memoize(rank @@ cohomology)
fano = memoize smoothFanoToricVariety
mbasis = memoize basis

SheafOfRings  List := CoherentSheaf => (O,a) -> O^1 toSequence a
CoherentSheaf List := CoherentSheaf => (F,a) -> F toSequence a

-- TODO: fix in the Core
Module ^ ZZ := Module => (M,i) -> if i > 0 then directSum (i:M) else 0*M

importFrom_Core {"printerr"}

-- remove boxes from netList
--(first frames netList)#0 = (first frames netList)#0 ++ { Boxes => false }
-- list c entries per row instead of 1
netList(ZZ, VisibleList) := o -> (c, L) -> netList(o, pack_c L)

--plotRegion = method()
plotRegion(Function, List, List) := (func, low, high) -> printerr netList(Boxes => false,
    table(last(high - low) + 1, first(high - low) + 1,
	(i, j) -> if func(j + first low, last high - i) then "." else "x"))
plotRegion(List, List, List) := (L, low, high) -> plotRegion(
    (x, y) -> any(L, ell -> x >= ell_0 and y >= ell_1), low, high)

-- functions for checking regularity for arbitrary smooth projective toric variety
-- whether M is d-regular
isRegular = (X, M, d) -> (
    N := nefGenerators X;
    r := rank source N;
    F := sheaf(X, M);
    coh(0, X, F d) == hilbertFunction_d M and
    all(1 .. dim X, i -> all(toList(i:0)..toList(i:r-1),
	    ell -> 0 == coh(i, X, F(d - sum entries transpose N_ell)))))
-- find regularity of M
-- TODO: make sure findRegion respects the Nef cone!
findRegularity = (X, M, low, high) -> findRegion({low, high}, M, (ell, M) -> isRegular(X, M, ell))
-- plot regularity of M, for X with Picard rank 2
plotRegularity = (X, M, low, high) -> plotRegion(findRegularity(X, M, low, high), low, high)

-- patch of a bug
degrees ChainComplex :=
supportOfTor ChainComplex := F -> (
    for i from min F to max F list (
	degs := unique degrees F_i;
	if #degs == 0 then continue else degs))

sot = netList @@ supportOfTor

-- compMin/compMax with respect to general cones
needsPackage "Polyhedra"
- Cone := C -> coneFromVData(-rays C) -- TODO: there's room for improvement
ring Cone := C -> ring linealitySpace C
coneMax = (C, L) -> first entries transpose sub(vertices intersection apply(unique L, ell -> C + convexHull matrix vector ell), ring C)
--coneMax = memoize coneMax
coneMin = (C, L) -> coneMax(-C, L)
--coneMin = memoize coneMin
if instance(coneComp, Symbol) then
coneComp = (C, u, v) -> (
    --if u == v                            then symbol== else
    if contains(C, matrix vector(v - u)) then symbol <= else
    if contains(C, matrix vector(u - v)) then symbol > else incomparable)
-*
nefX = coneFromVData nefGenerators X
aa = coneMin(nefX, L = degrees K_0)
K_0 == truncate(aa, K_0)
*-

getNefDivisor = X -> toricDivisor(
    first entries transpose solve(fromWDivToCl X, sum cols nefGenerators X), X)

-- much, MUCH, faster version!
fan List := Fan => inputCones -> (
    -- if #inputCones == 0 then return fan coneFromVData matrix{{0}};
    A := apply(inputCones, C ->
	if instance(C, Cone) then cols rays C else
	if instance(C, Matrix) then cols C else C);
    B := unique flatten A;
    H := hashTable apply(toList pairs B, reverse);
    -- FIXME: fails if there are no rays
    rayList := concatCols B;
    maxList := apply(A, C -> apply(C, ray -> H#ray));
    fan(rayList, -* linealityGens, *- maxList))

-- cached version
coneFromVData Matrix := (cacheValue symbol cone) (R -> (
    r := ring R;
    -- Generating the zero lineality space LS
    LS := map(target R, r^0,0);
    coneFromVData(R,LS)
    ))

show NormalToricVariety := X -> (
    if dim X > 3 then error "cannot visualize fans in dimensions higher than 3";
    name = temporaryFileName() | ".pm";
    name << concatenate(///
	use application "fulton";
	declare $F = new PolyhedralFan(
	    INPUT_RAYS => ///, toString apply(new Array from rays X, rho -> new Array from rho), ///,
	    INPUT_CONES => ///, toString apply(new Array from max X, sigma -> new Array from sigma), ///);
	declare $X = new NormalToricVariety($F);
	$X->VISUAL;
	///) << close;
    run("polymake --script " | name))
