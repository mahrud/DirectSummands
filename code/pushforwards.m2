needsPackage "PushForward"
debug needsPackage "DirectSummands"
needsPackage "Polyhedra"

importFrom_Core {"concatCols"}

cols = m -> apply(numcols m, j -> m_{j})
vecs = m -> entries transpose m

zonotopePoints = method()
zonotopePoints Matrix := eff -> (
    -- approximation of the half-open zonotope
    -- TODO: 1/1000 is hardcoded, should it be increased based on eff?
    Z := sum apply(cols eff, c -> convexHull(0*c | (1-1/1000) * c));
    L := latticePoints sum apply(cols eff, c -> convexHull(0*c | 1 * c));
    -- Trick: it's _much_ faster to find lattice lattice points of L \supset Z
    -- and check containment in Z than to find lattice points of Z!
    n := #L; L = concatCols select(L, p -> contains(Z, p));
    << "-- number of points in the half-open polytope: " << numcols L << " / " << n << endl;
    L_(sortColumns L))
--zonotopePoints = memoize zonotopePoints

decomposePushforwardPresentation = (d, f, N) -> (
    m := presentation N;
    tardegrees := degrees target m;
    srcdegrees := degrees source m;
    -- TODO: check this for multigraded or nonstandard graded case
    cube := vecs zonotopePoints effGenerators source f;
    tarclasses := apply(cube, i -> positions(tardegrees, deg -> deg % d == i));
    srcclasses := apply(cube, i -> positions(srcdegrees, deg -> deg % d == i));
    -- sorts the degrees of source and column
    tarclasses = apply(tarclasses, ell -> ell_(last \ sort \\ reverse \ toList pairs tardegrees_ell));
    srcclasses = apply(srcclasses, ell -> ell_(last \ sort \\ reverse \ toList pairs srcdegrees_ell));
    apply(tarclasses, srcclasses, (tarclass, srcclass) -> submatrix(m, tarclass, srcclass)))

-- TODO: replace PushForward
myPushFwd = method()
-- TODO: module Ring should be cached
myPushFwd RingMap := f -> myPushFwd(f, module target f)
-- TODO: cache this
myPushFwd(RingMap, Module) := (f, M) -> (
    (S, R) := (target f, source f);
    if ker f == 0 then (
	degs := apply(gens R, x -> degree f(x));
	-- if the variables are sent to different degrees
	if length unique degs > 1 then return pushFwd(f);
	deg := first degs_0;
	-- TODO: erases degree map and degree lift
	g := map(S, newRing(R, Degrees => deg * degrees R), f);
	N := myPushForward(g, M);
	-- TODO: not multigraded
	directSum apply(decomposePushforwardPresentation(deg, f, N), m -> coker sub(m, R)))
	--tardegs := apply(-flatten degrees cover N, d -> (d % deg) + d // deg);
	--coker map(R^tardegs, , sub(presentation N, R)))
    else (
	-- TODO: erases degree map and degree lift
	-- factor f as a surjection h and injection g
	h := map(coimage f, R, gens coimage f);
	g  = map(S, coimage f, f, DegreeMap => f.cache.DegreeMap);
	myPushForward(h, myPushFwd(g, M)))
    )
--
myPushFwd(RingMap, CoherentSheaf) := (f, F) -> sheaf first components myPushFwd(f, module F)

end--

restart
needs "pushforwards.m2"

needsPackage "NormalToricVarieties"
P1 = toricProjectiveSpace 1
P2 = toricProjectiveSpace 2
psi = map(P2, P1, matrix{{-2}, {1}})
assert isWellDefined psi
ideal psi

R = ring P2
S = ring P1 
f = inducedMap psi
ker f

T = coker transpose vars S

M = myPushFwd(f, T)
assert isHomogeneous M
L = summands M

-- FIXME: not isomorphic or map {{1},{1}}
G = myPushFwd(f, sheaf T)
F = myPushFwd(f, dual cotangentSheaf P1)
assert first isIsomorphic(module F, module G)

X = Proj quotient ann M
-- X is smooth <=> H is locally free
H = sheaf(X, module G ** quotient ann M)
T' = tangentSheaf X

hilbertPolynomial T'
hilbertPolynomial F
hilbertPolynomial G
hilbertPolynomial H

L = G' ** dual G'
-- H is locally ree <=> L is the trivial line bundle
OO_X^1 == prune L
1 == rank HH^0(X, L)

r = 1
0 == fittingIdeal(r - 1, module G ** quotient ann module G)
decompose fittingIdeal(r, module G ** quotient ann module G)
rank' module G
first fitting ideal of M


support Module := M -> quotient ann M
rank' = M -> rank tensor(M, support M)
rank' \ L


-----------
X = weightedProjectiveSpace {1,1,2}
P3 = toricProjectiveSpace 3

R = ring P3
S = ring X
-- psi = map(P3, X, ???)
f = map(S, R, {S_0^2, S_0*S_1, S_1^2, S_2}, DegreeMap => a -> 2 * a)
M = myPushFwd(f, S^{-2})
isHomogeneous M
