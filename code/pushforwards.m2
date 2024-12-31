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
	degs := degree \ f \ gens R;
	-- if the variables are sent to different degrees
	if length unique degs > 1 then return pushFwd(f, M);
	deg := sum degs_0;
	-- TODO: erases degree map and degree lift
	S' := newRing(S, Degrees => sum \ degrees S);
	R' := newRing(R, Degrees => deg * degrees R);
	g := map(S', R', sub(matrix f, S'));
	N := pushForward(g, M ** S');
	-- TODO: not multigraded: a // deg won't work if deg is multigraded
	ginv := map(R, source g, gens R, DegreeMap => a -> a // deg);
	directSum apply(decomposePushforwardPresentation(deg, f, N), m -> coker ginv m))
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
needs "finite.m2"

needsPackage "NormalToricVarieties"
P1 = toricProjectiveSpace 1
P2 = toricProjectiveSpace 2
psi = map(P2, P1, matrix{{-2}, {1}})
--psi = map(P2, P1, matrix{{1}, {2}})
assert isWellDefined psi
ideal psi

R = ring P2
S = ring P1 
f = inducedMap psi
ker f

toricFinitePushforward psi
psi

G = myPushFwd(f, OO_P1^1)
L = summands myPushFwd(f, S^1)
assert all(L, isHomogeneous)
needsPackage "IntegralClosure"
assert isNormal quotient ideal relations module G

T = coker transpose vars S

M = myPushFwd(f, T)
assert isHomogeneous M
L = summands M
assert all(L, isHomogeneous)

-- FIXME: not isomorphic or map {{1},{1}}
G = myPushFwd(f, sheaf T)
F = myPushFwd(f, dual cotangentSheaf P1)
assert first isIsomorphic(F, G) -- FIXME

X = Proj quotient ann M
-- X is smooth <=> H is locally free
H = sheaf(X, module F ** quotient ann M)
T' = tangentSheaf X

L = H ** dual H
-- H is locally free of rank 1 <=> L is the trivial line bundle
OO_X^1 == prune L
1 == rank HH^0(X, L)

r = 1
0 == fittingIdeal(r - 1, module G ** quotient ann module G)
decompose fittingIdeal(r, module G ** quotient ann module G)
rank' module G
first fitting ideal of M

--
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

--
restart
needs "pushforwards.m2"
needsPackage "NormalToricVarieties"
--needs "ample.m2"

X = (toricProjectiveSpace 1)^**2
Y = toricProjectiveSpace 3
R = ring Y
S = ring X
f = inducedMap map(Y, X, matrix {{0, 1}, {1, 0}, {1, 1}})
--f = map(S, R, {x_0*x_2,x_0*x_3,x_1*x_2,x_1*x_3}, DegreeMap => a -> a#0 * {1,1}, DegreeLift => a -> a#0)
f = map(S, coimage f, f, DegreeMap => f.cache.DegreeMap, DegreeLift => f.cache.DegreeLift);
M = S^1
myPushFwd(f, M)
pushFwd(f, M)
pushForward(f, M)



restart
needs "pushforwards.m2"
needsPackage "NormalToricVarieties"

X = toricProjectiveSpace(2, CoefficientRing => ZZ/3)
S = ring X

frobeniusPushforward(1, S)
frobeniusPushforward(1, OO_X^{1})
components oo
