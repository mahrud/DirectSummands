needs "helpers.m2"
needs "frobenius.m2"
needs "idempotents.m2"

-* needed for toric frobeniusDirectImage
path = append(path, "~/sasha/code/")
needs "~/sasha/code/frobenius.m2"
*-

try (
importFrom_Core {"submatrixFree", "listZZ", "rawSubmatrix"};
submatrixFree = (m, rows, cols) -> (if rows === null
    then rawSubmatrix(raw cover m, listZZ cols)
    else rawSubmatrix(raw cover m, listZZ rows,
	if cols =!= null then listZZ cols else 0 .. numgens source m - 1))
)

-- this is a kludge to handle the case when h^2 = ah
reduceScalar = m -> m // scan(unique flatten entries m | {1}, x -> if isConstant x and not zero x then break x)
isIdempotent = h -> reduceScalar(h^2) == reduceScalar h

-- TODO: perhaps also take degree into account
CoherentSheaf ? CoherentSheaf :=
Module ? Module := (M, N) -> rank M ? rank N

-- TODO: add this as a strategy to basis
smartBasis = (deg, M) -> (
    if instance(deg, ZZ) then deg = {deg};
    C := coneFromVData effGenerators ring M;
    degs := select(unique degrees M, d -> coneComp(C, d, deg) == symbol <=); -- TODO: could be faster
    -- M_(positions(degrees M, d -> d == deg))
    if degs == {deg} then map(M, , submatrixByDegrees(gens cover M, (, degs)))
    -- FIXME: this line forgets the homomorphism information
    --else basis(deg, image map(M, , submatrixByDegrees(gens cover M, (, degs))))) -- TODO: confirm that this is faster
    else basis(deg, M)) -- caching this causes issues!

-- Note: M may need to be extended to a field extensions
-- TODO: cache the inclusion maps
summands = method(Options => { Verbose => true, Endo => null }) --renamed End to Endo since End is taken as a method already
summands Module := List => opts -> (cacheValue symbol summands) (M -> sort(
    -- Note: rank does weird stuff if R is not a domain
    if opts.Verbose then printerr("encountered summand of rank: ", toString rank M);
    if 1 < #components M then return flatten apply(components M, summands);
    elapsedTime A := End M; -- most time consuming step
    elapsedTime B := smartBasis(degree 1_(ring M), A);
    -- FIXME: this currently does not find _all_ idempotents
    -- FIXME: why is B_{0} so slow for the Horrocks-Mumford example?!
    idem := if numcols B > 1 then position(cols B, f -> isIdempotent homomorphism f and homomorphism f != id_M);
    -- TODO: parallelize
    -- TODO: restrict End M to each summand and pass it on
    if idem === null then {M} else flatten join(
	h := homomorphism B_{idem};
	M1 := prune image h;
	M2 := prune coker h;
	-- Projection maps to the summands
	--p1 := inverse M1.cache.pruningMap * map(image h, M, h);
	--p2 := inverse M2.cache.pruningMap * map(coker h, M, h);
	--B1.cache.homomorphism = f -> map(M1, M1, adjoint'(p1 * f * inverse p1, M1, M1), Degree => first degrees source f + degree f);
	summands(M1, opts),
	summands(M2, opts))
    ))
summands CoherentSheaf := List => opts -> F -> apply(summands(module F, opts), N -> sheaf(variety F, N))
--summands Matrix  := List => opts -> f -> () -- TODO: should be functorial
--summands Complex := List => opts -> C -> () -- TODO: should be functorial

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

end--
restart
needs "splitting.m2"

-- basic multigraded test
R = kk[x,y,z] ** kk[a,b,c]
M = R^{{0,0},{0,1},{1,0},{-1,0},{0,-1},{1,-1},{-1,1}}
assert isIsomorphic(directSum summands M, M)

-- presentation of the Horrocks-Mumford bundle
restart
needs "splitting.m2"
needsPackage "BGG"
S = ZZ/32003[x_0..x_4];
E = ZZ/32003[e_0..e_4,SkewCommutative=>true];
alphad = matrix{{e_4*e_1, e_2*e_3},{e_0*e_2, e_3*e_4},
                {e_1*e_3, e_4*e_0},{e_2*e_4, e_0*e_1},
                {e_3*e_0, e_1*e_2}};
alphad=map(E^5,E^{-2,-2},alphad)
alpha=syz alphad
alphad=beilinson(alphad,S);
alpha=beilinson(alpha,S);

M = FHM = prune homology(alphad,alpha);
assert(rank FHM == 2)
elapsedTime assert(summands FHM == {FHM}) -- ~30s for End(FHM), ~110s for basis; ~35s in ZZ/2; now down to ~11

-- is smartBasis useful? yes!
restart
needs "splitting.m2"
R = (ZZ/7)[x,y,z]/(x^3+y^3+z^3);
X = Proj R;
M = End module frobeniusPushforward(OO_X,1);
-- 0.39809 seconds elapsed
elapsedTime basis({3}, M);
-- 0.171702 seconds elapsed
elapsedTime smartBasis({3}, M);


restart
needs "splitting.m2"

