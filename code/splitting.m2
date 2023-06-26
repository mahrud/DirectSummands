needs "helpers.m2"
needs "frobenius.m2"

-- needed for frobeniusDirectImage
--path = append(path, "~/sasha/code/")
--needs "~/sasha/code/frobenius.m2"

-- this is a kludge to handle the case when h^2 = 2h; note: assume m != 0
reduceScalar = m -> if m == 0 then m else m // scan(flatten entries m, x -> if not zero x then break x)
isIdempotent = h -> reduceScalar(h^2) == reduceScalar h

-- TODO: perhaps also take degree into account
CoherentSheaf ? CoherentSheaf :=
Module ? Module := (M, N) -> rank M ? rank N

-- Note: M may need to be extended to a field extensions
summands = method(Options => { Verbose => true })
summands Module := List => opts -> (cacheValue symbol summands) (M -> sort(
    if opts.Verbose then printerr("encountered summand of rank: ", toString rank M);
    if 1 < #components M then return flatten apply(components M, summands);
    elapsedTime A := End M; -- most time consuming step
    elapsedTime B := basis(degree 1_(ring M), A); -- cached version causes issues!
    -- FIXME: this currently does not find _all_ idempotents
    idem := position(cols B, f -> isIdempotent homomorphism f and homomorphism f != id_M);
    -- TODO: parallelize
    -- TODO: restrict End M to each summand and pass it on
    if idem === null then {M} else flatten join(
	summands(prune image homomorphism B_{idem}, opts),
	summands(prune coker homomorphism B_{idem}, opts))
    ))
-- TODO: is this fine?
summands CoherentSheaf := List => opts -> F -> apply(summands(module F, opts), N -> sheaf(variety F, N))
--summands Matrix  := List => opts -> f -> () -- TODO: should be functorial
--summands Complex := List => opts -> C -> () -- TODO: should be functorial

-- TODO: not done yet
diagonalize = M -> (
    m := presentation M;
    elapsedTime A := End M; -- most time consuming step
    elapsedTime B := basis(degree 1_(ring M), A);
    -- FIXME: this is currently not _all_ idempotents
    --homs := select(cols B, f -> isIdempotent f and homomorphism f != id_M);
    --if #homs == 0 then {M} else flatten apply(homs, f -> summands image homomorphism f)
    )

end--
restart
needs "splitting.m2"

-- basic multigraded test
R = kk[x,y,z] ** kk[a,b,c]
M = R^{{0,0},{0,1},{1,0},{-1,0},{0,-1},{1,-1},{-1,1}}
assert(prune directSum summands M == M)

-- presentation of the Horrocks-Mumford bundle
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

FHM = prune homology(alphad,alpha);
assert(rank FHM == 2)
assert(summands FHM == {FHM}) -- ~30s for End(FHM), ~110s for basis; ~35s in ZZ/2
