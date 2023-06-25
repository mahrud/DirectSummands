needs "helpers.m2"
needs "frobenius.m2"

-- needed for frobeniusDirectImage
--path = append(path, "~/sasha/code/")
--needs "~/sasha/code/frobenius.m2"

-- this is a kludge to handle the case when h^2 = 2h; note: assume m != 0
reduceScalar = m -> if m == 0 then m else m // scan(flatten entries m, x -> if not zero x then break x)
isIdempotent = h -> reduceScalar(h^2) == reduceScalar h

Module ? Module := (M, N) -> rank M ? rank N

-- Note: M may need to be extended to a field extensions
summands = M -> sort(
    -*if debugLevel > 1 then*- printerr("encountered summand of rank: ", toString rank M);
    --if rank M == 1 then return {M};
    elapsedTime A := End M; -- most time consuming step
    elapsedTime B := basis(degree 1_(ring M), A); -- cached version causes issues!
    --v = (B * random(kk^(rank source B), kk^1))
    --h = homomorphism v    
    --isUnit homomorphism v
    -- FIXME: this is currently not _all_ idempotents
    --homs := select(cols B, f -> isIdempotent f and homomorphism f != id_M);
    --if #homs == 0 then {M} else flatten apply(homs, f -> summands image homomorphism f)
    idem := position(cols B, f -> isIdempotent homomorphism f and homomorphism f != id_M);
    -- TODO: parallelize
    -- TODO: restrict End M to each summand and pass it on
    if idem === null then {M} else flatten join(
	summands prune image homomorphism B_{idem},
	summands prune coker homomorphism B_{idem})
    )
summands = memoize summands

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

-- Two cubics on P^2_(ZZ/2)
X = toricProjectiveSpace(2, CoefficientRing => ZZ/2)
S = ring X
I = ideal(x_0^3+x_1^3+x_2^3)
J = ideal(x_0^3+x_0^2*x_1+x_1^3+x_0*x_1*x_2+x_2^3)

R = quotient I
M = module frobeniusPushforward(1, OO_(Proj R))
M = coker sub(frobeniusPushforward(char S, I), R)
M = coker sub(presentation frobeniusPushforward(1, R), R)
M = coker sub(presentation frobeniusPushforward(R, 1), R)
M = frobeniusPushforward(R, 1)
summands M
assert(summands M == {M})

R = quotient J
M = module frobeniusPushforward(1, OO_(Proj R))
M = coker frobeniusPushforward(char S, J)
M = coker sub(frobeniusPushforward(char S, J), R)
M = frobeniusPushforward(1, R)
summands M
assert(rank \ summands M == {1,1})

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
