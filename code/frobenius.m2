needs "helpers.m2"
needsPackage "PushForward"
--needsPackage "Complexes"

frobeniusMap = method()
frobeniusMap(Ring, ZZ) := (R, e) -> frobeniusMap(e, R)
frobeniusMap(ZZ, Ring) := (e, R) -> (
    p := char R;
    -- TODO: cache these rings for each e
    Rpe := newRing(R, Degrees => p^e * degrees R);
    map(R, Rpe, apply(gens R, g -> g^(p^e))))

decomposeFrobeniusPresentation = (e, f) -> (
    p := char ring f;
    -- TODO: make this work for multigradings
    tarclasses := apply(p^e, i -> positions(degrees target f, deg -> deg % p^e == {i}));
    srcclasses := apply(p^e, i -> positions(degrees source f, deg -> deg % p^e == {i}));
    apply(tarclasses, srcclasses, (tarclass, srcclass) -> submatrix(f, tarclass, srcclass)))

frobeniusPushforward = method()
frobeniusPushforward(Thing, ZZ)   := (T, e) -> frobeniusPushforward(e, T)
frobeniusPushforward(ZZ, Ring)    := (e, R) -> frobeniusPushforward(e, module R)
frobeniusPushforward(ZZ, Ideal)   := (e, I) -> frobeniusPushforward(e, quotient I)
frobeniusPushforward(ZZ, Module)  := (e, M) -> (
    f := presentation pushFwd(frobeniusMap(e, ring M), M);
    if not isHomogeneous f then coker f
    else directSum apply(decomposeFrobeniusPresentation(e, f), coker))
frobeniusPushforward(ZZ, Matrix)  := (e, f) -> (
    g := pushFwd(frobeniusMap(e, ring f), f);
    if not isHomogeneous g then g
    else directSum decomposeFrobeniusPresentation(e, g))
--frobeniusPushforward(ZZ, Complex) := (e, C) -> () -- TODO

frobeniusPushforward(ZZ, SheafOfRings)  := (e, N0) -> frobeniusPushforward(e, N0^1)
frobeniusPushforward(ZZ, CoherentSheaf) := (e, N) -> (
    R := ring N;
    p := char R;
    --FN := frobeniusPushforward(e, module N);
    -- TODO: prune sheaf doesn't work with toric varieties
    -- also, why do this?
    --prune sheaf image basis(max degrees FN, FN)
    --
    -- FN := pushFwd(frobeniusMap(e, R), module N);
    -- gendeg := p^e * (max degrees FN // p^e);
    -- FNs := prune sheaf image basis(gendeg, FN);
    -- Fmatrix := sub(presentation module FNs, R);
    -- (tardegs, srcdegs) := toSequence(-degrees Fmatrix // p^e);
    -- prune sheaf coker map(R^tardegs,  R^srcdegs, Fmatrix)
    FN := first components frobeniusPushforward(e, module N);
    Fmatrix := sub(presentation FN, R);
    (tardegs, srcdegs) := toSequence(-degrees Fmatrix // p^e);
    -- TODO: add code to reorder summands of presentation?
    sheaf prune coker map(R^tardegs,  R^srcdegs, Fmatrix)
    )

end--
restart
needs "frobenius.m2"
needs "splitting.m2"

-- Two cubics on P^2_(ZZ/2)
X = toricProjectiveSpace(2, CoefficientRing => ZZ/2)
S = ring X
I = ideal(x_0^3+x_1^3+x_2^3)
J = ideal(x_0^3+x_0^2*x_1+x_1^3+x_0*x_1*x_2+x_2^3)

R = quotient I
M = frobeniusPushforward(1, module OO_(Proj R))
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

--
R = quotient I
M1 = frobeniusPushforward(1, module OO_(Proj R))
M2 = frobeniusPushforward(2, module OO_(Proj R))
f = presentation M
M0 = prune coker frobeniusPushforward(1, f)
