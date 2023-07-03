needs "helpers.m2"
needsPackage "PushForward"
--needsPackage "Complexes"

frobeniusRing = method(TypicalValue => Ring)
frobeniusRing(ZZ, Ring) := (e, R) -> (
    if not R.?cache then R.cache = new CacheTable;
    (Rp0, e0) := if R.cache.?FrobeniusFormation then R.cache.FrobeniusFormation else (R, 0);
    if Rp0.cache#?(symbol FrobeniusRing, e0 + e) then Rp0.cache#(symbol FrobeniusRing, e0 + e)
    else Rp0.cache#(symbol FrobeniusRing, e0 + e) = (
	Rpe := newRing(Rp0, Degrees => (char Rp0)^(e0 + e) * degrees Rp0);
	Rpe.cache = new CacheTable;
	Rpe.cache.FrobeniusFormation = (Rp0, e0 + e);
	Rpe)
    )

frobeniusMap = method(TypicalValue => RingMap)
frobeniusMap(Ring, ZZ) := (R, e) -> frobeniusMap(e, R)
frobeniusMap(ZZ, Ring) := (e, R) -> map(R, frobeniusRing(e, R), apply(gens R, g -> g^((char R)^e)))

decomposeFrobeniusPresentation = (e, f) -> (
    p := char ring f;
    tardegrees := degrees target f;
    srcdegrees := degrees source f;
    -- TODO: make this work for multigradings
    tarclasses := apply(p^e, i -> positions(tardegrees, deg -> deg % p^e == {i}));
    srcclasses := apply(p^e, i -> positions(srcdegrees, deg -> deg % p^e == {i}));
    -- sorts the degrees of source and column
    tarclasses = apply(tarclasses, ell -> ell_(last \ sort \\ reverse \ toList pairs tardegrees_ell));
    srcclasses = apply(srcclasses, ell -> ell_(last \ sort \\ reverse \ toList pairs srcdegrees_ell));
    apply(tarclasses, srcclasses, (tarclass, srcclass) -> submatrix(f, tarclass, srcclass)))

frobeniusPushforward = method()
frobeniusPushforward(Thing, ZZ)   := (T, e) -> frobeniusPushforward(e, T)
frobeniusPushforward(ZZ, Ring)    := (e, R) -> frobeniusPushforward(e, module R)
frobeniusPushforward(ZZ, Ideal)   := (e, I) -> frobeniusPushforward(e, quotient I)
-- TODO: cache in a way that the second pushforward is the same as applying pushforward twice
frobeniusPushforward(ZZ, Module)  := (e, M) -> (
    if  M.cache#?(FrobeniusPushforward, e)
    then M.cache#(FrobeniusPushforward, e)
    else M.cache#(FrobeniusPushforward, e) = (
    f := presentation pushFwd(frobeniusMap(e, ring M), M);
    if not isHomogeneous f then coker f
    else directSum apply(decomposeFrobeniusPresentation(e, f), coker)))
--
frobeniusPushforward(ZZ, Matrix)  := (e, f) -> (
    if  f.cache#?(FrobeniusPushforward, e)
    then f.cache#(FrobeniusPushforward, e)
    else f.cache#(FrobeniusPushforward, e) = (
    g := pushFwd(frobeniusMap(e, ring f), f);
    if not isHomogeneous g then g
    else directSum decomposeFrobeniusPresentation(e, g)))
--frobeniusPushforward(ZZ, Complex) := (e, C) -> () -- TODO

frobeniusPushforward(ZZ, SheafOfRings)  := (e, N0) -> frobeniusPushforward(e, N0^1) -- TODO: is this cached?
frobeniusPushforward(ZZ, CoherentSheaf) := (e, N) -> (
    R := ring N;
    p := char R;
    FN := first components frobeniusPushforward(e, module N);
    -- slow alternative:
    -- FN = pushFwd(frobeniusMap(e, R), module N);
    -- prune sheaf image basis(p^e * (max degrees FN // p^e), FN)
    Fmatrix := sub(presentation FN, R);
    (tardegs, srcdegs) := toSequence(-degrees Fmatrix // p^e);
    -- TODO: how long does this take? is it worth caching?
    sheaf prune coker map(R^tardegs,  R^srcdegs, Fmatrix))

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
assert(rank \ summands frobeniusPushforward(1, OO_(Proj R)) == {2})
assert(rank \ summands frobeniusPushforward(1, R) == {2,2})
--M = coker frobeniusPushforward(char S, I) -- TODO: consolidate with toric version

R = quotient J
assert(rank \ summands frobeniusPushforward(1, OO_(Proj R)) == {1,1})
assert(rank \ summands frobeniusPushforward(1, R) == {1, 1, 2}) -- FIXME: is this correct?
--M = coker frobeniusPushforward(char S, J) -- TODO: consolidate with toric version

--
R = quotient I
M = frobeniusPushforward(1, R);
N1 = frobeniusPushforward(2, R)
N2 = frobeniusPushforward(1, M)
assert(N1 == N2) -- FIXME: why is this different?
N2' = prune coker frobeniusPushforward(1, presentation M)
assert(N2 == N2')
