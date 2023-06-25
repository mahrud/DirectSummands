needsPackage "PushForward"
needsPackage "Complexes"

frobeniusMap = method()
frobeniusMap(Ring, ZZ) := (R, e) -> frobeniusMap(e, R)
frobeniusMap(ZZ, Ring) := (e, R) -> (
    p := char R;
    Rpe := newRing(R, Degrees => p^e * degrees R);
    map(R, Rpe, apply(gens R, g -> g^(p^e))))

frobeniusPushforward = method()
frobeniusPushforward(Thing, ZZ)   := (T, e) -> frobeniusPushforward(e, T)
frobeniusPushforward(ZZ, Ring)    := (e, R) -> frobeniusPushforward(e, module R)
frobeniusPushforward(ZZ, Ideal)   := (e, I) -> frobeniusPushforward(e, quotient I)
frobeniusPushforward(ZZ, Module)  := (e, M) -> (
    R := ring M;
    p := char R;
    f := presentation pushFwd(frobeniusMap(e, R), M);
    (tardegs, srcdegs) := -toSequence(degrees f // p^e);
    coker map(R^tardegs, R^srcdegs, sub(f, R)))
--frobeniusPushforward(ZZ, Module)  := (e, M) -> pushFwd(frobeniusMap(e, ring M), M)

frobeniusPushforward(ZZ, Matrix)  := (e, f) -> () -- TODO
frobeniusPushforward(ZZ, Complex) := (e, C) -> () -- TODO

frobeniusPushforward(ZZ, SheafOfRings)  := (e, N0) -> frobeniusPushforward(e, N0(0))
frobeniusPushforward(ZZ, CoherentSheaf) := (e, N) -> (
    R := ring N;
    p := char R;
    --FN := frobeniusPushforward(e, module N);
    -- TODO: prune sheaf doesn't work with toric varieties
    -- also, why do this?
    --prune sheaf image basis(max degrees FN, FN)
    FN := pushFwd(frobeniusMap(e, R), module N);
    gendeg := p^e * (max degrees FN // p^e);
    FNs := prune sheaf image basis(gendeg, FN);
    Fmatrix := sub(presentation module FNs, R);
    (tardegs, srcdegs) := -toSequence(degrees Fmatrix // p^e);
    prune sheaf coker map(R^tardegs,  R^srcdegs, Fmatrix)
    )

end--

--TODO: add tests
