needsPackage "PushForward"

frobeniusMap = method()
frobeniusMap(Ring, ZZ) := (R, e) -> (
    d := length gens R;
    p := char R;
    Rpe := newRing(R, Degrees => toList(d:p^e));
    F := map(R, Rpe, apply(gens R, R -> R^(p^e)));
    F
    )

frobeniusPushforward = method()
frobeniusPushforward(Ring, ZZ) := (R, e) -> (
    F := frobeniusMap(R, e);
    FR := pushFwd(F, R^1);
    FR
    )

frobeniusPushforward(Module, ZZ) := (M, e) -> (
    R := ring M;
    F := frobeniusMap(R, e);
    FM := pushFwd(F, M);
    FM
    )

frobeniusPushforward(SheafOfRings, ZZ) := (N0, e) -> (
    N := N0(0);
    R := ring N;
    p := char R;
    F := frobeniusMap(R, e);
    FN := pushFwd(F, module N);
    gendeg := p^e*(max( (degrees presentation FN )_0 )//p^e);
    FNs := prune sheaf image basis(gendeg, FN);
    Fmatrix := sub(presentation module FNs, R);
    L := degrees(Fmatrix);
    prune sheaf coker map(R^(-(flatten (L_0))//p^e),  R^(-(flatten( L_1))//p^e), Fmatrix)
    )


frobeniusPushforward(CoherentSheaf, ZZ) := (N, e) -> (
    R := ring N;
    p := char R;
    F := frobeniusMap(R, e);
    FN := pushFwd(F, module N);
    gendeg := p^e*(max( (degrees presentation FN )_0 )//p^e);
    FNs := prune sheaf image basis(gendeg, FN);
    Fmatrix := sub(presentation module FNs, R);
    L := degrees(Fmatrix);
    prune sheaf coker map(R^(-(flatten (L_0))//p^e),  R^(-(flatten( L_1))//p^e), Fmatrix)
    )
