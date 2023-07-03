needsPackage "RationalPoints2"

generalEndomorphism = method()
generalEndomorphism(Module):= M -> (
    R := ring M;
    EndM := End(M);
    B := smartBasis(0, EndM);
    r := rank source B;
if r == 1 then print "warning: End(M)_0 is 1-dimensional";
    homomorphism(B * random(R^r, R^1))
    )
generalEndomorphism CoherentSheaf := M -> generalEndomorphism module M

charMatrix = A -> (
    R := ring A;
    m := ideal gens R;
    k := coefficientRing R;
    T := k[t];
    AT := sub(cover A, T);
    n := rank source AT;
    AT-t*id_(T^n)
    )

findIdem = method()
findIdem Module := M -> findIdem(M,fieldExponent coefficientRing ring M)

findIdem(Module,ZZ):= (M,e) -> (
    A := generalEndomorphism M;
    L:=coefficientRing ring M;
    p:=char L;
 eigen := flatten rationalPoints ideal det charMatrix(A);
if p> 0 then 
    subbedList = for i in eigen list ((A-i*id_M)^(p^e))^(p^e-1)
else
    subbedList = for i in eigen list (A-i*id_M);
    idem := position(subbedList, g -> isIdempotent g and g != id_M and g !=0);
    if idem === null  then return "no idempotents found (consider extending the base field)" else
    subbedList_idem
    )



findIdem CoherentSheaf := M -> findIdem module M

testSplitting = (L,M0)->(
    B:=smartBasis(0,module sheafHom(L,M0));
    b:=rank source B;
    C:=smartBasis(0,module sheafHom(M0,L));
    c:=rank source C;
isSplitting:=(i,j)->reduceScalar(homomorphism(C_{j})*homomorphism(B_{i}))==id_(module L);
    l:=first position'(0..b-1,0..c-1,isSplitting);
    sheaf coker homomorphism (B_{l})
    )

position' = (B, C, f) -> for b in B do for c in C do if f(b,c) then return (b,c)

fieldExponent= (L)->(
p := char L;
if p == 0 then return 1 else(
a:=L_0;
e := 1;
while a^(p^e) != a do (e=e+1);
e)
)

