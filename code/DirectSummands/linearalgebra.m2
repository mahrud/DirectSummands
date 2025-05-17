debug needsPackage "FGLM" -- for LUincremental

fieldElements = method()
fieldElements QuotientRing := ZZp -> ZZp.cache.elements ??= apply(ZZp.order, i -> i_ZZp)
fieldElements GaloisField  := GFq -> GFq.cache.elements ??= prepend_(0_GFq) apply(GFq.order - 1, i -> GFq_0^i)

-- given {({e},c),...} make c*m^e + ...
evalListForm = (L, m) -> sum(L, (e, c) -> c * m ^ (first e))

-- given {a,b,c,...} make a+bt+ct^2+...
polynomial = (L, t) -> evalListForm(apply(#L, i -> ({i}, L#i)), t)

-- TODO: adjust RingElement Array to check if the input is a Matrix?
RingElement Matrix := (f, m) -> evalListForm(listForm f, m)

-- finds the characteristic polynomial of a matrix mod the maximal ideal
char Matrix := A -> A.cache.char ??= (
    if source A =!= target A then error "expected an endomorphism";
    b := symbol b;
    T := (groundField ring A)(monoid[b]);
    B := sub(cover A, T);
    I := id_(source B);
    -- TODO: this is a major step in large examples
    det(B - T_0 * I, Strategy => Bareiss))

minimalPolynomial = A -> A.cache.minimalPolynomial ??= (
    kk := ring A;
    t := local t;
    T := kk(monoid[t]);
    --
    -- naive exact method
    -- B := id_(target A);
    -- m := transpose flatten B;
    -- while syz m == 0 do m |= transpose flatten(B *= A);
    --
    -- naive probabilistic method
    -- m := v := random(target A, kk^1);
    -- while syz m == 0 do m |= (v = A * v);
    -- polynomial(entries (syz m)_0, T_0)
    --
    -- incremental method
    n := numcols A;
    N := n^2;
    P := toList(0..N-1);
    B := id_(target A);
    v := mutableMatrix reshape(kk^N, kk^1, B);
    LU := mutableMatrix map(kk^N, kk^(n+1), 0);
    LUincremental(P, LU, v, s := 0);
    while LU_(s, s) != 0 do (
	s = s + 1;
	v = mutableMatrix reshape(kk^N, kk^1, B *= A);
	P = LUincremental(P, LU, v, s));
    lambda := mutableMatrix map(kk^s, kk^1, 0);
    backSub(submatrix(LU, toList(0..s-1), toList(0..s)), lambda, s);
    T_{s} - polynomial(flatten entries lambda, T_0))

projectorsFromMinimalPolynomial = (f, mp) -> (
    L := select(value \ toList factor mp, p -> degree p > {0});
    apply(L, p -> evalListForm(listForm p, f)))

-- TODO: is it faster to search over fieldElements for finite fields?
roots' = f -> (
    R := ring f;
    p := char R;
    L := listForm f;
    F := groundField R;
    if instance(F, InexactField) then return roots f;
    -- fallback for characteristic 0 or very large fields
    if p == 0 or not F.?order or F.order > 1000
    then flatten rationalPoints ideal f
    else select(fieldElements F, e -> zero evalListForm(L, e)))

-- Linear algebra 101+epsilon algorithm
eigenvalues' = A -> roots' minimalPolynomial A

-- Naive search over finite fields
eigenvalues'' = A -> (
    R := ring A;
    p := char R;
    F := groundField R;
    I := id_(target A);
    -- fallback to LA101 algorithm for characteristic 0 or very large fields
    if p == 0 or not F.?order or F.order > 1000 then return eigenvalues' A;
    select(fieldElements F, e -> zero det(A - e * I)))

end--

check "DirectSummands"

///
  restart
  debug needsPackage "DirectSummands"

  K = ZZ/32003;
  f = random(K^50, K^50);
  elapsedTime eigenvalues'' f -- 0.02s
  elapsedTime eigenvalues' f  -- 5s
  profileSummary

  R = K[b]
  f = random(R^250, R^250);
  elapsedTime select(7, i -> 0 == det(f - i * id_(target f))) -- only 33s for 250x250 over ZZ/7
  elapsedTime select(K.order, i -> 0 == det(f - K_0^i * id_(target f))) -- only 33s for 250x250 over ZZ/7

  scan(20, n -> elapsedTime eigenvalues' random(R^(n+5), R^(n+5)));
///

restart
debug needsPackage "DirectSummands"
  R = ZZ/32003[x,y,z]/(x^3, x^2*y, x*y^2, y^4, y^3*z)
  C = res(coker vars R, LengthLimit => 3)
  D = res(coker transpose C.dd_3, LengthLimit => 3)
  M = coker D.dd_3
  errorDepth=2
findProjectors M

K = quotient ideal gens R;
F = groundField R
elapsedTime h = generalEndomorphism M;
A = h0 = sub(K ** cover h, groundField R)

f = minimalPolynomial h0
f(h0)
tally apply(100, i -> (minimalPolynomial h0) h0)

elapsedTime f = minimalPolynomial h0
assert(f(h0) == 0)

elapsedTime eigenvalues' h0
elapsedTime benchmark"eigenvalues'' h0"
elapsedTime benchmark"eigenvalues''' h0"

I = h0^0
L = listForm f
elapsedTime select(fieldElements F, e -> zero det(h0 - e * I))
elapsedTime select(fieldElements F, e -> zero evalListForm(L, e))
elapsedTime roots' f
