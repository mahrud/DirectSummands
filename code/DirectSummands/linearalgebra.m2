debug needsPackage "FGLM" -- for LUincremental

fieldElements = method()
fieldElements QuotientRing := ZZp -> apply(ZZp.order, i -> i_ZZp)
fieldElements GaloisField  := GFq -> prepend_(0_GFq) apply(GFq.order - 1, i -> GFq_0^i)
fieldElements' = memoize fieldElements -- FIXME: don't cache globally

-- given {({e},c),...} make c*m^e + ...
evalListForm = (L, m) -> sum(L, (e, c) -> c * m ^ (first e))

-- given {a,b,c,...} make a+bt+ct^2+...
polynomial = (L, t) -> evalListForm(apply(#L, i -> ({i}, L#i)), t)

-- TODO: adjust RingElement Array to check if the input is a Matrix?
RingElement Matrix := (f, m) -> evalListForm(listForm f, m)

-- finds the characteristic polynomial of a matrix mod the maximal ideal
char Matrix := A -> A.cache.char ??= (
    if numRows A != numColumns A then error "expected a square matrix";
    b := symbol b;
    T := (groundField ring A)(monoid[b]);
    B := sub(cover A, T);
    I := id_(source B);
    -- TODO: this is a major step in large examples
    det(B - T_0 * I, Strategy => Bareiss))

-- TODO: is it worth it to use mutable matrices to concatenate?
minimalPolynomial = A -> (
    kk := ring A;
    t := local t;
    T := kk(monoid[t]);
    --
    -- exact method
    -- B := id_(target A);
    -- m := transpose flatten B;
    -- while syz m == 0 do m |= transpose flatten(B *= A);
    --
    -- probabilistic method
    -- m := v := random(target A, kk^1);
    -- while syz m == 0 do m |= (v = A * v);
    -- polynomial(entries (syz m)_0, T_0)
    --
    -- incremental method
    n := numcols A;
    N := n^2;
    -- initiating LU-decomposition matrices
    P := toList(0..N-1);
    B := id_(kk^n);
    v := mutableMatrix reshape(kk^N, kk^1, B);
    LU := mutableMatrix map(kk^N, kk^(N+1), 0);
    LUincremental(P, LU, v, s := 0);
    while LU_(s, s) != 0 do (
	s = s + 1;
	v = mutableMatrix reshape(kk^N, kk^1, B *= A);
	-- ~6.2s in this line
	-- TODO: can we not copy v?
	P = LUincremental(P, LU, v, s));
    lambda := mutableMatrix map(kk^n, kk^1, 0);
    backSub(submatrix(LU, toList(0..s-1), toList(0..s)), lambda, s);
    T_{s} - polynomial(flatten entries lambda, T_0))

-- TODO: is it faster to search over fieldElements' for finite fields?
roots' = f -> (
    R := ring f;
    p := char R;
    L := listForm f;
    F := groundField R;
    if instance(F, InexactField) then return roots f;
    -- fallback for characteristic 0 or very large fields
    if p == 0 or not F.?order or F.order > 1000
    then flatten rationalPoints ideal f
    else select(fieldElements' F, e -> zero evalListForm(L, e)))

-- Linear algebra 101 algorithm
eigenvalues' = A -> roots' char A

-- Naive search over finite fields
eigenvalues'' = A -> (
    R := ring A;
    p := char R;
    F := groundField R;
    I := id_(target A);
    -- fallback to LA101 algorithm for characteristic 0 or very large fields
    if p == 0 or not F.?order or F.order > 1000 then return eigenvalues' A;
    select(fieldElements' F, e -> zero det(A - e * I)))

eigenvalues''' = A -> roots' minimalPolynomial A

end--

///
  restart
  debug needsPackage "DirectSummands"
  K = GF(9)
  K = ZZ/7
  R = K[b]
  f = random(R^95, R^95);
  elapsedTime select(7, i -> 0 == det(f - i * id_(target f))) -- only 33s for 250x250 over ZZ/7
  elapsedTime select(K.order, i -> 0 == det(f - K_0^i * id_(target f))) -- only 33s for 250x250 over ZZ/7
  elapsedTime eigenvalues'' f
  elapsedTime eigenvalues''' f
  scan(20, n -> elapsedTime eigenvalues' random(R^(n+5), R^(n+5)));
///

restart
debug needsPackage "DirectSummands"
  R = ZZ/32003[x,y,z]/(x^3, x^2*y, x*y^2, y^4, y^3*z)
  C = res(coker vars R, LengthLimit => 3)
  D = res(coker transpose C.dd_3, LengthLimit => 3)
  M = coker D.dd_3
#  summands M

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
elapsedTime select(fieldElements' F, e -> zero det(h0 - e * I))
elapsedTime select(fieldElements' F, e -> zero evalListForm(L, e))
elapsedTime roots' f
