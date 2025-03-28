TEST /// -- basic test
  S = QQ[x,y]
  M = coker matrix{{1,0},{1,y}}
  A = summands M
  B = summands prune M
  C = summands trim M
  -- FIXME: this keeps annoyingly breaking
  assert same(A, {prune M}, B, prune \ C)
///

TEST /// -- direct summands of a free module
  R = ZZ/2[x_0..x_5]
  M = R^{100:-2,100:0,100:2}
  A = summands M;
  B = summands(M, ExtendGroundField => 2);
  C = summands(M, ExtendGroundField => 4);
  D = summands(M, ExtendGroundField => ZZ/101);
  E = summands(M, ExtendGroundField => GF(2,2));
  assert same(M, directSum A)
  assert same(A, B, C, D, E)
///

TEST /// -- direct summands of a multigraded free module
  R = QQ[x,y,z] ** QQ[a,b,c]
  M = R^{{0,0},{0,1},{1,0},{-1,0},{0,-1},{1,-1},{-1,1}}
  assert same(M, directSum summands M)
  --assert first isIsomorphic(directSum elapsedTime summands M, M)
///

TEST /// -- direct summands of a ring
  S = ZZ/3[x,y,z]
  R = ZZ/3[x,y,z,w]/(x^3+y^3+z^3+w^3)
  f = map(R, S)
  M = pushForward(f, module R)
  assert(M == S^{0,-1,-2})
///

-- FIXME: takes 13s, which is more than it used to
TEST /// -- direct summands over field extensions
  debug needsPackage "DirectSummands"
  R = (ZZ/7)[x,y,z]/(x^3+y^3+z^3);
  X = Proj R;
  M = module frobeniusPushforward(1, OO_X);
  -* is smartBasis useful? yes!
  elapsedTime A = End M; -- ~0.65s
  elapsedTime B = basis({0}, A); -- ~0.23s
  elapsedTime B = smartBasis({0}, A); -- ~0.03s
  *-
  -- if this test fails, check if "try findIdempotent M" if hiding any unexpected errors
  elapsedTime assert({1, 2, 2, 2} == rank \ summands M) -- 2.28s
  elapsedTime assert({1, 2, 2, 2} == rank \ summands(M, ExtendGroundField => GF 7)) -- 2.87s -> 2.05
  elapsedTime assert({1, 2, 2, 2} == rank \ summands(M, ExtendGroundField => GF(7, 3))) -- 3.77s -> 2.6
  elapsedTime assert(toList(7:1)  == rank \ summands(M, ExtendGroundField => GF(7, 2))) -- 2.18s -> 0.47
///

TEST ///
  R = ZZ/101[x,y,z]/(x^3, x^2*y, x*y^2, y^4, y^3*z)
  C = res(coker vars R, LengthLimit => 3)
  D = res(coker transpose C.dd_3, LengthLimit => 3)
  M = coker D.dd_3
  assert(8 == #summands M)
///

TEST ///
  debug needsPackage "DirectSummands"
  n = 4
  S = ZZ/11[x_0..x_(n-1)]
  I = trim minors_2 matrix { S_*_{0..n-2}, S_*_{1..n-1}}
  R = quotient I
  C = res coker vars R
  M = image C.dd_3
  needsPackage "RationalPoints2"
  h = generalEndomorphism M
  rationalPoints ideal char h
  -- TODO: does the kernel and cokernel of this give summands?
  h' = h - 1 * id_(target h)
  prune ker h'
  prune coker h'
  summands M
///

TEST ///
  n = 3
  S = (ZZ/2)[x_0..x_(n-1)]
  R = quotient (ideal vars S)^3
  F = res coker vars R
  M = image F.dd_3
  summands M
  summands(image F.dd_1, M)
  -- TODO: have a flag to test for twists of input summands as well
  summands({image F.dd_1, coker vars R}, M)
///

TEST /// -- testing in char 0
  -- FIXME:
  --S = ZZ[x,y];
  --assert(2 == #summands coker matrix "x,y;y,x")
  S = QQ[x,y];
  assert(2 == #summands coker matrix "x,y; y,x")
  assert(1 == #summands coker matrix "x,y;-y,x")
  -- restart
  debug needsPackage "DirectSummands"
  S = QQ[a,b,c,d];
  M = coker matrix "a,b,c,d;d,a,b,c;c,d,a,b;b,c,d,a"
  findIdempotent M
  -- TODO: can we make sure the last block remains symmetric?
  assert(3 == #summands coker matrix "a,b,c,d;d,a,b,c;c,d,a,b;b,c,d,a")
  K = toField(QQ[i]/(i^2+1));
  S = K[x,y];
  assert(2 == #summands coker matrix "x,y; y,x")
  assert(2 == #summands coker matrix "x,y;-y,x")
  S = K[a,b,c,d];
  assert(4 == #summands coker matrix "a,b,c,d;d,a,b,c;c,d,a,b;b,c,d,a")
  S = CC[x,y];
  scan(20, i -> assert(set summands coker matrix {{x,y},{-y,x}} == set {cokernel matrix {{x-ii*y}}, cokernel matrix {{x+ii*y}}}))
///

-- FIXME: takes 78s
TEST ///
  --tests largepowers
  K = ZZ/7
  R = K[x,y,z]/(x^3+y^3+z^3)
  X = Proj R
  M1 = summands(frobeniusPushforward(1, OO_X), ExtendGroundField => 2)
  M2 = frobeniusPushforward(1, M1#1)
  L = potentialExtension M2
  findIdem changeBaseField(L, M2)
///

///
  -- from David's email: reaches recursion limit overnight
  needsPackage "DirectSummands"
  kk = ZZ/101
  S = kk[x,y,z]
  I = monomialIdeal(x^4,x*y,y^4,x*z,y^2*z,z^4)
  R = S/I
  F = res(coker vars R, LengthLimit => 5)
  M = coker F.dd_5;
  debugLevel = 1
  elapsedTime L5 = summands M;
///

///
needsPackage "DirectSummands"
  kk = ZZ/101
  S = kk[x,y,z]
  P = Proj S 
  TP = tangentSheaf P
  R = S/(x*y-z^2)
  assert(length summands prune sheaf(module TP ** R) == rank TP)
  assert(length summands sheaf(module TP ** R) == length summands prune sheaf(module TP ** R))
///

///
  debug needsPackage "DirectSummands"
  kk = ZZ/13
  S = kk[x,y,z]
  R = S/(x*z-y^2)
  L = summands frobeniusPushforward(1, R);
  L = summands S^30000;
  elapsedTime isomorphismTally L
  elapsedTime tallySummands L
  set(last \ isomorphismTally summands frobeniusPushforward(1,R)) == set{12,13}
///


///
  debug needsPackage "DirectSummands"
  kk = ZZ/11
  S = kk[x,y,z,Degrees=>{5,1,5}]
  R = S/(x*z-y^10)
  L = summands frobeniusPushforward(1, R);
  elapsedTime isomorphismTally L;
  elapsedTime tallySummands L;
  set(last \ isomorphismTally summands frobeniusPushforward(1,R)) == set{12,13}
///


load "./large-tests.m2"
