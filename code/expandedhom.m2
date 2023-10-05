Hom(Module, Module) := Module => (M, N) -> (
    Y := youngest(M.cache.cache, N.cache.cache);
    if Y#?(Hom, M, N) then return Y#(Hom, M, N);
    H := trim kernel (transpose presentation M ** N);
    H.cache.homomorphism = f -> map(N, M, adjoint'(f, M, N), Degree => first degrees source f);
    H.cache.formation = FunctionApplication { Hom, (M, N) };
    Y#(Hom, M, N) = H) -- a hack: we really want to type "Hom(M, N) = ..."
-- finds submodule of Hom containing at least the homomorphisms of degree e
-- TODO: add DegreeLimit as an option to Hom instead
Hom(Module, Module, ZZ)   := Module => (M, N, e) -> Hom(M, N, {e})
Hom(Module, Module, List) := Module => (M, N, e) -> (
    Y := youngest(M.cache.cache, N.cache.cache);
    if Y#?(Hom, M, N, e) then return Y#(Hom, M, N, e);
    A := presentation M;
    B := presentation N;
    (G, F, piM) := (target A, source A, inducedMap(M, G, gens M)); -- not used
    (K, H, piN) := (target B, source B, inducedMap(N, K, gens N));
    Psi := (Hom(A, N) * Hom(G, piN)) // Hom(F, piN);
    L := syz(Psi | (-Hom(F, B)), DegreeLimit => e);
    p := map(Hom(G, K), Hom(G, K) ++ Hom(F, H), (id_(Hom(G, K)) | map(Hom(G, K), Hom(F, H), 0)));
    HMN := trim image(Hom(G, piN) * p * L);
    HMN.cache.homomorphism = f -> map(N, M, adjoint'(f, M, N), Degree => first degrees source f);
    Y#(Hom, M, N, e) = HMN; -- a hack: we really want to type "Hom(M, N) = ..."
    HMN.cache.formation = FunctionApplication { Hom, (M, N, e) };
    HMN)

end--

(M, N) = (S^{-2,-3}, S^{0})
A = Hom(M, N)

h = map(N, M, {{x_0^2,x_0^3}})

homomorphism A_{0}
homomorphism A_{1}


N = frobeniusPushforward(1, R)
A = Hom(N, N);

g = A_{0} + A_{2}
h = A_{1} + A_{3}

g' = homomorphism g
h' = homomorphism h
gh' = g' * h'


adjoint(g, module ring N, N)


homomorphism A_{0}
g' * M_{1}
g, h
