needsPackage "NormalToricVarieties"
needsPackage "DirectSummands"

kk = ZZ/5
X = toricProjectiveSpace(2, CoefficientRing => kk)
S = ring X
f = x_0^3+x_1^3+x_2^3+x_0^2*x_1+x_1^2*x_2
R = S/f
Z = Proj R

M = prune frobeniusPushforward(1, OO_Z)

end--
restart
needs "elliptic.m2"

elapsedTime L = summands M
