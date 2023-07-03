needs "splitting.m2"
--needs "frobenius.m2"

kk = ZZ/5
 X = toricProjectiveSpace(2, CoefficientRing => kk)
S = ring X -- kk[x,y,z]
f = x_0^3+x_1^3+x_2^3+x_0^2*x_1+x_1^2*x_2
R = S/f

--M = prune frobeniusPushforward(R, 1)
--= prune 
f' = sub(frobeniusPushforward(5, f), R)
M = prune coker f'
rank M

end--
restart
needs "elliptic.m2"

elapsedTime L = summands M
