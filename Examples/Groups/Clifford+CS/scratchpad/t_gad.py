import gadgetlib as G
from deriv import show
for g in [G.Gad(0), G.Gad(0, (2,)), G.Gad(0, (), ['S', 'K'], -1), G.Gad(1, (3,), ['K'], 1)]:
    for c in g.controls():
        if c in g.W: continue
        for x in ('K', 'S'):
            G.nc_pass(c, x, g)
            n, g2 = G.ca(c, x, g)
print('nc_pass and ca: ok', G.Gad(0, (), ['S','K'], -1).letters()[:6])
