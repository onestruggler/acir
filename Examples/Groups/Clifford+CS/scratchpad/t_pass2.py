import passes as P
from gadgets4 import setup
G = setup()
cases = [
  ('t0 vs t1 white3', [P.Col([], G[0])] if False else G[0], [P.Col([3], G[1])]),
  ('t0 vs t1 white23', G[0], [P.Col([2, 3], G[1])]),
  ('t0 w1 vs t1 white3', [P.Col([1], G[0])], [P.Col([3], G[1])]),
  ('t0 vs t1 w0 white3', G[0], [P.Col([0, 3], G[1])]),
  ('t0 vs t1 adjacent', G[0], G[1]),
]
for nm, A, B in cases:
    try: P.prove(A, B); print('PROVED', nm)
    except P.Fail as e: print('FAIL', nm, str(e)[:300])
