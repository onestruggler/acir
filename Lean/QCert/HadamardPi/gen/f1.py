import sys, time
from deriv import *
def f1_chain(a, b, c, d):
    Hab, Hcd, Hac, Hbd = H(a, b), H(c, d), H(a, c), H(b, d)
    Xw = (Hab, Hcd, Hac, Hbd)
    T = (Hcd, Hac, Hbd)
    return [Xw + Xw,
            T * 4 + (Hac, Hbd) + Xw,
            T * 3 + (Hcd,) + Xw,
            (Hbd, Hac, Hcd, Hcd, Hac, Hbd) + T * 3 + (Hcd,) + Xw,
            (Hbd, Hac, Hcd, Hab, Hcd, Hcd) + Xw,
            (Hbd, Hac, Hcd, Hab) + Xw,
            ()]
if __name__ == '__main__':
  eng = Engine(4)
  for ix in [(0, 1, 2, 3), (0, 2, 1, 3)]:
      t = time.time()
      ch = f1_chain(*ix)
      for u, v in zip(ch, ch[1:]): assert same_matrix(u, v, 4)
      st = eng.chain(ch, maxd=6)
      check_steps(st, ch[0], ch[-1], eng)
      print(ix, len(st), "steps", round(time.time() - t, 1), "s")
      print(lean_word(ch[0]))
      print(lean_steps(st))
