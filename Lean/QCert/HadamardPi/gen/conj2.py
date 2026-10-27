from deriv import *
ch_iv = [parse(s) for s in ["H01 X02", "H01 X12 X01 X12", "X12 H02 X01 X12", "X12 X01 H12 X12",
                            "X12 X01 Z2 H12", "X02 Z1 X12 H12"]]
ch_v = [parse(s) for s in ["H12 X02", "H12 X01 X12 X01", "X01 H02 X12 X01", "X01 X12 H01 X01",
                           "X01 X12 Z1 H01", "X02 Z0 X01 H01"]]
for name, ch in [('iv', ch_iv), ('v', ch_v)]:
    for u, v in zip(ch, ch[1:]): assert same_matrix(u, v, 3), (name, fmt(u), fmt(v))
    eng = Engine(3)
    st = eng.chain(ch, maxd=7)
    check_steps(st, ch[0], ch[-1], eng)
    print(name, len(st)); print("  ", lean_word(ch[0]), "->", lean_word(ch[-1])); print("  ", lean_steps(st))
