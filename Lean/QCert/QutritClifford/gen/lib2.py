"""Two-wire lemmas (free one-wire segments), checked by engine.Engine(2)."""
import cliff
import qc
import cosets
import engine

H0, S0, H1, S1 = ('H', 0), ('S', 0), ('H', 1), ('S', 1)
C = ('CZ', 0)
W = qc.SWAP(0)
XC = [H1, C, H1, H1, H1]
CX = [H0, C, H0, H0, H0]
Sp0 = [H0, H0, S0, H0, H0]
Sp1 = [H1, H1, S1, H1, H1]


def base():
    return [(nm, cliff.strip(l), cliff.strip(r)) for nm, l, r in cosets.rules2()]


def build():
    E = engine.Engine(2, base())
    E.chain('WS1', [W + [S1], W + [S1] + W + W, W + W + [S0] + W, [S0] + W])
    E.chain('WH1', [W + [H1], W + [H1] + W + W, W + W + [H0] + W, [H0] + W])
    E.chain('CS0', [[C, S0], W + W + [C, S0], W + [C] + W + [S0], W + [C, S1] + W,
                    W + [S1, C] + W, [S0] + W + [C] + W, [S0, C] + W + W, [S0, C]])
    E.chain('CH0', [[H0, H0, C, C], W + W + [H0, H0, C, C], W + [H1] + W + [H0, C, C],
                    W + [H1, H1] + W + [C, C], W + [H1, H1, C] + W + [C],
                    W + [H1, H1, C, C] + W, W + [C, H1, H1] + W, W + [C, H1] + W + [H0],
                    W + [C] + W + [H0, H0], [C] + W + W + [H0, H0], [C, H0, H0]])
    return E


if __name__ == '__main__':
    E = build()
    for nm, l, r, st in E.lemmas:
        print(nm, len(st))
