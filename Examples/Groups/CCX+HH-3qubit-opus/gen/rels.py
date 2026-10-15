"""The relations of Syntactics.agda, as word pairs (operator order)."""
from model import W, same

R0 = {
    'r1': ('CZ01', 'K12 CX01 K12'),
    'r2': ('X1', 'CX01 X0 CX01 X0'),
    'r3': ('Z0', 'CZ01 CX01 CZ01 CX01'),
    'r4': ('Z1', 'K12 X1 K12'),
    'r5': ('CX20', 'X1 CCX12 X1 CCX12'),
    'r6': ('CX21', 'CX20 CX01 CX20 CX01'),
    'r7': ('CX12', 'K12 CX21 K12'),
    'r8': ('SW12', 'CX12 CX21 CX12'),
    'r9': ('CX02', 'SW12 CX01 SW12'),
    'r10': ('SW02', 'CX02 CX20 CX02'),
    'r11': ('K01', 'SW02 K12 SW02'),
    'r12': ('CX10', 'K01 CX01 K01'),
    'r13': ('SW01', 'CX01 CX10 CX01'),
    'r14': ('CCX02', 'SW01 CCX12 SW01'),
    'r15': ('X2', 'SW02 X0 SW02'),
    'r16': ('Z2', 'SW02 Z0 SW02'),
    'r17': ('CCX01', 'K12 CCX02 K12'),
    'r18': ('CZ02', 'SW12 CZ01 SW12'),
    'r19': ('CZ12', 'SW01 CZ02 SW01'),
    'r20': ('SW12', 'CZ12 K12 CZ12 K12 CZ12 K12'),
    'r21': ('X0 X0', ''),
    'r22': ('CX01 CX01', ''),
    'r23': ('K12 K12', ''),
    'r24': ('CCX12 CCX12', ''),
    'r25': ('K01 K01', ''),
    'r26': ('CX12 X0', 'X0 CX12'),
    'r27': ('X0 K12', 'K12 X0'),
    'r28': ('X1', 'SW01 X0 SW01'),
    'r29': ('CX20', 'SW02 CX02 SW02'),
    'r30': ('CX12', 'SW01 CX02 SW01'),
    'r31': ('CX21', 'SW01 CX20 SW01'),
    'r32': ('CCX01', 'SW02 CCX12 SW02'),
    'r33': ('CCX01', 'SW12 CCX02 SW12'),
    'r34': ('Z1', 'SW01 Z0 SW01'),
    'r35': ('K01', 'SW01 K01 SW01'),
    'r36': ('CCX12 CX10', 'CX10 CCX12'),
    'r37': ('X0 CCX12', 'CCX12 X0'),
    'r38': ('X0 CX10', 'CX10 X0'),
    'r39': ('K01 K12', 'K12 K01'),
    'r40': ('CZ01 CZ12', 'CZ12 CZ01'),
    'r41': ('K01 Z0', 'X0 K01'),
    'r42': ('X0 CCX01', 'CCX01 CX12 X0'),
    'r43': ('CX01 CZ12', 'CZ12 CZ02 CX01'),
    'r44': ('CX12 CCX12', 'CCX12 CX10 CX12'),
    'r45': ('CCX12 CX01', 'CX01 CCX02 CCX12 CCX02'),
    'r46': ('CCX01 CCX02', 'CCX02 CCX01 CCX02 CCX01'),
}
R0 = {k: (W(a), W(b)) for k, (a, b) in R0.items()}


def T(a):
    return W({0: 'X0 X1 CCX01 X1 X0',
              1: 'X0 CCX01 CCX02 CCX01 X0',
              2: 'X0 CCX01 X0',
              3: 'X0 X2 CCX01 X0 CCX12 CCX02 CCX12 X0 CCX01 X2 X0',
              4: 'X1 CCX01 X1',
              5: 'CCX01 CCX02 CCX01'}.get(a, 'CCX01'))


def Tr(a, d):
    if d == 0:
        return T(a)
    return T(a) + Tr(a + 1, d - 1) + T(a)


def Xab(a, b):
    return () if b <= a else Tr(a, b - a - 1)


m0 = W('X0 X1 X2 CCZ X2 X1 X0')


def m(c):
    return Xab(0, c) + m0 + Xab(0, c)


NKw = ('NK',)


def Kq(a, b, c, d):
    return Xab(0, a) + Xab(1, b) + Xab(2, c) + Xab(3, d) + NKw + Xab(3, d) + Xab(2, c) + Xab(1, b) + Xab(0, a)


Omega = Kq(4, 5, 6, 7) + NKw + T(3) + NKw + Kq(4, 5, 6, 7)

R7 = {
    'r83': (m0 + m0, ()),
    'r84': (NKw + NKw, ()),
    'r85': (T(1) + m0, m0 + T(1)),
    'r86': (T(2) + m0, m0 + T(2)),
    'r87': (T(3) + m0, m0 + T(3)),
    'r88': (T(4) + m0, m0 + T(4)),
    'r89': (T(5) + m0, m0 + T(5)),
    'r90': (T(6) + m0, m0 + T(6)),
    'r91': (T(4) + NKw, NKw + T(4)),
    'r92': (T(5) + NKw, NKw + T(5)),
    'r93': (T(6) + NKw, NKw + T(6)),
    'r94': (m(4) + NKw, NKw + m(4)),
    'r95': (m0 + m(4), m(4) + m0),
    'r96': (NKw + Kq(4, 5, 6, 7), Kq(4, 5, 6, 7) + NKw),
    'r97': (T(0) + NKw, NKw + Xab(1, 3) + m(1) + m(3)),
    'r98': (T(1) + NKw, m0 + NKw + m0 + NKw + m0),
    'r99': (T(2) + NKw, NKw + Xab(1, 3)),
    'r100': (NKw + Kq(1, 3, 4, 5), Kq(2, 3, 4, 5) + Kq(0, 1, 2, 4)),
    'r101': (m0 + m(4) + Xab(0, 4) + Omega + Xab(0, 4) + m(4) + m0, Omega),
}

RK = {'rK': (W('K12'), W('X0 NK X0 NK'))}

if __name__ == '__main__':
    bad = [k for k, (l, r) in {**R0, **R7, **RK}.items() if not same(l, r)]
    print('unsound:', bad)
