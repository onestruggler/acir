"""W(D8) over S8: the semidirect-product relations for Z1.

    python3 -B d8rels.py
"""
import sys
import levels as Lv

BASE = [
    'CX1 CXr1 CX1 CCX0 CX1 CXr1 CX1 CCX0',
    'X1 CCX0 X1 CX1 CXr1 CX1 CX0 CX1 CXr1 CX1 CCX0',
    'CCX0 CXr0 CCX0 CXr0 CCX0 CX0 CXr0 CX0 CCX0 CX0 CXr0 CX0',
    'CXr0 CXr1 CXr0 CXr1 CXr0 CXr1 CXr0 CXr1',
    'CX0 CX1 CX0 CX1 CXr0 CX0 CX1 CX0 CXr0',
    'CX0 CX1 CX0 CX1 CXr1 CX1 CX0 CX1 CXr1',
]
EX1 = 'CX1 CXr1 CX1'
W = 'X1 Z1 X1 Z1'
Z2 = f'{EX1} Z1 {EX1}'
EXTRA = {
    'Z1-CXr1': 'Z1 CXr1 Z1 CXr1',
    'Z1-CCX0': 'Z1 CCX0 Z1 CCX0',
    'W-CX1': f'{W} CX1 {W} CX1',
    'W-CXr1': f'{W} CXr1 {W} CXr1',
    'W-CCX0': f'{W} CCX0 {W} CCX0',
    'CX1-Z1': f'CX1 Z1 CX1 {Z2} Z1',
    'Z1-Z2': f'Z1 {Z2} Z1 {Z2}',
}

def words(ts):
    return [tuple(t.split()) for t in ts]

if __name__ == '__main__':
    letters, below = Lv.LEVELS['d8'], Lv.LEVELS['s8']
    fr = list(Lv.free(letters))
    for name, t in EXTRA.items():
        assert Lv.ev(tuple(t.split())) == Lv.rep.identity, name
    names = list(EXTRA)
    got = Lv.index(letters, fr + words(BASE) + words(EXTRA[n] for n in names), below)
    print('all ->', got, flush=True)
    if got == 128:
        keep = list(names)
        for n in names:
            trial = [m for m in keep if m != n]
            if Lv.index(letters, fr + words(BASE) + words(EXTRA[m] for m in trial), below) == 128:
                keep = trial
        print('needed:', keep)
