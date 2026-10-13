"""Generate the box letter lists of NormalForm.agda from boxes.py."""
from boxes import A, B, C, D, E, F
from gen_axioms import LET

SUB = '₀₁₂'

def ops(time_toks):
    """time order -> operator-order letter list (Agda)."""
    toks = list(reversed(time_toks))
    if not toks:
        return '[]'
    return ' ∷ '.join(LET[t] for t in toks) + ' ∷ []'

def name(k, *ix):
    return k + ''.join(SUB[i] for i in ix)

AS = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
ALL = [(a, b) for a in range(3) for b in range(3)]

def section():
    L = []
    L.append('data AT : Set where')
    L.append('  ' + ' '.join(name('A', a, b) for a, b in AS) + ' : AT')
    L.append('')
    L.append('data BT : Set where')
    L.append('  ' + ' '.join(name('B', a, b) for a, b in ALL) + ' : BT')
    L.append('')
    L.append('data CT : Set where')
    L.append('  ' + ' '.join(name('C', b) for b in range(3)) + ' : CT')
    L.append('')
    L.append('data DT : Set where')
    L.append('  ' + ' '.join(name('D', a, b) for a, b in ALL) + ' : DT')
    L.append('')
    L.append('data ET : Set where')
    L.append('  ' + ' '.join(name('E', b) for b in range(3)) + ' : ET')
    L.append('')
    L.append('data FT : Set where')
    L.append('  ' + ' '.join(name('F', b) for b in range(3)) + ' : FT')
    L.append('')
    L.append('-- Their letters, in operator order, on the bottom wires; a two-wire')
    L.append("-- box's upper wire is wire 1.")
    L.append('Al : AT → List (Gen (₁₊ n))')
    for a, b in AS:
        L.append(f'Al {name("A", a, b)} = {ops(A(a, b))}')
    L.append('')
    L.append('Bl : BT → List (Gen (₂₊ n))')
    for a, b in ALL:
        L.append(f'Bl {name("B", a, b)} = {ops(B(a, b))}')
    L.append('')
    L.append('Cl : CT → List (Gen (₁₊ n))')
    for b in range(3):
        L.append(f'Cl {name("C", b)} = {ops(C(b))}')
    L.append('')
    L.append('Dl : DT → List (Gen (₂₊ n))')
    for a, b in ALL:
        L.append(f'Dl {name("D", a, b)} = {ops(D(a, b))}')
    L.append('')
    L.append('El : ET → List (Gen (₁₊ n))')
    for b in range(3):
        L.append(f'El {name("E", b)} = {ops(E(b))}')
    L.append('')
    L.append('Fl : FT → List (Gen (₁₊ n))')
    for b in range(3):
        L.append(f'Fl {name("F", b)} = {ops(F(b))}')
    return '\n'.join(L)

if __name__ == '__main__':
    print(section())
