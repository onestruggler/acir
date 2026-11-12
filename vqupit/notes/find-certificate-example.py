#!/usr/bin/env python3
"""Reproduce the two-qutrit candidate; this search is outside the trust base.

Enumerate shortest projective representatives through depth six, then
sample length-twelve words using seed 2027. Select the first replacement
with fewer CZ gates and a nonzero scalar correction. Agda independently
checks the selected pair in Qupit-Clifford.CertificateExample.
This is a small, deterministic discovery experiment, not a benchmark.
"""

from collections import deque
import json
from random import Random

P = 3
IDENTITY_MATRIX = tuple(int(i == j) for i in range(4) for j in range(4))
ZERO = (0, 0, 0, 0)


def multiply(a, b):
    return tuple(sum(a[4*i+k] * b[4*k+j] for k in range(4)) % P
                 for i in range(4) for j in range(4))


def apply(a, vector):
    return tuple(sum(a[4*i+k] * vector[k] for k in range(4)) % P
                 for i in range(4))


def symplectic_form(a, b):
    return sum(-a[i]*b[i+1] + b[i]*a[i+1] for i in (0, 2)) % P


def gates():
    result = {}
    for name, wire in [('H0', 0), ('S0', 0), ('H1', 2), ('S1', 2), ('CZ', 0)]:
        matrix, pauli = list(IDENTITY_MATRIX), list(ZERO)
        if name.startswith('H'):
            matrix[4*wire+wire] = matrix[4*(wire+1)+wire+1] = 0
            matrix[4*wire+wire+1], matrix[4*(wire+1)+wire] = -1, 1
        elif name.startswith('S'):
            matrix[4*(wire+1)+wire], pauli[wire+1] = 1, -2
        else:
            matrix[6] = matrix[12] = 1
        result[name] = (0, tuple(x % P for x in pauli),
                        tuple(x % P for x in matrix))
    return result


def product(left, right):
    e, pauli, matrix = left
    f, other_pauli, other_matrix = right
    moved = apply(matrix, other_pauli)
    return ((e + f + 2*symplectic_form(pauli, moved)) % P,
            tuple((x+y) % P for x, y in zip(pauli, moved)),
            multiply(matrix, other_matrix))


def main():
    alphabet = gates()
    identity = (0, ZERO, IDENTITY_MATRIX)
    seen = {identity[1:]: ((), 0)}
    queue = deque([(identity, ())])
    while queue:
        value, word = queue.popleft()
        if len(word) == 6:
            continue
        for name, gate in alphabet.items():
            new = product(value, gate)
            if new[1:] not in seen:
                extended = word + (name,)
                seen[new[1:]] = (extended, new[0])
                queue.append((new, extended))
    rng = Random(2027)
    for trial in range(10000):
        word = tuple(rng.choice(tuple(alphabet)) for _ in range(12))
        if any(word[i] == word[i+1] for i in range(11)):
            continue
        value = identity
        for name in word:
            value = product(value, alphabet[name])
        if value[1:] not in seen:
            continue
        replacement, phase = seen[value[1:]]
        correction = (value[0] - phase) % P
        if (len(replacement) >= 4 and correction and
                0 < replacement.count('CZ') < word.count('CZ')):
            print(json.dumps({
                'prime': P, 'width': 2, 'seed': 2027,
                'enumerated_projective_values': len(seen), 'trial': trial,
                'input': word, 'output': replacement,
                'input_phase': value[0], 'output_phase': phase,
                'correction': correction,
                'gate_counts_excluding_scalar': [len(word), len(replacement)],
                'cz_counts': [word.count('CZ'), replacement.count('CZ')],
            }, indent=2))
            return
    raise RuntimeError('No candidate found within the specified search')


if __name__ == '__main__':
    main()
