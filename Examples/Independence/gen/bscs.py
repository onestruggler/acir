"""Bian and Selinger's relations for 3-qubit Clifford+CS operators
(Examples.Groups.Clifford+CS-3qubit.Theorem, module CliffordCS), read
from that module: words in operator order over iI, S0, S1, S2, K0, K1,
K2, CS01, CS12, their abbreviations expanded.  The decoding F into
CliffCS₂ on three wires reads them as written (as the paper reads them,
every gate's matrix being symmetric): qubit k on wire k (the high bit
of their numbering first), iI as ω ω, K as ω⁷ H (K = ω̄ H), CS01 and
CS12 as CS on the wires 0 1 and 1 2."""
import os
import re

THEOREM = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'Groups',
                       'Clifford+CS-3qubit', 'Theorem.agda')

GENS = {'S0', 'S1', 'S2', 'CS01', 'CS12', 'iI', 'K0', 'K1', 'K2'}


def _read():
    src = open(THEOREM, encoding='utf-8').read()
    body = src[src.index('module CliffordCS where'):src.index('open TwoLevel')]
    abbrev, rels = {}, []
    for line in body.splitlines():
        m = re.match(r"  ([A-Za-z0-9']+) = (.*)$", line)
        if m and '[' not in m.group(2):
            abbrev[m.group(1)] = m.group(2).split(' • ')
            continue
        m = re.match(r"    (ax-\S+) : (.*) === (.*) ∈ Rel$", line)
        if m:
            rels.append((m.group(1), m.group(2).split(' • '), m.group(3).split(' • ')))
    return abbrev, rels


ABBREV, RELS = _read()


def expand(word):
    out = []
    for g in word:
        if g == 'ε':
            continue
        if g in GENS:
            out.append(g)
        else:
            out += expand(ABBREV[g])
    return out


C = {name: (expand(l), expand(r)) for name, l, r in RELS}

SPELL = {'iI': 'w w', 'S0': 'S0', 'S1': 'S1', 'S2': 'S2', 'K0': 'wd H0', 'K1': 'wd H1',
         'K2': 'wd H2', 'CS01': 'CS10', 'CS12': 'CS21'}


def F(word):
    """The decoding in the order written, in the transcription notation."""
    return ' '.join(SPELL[g] for g in word)


if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf-8')
    import cscliff
    from circ import parse, same
    print(len(C), 'relations')
    for k, (l, r) in C.items():
        print(same(parse(F(l)), parse(F(r)), 3), k)
