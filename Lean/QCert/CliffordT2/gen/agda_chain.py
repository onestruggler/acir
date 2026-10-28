# Read the words around the non-obvious steps of the authors' equational proofs
# (Equation21/28/30/43/44/46.agda), expanding their abbreviations into letters.
import sys, os, re
sys.path.insert(0, os.path.dirname(__file__))
from ct import X, CX, CH, Tdg, Sdg, SWAP
from rot import CW, inv

from paths import ANC

PNAME = {'I⊗X': 'IX', 'I⊗Y': 'IY', 'I⊗Z': 'IZ', 'X⊗I': 'XI', 'X⊗X': 'XX', 'X⊗Y': 'XY', 'X⊗Z': 'XZ',
         'Y⊗I': 'YI', 'Y⊗X': 'YX', 'Y⊗Y': 'YY', 'Y⊗Z': 'YZ', 'Z⊗I': 'ZI', 'Z⊗X': 'ZX', 'Z⊗Y': 'ZY',
         'Z⊗Z': 'ZZ'}

def rw(p): return CW[p] + 'T' + inv(CW[p])

TOK = {
    'H0': 'H', 'H1': 'h', 'S0': 'S', 'S1': 's', 'T0': 'T', 'T1': 't', 'CZ': 'Z', 'W': 'w',
    'W⁻¹': 'w' * 7, 'T0⁻¹': Tdg(0), 'T1⁻¹': Tdg(1), 'S0⁻¹': Sdg(0), 'S1⁻¹': Sdg(1),
    'X0': X(0), 'X1': X(1), 'CX0': CX(0), 'CX1': CX(1), 'CH0': CH(0), 'CH1': CH(1), 'Swap': SWAP,
    'ε': '',
}

def tokens(line):
    line = line.strip()
    if line.startswith('equals '): line = line[len('equals '):]
    if line.startswith('equational '): line = line[len('equational '):]
    # protect R (sign , P)
    toks = []
    for t in re.split(r' • ', line):
        t = t.strip()
        toks.append(t)
    return toks

def expand_tok(t):
    mp = re.match(r'^\(?(.+?)\)? \^ (\d+)$', t)
    if mp:
        return expand_tok(mp.group(1)) * int(mp.group(2))
    m = re.match(r'R \((plus|minus) , (.+)\)$', t)
    if m:
        s = 1 if m.group(1) == 'plus' else -1
        return rw((s, PNAME[m.group(2)]))
    return TOK[t]

def expand(toks):
    return ''.join(expand_tok(t) for t in toks)

def steps_of(n):
    """The chain of (word tokens, justification) of Equation n."""
    src = open(os.path.join(ANC, 'Equation%d.agda' % n), encoding='utf-8').read()
    lines = src.split('\n')
    chain = []   # list of (tokens, 'by' line that follows)
    cur = None
    for ln in lines:
        s = ln.strip()
        if s.startswith('equational ') or s.startswith('equals '):
            cur = tokens(s)
            chain.append([cur, None])
        elif s.startswith('by ') and chain and chain[-1][1] is None:
            chain[-1][1] = s
    return chain

def hard_steps(n):
    """For each non-obvious step: (word before, position, length in tokens, lemma name, word after)."""
    chain = steps_of(n)
    out = []
    for i, (toks, by) in enumerate(chain):
        if by and ('rel-A' in by or 'rel-B' in by or 'rel-C' in by):
            m = re.match(r'by in-context (\d+) (\d+) auto (\S+)', by)
            pos, ln, name = int(m.group(1)), int(m.group(2)), m.group(3)
            if by.endswith('reversed'): name += ' reversed'
            before = toks
            after = chain[i + 1][0]
            out.append((before, pos, ln, by, after))
    return out

if __name__ == '__main__':
    for n in (21, 28, 30, 43, 44, 46):
        for (before, pos, ln, by, after) in hard_steps(n):
            print(n, by, len(before), ' '.join(before[pos:pos + ln]))

def chains(n):
    """name -> chain [(tokens, by)] for each top-level equational proof of Equation n."""
    src = open(os.path.join(ANC, 'Equation%d.agda' % n), encoding='utf-8').read()
    out = {}
    cur = None
    for ln in src.split('\n'):
        m = re.match(r'^([a-z][A-Za-z0-9-]*) : ', ln)
        if m:
            cur = m.group(1); out[cur] = []; continue
        s = ln.strip()
        if cur is None: continue
        if s.startswith('equational ') or s.startswith('equals '):
            out[cur].append([tokens(s), None])
        elif s.startswith('by ') and out[cur] and out[cur][-1][1] is None:
            out[cur][-1][1] = s
    return out

def special_steps(chain, local):
    """Steps of a chain by rel-A/rel-B/rel-C or by a local lemma:
    (before, pos, len, by, after, name, forward)."""
    out = []
    for i, (toks, by) in enumerate(chain):
        if not by: continue
        m = re.match(r'by in-context (\d+) (\d+) auto (\(symm |\(axiom )?([A-Za-z0-9-]+)\)?( reversed)?', by)
        if not m: continue
        name = m.group(4)
        fwd = not (m.group(3) == '(symm ' or m.group(5))
        if name in ('lemma-rel-A', 'lemma-rel-B', 'rel-C') or name in local:
            out.append((toks, int(m.group(1)), int(m.group(2)), by, chain[i + 1][0], name, fwd))
    return out
