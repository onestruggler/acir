"""Writes BaseComm.lean: the three base commutations of bc_results.json
(BC211, BC31, BC4) as PlacedEngine derivations.

Port of the Agda's gen/mk_basecomm.py, writing Lean instead of Agda.  It
reads the same saved search results (the Agda's gen/bc_results.json, found
by the Agda's gen/bc_targets.py with the equations of Equations4 as lemmas)
and writes the steps exactly as this folder's mk_equations4.py writes its
own (`emit_step`, after the Agda generator's `steps_of`, which replays a
search result as engine steps).

Each says that Ḡ = X₃ CX₃₀ X₃ commutes with Q CX₃₀ Q⁻¹ for a base circuit
Q of CLabels (baseQ 2, 3, 4).  Unlike the Agda's, a derivation is cut into
segments of at most CHUNK steps, each checked on its own (`derive` from the
word before the segment to the word after it, replayed here), and the
segments are joined by transitivity: one Boolean per segment keeps the
kernel's work, and its memory, per check small.  Like the Agda's, this
generator is untrusted: Lean checks what it writes.

Run with WSL's python3 from this folder: `python3 mk_basecomm.py`.
"""
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent                       # Lean/QCert/XCXCCX4bit
REPO = LEAN.parents[2]                   # the repository root
AGEN = REPO / 'Examples' / 'Groups' / 'XCXCCX-4bit' / 'gen'
OUT = LEAN / 'BaseComm.lean'

CHUNK = 40

# This folder's mk_equations4 (which imports the Agda's mk_equations4 by the
# same module name), loaded under another name.
_spec = importlib.util.spec_from_file_location('lean_mk_equations4',
                                               HERE / 'mk_equations4.py')
me4 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(me4)
ag = me4.ag                              # the Agda's mk_equations4

NAMES = {
    'BC211': ('BC211E', [
        "Ḡ against G placed by CCX_{2,0→1} (union type 2 + 1 + 1)."]),
    'BC31': ('BC31E', [
        "Ḡ against G placed by CCX_{2,0→1} CCX_{1,0→2} (union type 3 + 1)."]),
    'BC4': ('BC4E', [
        "Ḡ against G placed by CX_{0→1} CCX_{1,0→2} (union type 4)."]),
}


def replay(t, steps):
    """The word after each step (normalised letters), from the left side."""
    cur = [ag.norm(j) for j in t['lhs']]
    words = []
    for s in steps:
        if s[0] == 'perm':
            cur = [ag.norm(j) for j in s[1]]
        elif s[0] == 'narrow':
            _, i, k, new = s
            cur = cur[:i] + [ag.norm(j) for j in new] + cur[i + k:]
        else:
            _, p, d, i = s
            if d == 'fwd':
                assert cur[i:i + 3] == ag.r7_side(p, ag.R7L)
                cur = cur[:i] + ag.r7_side(p, ag.R7R) + cur[i + 3:]
            else:
                assert cur[i:i + 2] == ag.r7_side(p, ag.R7R)
                cur = cur[:i] + ag.r7_side(p, ag.R7L) + cur[i + 2:]
        words.append(list(cur))
    assert cur == [ag.norm(j) for j in t['rhs']], t['name']
    return words


def emit(name, comment, t):
    st = ag.steps_of(t)
    words = replay(t, st)
    cuts = list(range(0, len(st), CHUNK)) + [len(st)]
    nseg = len(cuts) - 1
    out = []
    ws = [('%s_w%d' % (name, k)) for k in range(nseg + 1)]
    for k in range(nseg + 1):
        w = t['lhs'] if k == 0 else (t['rhs'] if k == nseg else words[cuts[k] - 1])
        out.append('/-- The word after %d steps. -/' % cuts[k] if 0 < k < nseg else
                   ('/-- The left side. -/' if k == 0 else '/-- The right side. -/'))
        out.append('def %s : List PG :=' % ws[k])
        out.append('  ' + me4.lean_list(w, 2))
        out.append('')
    for k in range(nseg):
        seg = st[cuts[k]:cuts[k + 1]]
        out.append('theorem %s_d%d : 4 ⊢ ιs %s ≈ ιs %s := check_sound (ss :=' % (name, k + 1, ws[k], ws[k + 1]))
        for j, s in enumerate(seg):
            lead = '  [' if j == 0 else '   '
            sep = ',' if j + 1 < len(seg) else '])'
            out.append(lead + me4.emit_step(s, 3) + sep)
        out.append('  (by decide +kernel)')
        out.append('')
    out.append('/-- ' + '\n'.join(comment) + ' -/')
    chain = '%s_d1' % name
    for k in range(2, nseg + 1):
        chain = '(%s).trans %s_d%d' % (chain, name, k)
    out.append('def %s : Eqnp := ⟨%s, %s, %s⟩' % (name, ws[0], ws[nseg], chain))
    return '\n'.join(out)


HDR = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The three base commutations of the controlled matchings

Translation of `BaseComm.agda`.  `Ḡ = X₃ CX₃₀ X₃` is `X` on wire 0
controlled by wire 3 = 0, and `Q CX₃₀ Q⁻¹`, for a circuit `Q` of the lower
wires, is the matching `Q μ₀ Q⁻¹` controlled by wire 3 = 1.  They act on
disjoint halves of the states, so they commute; `CRel` needs this for one
`Q` of each of the five union types of the matching with `μ₀` (`CLabels`'
`baseQ`).  Two of them are three-wire identities (`CBC`); the other three,
written here, are derivations of `PlacedEngine` whose steps are rule (7)
under a relabelling of the wires and three-wire steps justified by
completeness on three wires, found by the Agda's `gen/bc_targets.py` with
the equations of `Equations4` as lemmas (`gen/bc_results.json`) and written
out by `gen/mk_basecomm.py` (the port of the Agda's, from the same saved
search results).  A letter `CCX_{a,b→t}` is the Toffoli with controls
`a, b` and target `t`.  Wire 0 is the bottom wire, and words are in diagram
order.

The Agda's `BC211⁼`, `BC31⁼`, `BC4⁼` are `BC211E`, `BC31E`, `BC4E`.

**Deviation from the Agda.**  The Agda checks each derivation as one
`derive … refl`.  Here a derivation is cut into segments of at most %d
steps (the same steps, in the same order): the words between them (`…_wk`,
replayed by the generator) are named, each segment is one Boolean
(`PlacedEngine.check`) decided by `decide +kernel` (`…_dk`), and the
segments are joined by transitivity.  One check per derivation of up to
496 steps made the kernel's caches grow beyond 9 GB.

Generated by `gen/mk_basecomm.py`.
-/
import QCert.XCXCCX4bit.PlacedEngine

namespace QCert.XCXCCX4bit.BaseComm

open Placed PlacedEngine''' % CHUNK

FTR = '''
end QCert.XCXCCX4bit.BaseComm
'''


def main():
    d = json.load(open(AGEN / 'bc_results.json', encoding='utf-8'))
    tg = {t['name']: t for t in d['targets']}
    parts = [HDR]
    for n in ('BC211', 'BC31', 'BC4'):
        t = tg[n]
        assert t['found'] and t['check'] == 'ok', n
        nm, cm = NAMES[n]
        parts.append(emit(nm, cm, t))
    with open(OUT, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n\n'.join(parts) + '\n' + FTR)
    print('wrote', OUT)


if __name__ == '__main__':
    main()
