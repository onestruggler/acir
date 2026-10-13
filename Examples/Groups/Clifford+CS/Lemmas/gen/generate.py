"""Write kbc inputs, and the Agda modules from kbc outputs.

  python3 generate.py input STAGE MAXLEN SECONDS QUEUE [mirror | only=OUT]
      kbc input for a stage of model.py (QUEUE is small or fifo); with
      only=OUT, only the targets the kbc output OUT left unproved
  python3 generate.py agda REPO s0=TAG:d,TAG:m tc=TAG s1=TAG:d,TAG:m t2a=TAG t2=TAG
      write Lemmas/TwoWire.agda, Lemmas/TwoWireMacro.agda and
      TwoQubit/Decoding.agda under REPO/Examples/Groups/Clifford+CS from
      the runs (kbc outputs out-TAG.txt in the current directory; :m marks
      a mirrored run)
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model
from emit import Emitter


# ----------------------------------------------------------------------
# kbc input

def write_input(st, maxlen, secs, queue, mirrored, only=None, f=sys.stdout):
    letters, axioms, targets = model.stage(st)
    if only is not None:
        left = {ln.split()[1] for ln in open(only, encoding='utf-8') if ln.startswith('unproved')}
        targets = [t for t in targets if t[0].replace(' ', '_') in left]
    if mirrored:
        targets = [(n, model.mirror(l), model.mirror(r)) for (n, l, r) in targets]
    sp = lambda w: ' '.join(w) if w else '.'
    print('letters ' + ' '.join(letters), file=f)
    print('maxlen %d' % maxlen, file=f)
    print('seconds %g' % secs, file=f)
    print('queue %s' % queue, file=f)
    for (n, l, r) in axioms:
        print('axiom %s : %s = %s' % (n, sp(l), sp(r)), file=f)
    for (n, l, r) in targets:
        print('target %s : %s = %s' % (n.replace(' ', '_'), sp(l), sp(r)), file=f)


# ----------------------------------------------------------------------
# Agda: the letters and the axioms' terms

BASE_LETTER = {'I': 'ι', 's': 's₀', 'k': 'k₀', 't': 's₁', 'l': 'k₁', 'C': 'cs'}
MACRO_LETTER = {'I': 'ι', 's': 's₀', 't': 's₁', 'C': 'cs', 'x': 'x₀', 'y': 'x₁', 'a': 'cx', 'b': 'cx′',
                'p': 'ck', 'q': 'ck′', 'k': 'k₀', 'l': 'k₁'}
MIRROR = {'s': 't', 't': 's', 'k': 'l', 'l': 'k'}

AXTERM = {
    'order-I':    '⌊ axiom (srel order-I) ⌋⁼',
    'order-S0':   '⌊ axiom (srel order-S) ⌋⁼',
    'order-K0':   '⌊ axiom (srel order-K) ⌋⁼',
    'order-SK0':  '⌊ axiom (srel order-SK) ⌋⁼',
    'order-S1':   '⌊ lemma-cong↑ _ _ (PB.axiom (srel order-S)) ⌋⁼',
    'order-K1':   'K²₁',
    'order-SK1':  'SK³₁',
    'comm-IS0':   '⌊ comm₀ I-gate S-gen ⌋⁼',
    'comm-IK0':   '⌊ comm₀ I-gate K-gen ⌋⁼',
    'comm-IS1':   '⌊ comm₀ I-gate (S-gen ↥) ⌋⁼',
    'comm-IK1':   '⌊ comm₀ I-gate (K-gen ↥) ⌋⁼',
    'comm-IC':    '⌊ comm₀ I-gate CS-gen ⌋⁼',
    'comm-ts':    '⌊ axiom (comm₁ S-gate S-gen) ⌋⁼',
    'comm-lk':    '⌊ axiom (comm₁ K-gate K-gen) ⌋⁼',
    'comm-tk':    '⌊ axiom (comm₁ K-gate S-gen) ⌋⁼',
    'comm-ls':    '⌊ axiom (comm₁ S-gate K-gen) ⌋⁼',
    'order-CS':   '⌊ axiom (srel order-CS) ⌋⁼',
    'comm-CS-S0': '⌊ axiom (srel comm-CS-S₀) ⌋⁼',
    'comm-CS-S1': '⌊ axiom (srel comm-CS-S₁) ⌋⁼',
    'X-CS0':      '⌊ axiom (srel X-CS₀) ⌋⁼',
    'X-CS1':      'X-CS₁′',
    'CS-K0':      '⌊ axiom (srel CS-K₀) ⌋⁼',
    'CS-K1':      '⌊ axiom (srel CS-K₁) ⌋⁼',
}


def agda_name(n):
    return n.replace("'", '′').replace(' ', '-')


def lst(w, letter):
    return ' ∷ '.join(letter[a] for a in w) + ' ∷ []' if w else '[]'


def privately(text):
    if not text.strip():
        return ''
    return 'private\n' + ''.join(('  ' + ln if ln.strip() else ln) for ln in text.splitlines(True))


def stage_text(E, targets, keep, name=lambda n: 'ax-' + n):
    """(the needed rules, {name: definition}, missing)."""
    defs, missing = {}, []
    for (n, l, r) in targets:
        if keep is not None and n not in keep:
            continue
        t = E.emit_target(n.replace(' ', '_'), name(n), list(l), list(r))
        if t is None:
            missing.append(n)
        else:
            defs[n] = t
    return E.emit_rules(), defs, missing


def split(defs, public):
    priv = [t for n, t in defs.items() if n not in public]
    pub = [t for n, t in defs.items() if n in public]
    return privately('\n'.join(priv)) + ('\n' if priv else ''), '\n'.join(pub) + ('\n' if pub else '')


def runs_of(spec):
    out = []
    for item in spec.split(','):
        if item:
            tag, _, kind = item.partition(':')
            out.append((tag, 'out-%s.txt' % tag, kind == 'm'))
    return out


def write_agda(repo, spec):
    base = os.path.join(repo, 'Examples', 'Groups', 'Clifford+CS')
    pairs = lambda A: {n: (list(l), list(r)) for (n, l, r) in A}

    # tier 2: the decoded relations, over the macro letters
    axw2 = pairs(model.macro_axioms())
    E2 = Emitter(MACRO_LETTER, {n: 'ax-' + n for n in axw2}, axw2)
    for run in runs_of(spec['t2']):
        E2.load(*run)
    r2, d2, miss2 = stage_text(E2, model.relations() + model.lemma74(), None, agda_name)
    used2 = E2.axioms_used()

    # tier 2a: the derived macro axioms, from the others
    axw2a = {n: v for n, v in axw2.items() if n not in model.DERIVED}
    E2a = Emitter(MACRO_LETTER, {n: 'ax-' + n for n in axw2a}, axw2a)
    for run in runs_of(spec['t2a']):
        E2a.load(*run)
    D = [a for a in model.macro_axioms() if a[0] in model.DERIVED and a[0] in used2]
    r2a, d2a, miss2a = stage_text(E2a, D, None)
    used2 = sorted((used2 | E2a.axioms_used()) - set(model.DERIVED))

    # stage 1: the non-Clifford macro axioms, on the gates
    tcT = model.tc_targets()
    ax1 = pairs(model.base_axioms())
    ax1.update({n: (list(model.cliff_expand(l)), list(model.cliff_expand(r))) for (n, l, r) in tcT})
    t1 = dict(AXTERM)
    t1.update({n: 'ax-' + n for (n, _, _) in tcT})
    E1 = Emitter(BASE_LETTER, t1, ax1, MIRROR)
    for run in runs_of(spec['s1']):
        E1.load(*run)
    ncl = model.split_macro_axioms()[1]
    r1, d1, miss1 = stage_text(E1, ncl, set(used2) & {n for (n, _, _) in ncl})

    # tier C: the Clifford ones, and what stage 1 uses of them
    axC = pairs(model.cliff_axioms())
    EC = Emitter(BASE_LETTER, {n: 'ax-' + n for n in axC}, axC, MIRROR, {'z': 'CC'})
    for run in runs_of(spec['tc']):
        EC.load(*run)
    rC, dC, missC = stage_text(EC, tcT, (set(used2) | E1.axioms_used()) & {n for (n, _, _) in tcT})

    # stage 0: the axioms of tier C, on the gates
    E0 = Emitter(BASE_LETTER, AXTERM, pairs(model.base_axioms()), MIRROR)
    for run in runs_of(spec['s0']):
        E0.load(*run)
    s0T = [(n, model.cliff_expand(l), model.cliff_expand(r)) for (n, l, r) in model.cliff_axioms()]
    r0, d0, miss0 = stage_text(E0, s0T, EC.axioms_used())

    for (st, E, miss) in [('tier 2', E2, miss2), ('tier 2a', E2a, miss2a), ('stage 1', E1, miss1),
                          ('tier C', EC, missC), ('stage 0', E0, miss0)]:
        print('%-8s %4d rules%s' % (st, len(E.need), ('; MISSING ' + ' '.join(miss)) if miss else ''))
    if miss2 or miss2a or miss1 or missC or miss0:
        sys.exit(1)

    public = set(used2)
    pv0, pb0 = split(d0, set())
    pvC, pbC = split(dC, public)
    pv1, pb1 = split(d1, public)
    with open(os.path.join(base, 'Lemmas', 'TwoWire.agda'), 'w', encoding='utf-8') as f:
        f.write(TW_HEAD)
        f.write(SECTION % "Selinger's relations for the two-qubit Clifford group")
        f.write(r0 + pv0)
        f.write(SECTION % 'The Clifford equations')
        f.write(rC + pvC + pbC)
        f.write(SECTION % 'The equations with CS and the controlled K gates')
        f.write(r1 + pv1 + pb1)

    ax = []
    for n in used2:
        l, r = axw2[n]
        ax.append('  ax-%s : Eqn\n  ax-%s = eqn (%s) (%s)\n'
                  '    (PB.axiom (PB.trans (B.by-assoc refl)\n'
                  '      (PB.trans (TW.prf TW.ax-%s) (B.by-assoc refl))))\n'
                  % (n, n, lst(l, MACRO_LETTER), lst(r, MACRO_LETTER), n))
    with open(os.path.join(base, 'Lemmas', 'TwoWireMacro.agda'), 'w', encoding='utf-8') as f:
        f.write(T2_HEAD)
        f.write('private\n' + '\n'.join(ax) + '\n')
        f.write(SECTION % 'Equations between the letters that follow from the others')
        f.write(r2a + privately('\n'.join(d2a.values())) + '\n')
        f.write(SECTION % 'The derived rules')
        f.write(r2)
        f.write(SECTION % 'The decoded relations, and the decoded encodings of the generators')
        f.write('\n'.join(d2.values()))

    with open(os.path.join(base, 'TwoQubit', 'Decoding.agda'), 'w', encoding='utf-8') as f:
        f.write(DEC_HEAD)
        for (rname, idx, hyps, tgt) in REL:
            for c in clauses(rname, idx, hyps, tgt):
                f.write(c + '\n')


SECTION = ('------------------------------------------------------------------------\n'
           '-- %s\n\n')

# ----------------------------------------------------------------------
# Agda: Lemma 7.5's clauses
#
# One clause per relation of Figure 1 and assignment of its indices in
# Fin 4; the valid ones by the decoded relation of Lemmas.TwoWireMacro,
# the others refuted from the hypothesis that fails.  The indices are
# split in the order the hypotheses constrain them, so that a pair out
# of order is refuted before the indices after it are split.

F = ['₀', '₁', '₂', '₃']

# name, the indices in split order, the explicit hypotheses in order —
# ('lt', x, y) an irrelevant x < y, ('ltr', x, y) a relevant one,
# ('ne', x, y) x ≢ y — and the decoded relation's name
REL = [
    ('order-i',  ['j'],                [],                                         'order-i-{j}'),
    ('order-X',  ['j', 'k'],           [('lt', 'j', 'k')],                         'order-X-{j}{k}'),
    ('order-K',  ['j', 'k'],           [('lt', 'j', 'k')],                         'order-K-{j}{k}'),
    ('comm-ii',  ['j', 'k'],           [('ne', 'j', 'k')],                         'comm-ii-{j}{k}'),
    ('comm-iX',  ['k', 'l', 'j'],      [('lt', 'k', 'l'), ('ne', 'j', 'k'), ('ne', 'j', 'l')], 'comm-iX-{j}{k}{l}'),
    ('comm-iK',  ['k', 'l', 'j'],      [('lt', 'k', 'l'), ('ne', 'j', 'k'), ('ne', 'j', 'l')], 'comm-iK-{j}{k}{l}'),
    ('comm-XX',  ['j', 'k', 'l', 'm'], [('lt', 'j', 'k'), ('lt', 'l', 'm'), ('ne', 'j', 'l'), ('ne', 'j', 'm'), ('ne', 'k', 'l'), ('ne', 'k', 'm')], 'comm-XX-{j}{k}{l}{m}'),
    ('comm-XK',  ['j', 'k', 'l', 'm'], [('lt', 'j', 'k'), ('lt', 'l', 'm'), ('ne', 'j', 'l'), ('ne', 'j', 'm'), ('ne', 'k', 'l'), ('ne', 'k', 'm')], 'comm-XK-{j}{k}{l}{m}'),
    ('comm-KK',  ['j', 'k', 'l', 'm'], [('lt', 'j', 'k'), ('lt', 'l', 'm'), ('ne', 'j', 'l'), ('ne', 'j', 'm'), ('ne', 'k', 'l'), ('ne', 'k', 'm')], 'comm-KK-{j}{k}{l}{m}'),
    ('swap-iX',  ['j', 'k'],           [('lt', 'j', 'k')],                         'swap-iX-{j}{k}'),
    ('swap-XX',  ['j', 'k', 'l'],      [('ltr', 'j', 'k'), ('ltr', 'k', 'l')],      'swap-XX-{j}{k}{l}'),
    ("swap-XX′", ['j', 'k', 'l'],      [('ltr', 'j', 'k'), ('ltr', 'k', 'l')],      'swap-XX′-{j}{k}{l}'),
    ('swap-KX',  ['j', 'k', 'l'],      [('ltr', 'j', 'k'), ('ltr', 'k', 'l')],      'swap-KX-{j}{k}{l}'),
    ("swap-KX′", ['j', 'k', 'l'],      [('ltr', 'j', 'k'), ('ltr', 'k', 'l')],      'swap-KX′-{j}{k}{l}'),
    ('rel-13',   ['j', 'k'],           [('lt', 'j', 'k')],                         'rel-13-{j}{k}'),
    ('rel-14',   ['j', 'k'],           [('lt', 'j', 'k')],                         'rel-14-{j}{k}'),
    ('rel-15',   ['j', 'k'],           [('lt', 'j', 'k')],                         'rel-15-{j}{k}'),
    ('rel-16',   ['j', 'k'],           [('lt', 'j', 'k')],                         'rel-16-{j}{k}'),
    ('rel-17',   ['j', 'k', 'l', 'm'], [('lt', 'j', 'k'), ('lt', 'l', 'm'), ('lt', 'j', 'l'), ('lt', 'k', 'm'), ('ne', 'k', 'l')], 'rel-17-{j}{k}{l}{m}'),
]


def clauses(name, idx, hyps, tgt):
    out = []
    hv = ['h%d' % q for q in range(len(hyps))]

    def holds(h, env):
        kind, x, y = h
        return env[x] < env[y] if kind in ('lt', 'ltr') else env[x] != env[y]

    def refute(h, var, env):
        kind, x, y = h
        if kind == 'ne':
            return '%s refl' % var
        return '%s {%s} {%s} %s' % ('bad' if kind == 'lt' else 'bad′', F[env[x]], F[env[y]], var)

    def go(k, env):
        for q, h in enumerate(hyps):
            if h[1] in env and h[2] in env and not holds(h, env):
                args = ' '.join('{%s = %s}' % (v, F[env[v]]) for v in idx if v in env)
                hs = ' '.join(hv[p] if p == q else '_' for p in range(len(hyps)))
                out.append(' '.join(x for x in ['lemma-7-5 (TL.' + name, args, hs] if x)
                           + ') = ⊥-elim (%s)' % refute(h, hv[q], env))
                return
        if k == len(idx):
            args = ' '.join('{%s = %s}' % (v, F[env[v]]) for v in idx)
            hs = ' '.join('_' for _ in hyps)
            t = tgt.format(**{v: env[v] for v in idx})
            out.append(' '.join(x for x in ['lemma-7-5 (TL.' + name, args, hs] if x)
                       + ') = TM.inst TM.%s refl refl' % t)
            return
        for a in range(4):
            go(k + 1, dict(env, **{idx[k]: a}))

    go(0, {})
    return out


# ----------------------------------------------------------------------
# Agda: the module headers

TW_HEAD = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'TwoWire.head'), encoding='utf-8').read()
T2_HEAD = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'TwoWireMacro.head'), encoding='utf-8').read()
DEC_HEAD = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'Decoding.head'), encoding='utf-8').read()


if __name__ == '__main__':
    if sys.argv[1] == 'input':
        opt = sys.argv[6] if len(sys.argv) > 6 else ''
        write_input(sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), sys.argv[5],
                    opt == 'mirror', opt[5:] if opt.startswith('only=') else None)
    elif sys.argv[1] == 'agda':
        write_agda(sys.argv[2], dict(a.split('=', 1) for a in sys.argv[3:]))
    else:
        sys.exit(__doc__)
