# The two-wire λ-images that Five.D.TR needs, in a module of their own.
#
# TR (the transports of the de-borrowing) needs the λ-images of the
# instances on two wires (`ok₂`) and lem-calc-x4x4.  write_group puts
# those derivations with the other `tr`/`calc` ones, at the end of the D
# modules, after the de-borrowing's derivations, which import TR: an
# import cycle (D112 → TR → D138 → D121 → D112).  Their own dependencies
# lie well before the de-borrowing, so this pass moves them, with their
# order kept, into Five/D/TRL.agda, between the modules they need and TR,
# and points every import of them there.  It runs after winlib5, on the
# final text of the modules.
#
#   python trsplit5.py <Five directory>

import io, os, re, sys

NL = '\n'
MOD = 'Examples.Groups.Clifford+CS.Five'
DIMP = re.compile(r'^open import ' + re.escape(MOD) + r'\.D\.(\w+) using \(([^)]*)\)$', re.M)
WINIMP = re.compile(r'^open import ' + re.escape(MOD) + r'\.WinSig using \(([^)]*)\)$', re.M)
LEMREF = re.compile(r'\b(lem-[^\s()]+)')
WINREF = re.compile(r'\b(w[lp]\d{4}|e2-\d+)\b')


def read(p): return io.open(p, encoding='utf-8').read()


def write(p, s): io.open(p, 'w', encoding='utf-8', newline=NL).write(s)


def blocks(s):
    """the header of a D module and its lemma blocks (comment line,
    signature, definition), as (name, derivation, text)."""
    starts = [m.start() for m in re.finditer(r'^-- [^\n]*\nlem-\S+ : ', s, re.M)]
    head = s[:starts[0]] if starts else s
    out = []
    for i, a in enumerate(starts):
        b = starts[i + 1] if i + 1 < len(starts) else len(s)
        txt = s[a:b]
        deriv = re.match(r'-- (.*): \d+ steps?\n', txt)
        name = re.search(r'^(lem-\S+) : ', txt, re.M).group(1)
        out.append((name, deriv.group(1) if deriv else None, txt))
    return head, out


def names_of(using): return [n.strip() for n in using.split(';') if n.strip()]


def split(root):
    ddir = os.path.join(root, 'D')
    tr = read(os.path.join(ddir, 'TR.agda'))
    need = {n for _, us in DIMP.findall(tr) for n in names_of(us)}
    files = sorted(f[:-5] for f in os.listdir(ddir) if f.endswith('.agda') and f not in ('TR.agda', 'TRL.agda'))
    defs, parsed = {}, {}
    for m in files:
        parsed[m] = blocks(read(os.path.join(ddir, m + '.agda')))
        for n, _, _ in parsed[m][1]:
            defs[n] = m
    srcs = sorted({defs[n] for n in need})
    moved = [(m, b) for m in srcs for b in parsed[m][1] if b[0] in need]
    assert {b[0] for _, b in moved} == need, need - {b[0] for _, b in moved}

    # Five/D/TRL.agda.
    body = ''.join(b[2] for _, b in moved)
    refs = {n for n in LEMREF.findall(body) if n in defs and n not in need}
    bym = {}
    for n in refs: bym.setdefault(defs[n], set()).add(n)
    # The first module of the de-borrowing: the first to import TR.
    cut = min((m for m in files if m.startswith('D')
               and f'open import {MOD}.D.TR using' in parsed[m][0]), default='D999')
    bad = [m for m in bym if m.startswith('D') and m >= cut or m in srcs]
    assert not bad, ('TRL would import', bad, 'the de-borrowing starts at', cut)
    wins = sorted(set(WINREF.findall(body)))
    head0 = parsed[srcs[0]][0]
    std = head0[head0.index('open import Data.List'):head0.index(f'open import {MOD}.WinSig')]
    head = ('------------------------------------------------------------------------\n'
            '-- Presentations of groups\n--\n'
            '-- The two-wire λ-images of Five.D.TR\n--\n'
            '-- The derivations that Five.D.TR needs (its `ok₂` and lem-calc-x4x4),\n'
            '-- apart from the de-borrowing\'s, which import TR.  Written by\n'
            '-- `scratchpad/five/trsplit5.py`.\n'
            '------------------------------------------------------------------------\n\n'
            '{-# OPTIONS --without-K --safe #-}\n\n'
            f'module {MOD}.D.TRL where\n\n' + std
            + f'open import {MOD}.WinSig using ({" ; ".join(["Ws", "lit"] + wins)})\n'
            + f'open import {MOD}.Chain\n'
            + ''.join(f'open import {MOD}.D.{m} using ({" ; ".join(sorted(ns))})\n' for m, ns in sorted(bym.items())))
    write(os.path.join(ddir, 'TRL.agda'), head + body)

    # The modules they leave.
    for m in srcs:
        h, bs = parsed[m]
        rest = ''.join(b[2] for b in bs if b[0] not in need)
        used = sorted(set(LEMREF.findall(rest)) & need)
        if used:
            h = h.replace(f'open import {MOD}.Chain\n',
                          f'open import {MOD}.Chain\nopen import {MOD}.D.TRL using ({" ; ".join(used)})\n', 1)
        write(os.path.join(ddir, m + '.agda'), h + rest)

    # Every import of a moved lemma, now from TRL.
    def repoint(s):
        to_trl = set()

        def rep(mt):
            mod, us = mt.groups()
            ns = names_of(us)
            if mod not in srcs or not any(n in need for n in ns): return mt.group(0)
            to_trl.update(n for n in ns if n in need)
            keep = [n for n in ns if n not in need]
            return f'open import {MOD}.D.{mod} using ({" ; ".join(keep)})' if keep else '\0'
        s = DIMP.sub(rep, s)
        if to_trl:
            line = f'open import {MOD}.D.TRL using ({" ; ".join(sorted(to_trl))})'
            i = s.index('\0') if '\0' in s else None
            if i is not None:
                s = s[:i] + line + s[i + 1:]
            else:
                last = list(DIMP.finditer(s))[-1]
                s = s[:last.end()] + NL + line + s[last.end():]
            s = re.sub('\0\n', '', s)
        return s

    targets = [os.path.join(ddir, f) for f in os.listdir(ddir) if f.endswith('.agda') and f != 'TRL.agda']
    targets += [os.path.join(root, f) for f in os.listdir(root) if f.endswith('.agda')]
    tdir = os.path.join(root, 'TransportAx')
    if os.path.isdir(tdir):
        targets += [os.path.join(tdir, f) for f in os.listdir(tdir) if f.endswith('.agda')]
    for p in targets:
        s = read(p)
        t = repoint(s)
        if t != s: write(p, t)

    # The index.
    ip = os.path.join(ddir, 'INDEX.txt')
    if os.path.exists(ip):
        dn = {b[1] for _, b in moved if b[1]}
        lines = []
        for l in read(ip).splitlines():
            mod, steps, name = l.split(' ', 2)
            lines.append(f'TRL {steps} {name}' if name in dn else l)
        write(ip, NL.join(lines) + NL)
    return len(moved), srcs, sorted(bym), cut


if __name__ == '__main__':
    n, srcs, deps, cut = split(sys.argv[1])
    print(n, 'lemmas moved from', ' '.join(srcs), 'to D/TRL; it imports', ' '.join(deps))
