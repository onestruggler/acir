"""Merge the one-line certificate modules into chunk modules.

The generators write one module per certificate: PermProofs/*,
Tietze/* and Proofs/* (and, before TwoLevel transported the relations
generically, the frame moves and the 2,123 transport cases, some 7500
modules in all).  Agda pays for a module
apart from its contents: it is loaded, merged into the state of every
module that imports it, and has an interface of its own.  So this
script, run after the generators, writes each folder as chunk modules
B000, B001, …, each
certificate a nested module of its chunk under its old name, deletes
the single modules, and rewrites every module of the development that
imported one: `import P.F.N as A` becomes `open import P.F.Bk using
(module N)` with `A.` read as `N.`, and a plain `import P.F.N` an
import of its chunk.  On 606 frame certificates this made checking
from scratch twice as fast and loading them ten times as fast (the
repository's typecheck-efficiency.md).

The chunks follow a topological order of the certificates, and a chunk
is closed early when the next certificate would make two chunks import
each other through a module outside them.  The output depends only on
the generated files, so regenerating reproduces it byte for byte.
"""
import re
import generate as g

ROOT = g.ROOT
P = g.PREFIX
FOLDERS = ['Tietze', 'PermProofs', 'Proofs']
# Characters of certificate text per chunk: about a hundred frame moves.
CHUNK = 48000

IMPORT = re.compile(r'^import (\S+)(?: as (\S+))?$')
DEPLINE = re.compile(r'^(?:open )?import (\S+)')
NESTED = re.compile(r'^module (\S+) where$', re.M)
KITLINE = re.compile(r'^import ' + re.escape(P) + r'\.(Kit) as K using \((.*)\)$')
CHUNKNAME = re.compile(r'^B\d+$')


def modname(path):
    return P + '.' + '.'.join(path.relative_to(ROOT).with_suffix('').parts)


def group(folder, name):
    """Certificates of one group share chunks."""
    return ''


def chunk_name(folder, grp, k):
    return f'{grp}_B{k:02d}' if grp else f'B{k:03d}'


def substitute(alias, s):
    """s with each qualified name A.x read as alias[A].x."""
    if not alias:
        return s
    pat = re.compile(r'(?<![^\s(){};])(' + '|'.join(map(re.escape, sorted(alias))) + r')\.')
    return pat.sub(lambda x: alias[x.group(1)] + '.', s)


def main():
    files = {}
    for folder in FOLDERS:
        for path in sorted((ROOT / folder).glob('*.agda')):
            name = path.stem
            if CHUNKNAME.match(name):
                continue
            files[f'{P}.{folder}.{name}'] = path
    if not files:
        print('Nothing to bundle')
        return
    # The chunks of an earlier run, in the folders written anew.
    for folder in {m.split('.')[-2] for m in files}:
        for path in (ROOT / folder).glob('*.agda'):
            if CHUNKNAME.match(path.stem):
                path.unlink()
    # Every module of the development, its text and its imports in it.
    text, deps = {}, {}
    for path in sorted(ROOT.rglob('*.agda')):
        m = modname(path)
        text[m] = path.read_text(encoding='utf-8')
    for m, s in text.items():
        deps[m] = [i.group(1) for l in s.split('\n') for i in [DEPLINE.match(l)]
                   if i and i.group(1) in text]
    # Topological order, by name among ready modules; closures as bit sets.
    order, seen = [], set()

    def visit(m):
        stack = [(m, iter(sorted(deps[m])))]
        seen.add(m)
        while stack:
            n, it = stack[-1]
            for d in it:
                if d not in seen:
                    seen.add(d)
                    stack.append((d, iter(sorted(deps[d]))))
                    break
            else:
                stack.pop()
                order.append(n)

    for m in sorted(text):
        if m not in seen:
            visit(m)
    bit = {m: 1 << i for i, m in enumerate(order)}
    below = {}
    for m in order:
        b = 0
        for d in deps[m]:
            b |= below[d] | bit[d]
        below[m] = b
    # Chunks: certificates in topological order, per folder and group.
    where, chunks, open_ = {}, {}, {}

    def close(key):
        open_.pop(key, None)

    for m in order:
        if m not in files:
            continue
        folder, name = m[len(P) + 1:].split('.')
        key = (folder, group(folder, name))
        cur = open_.get(key)
        if cur is not None:
            members, size, bits = cur
            # A module outside the chunk below m that depends on a member.
            outside = below[m] & ~bits
            clash = False
            x = outside
            while x:
                low = x & -x
                d = order[low.bit_length() - 1]
                if below[d] & bits:
                    clash = True
                    break
                x ^= low
            if clash or size + len(text[m]) > CHUNK:
                close(key)
                cur = None
        if cur is None:
            k = len(chunks.setdefault(key, []))
            chunks[key].append([])
            cur = open_[key] = [chunks[key][k], 0, 0]
        cur[0].append(m)
        cur[1] += len(text[m])
        cur[2] |= bit[m]
        where[m] = (folder, chunk_name(folder, key[1], len(chunks[key]) - 1))

    # Certificates merged by an earlier run, in the folders not written
    # anew: a regenerated module may still name them singly.
    for folder in FOLDERS:
        if any(m.split('.')[-2] == folder for m in files):
            continue
        for path in sorted((ROOT / folder).glob('*.agda')):
            if CHUNKNAME.match(path.stem):
                for nm in NESTED.findall(text[modname(path)]):
                    where[f'{P}.{folder}.{nm}'] = (folder, path.stem)

    def bundle(m):
        folder, c = where[m]
        return f'{P}.{folder}.{c}'

    # The chunks and the other modules import each other acyclically.
    node = {m: bundle(m) if m in where else m for m in order}
    edges = {}
    for m in order:
        edges.setdefault(node[m], set()).update(node[d] for d in deps[m] if node[d] != node[m])
    state = {}
    for start in sorted(edges):
        if start in state:
            continue
        stack = [(start, iter(sorted(edges[start])))]
        state[start] = 1
        while stack:
            n, it = stack[-1]
            for d in it:
                assert state.get(d) != 1, ('import cycle through', n, d)
                if d not in state:
                    state[d] = 1
                    stack.append((d, iter(sorted(edges[d]))))
                    break
            else:
                state[n] = 2
                stack.pop()

    def rewrite(lines, own=None):
        """Imports of certificates in lines, and the body with them read.

        Returns (imports, body): imports maps a chunk to the nested
        modules used from it (None for a plain import); own is the chunk
        being written, whose members need no import."""
        imports, body, alias = {}, [], {}
        for l in lines:
            i = IMPORT.match(l)
            if i and i.group(1) in where:
                n = i.group(1).rsplit('.', 1)[1]
                b = bundle(i.group(1))
                if i.group(2):
                    alias[i.group(2)] = n
                    if b != own:
                        imports.setdefault(b, set()).add(n)
                elif b != own:
                    imports.setdefault(b, set())
                continue
            body.append(l)
        return imports, substitute(alias, '\n'.join(body))

    def import_lines(imports):
        out = []
        for b in sorted(imports):
            ns = imports[b]
            if ns:
                out.append(f'open import {b} using ({" ; ".join("module " + n for n in sorted(ns))})')
            else:
                out.append(f'import {b}')
        return out

    # The chunks.
    written = set()
    for (folder, grp), cs in chunks.items():
        for k, members in enumerate(cs):
            c = chunk_name(folder, grp, k)
            own = f'{P}.{folder}.{c}'
            kit, kitnames, hoisted, imports, bodies = None, set(), {}, {}, []
            for m in members:
                lines = text[m].split('\n')
                assert lines[0] == '{-# OPTIONS --without-K --safe #-}', m
                assert lines[2] == f'module {m} where', m
                rest = lines[3:]
                kl = [i for i, l in enumerate(rest) if KITLINE.match(l)]
                assert len(kl) == 1 and rest[kl[0] + 1] == 'open K', m
                km = KITLINE.match(rest[kl[0]])
                assert kit in (None, km.group(1)), m
                kit = km.group(1)
                kitnames |= {x.strip() for x in km.group(2).split(';')}
                del rest[kl[0]:kl[0] + 2]
                # A certificate is read as its nested module, and any other
                # import is hoisted under the last component of its name.
                alias, body = {}, []
                for l in rest:
                    i = IMPORT.match(l)
                    if not i:
                        body.append(l)
                        continue
                    target, a = i.groups()
                    assert a, (m, l)
                    h = target.rsplit('.', 1)[1]
                    alias[a] = h
                    if target in where:
                        if bundle(target) != own:
                            imports.setdefault(bundle(target), set()).add(h)
                    else:
                        assert hoisted.get(h, target) == target, (m, l)
                        hoisted[h] = target
                body = substitute(alias, '\n'.join(body)).strip('\n')
                n = m.rsplit('.', 1)[1]
                assert n not in hoisted, m
                bodies.append(f'module {n} where\n\n' +
                              '\n'.join('  ' + l if l else l for l in body.split('\n')))
            s = g.header(f'{folder}.{c}')
            s += f'import {P}.{kit} as K using ({" ; ".join(sorted(kitnames))})\nopen K\n'
            for h in sorted(hoisted):
                s += f'import {hoisted[h]} as {h}\n'
            for l in import_lines(imports):
                s += l + '\n'
            s += '\n' + '\n\n'.join(bodies) + '\n'
            (ROOT / folder / f'{c}.agda').write_text(s, encoding='utf-8')
            written.add(own)
    for m, path in files.items():
        path.unlink()
    # The modules that imported certificates.
    changed = 0
    for m, s in text.items():
        if m in files or m in written:
            continue
        lines = s.split('\n')
        if not any((i := IMPORT.match(l)) and i.group(1) in where for l in lines):
            continue
        first = next(j for j, l in enumerate(lines) if IMPORT.match(l) and IMPORT.match(l).group(1) in where)
        imports, body = rewrite(lines)
        body = body.split('\n')
        body[first:first] = import_lines(imports)
        path = ROOT.joinpath(*m[len(P) + 1:].split('.')).with_suffix('.agda')
        path.write_text('\n'.join(body), encoding='utf-8')
        changed += 1
    print('Bundled', len(files), 'certificates into', len(written), 'chunks;',
          'rewrote', changed, 'modules')


if __name__ == '__main__':
    main()
