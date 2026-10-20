# Repack generated derivation modules (Four/D, Five/D) by lemma depth.
#
# The emitters (four/emit.py, five/emit5.py) pack consecutive lemmas into
# modules D001, D002, ..., and a module imports the earlier ones whose
# lemmas it uses, so the modules formed chains -- Four/D 122 long (D070
# importing D069, ...), Five/D 47 -- which no number of parallel jobs
# could shorten.  The lemmas themselves are only 20 and 18 deep: a lemma's
# depth is one more than the deepest lemma it uses.  This puts the lemmas
# of each depth together, in their emitted order, in modules of at most
# CAP bytes, numbered level by level within each family of modules (the
# prefix of their names: Five/D's R modules take the record WsL, its D
# modules Ws); a module then imports only modules of lower levels, and the
# longest chain is the lemma depth.  Each lemma's text is unchanged.  A
# module's header is the union of the headers of the modules its lemmas
# came from, its lists of window and lemma names (wl…, wp…, lem-…) cut
# to those its lemmas mention.  INDEX.txt is rewritten for the new
# modules, and so are the imports of the modules that use the lemmas
# (their `open import … TREE.D.Xnnn using (…)` lines, regrouped).
#
#   python3 repack.py REPO_ROOT TREE [CAP]      (TREE: Four or Five)
# Run after the emitter; the generators that read INDEX.txt find the
# lemmas in their new modules.
import os, re, sys, collections

ROOT, TREE = sys.argv[1], sys.argv[2]
CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 110_000
C = os.path.join(ROOT, 'Examples', 'Groups', 'Clifford+CS')
D = os.path.join(C, TREE, 'D')
MOD = f'Examples.Groups.Clifford+CS.{TREE}.D.'
NL = '\n'
IMPD = re.compile(r'^open import ' + re.escape(MOD) + r'([A-Z]\d+) using \(([^)]*)\)\s*$')
USING = re.compile(r'^(open import \S+(?: [^u(]\S*)*) using \(([^)]*)\)\s*$')
CUT = re.compile(r'^(wl|wp|lem-)')            # names kept only where mentioned

mods = sorted(f[:-5] for f in os.listdir(D) if re.fullmatch(r'[A-Z]\d+\.agda', f))


# INDEX.txt lists each lemma by its derivation's name, not in the order of
# the modules (Five/D's is in emission order), so a line goes with the
# lemma the emitter named from it: four/emit.py's and five/emit5.py's
# lemname, copied here; a line no name matches goes with the next lemma of
# its module in order.
def lemname(name, tree):
    if tree == 'Four':
        TR = {'(': '⟨', ')': '⟩', '.': '·', '>': '⟶', '|': '∣', ';': '', '{': '', '}': '', '"': ''}
        s = (name.replace('] [', '-vs-').replace(' ', '-').replace('=', '≡').replace('[', '')
             .replace(']', '').replace(',', '').replace('@', 'at').replace('^', 'ᵖ'))
        return 'lem-' + ''.join(TR.get(ch, ch) for ch in s)
    TR = {'(': '⟨', ')': '⟩', '.': '·', '>': '⟶', '|': '∣', ';': '·', '{': '', '}': '', '"': '', ',': '',
          '@': 'at', '^': 'ᵖ', '[': '', ']': '', '=': '≡', ':': '∶'}
    s = ''.join(TR.get(ch, ch) for ch in name.replace(' ', '-'))
    while '--' in s: s = s.replace('--', '-')
    return 'lem-' + s


def index_entries(index, order, module_of, tree):
    """lemma -> its INDEX line [module, steps, name]"""
    byname, left = {}, collections.defaultdict(list)
    for e in index:
        byname.setdefault((e[0], lemname(e[2].strip(), tree)), e)
        left[e[0]].append(e)
    entry = {}
    for n in order:
        e = byname.get((module_of[n], n))
        if e and e in left[module_of[n]]:
            entry[n] = e; left[module_of[n]].remove(e)
    for n in order:
        if n not in entry:
            entry[n] = left[module_of[n]].pop(0)
    assert all(entry[n][0] == module_of[n] for n in order)
    return entry
# The numbered modules are repacked; others in the directory (clifford-cs's
# Five/D/TR and TRL, written by trsplit5.py between levels) are kept as they
# are and treated as outside modules, their INDEX lines kept too.
allidx = [l.rstrip('\n').split(' ', 2) for l in open(os.path.join(D, 'INDEX.txt'), encoding='utf-8') if l.strip()]
index = [e for e in allidx if e[0] in mods]
kept_idx = [e for e in allidx if e[0] not in mods]


def parse(m):
    """the module's header lines other than its imports of TREE/D, and its lemma blocks"""
    lines = open(os.path.join(D, m + '.agda'), encoding='utf-8').read().split(NL)
    head, i = [], 0
    while i < len(lines) and not (lines[i].startswith('--') or lines[i].startswith('lem-')):
        if not IMPD.match(lines[i]):
            head.append(lines[i])
        i += 1
    blocks, cur, has_def = [], [], None
    for line in lines[i:]:
        top = line and not line[0].isspace()
        sig = re.match(r'^(lem-\S+) : ', line)
        if top and (line.startswith('--') and has_def or sig and has_def and sig.group(1) != has_def):
            blocks.append((has_def, cur))
            cur, has_def = [], None
        cur.append(line)
        if sig: has_def = sig.group(1)
    if has_def: blocks.append((has_def, cur))
    return head, blocks


heads, lemmas, order = {}, {}, []          # lemma -> (text, origin module)
for m in mods:
    head, blocks = parse(m)
    heads[m] = head
    for name, text in blocks:
        while text and text[-1] == '':
            text = text[:-1]
        lemmas[name] = (NL.join(text), m)
        order.append(name)
assert len(order) == len(index), (len(order), len(index))
entry = index_entries(index, order, {n: lemmas[n][1] for n in order}, TREE)
names = set(lemmas)
uses = {n: set(re.findall(r'\blem-[^\s()]+', t)) & names - {n} for n, (t, _) in lemmas.items()}

# Dependencies through modules outside the tree: a lemma that uses a name
# of an outside module X (Five/D's lemmas use Five.TR2's transports) needs
# every lemma of the tree that X needs, through its own imports (TR2
# imports F1Low, which imports (F1) items of Five/D).  Without this the
# modules using TR2 could land below those items, and the imports cycle.
OUT = re.compile(r'^open import (\S+) using \(([^)]*)\)\s*$')


def modpath(m): return os.path.join(ROOT, *m.split('.')) + '.agda'


ext_of = {}                                # name -> outside module it comes from
for m in mods:
    for line in heads[m]:
        o = OUT.match(line)
        if o and o.group(1)[len(MOD):] not in mods and os.path.exists(modpath(o.group(1))):
            for x in o.group(2).split(';'):
                if x.strip(): ext_of[x.strip()] = o.group(1)
need = {}


def needs(x):
    """the lemmas of the tree an outside module needs, through its imports"""
    if x in need: return need[x]
    need[x], todo, seen = set(), [x], set()
    while todo:
        y = todo.pop()
        if y in seen: continue
        seen.add(y)
        src = open(modpath(y), encoding='utf-8').read()
        for i in re.findall(r'^\s*(?:open\s+)?import\s+([A-Za-z][^\s(;]*)', src, re.M):
            if i.startswith(MOD) and i[len(MOD):] in mods:
                o = re.search(r'^open import ' + re.escape(i) + r' using \(([^)]*)\)', src, re.M)
                if o: need[x] |= {z.strip() for z in o.group(1).split(';') if z.strip()} & names
            elif os.path.exists(modpath(i)):
                todo.append(i)
    return need[x]


for n, (t, _) in lemmas.items():
    words = set(re.findall(r'[^\s()]+', t))
    for x in {ext_of[w] for w in words if w in ext_of}:
        uses[n] |= needs(x) - {n}
sys.setrecursionlimit(100000)
depth = {}


def dep(n):
    if n not in depth:
        depth[n] = 1 + max((dep(u) for u in uses[n]), default=0)
    return depth[n]


for n in order: dep(n)


def family(n): return lemmas[n][1][0]


# Pack each family's levels, in emitted order, into modules of at most CAP bytes.
new, fam = [], []
for f in sorted({family(n) for n in order}):
    cur, size, level = [], 0, None
    for lv in sorted(set(depth.values())):
        for n in [n for n in order if family(n) == f and depth[n] == lv]:
            b = len(lemmas[n][0].encode('utf-8'))
            if cur and (size + b > CAP or level != lv):
                new.append(cur); fam.append(f); cur, size = [], 0
            cur.append(n); size += b; level = lv
    if cur: new.append(cur); fam.append(f)
count = collections.Counter(fam)
width = max(3, max(len(str(v)) for v in count.values()))
seq, mname = collections.Counter(), []
for f in fam:
    seq[f] += 1
    mname.append(f'{f}{seq[f]:0{width}d}')
where = {n: mname[i] for i, ms in enumerate(new) for n in ms}


def header(i, ms):
    """the union of the origin modules' headers, name lists cut to what is used"""
    text = NL.join(lemmas[n][0] for n in ms)
    words = set(re.findall(r'[^\s()]+', text))
    lines, keyed = [], {}
    for o in dict.fromkeys(lemmas[n][1] for n in ms):
        for line in heads[o]:
            if line.startswith('module '):
                line = f'module {MOD}{mname[i]} where'
            u = USING.match(line)
            if u:
                key = u.group(1)
                if key not in keyed:
                    keyed[key] = []
                    lines.append(key)
                for x in u.group(2).split(';'):
                    x = x.strip()
                    if x and x not in keyed[key]: keyed[key].append(x)
            elif line not in lines or line == '':
                lines.append(line)
    out = []
    for line in lines:
        if line in keyed:
            # an outside module that needs lemmas of the tree (Five.TR2,
            # clifford-cs's Five/D/TR) is imported only for names the
            # lemmas mention: imported for another module's lemmas, it
            # made an import cycle
            x0 = line.split()[2]
            dependent = os.path.exists(modpath(x0)) and bool(needs(x0))
            xs = [x for x in keyed[line] if not (dependent or CUT.match(x)) or x in words]
            if xs or (not keyed[line] and not dependent):
                out.append(f'{line} using ({" ; ".join(xs)})')
        else:
            out.append(line)
    # drop the repeated blank lines the union leaves
    clean = []
    for line in out:
        if line == '' and clean and clean[-1] == '': continue
        clean.append(line)
    while clean and clean[-1] == '': clean.pop()
    return clean


# Every file touched is remembered, so that a layout with an import cycle
# (checked at the end) is undone.
touched = {}


def put(p, text):
    if p not in touched:
        touched[p] = open(p, encoding='utf-8').read() if os.path.exists(p) else None
    with open(p, 'w', encoding='utf-8', newline=NL) as f:
        f.write(text)


for m in mods:
    p = os.path.join(D, m + '.agda')
    touched[p] = open(p, encoding='utf-8').read()
    os.remove(p)
for i, ms in enumerate(new):
    hd = header(i, ms)
    imp = collections.defaultdict(set)
    for n in ms:
        for u in uses[n]:
            if where[u] != mname[i]: imp[where[u]].add(u)
    hd += [f'open import {MOD}{w} using ({" ; ".join(sorted(imp[w]))})' for w in sorted(imp)]
    body = (NL + NL).join(lemmas[n][0] for n in ms)
    put(os.path.join(D, mname[i] + '.agda'), NL.join(hd) + NL + NL + body + NL)
put(os.path.join(D, 'INDEX.txt'),
    ''.join(f'{mname[i]} {entry[n][1]} {entry[n][2]}' + NL for i, ms in enumerate(new) for n in ms)
    + ''.join(' '.join(e) + NL for e in kept_idx))

# The modules that use the lemmas: their imports of TREE/D, regrouped.
users = 0
for dirpath, _, files in os.walk(C):
    if 'scratchpad' in dirpath: continue
    for fn in files:
        if not fn.endswith('.agda'): continue
        if os.path.abspath(dirpath) == os.path.abspath(D) and fn[:-5] in mname: continue
        p = os.path.join(dirpath, fn)
        lines = open(p, encoding='utf-8').read().split(NL)
        got, first, keep = set(), None, []
        for line in lines:
            mm = IMPD.match(line)
            if mm:
                got |= {x.strip() for x in mm.group(2).split(';') if x.strip()}
                if first is None: first = len(keep)
                continue
            keep.append(line)
        if first is None: continue
        imp = collections.defaultdict(set)
        for n in got: imp[where[n]].add(n)
        keep[first:first] = [f'open import {MOD}{w} using ({" ; ".join(sorted(imp[w]))})' for w in sorted(imp)]
        put(p, NL.join(keep))
        users += 1
lv = collections.Counter(depth.values())
print(f'{TREE}/D: {len(order)} lemmas in {len(mods)} modules -> {len(new)} modules '
      f'({dict(count)}) over {max(lv)} levels; {users} using modules rewritten')

# No import cycle, through modules outside the tree included.
graph = {}


def imps(m):
    if m not in graph:
        p = modpath(m)
        src = open(p, encoding='utf-8').read() if os.path.exists(p) else ''
        graph[m] = [i for i in re.findall(r'^\s*(?:open\s+)?import\s+([A-Za-z][^\s(;]*)', src, re.M)
                    if os.path.exists(modpath(i))]
    return graph[m]


state = {}
for start in [MOD + x for x in mname]:
    if start in state: continue
    stack = [(start, iter(imps(start)))]
    state[start] = 1
    while stack:
        m, it = stack[-1]
        nxt = next(it, None)
        if nxt is None:
            state[m] = 2; stack.pop(); continue
        if state.get(nxt) == 1:
            cyc = [x for x, _ in stack][[x for x, _ in stack].index(nxt):] + [nxt]
            for p, text in touched.items():          # undo
                if text is None:
                    os.remove(p)
                else:
                    with open(p, 'w', encoding='utf-8', newline=NL) as f: f.write(text)
            sys.exit('import cycle, nothing changed: ' + ' -> '.join(cyc))
        if nxt not in state:
            state[nxt] = 1; stack.append((nxt, iter(imps(nxt))))
print('no import cycle')
