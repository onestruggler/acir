import re, sys
sys.stdout.reconfigure(encoding="utf-8")
lines = open(sys.argv[1], encoding='utf-8').read().split('\n')
deps = {}; order=[]
cur=None
for l in lines:
    if not l.strip(): continue
    parts = l.split('\t')
    head = parts[0]; cites = parts[2].split() if len(parts)>2 else []
    m = re.match(r'^(\d+)$', head)
    if m: cur = int(m.group(1))
    elif head.startswith('dec'): cur = head
    elif head.startswith('Proof of Lemma 8'): cur = head.replace('Proof of ','')
    elif head.startswith('Lemma D.3') or head.startswith('Lemma D.6'):
        pass  # continuation block of current proof
    else:
        cur = None
    if cur is None: continue
    deps.setdefault(cur, set())
    if cur not in order: order.append(cur)
    for c in cites:
        mm = re.match(r'^(\d+)(n|n−1|n−2|\d)?$', c.replace('𝑛','n'))
        if not mm: continue
        num = int(mm.group(1)); sub = mm.group(2)
        if num < 269: continue  # fixed width <=5 equation: semantic at n>=6
        if sub in ('n−1','n−2'): continue
        if sub and sub.isdigit(): continue  # base case k-qubit instance
        if num == cur: continue
        deps[cur].add(num)
roots = [k for k in order if isinstance(k,str)]
need=set(); stack=list(roots)
while stack:
    k=stack.pop()
    for d in deps.get(k,()):
        if d not in need:
            need.add(d); stack.append(d)
print("roots:", roots)
print("needed n-width eqs (%d):"%len(need), sorted(need))
print("not needed:", sorted(set(x for x in deps if isinstance(x,int)) - need))
# small equations cited by needed proofs (and roots)
small=set()
for k in list(need)+roots:
    pass
import collections
smallcites=collections.defaultdict(set)
cur=None
for l in lines:
    if not l.strip(): continue
    parts=l.split('\t'); head=parts[0]; cites=parts[2].split() if len(parts)>2 else []
    m=re.match(r'^(\d+)$',head)
    if m: cur=int(m.group(1))
    elif head.startswith('dec'): cur=head
    elif head.startswith('Proof of Lemma 8'): cur=head.replace('Proof of ','')
    elif head.startswith('Lemma D.3') or head.startswith('Lemma D.6'): pass
    else: cur=None
    if cur is None or not (cur in need or cur in roots): continue
    for c in cites:
        mm=re.match(r'^(\d+)$',c)
        if mm and int(mm.group(1))<269: smallcites[int(mm.group(1))].add(cur)
print("small eqs cited:", sorted(smallcites))
for s in sorted(smallcites):
    if s>=117: print(s, sorted(map(str,smallcites[s])))
