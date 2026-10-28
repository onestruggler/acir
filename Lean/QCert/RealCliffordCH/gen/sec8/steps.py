import re, sys
sys.stdout.reconfigure(encoding="utf-8")
txt = open(sys.argv[1], encoding='utf-8').read().split('\n')
start, end = int(sys.argv[2]), int(sys.argv[3])
pat_head = re.compile(r'^(Proof of Equations? \(([0-9]+)\)|Decoding Equation \(([0-9]+)\)|Proof of Lemma [0-9.]+|Lemma D\.[0-9]+)')
cur=None; counts=[]
for i in range(start, end):
    l=txt[i]
    m=pat_head.match(l)
    if m:
        if cur: counts.append(cur)
        cur=[m.group(1)[:40], 0, i+1]
    if cur and l.strip()=='=': cur[1]+=1
    if cur and re.match(r'^\(.*\)\s*$', l) and False: pass
if cur: counts.append(cur)
tot=0
for c in counts:
    print(f"{c[0]}\t{c[1]}\t@{c[2]}"); tot+=c[1]
print("TOTAL", tot)
