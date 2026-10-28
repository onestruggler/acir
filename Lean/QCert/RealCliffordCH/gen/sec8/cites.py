import re, sys, json
sys.stdout.reconfigure(encoding="utf-8")
# Extract, for each "Proof of Equation (N)" block in Appendix D/E, the equations it cites,
# with their width subscripts.
txt = open(sys.argv[1], encoding='utf-8').read().split('\n')
start = int(sys.argv[2]) if len(sys.argv) > 2 else 11600
end = int(sys.argv[3]) if len(sys.argv) > 3 else len(txt)
blocks = []
cur = None
pat_head = re.compile(r'^Proof of Equations? \(([0-9]+)\)(?:𝑛|[0-9]*)?')
pat_cite = re.compile(r'\(([0-9]{1,3})\)(𝑛−2|𝑛−1|𝑛|[0-9])?')
for i in range(start, end):
    line = txt[i]
    m = pat_head.match(line)
    if m or line.startswith('Decoding Equation') or line.startswith('Lemma D.') or line.startswith('Proof of Lemma'):
        if cur: blocks.append(cur)
        if m:
            cur = {'eq': int(m.group(1)), 'line': i + 1, 'cites': [], 'head': line[:120]}
        elif line.startswith('Decoding Equation'):
            mm = re.match(r'Decoding Equation \(([0-9]+)\)', line)
            cur = {'eq': 'dec' + mm.group(1), 'line': i + 1, 'cites': [], 'head': line[:120]}
        else:
            cur = {'eq': line[:30], 'line': i + 1, 'cites': [], 'head': line[:120]}
        rest = line[m.end():] if m else line
    else:
        rest = line
    if cur is None: continue
    for c in pat_cite.finditer(rest):
        cur['cites'].append(c.group(1) + (c.group(2) or ''))
    for k in ['Lemma 5.1', 'Lemma D.3', 'Lemma D.6', 'Lemma 7.6', 'Lemma B.3', 'Lemma D.9', 'Lemma D.11', 'induction']:
        if k in rest:
            cur['cites'].append(k)
if cur: blocks.append(cur)
for b in blocks:
    seen = []
    for c in b['cites']:
        if c not in seen: seen.append(c)
    print(f"{b['eq']}\t@{b['line']}\t{' '.join(seen)}")
