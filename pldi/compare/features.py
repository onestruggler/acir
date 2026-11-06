"""Syntactic features of the two corpora, per Table 1 row, over the files
classified as written (neither generated nor ported) by loc.py.

Agda: options (--safe, --without-K, --cubical-compatible), postulates,
`with` abstractions, `rewrite`, absurd patterns, reflection macros.
Lean: noncomputable definitions, `by` blocks, automation tactics, case
splits, `decide +kernel`.  Also the library modules imported (stdlib /
Mathlib), over all files.  Declarations marked noncomputable are counted
both over the written files (`noncomputable_decl`) and over all files
(`noncomputable_decl_all`, which includes the data of generated
certificates and kernel-only checkers), and so are Lean's `by` blocks and
automation calls (`by_all`, `automation_all`), the counts Section 3.3 quotes.
"""
import json, os, re, sys, collections

here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, 'loc.py'), encoding='utf-8').read().split('def main')[0]
src = src.replace("ROOT = sys.argv[1]", "ROOT = sys.argv[1]")
exec(src)

STDLIB = re.compile(r'^\s*(?:open\s+)?import\s+((?:Algebra|Axiom|Codata|Data|Effect|Function|Induction|IO|'
                    r'Level|Reflection|Relation|Size|Strict|Text|Tactic|Universe)(?:\.[^\s;()]+)?)', re.M)
EUC = re.compile(r'^\s*(?:open\s+)?import\s+((?:GauInt|Quantum|EucDomain)[^\s;()]*)', re.M)
MATHLIB = re.compile(r'^\s*import\s+(Mathlib[^\s]*)', re.M)

def strip_comments(text, lang):
    op, cl = ('{-', '-}') if lang == 'agda' else ('/-', '-/')
    out = []; depth = 0; i = 0
    while i < len(text):
        if depth:
            if text.startswith(op, i): depth += 1; i += 2
            elif text.startswith(cl, i): depth -= 1; i += 2
            else: i += 1
            continue
        if text.startswith('--', i):
            j = text.find('\n', i); i = len(text) if j < 0 else j
            continue
        if text.startswith(op, i): depth += 1; i += 2; continue
        out.append(text[i]); i += 1
    return ''.join(out)

AG = {
    'safe': re.compile(r'\{-#\s*OPTIONS[^#]*--safe'),
    'without_K': re.compile(r'\{-#\s*OPTIONS[^#]*--without-K'),
    'cubical_compatible': re.compile(r'\{-#\s*OPTIONS[^#]*--cubical-compatible'),
}
AG_BODY = {
    'postulate': re.compile(r'^\s*postulate\b', re.M),
    'with': re.compile(r'\swith\s'),
    'rewrite': re.compile(r'\srewrite\s'),
    'absurd': re.compile(r'\(\s*\)\s*$|\(\s*\)\s', re.M),
    'macro': re.compile(r'\bmacro\b|\bunquoteDecl\b|\bunquote\b'),
    'solver': re.compile(r'\bsolve\b|\bby-assoc\b|\bby-passoc\b|\bderive\b'),
}
LE_BODY = {
    'noncomputable': re.compile(r'\bnoncomputable\b'),
    'by': re.compile(r'\bby\b'),
    'automation': re.compile(r'\b(simp|simp_all|omega|ring|ring_nf|norm_num|linarith|nlinarith|positivity|'
                             r'aesop|grind|field_simp|decide|tauto|norm_cast|push_cast|polyrith|abel|gcongr)\b'),
    'case_split': re.compile(r'\b(cases|rcases|obtain|fin_cases|interval_cases|match|induction|split|by_cases)\b'),
    'decide_kernel': re.compile(r'decide\s*\+kernel'),
    'theorem': re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:theorem|lemma)\b', re.M),
}

# Declarations marked noncomputable (not `noncomputable section`), all files.
NC_DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?noncomputable\s+'
                     r'(?:def|abbrev|instance)\b', re.M)

out = {}
libs = {'agda_stdlib': set(), 'agda_eucdomain': set(), 'mathlib': set()}
for lang, table, ext in (('agda', AGDA, '.agda'), ('lean', LEAN, '.lean')):
    for row, paths in table.items():
        c = collections.Counter()
        for f in sorted(set(files(paths, ext))):
            if lang == 'lean' and '/gen/' in f.replace(os.sep, '/'):
                continue
            text = open(f, encoding='utf-8', errors='replace').read()
            if lang == 'agda':
                libs['agda_stdlib'].update(STDLIB.findall(text))
                libs['agda_eucdomain'].update(EUC.findall(text))
                for k, r in AG.items():
                    c[k] += bool(r.search(text))
            else:
                libs['mathlib'].update(MATHLIB.findall(text))
                c['noncomputable_decl_all'] += len(NC_DECL.findall(text))
                body_all = strip_comments(text, lang)
                c['by_all'] += len(LE_BODY['by'].findall(body_all))
                c['automation_all'] += len(LE_BODY['automation'].findall(body_all))
            c['files'] += 1
            if kind(f):
                continue
            body = strip_comments(text, lang)
            c['written_files'] += 1
            if lang == 'lean':
                c['noncomputable_decl'] += len(NC_DECL.findall(text))
            for k, r in (AG_BODY if lang == 'agda' else LE_BODY).items():
                c[k] += len(r.findall(body))
            # postulates count in every file, written or not
        if lang == 'agda':
            c['postulate_any'] = sum(len(AG_BODY['postulate'].findall(strip_comments(
                open(f, encoding='utf-8', errors='replace').read(), 'agda'))) for f in set(files(paths, ext)))
        out.setdefault(row, {})[lang] = dict(c)
out['_libs'] = {k: sorted(v) for k, v in libs.items()}
json.dump(out, open(sys.argv[2], 'w'), indent=1)
for row in out:
    if row.startswith('_'):
        continue
    print(row, 'AGDA', out[row]['agda'], '\n   LEAN', out[row]['lean'])
print({k: len(v) for k, v in libs.items()})
