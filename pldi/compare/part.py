"""The Lean translation of CCX+H-3qubit-Tietze, as far as it went, against
the same Agda modules: code lines and code characters.

    python part.py ../.. part.json

Lean/QCert/ToffoliHadamardTietze translates the first modules of
Examples/Groups/CCX+H-3qubit-Tietze (the relations, the derivations replayed
from the authors' TIETZE2 files, the permutation certificates, the frame
words); each Lean module is compared with the Agda module of the same name.
Counted as th4.py counts: code lines as loc.py (blank lines and comments
excluded, `generated` by loc.kind), and code characters, the non-blank
characters outside comments.  figdata.py reads part.json for the second
Toffoli-Hadamard row of fig:compare(a).
"""
import datetime, json, os, subprocess, sys

ROOT = os.path.abspath(sys.argv[1])
OUT = sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, 'loc.py'), encoding='utf-8').read().split('def main')[0]
sys.argv = [sys.argv[0], ROOT, os.devnull]
exec(src)
th4 = open(os.path.join(here, 'th4.py'), encoding='utf-8').read()
exec(th4[th4.index('def chars'):th4.index('def lines')])

LEANF = 'Lean/QCert/ToffoliHadamardTietze'
AGDAF = 'Examples/Groups/CCX+H-3qubit-Tietze'


def measure(path, lang):
    return dict(count(path, lang), chars=chars(path, lang), generated=kind(path) == 'generated')


mods = {}
for f in sorted(set(files([LEANF], '.lean'))):
    rel = os.path.relpath(f, os.path.join(ROOT, LEANF)).replace(os.sep, '/')
    if rel.startswith('gen/'):
        continue
    m = rel[:-5]
    a = os.path.join(ROOT, AGDAF, m + '.agda')
    assert os.path.normpath(a) in TRACKED, m
    mods[m] = dict(agda=measure(a, 'agda'), lean=measure(f, 'lean'))

tot = {}
for lang in ('agda', 'lean'):
    xs = [v[lang] for v in mods.values()]
    tot[lang] = dict(files=len(xs), code=sum(x['code'] for x in xs),
                     generated_code=sum(x['code'] for x in xs if x['generated']),
                     chars=sum(x['chars'] for x in xs),
                     generated_chars=sum(x['chars'] for x in xs if x['generated']))
whole = [measure(f, 'agda') for f in sorted(set(files([AGDAF], '.agda')))]
rev = subprocess.run(['git', '-C', ROOT, 'rev-parse', '--short', 'HEAD'], capture_output=True,
                     text=True).stdout.strip()
out = dict(run=dict(date=datetime.datetime.now().astimezone().strftime('%Y-%m-%d %H:%M %z'),
                    revision=rev),
           totals=tot, agda_folder=dict(files=len(whole), code=sum(x['code'] for x in whole)),
           modules=mods)
json.dump(out, open(OUT, 'w'), indent=1)
print('modules', len(mods), tot, 'of the Agda folder', out['agda_folder'])
