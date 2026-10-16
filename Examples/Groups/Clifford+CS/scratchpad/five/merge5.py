# Join the pickles of separate runs of load5.py (each run_all's base and
# some of its parts, RUN_PARTS) into one, in the order given: a
# derivation already present (the base, or a lemma two parts both built)
# is kept from its first run, and must prove the same equation.
#   python3 merge5.py OUT.pkl IN1.pkl IN2.pkl ...
import sys, pickle

out = {'derivs': [], 'L': {}, 'TRS': [], 'parts': []}
seen = {}
for path in sys.argv[2:]:
    D = pickle.load(open(path, 'rb'))
    for d in D['derivs']:
        if d['name'] in seen:
            assert (seen[d['name']]['lhs'], seen[d['name']]['rhs']) == (d['lhs'], d['rhs']), d['name']
            continue
        seen[d['name']] = d
        out['derivs'].append(d)
    for name, eq in D['L'].items():
        if name in out['L']:
            assert out['L'][name] == eq, name
        else:
            out['L'][name] = eq
    have = {t[0] for t in out['TRS']}
    out['TRS'] += [t for t in D.get('TRS', []) if t[0] not in have]
    out['parts'].append(D.get('parts'))
pickle.dump(out, open(sys.argv[1], 'wb'))
print(len(out['derivs']), 'derivations,', sum(len(d['steps']) for d in out['derivs']), 'steps,',
      len(out['TRS']), 'TR2 axioms, from', out['parts'])
