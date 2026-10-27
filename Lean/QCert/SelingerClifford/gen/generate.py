"""Regenerate the modules Axioms, Lemmas and Rules1-Rules5 of
QCert/SelingerClifford from Selinger's supplement.

    python generate.py              write the modules next to this folder
    python generate.py --check      compare with the modules there instead
    python generate.py --out DIR    write them into DIR
    python generate.py --cache F    keep the derivations in the pickle F
                                    (read if it exists, written otherwise)

The supplement is the ancillary file clifford-supplement.txt of
arXiv:1310.6813 (see supp.py for where it is looked for).
"""
import argparse
import hashlib
import os
import pickle
import sys
import time

import engine
import genlean
import lemmas
import rules
import supp

LEAN = os.path.dirname(supp.HERE)
FILES = ['Axioms.lean', 'Lemmas.lean'] + [f'Rules{i}.lean' for i in range(1, 6)]


def log(msg):
    print(msg, flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--out', default=LEAN)
    ap.add_argument('--cache')
    args = ap.parse_args()

    if not os.path.exists(supp.SUPP):
        sys.exit(f'supplement not found: {supp.SUPP} (set SELINGER_SUPPLEMENT)')
    digest = hashlib.sha256(open(supp.SUPP, 'rb').read()).hexdigest()
    if digest != supp.SUPP_SHA256:
        log(f'warning: the supplement differs from the one used ({digest})')
    engine.check_db()
    log(f'{supp.check_supp()} proof lines of the supplement checked numerically')

    t0 = time.time()
    if args.cache and os.path.exists(args.cache):
        lemd, derivs = pickle.load(open(args.cache, 'rb'))
    else:
        lemd = lemmas.derive_all(log)
        derivs = rules.derive_all(log)
        if args.cache:
            pickle.dump((lemd, derivs), open(args.cache, 'wb'))
    log(f'derivations: {time.time() - t0:.0f} s')

    texts = genlean.gen_all(lemd, derivs, supp.parse_supp())
    bad = 0
    for fn in FILES:
        path = os.path.join(args.out, fn)
        if args.check:
            old = open(path, encoding='utf-8', newline='').read() if os.path.exists(path) else None
            same = old == texts[fn]
            bad += not same
            log(f'{fn}: {"same" if same else "DIFFERS"}')
        else:
            with open(path, 'w', encoding='utf-8', newline='\n') as f:
                f.write(texts[fn])
            log(f'wrote {path}')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
