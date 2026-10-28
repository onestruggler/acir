"""Writes Lib2Data.lean and Lib2_*.lean: the two-wire library (stabiliser
facts of the width-2 coset table)."""
import facts2
import mk_lib

E, Pa, out = facts2.build_stab()
facts2.d27_facts(E, Pa, out)
doc = '''# The two-wire lemma library

The lemmas of `gen/facts2.py` over (C6)-(C14) with free one-wire segments:
the swap lemmas, `X` and the other generators of `P` passing `CZ`, and the
stabiliser facts of the width-2 coset table.'''
files, last = mk_lib.write_lib('lib2', 'Lib2', E, 2, 'base2', 'fo2', 'fo2_sound', '(hc : Complete 1)',
                               doc, 'mk_lib2.py', chunk=40)
print(files, last, len(E.lemmas))
