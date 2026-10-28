"""Writes Lib2.lean: the two-wire library (stabiliser facts of the width-2
coset table)."""
import facts2
import emit

E, Pa, out = facts2.build_stab()
facts2.d27_facts(E, Pa, out)
doc = '''# The two-wire lemma library

The lemmas of `gen/facts2.py` over (C6)-(C14) with free one-wire segments:
the swap lemmas, `X` and the other generators of `P` passing `CZ`, and the
stabiliser facts of the width-2 coset table (`Cos2.lean`).'''
src = emit.HEADER % (doc, 'mk_lib2.py', 'Local')
src += 'def lib2D : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ)) := [\n'
src += emit.lib_lines(E.lemmas) + ']\n\n'
src += '''theorem lib2_ok : libOk fo2 base2 (decLib lib2D) = true := by decide +kernel

theorem lib2_valid (hc : Complete 1) : Valid 2 (libTbl base2 (decLib lib2D)) :=
  libOk_valid fo2 (fo2_sound hc) base2 _ base2_valid lib2_ok

end QCert.QutritClifford
'''
open('../Lib2.lean', 'w', encoding='utf-8', newline='\n').write(src)
print('lemmas', len(E.lemmas), 'bytes', len(src))
