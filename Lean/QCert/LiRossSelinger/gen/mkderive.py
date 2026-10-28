"""Write the derived-relation theorems and the macro checker into Derive.lean."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import json
from macros import BASE
from flatten import flatten, BOOT
from bfs import apply_steps
from leanfmt import *

ORDER = ['ksym2', 'ksym6', 'ksym4', 'ksym5', 'k21', 'k11', 'k31', 'relk4', 'k12', 'k22', 'k32', 'knk0']
DOC = {
    'ksym2': "(8c) `X_[b,c] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[b,c]`.",
    'ksym6': "(8d) `X_[b,d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[c,d]`.",
    'ksym4': "(8a) `X_[a,c] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[c,d] (−1)_[c] (−1)_[d]`.",
    'ksym5': "(8b) `X_[a,d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[b,d] X_[c,d] X_[b,d] (−1)_[b] (−1)_[c]`.",
    'k21': "(9e) `(−1)_[b] (−1)_[d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[a,b] X_[c,d]`.",
    'k11': "(9f) `(−1)_[c] (−1)_[d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[a,c] X_[b,d]`.",
    'k31': "(9d) `(−1)_[b] (−1)_[c] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[a,d] X_[b,c]`.",
    'relk4': "(9g) `(−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d] K ≈ K (−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d]`.",
    'k12': "(9a) `(−1)_[a] (−1)_[b] K ≈ K X_[a,c] X_[b,d] (−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d]`.",
    'k22': "(9b) `(−1)_[a] (−1)_[c] K ≈ K X_[a,b] X_[c,d] (−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d]`.",
    'knk0': "`K_[a,b,c,d] (−1)_[a] K_[a,b,c,d] ≈ X_[b,c] (−1)_[a] K_[a,b,c,d] (−1)_[a]`, from (4b).",
    'k32': "(9c) `(−1)_[a] (−1)_[d] K ≈ K X_[a,d] X_[b,c] (−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d]`.",
}
NAMES = ['a', 'b', 'c', 'd']

def thm(name):
    k, l, r = BASE[name]
    st = flatten(BOOT[name])
    assert apply_steps(l, st) == r, name
    return f"""/-- {DOC[name]} -/
theorem dr_{name} {{a b c d : Fin n}} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList {word_sym(l, NAMES)})
      (FreeMonoid.ofList {word_sym(r, NAMES)}) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ({word_lit(l)} : List (Gen 4)))
    (w' := {word_lit(r)})
    (sts := {steps_lit(st, step_r)})
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h
""", len(st)

out = []
tot = 0
for nm in ORDER:
    s, ln = thm(nm)
    out.append(s); tot += ln
mf = " | ".join(ORDER)
words = []
for nm in ORDER:
    k, l, r = BASE[nm]
    words.append(f"  | .{nm}, a, b, c, d, h1, h2, h3 =>\n    ({word_sym(l, NAMES)},\n      {word_sym(r, NAMES)})")
sound = "\n".join(f"  | .{nm}, _, _, _, _, h1, h2, h3 => dr_{nm} h1 h2 h3" for nm in ORDER)
out.append(f"""/-! ## Derived relations as steps -/

/-- The derived relations, on four increasing indices. -/
inductive MFam
  | {mf}
  deriving DecidableEq

/-- The two sides of a derived relation at `a < b < c < d`. -/
def mword : MFam → (a b c d : Fin m) → a < b → b < c → c < d → List (Gen m) × List (Gen m)
{chr(10).join(words)}

theorem mword_sound : ∀ (f : MFam) (a b c d : Fin m) (h1 : a < b) (h2 : b < c) (h3 : c < d),
    Derivable (Table1 m) (FreeMonoid.ofList (mword f a b c d h1 h2 h3).1)
      (FreeMonoid.ofList (mword f a b c d h1 h2 h3).2)
{sound}

/-- The sides of a derived relation at the given indices. -/
def msides : MFam → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | f, [a, b, c, d] => if h : a < b ∧ b < c ∧ c < d then some (mword f a b c d h.1 h.2.1 h.2.2)
      else none
  | _, _ => none

theorem msides_sound (f : MFam) (ps : List (Fin m)) (u v : List (Gen m))
    (h : msides f ps = some (u, v)) :
    Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v) := by
  unfold msides at h
  split at h
  · split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact mword_sound f _ _ _ _ hc.1 hc.2.1 hc.2.2
  · exact absurd h (by simp)

/-- Table 1 and the derived relations. -/
def bsides : Fam ⊕ MFam → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | .inl f, ps => sides f ps
  | .inr f, ps => msides f ps

theorem bsides_sound : ∀ (f : Fam ⊕ MFam) (ps : List (Fin m)) (u v : List (Gen m)),
    bsides f ps = some (u, v) → Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v)
  | .inl f, ps, u, v, h => Derivable.of (sides_sound h)
  | .inr f, ps, u, v, h => msides_sound f ps u v h

/-- Table 1 and the derived relations, read backwards when the flag is set. -/
def dsides : (Fam ⊕ MFam) × Bool → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | (f, false), ps => bsides f ps
  | (f, true), ps => (bsides f ps).map fun p => (p.1.reverse, p.2.reverse)

theorem dsides_sound : ∀ (f : (Fam ⊕ MFam) × Bool) (ps : List (Fin m)) (u v : List (Gen m)),
    dsides f ps = some (u, v) → Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v)
  | (f, false), ps, u, v, h => bsides_sound f ps u v h
  | (f, true), ps, u, v, h => by
    simp only [dsides, Option.map_eq_some_iff] at h
    obtain ⟨⟨u', v'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact rev_derivable (bsides_sound f ps u' v' h1)

/-- A derivation with derived relations as steps, checked by evaluation. -/
abbrev checkD (w w' : List (Gen m)) (sts : List (GStep ((Fam ⊕ MFam) × Bool) m)) : Bool :=
  gCheck dsides w w' sts

theorem checkD_sound {{w w' : List (Gen m)}} {{sts : List (GStep ((Fam ⊕ MFam) × Bool) m)}}
    (h : checkD w w' sts = true) :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') :=
  gCheck_sound dsides_sound h
""")
body = "\n".join(out)
path = os.path.join(LEAN, 'Derive.lean')
src = open(path, encoding='utf-8').read()
marker = '/-! ## Derived relations (generated) -/\n'
end = '\nend QCert.LiRossSelinger\n'
if marker in src:
    src = src[:src.index(marker)]
else:
    src = src[:src.rindex(end)] + '\n'
src = src + marker + '\n' + body + end
open(path, 'w', encoding='utf-8', newline='\n').write(src)
print('flattened steps total', tot)
