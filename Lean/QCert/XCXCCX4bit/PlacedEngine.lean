/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A proof engine over placed letters on four wires

Translation of `PlacedEngine.agda`: `Engine` for the alphabet `PG` of
`Placed`.  An equation is a pair of lists of placed letters with a
derivation between their circuits (`Eqnp`: `4 ⊢ ιs lhs ≈ ιs rhs`), and a new
one is derived by a list of steps run on the letters,
`derive l r steps (by decide +kernel)`:

    Step.perm ys        the same word up to commuting letters on disjoint
                        wires (Placed.disj_comm), compared by the canonical
                        forms of Lib/Words (Commuting);
    Step.rw i e         rewrite the occurrence of e.lhs at position i to
                        e.rhs;
    Step.narrow i k ys  replace the k letters at position i by ys, where
                        both lie on three of the four wires (the first of
                        wires 3, 2, 1, 0 that they leave alone) and have the
                        same function: decided by evaluating semPs, and
                        sound by completeness on three wires
                        (Narrow3.narrowP).

Equations: `symE`, `relabelE` (along any permutation of the wires), `r7E`
(rule (7), `Placed.lhs₇ = Placed.rhs₇`), and `r7at a b c d`, rule (7) with
its wires 0, 1, 2, 3 on the wires `a, b, c, d`.  A derivation is checked by
running it (`run`, a Boolean computation on lists), and `run_sound` turns a
successful run into a derivation.  Lists are in diagram order, the head
first.

Names.  The Agda's `Eqnᵖ`, `eqnᵖ`, `lhs⁼`, `rhs⁼`, `sym⁼`, `relabel⁼`, `r7⁼`,
`Γᵖ`, `comm?`, `rewrite-at`, `matches-at`, `narrow-at`, `narrow-check` are
`Eqnp`, `Eqnp.eqnp`, `lhs`, `rhs`, `symE`, `relabelE`, `r7E`, `Γp`, `commP`,
`rewriteAt`, `matchesAt`, `narrowAt`, `narrowCheck`.  Write steps with their
qualified constructors (`Step.perm`, `Step.rw`, `Step.narrow`): `Kit`'s
`perm` and `rw` are visible in the namespace `QCert.XCXCCX4bit`.

**Deviation from the Agda.**  The Agda closes `derive l r steps refl`, the
type checker running the steps; here `run` is followed by one Boolean
comparison (`check`), decided by `decide +kernel`.  `comm?` is the Boolean
`commP` (`Placed.disjoint`) with its soundness `commP_sound`, as
`Lib/Words`' `Commuting` takes them.
-/
import QCert.XCXCCX4bit.Narrow3
import QCert.XCXCCX4bit.Lib.Words

namespace QCert.XCXCCX4bit.PlacedEngine

open QCert QCert.Circuit CircuitProp IndepProp
open Placed

/-! ## Equality and order of letters -/

def eqPG : PG → PG → Bool
  | .Xₚ t, .Xₚ t' => weq t t'
  | .CXₚ c t _, .CXₚ c' t' _ => weq c c' && weq t t'
  | .CCXₚ a b t _, .CCXₚ a' b' t' _ => weq a a' && (weq b b' && weq t t')
  | _, _ => false

theorem eqPG_sound : ∀ g h : PG, eqPG g h = true → g = h
  | .Xₚ t, .Xₚ t', e => by rw [weq_sound e]
  | .CXₚ c t _, .CXₚ c' t' _, e => by
    simp only [eqPG, Bool.and_eq_true] at e
    cases weq_sound e.1; cases weq_sound e.2; rfl
  | .CCXₚ a b t _, .CCXₚ a' b' t' _, e => by
    simp only [eqPG, Bool.and_eq_true] at e
    cases weq_sound e.1; cases weq_sound e.2.1; cases weq_sound e.2.2; rfl
  | .Xₚ _, .CXₚ _ _ _, e => nomatch e
  | .Xₚ _, .CCXₚ _ _ _ _, e => nomatch e
  | .CXₚ _ _ _, .Xₚ _, e => nomatch e
  | .CXₚ _ _ _, .CCXₚ _ _ _ _, e => nomatch e
  | .CCXₚ _ _ _ _, .Xₚ _, e => nomatch e
  | .CCXₚ _ _ _ _, .CXₚ _ _ _, e => nomatch e

def eqL : List PG → List PG → Bool
  | [], [] => true
  | x :: xs, y :: ys => eqPG x y && eqL xs ys
  | _, _ => false

theorem eqL_sound : ∀ xs ys : List PG, eqL xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, e => by
    simp only [eqL, Bool.and_eq_true] at e
    rw [eqPG_sound x y e.1, eqL_sound xs ys e.2]
  | [], _ :: _, e => nomatch e
  | _ :: _, [], e => nomatch e

/-- The order of the canonical forms: by a code of the letters. -/
def code : PG → ℕ
  | .Xₚ t => t.1
  | .CXₚ c t _ => 4 + (4 * c.1 + t.1)
  | .CCXₚ a b t _ => 20 + (16 * a.1 + (4 * b.1 + t.1))

def less (g h : PG) : Bool := Nat.blt (code g) (code h)

/-! ## Commutation -/

/-- The theory read back on words of letters: two words are related when
their circuits are. -/
def Γp : WRel PG := fun u v => 4 ⊢ ιw u ≈ ιw v

theorem back {u v : Word PG} (h : Derivable Γp u v) : 4 ⊢ ιw u ≈ ιw v := by
  let c : Con (Word PG) :=
    { r := fun u v => 4 ⊢ ιw u ≈ ιw v
      iseqv := ⟨fun _ => Derivable.refl _, Derivable.symm, Derivable.trans⟩
      mul' := fun {u u' v v'} hu hv => by
        show 4 ⊢ ιw (u * v) ≈ ιw (u' * v')
        rw [ιw_mul, ιw_mul]
        exact hu.mul hv }
  have : conGen Γp ≤ c := Con.conGen_le fun _ _ r => r
  exact this h

/-- Letters on disjoint wires commute: the test (the Agda's `comm?`). -/
def commP (x y : PG) : Bool := disjoint x y

theorem commP_sound (x y : PG) (h : commP x y = true) : Words.commutes Γp x y := by
  apply Derivable.of
  show 4 ⊢ ι x * (ι y * 1) ≈ ι y * (ι x * 1)
  rw [mul_one, mul_one]
  exact disj_comm x y h

/-- The canonical form of a word of letters modulo commutation. -/
abbrev commCanonical (xs : List PG) : List PG := Words.Commuting.commCanonical commP less xs

/-! ## Equations -/

/-- An equation between lists of placed letters, with its derivation. -/
structure Eqnp where
  eqnp ::
  lhs : List PG
  rhs : List PG
  prf : 4 ⊢ ιs lhs ≈ ιs rhs

def symE (e : Eqnp) : Eqnp := ⟨e.rhs, e.lhs, e.prf.symm⟩

/-- An equation on other wires. -/
def relabelE (R : Relabel) (e : Eqnp) : Eqnp :=
  ⟨e.lhs.map (relabel R), e.rhs.map (relabel R), relabel_eq R e.prf⟩

/-- Rule (7): `CCX_{3,2→1} CX_{1→0} CCX_{3,2→1} = CCX_{3,2→0} CX_{1→0}`. -/
def r7E : Eqnp := ⟨lhs₇, rhs₇, rule7₀⟩

/-- Rule (7) with its wires 0, 1, 2, 3 on `a, b, c, d`. -/
def r7at (a b c d : Wire) (p : distinct4 a b c d = true := by decide) : Eqnp :=
  relabelE (ρ4 a b c d p) r7E

/-! ## Running a derivation -/

inductive Step : Type
  | perm : List PG → Step
  | rw : ℕ → Eqnp → Step
  | narrow : ℕ → ℕ → List PG → Step

def rewriteAt (i : ℕ) (e : Eqnp) (xs : List PG) : List PG :=
  xs.take i ++ (e.rhs ++ (xs.drop i).drop e.lhs.length)

def matchesAt (i : ℕ) (e : Eqnp) (xs : List PG) : Bool :=
  eqL ((xs.drop i).take e.lhs.length) e.lhs

def narrowAt (i k : ℕ) (ys xs : List PG) : List PG :=
  xs.take i ++ (ys ++ (xs.drop i).drop k)

/-- `u` and `v` leave wire `m` alone and have the same function. -/
def checkAt (m : Wire) (u v : List PG) : Bool :=
  (every (avoids m) u && every (avoids m) v) && eqF 4 (semPs u) (semPs v)

def narrowCheck (u v : List PG) : Bool :=
  checkAt 3 u v || (checkAt 2 u v || (checkAt 1 u v || checkAt 0 u v))

def run : List Step → List PG → Option (List PG)
  | [], xs => some xs
  | .perm ys :: ss, xs => bif eqL (commCanonical xs) (commCanonical ys) then run ss ys else none
  | .rw i e :: ss, xs => bif matchesAt i e xs then run ss (rewriteAt i e xs) else none
  | .narrow i k ys :: ss, xs =>
    bif narrowCheck ((xs.drop i).take k) ys then run ss (narrowAt i k ys xs) else none

/-- The steps turn `l` into `r`. -/
def check (ss : List Step) (l r : List PG) : Bool :=
  match run ss l with
  | some y => eqL y r
  | none => false

/-! ## Soundness -/

/-- Replacing the `k` letters at position `i`. -/
theorem splice (i k : ℕ) (xs ys : List PG) (p : 4 ⊢ ιs ((xs.drop i).take k) ≈ ιs ys) :
    4 ⊢ ιs xs ≈ ιs (xs.take i ++ (ys ++ (xs.drop i).drop k)) := by
  conv_lhs => rw [← List.take_append_drop i xs, ← List.take_append_drop k (xs.drop i)]
  simp only [ιs_append]
  exact (Derivable.refl _).mul (p.mul (Derivable.refl _))

theorem checkAt_sound (m : Wire) (u v : List PG) (h : checkAt m u v = true) :
    4 ⊢ ιs u ≈ ιs v := by
  simp only [checkAt, Bool.and_eq_true] at h
  exact Narrow3.narrowP m u v h.1.1 h.1.2 (eqF_sound 4 _ _ h.2)

theorem perm_sound (xs ys : List PG) (e : commCanonical xs = commCanonical ys) :
    4 ⊢ ιs xs ≈ ιs ys := by
  have a := back (Words.Commuting.lemma_comm_canonical commP less commP_sound xs)
  have b := back (Words.Commuting.lemma_comm_canonical commP less commP_sound ys)
  have e' : Words.Commuting.commCanonical commP less xs =
      Words.Commuting.commCanonical commP less ys := e
  rw [ιw_ofList, ιw_ofList, e'] at a
  rw [ιw_ofList, ιw_ofList] at b
  exact a.trans b.symm

theorem rw_sound (i : ℕ) (e : Eqnp) (xs : List PG) (h : matchesAt i e xs = true) :
    4 ⊢ ιs xs ≈ ιs (rewriteAt i e xs) := by
  have hm : (xs.drop i).take e.lhs.length = e.lhs := eqL_sound _ _ h
  exact splice i e.lhs.length xs e.rhs (by rw [hm]; exact e.prf)

theorem narrow_sound (u v : List PG) (h : narrowCheck u v = true) : 4 ⊢ ιs u ≈ ιs v := by
  simp only [narrowCheck, Bool.or_eq_true] at h
  rcases h with h | h | h | h
  exacts [checkAt_sound 3 u v h, checkAt_sound 2 u v h, checkAt_sound 1 u v h,
    checkAt_sound 0 u v h]

theorem run_sound : ∀ (ss : List Step) (xs ys : List PG), run ss xs = some ys →
    4 ⊢ ιs xs ≈ ιs ys
  | [], xs, ys, h => by
    simp only [run, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | .perm zs :: ss, xs, ys, h => by
    simp only [run] at h
    cases hc : eqL (commCanonical xs) (commCanonical zs)
    · rw [hc] at h; simp at h
    · rw [hc] at h
      exact (perm_sound xs zs (eqL_sound _ _ hc)).trans (run_sound ss zs ys h)
  | .rw i e :: ss, xs, ys, h => by
    simp only [run] at h
    cases hm : matchesAt i e xs
    · rw [hm] at h; simp at h
    · rw [hm] at h
      exact (rw_sound i e xs hm).trans (run_sound ss _ ys h)
  | .narrow i k zs :: ss, xs, ys, h => by
    simp only [run] at h
    cases hn : narrowCheck ((xs.drop i).take k) zs
    · rw [hn] at h; simp at h
    · rw [hn] at h
      exact (splice i k xs zs (narrow_sound _ _ hn)).trans (run_sound ss _ ys h)

theorem check_sound {ss : List Step} {l r : List PG} (h : check ss l r = true) :
    4 ⊢ ιs l ≈ ιs r := by
  unfold check at h
  split at h
  · rename_i y hy
    rw [← eqL_sound _ _ h]; exact run_sound ss l y hy
  · simp at h

/-- A derivation: an equation from the steps that turn `l` into `r`. -/
def derive (l r : List PG) (ss : List Step) (h : check ss l r = true) : Eqnp :=
  ⟨l, r, check_sound h⟩

/-! ## Tests -/

/-- `X` on wire 0 passes the Toffoli on the wires above it (perm), two of
them cancel (narrow, on the wires 0 1 2), and rule (7) applies (rw). -/
private def test₁ : Eqnp := derive
  [PG.Xₚ 0, PG.CCXₚ 2 3 1, PG.Xₚ 0, PG.CXₚ 1 0, PG.CCXₚ 2 3 1]
  [PG.CCXₚ 2 3 0, PG.CXₚ 1 0]
  [Step.perm [PG.CCXₚ 2 3 1, PG.Xₚ 0, PG.Xₚ 0, PG.CXₚ 1 0, PG.CCXₚ 2 3 1],
   Step.narrow 1 2 [],
   Step.rw 0 (r7at 0 1 2 3)]
  (by decide +kernel)

/-- Rule (7) upside down, forwards and backwards, with narrow steps on the
wires 1 2 3 and 0 2 3. -/
private def test₂ : Eqnp := derive
  [PG.CCXₚ 0 1 2, PG.CXₚ 2 3, PG.CCXₚ 0 1 2, PG.CXₚ 2 3]
  [PG.CCXₚ 0 1 3, PG.CXₚ 3 2, PG.CXₚ 3 2]
  [Step.rw 0 (r7at 3 2 1 0),
   Step.narrow 1 2 [],
   Step.narrow 1 0 [PG.CXₚ 3 2, PG.CXₚ 3 2]]
  (by decide +kernel)

private def test₃ : Eqnp := derive
  [PG.CCXₚ 0 1 3, PG.CXₚ 2 3, PG.CXₚ 2 3]
  [PG.CCXₚ 0 1 2, PG.CXₚ 2 3, PG.CCXₚ 0 1 2, PG.CXₚ 2 3]
  [Step.rw 0 (symE (r7at 3 2 1 0))]
  (by decide +kernel)

/-- Two CNOTs on disjoint pairs of wires commute, and `CCX_{3,2→0}` is an
involution. -/
private def test₄ : Eqnp := derive
  [PG.CXₚ 1 0, PG.CXₚ 3 2, PG.CCXₚ 2 3 0, PG.CCXₚ 2 3 0]
  [PG.CXₚ 3 2, PG.CXₚ 1 0]
  [Step.narrow 2 2 [],
   Step.perm [PG.CXₚ 3 2, PG.CXₚ 1 0]]
  (by decide +kernel)

end QCert.XCXCCX4bit.PlacedEngine
