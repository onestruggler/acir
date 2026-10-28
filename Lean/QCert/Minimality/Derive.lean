/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Checking derivations

A derivation in a theory `Lift R` on `n` wires is given as a list of
equations already derived (`DEqn`: two circuits and a derivation, e.g. an
instance of an axiom placed on some wires, `DEqn.inst`) and a list of steps
on the word in operator order (`Step`): rewrite the occurrence of one side
of equation `e` at position `i` into its other side, or exchange the two
generators at positions `i, i + 1` when they act on disjoint wires.
`run` replays the steps and `derive` turns a successful replay, checked by
`decide`, into a derivation.
-/
import QCert.Minimality.Comm

namespace QCert.Minimality

open Circuit

variable {Gate : ℕ → Type}

/-- A circuit moved up `p` wires. -/
def shiftN {n : ℕ} : (p : ℕ) → Circuit Gate n →* Circuit Gate (n + p)
  | 0 => MonoidHom.id _
  | p + 1 => Circuit.shift.comp (shiftN p)

theorem derivable_shiftN {R : CRel Gate} {n : ℕ} {w v : Circuit Gate n} :
    ∀ (p : ℕ), Derivable (Lift R n) w v → Derivable (Lift R (n + p)) (shiftN p w) (shiftN p v)
  | 0, d => d
  | p + 1, d => derivable_shift (derivable_shiftN p d)

/-- A derived equation between `n`-wire circuits. -/
structure DEqn (R : CRel Gate) (n : ℕ) where
  lhs : Circuit Gate n
  rhs : Circuit Gate n
  proof : Derivable (Lift R n) lhs rhs

namespace DEqn

/-- An axiom of a presentation (or a law of the symmetry) on the wires
`m, …, m + k - 1` of `m + k + p`... placed with `m` idle wires below?  No:
on the bottom of `m + k` wires (`m` idle wires on top), moved up `p`
wires. -/
def inst {P : PropPresentation Gate} {S : P.Ax → Prop} (a : P.Ax) (ha : S a) (m p : ℕ) :
    DEqn (Padded (P.Base S)) (m + P.arity a + p) where
  lhs := shiftN p (Circuit.pad m (P.lhs a))
  rhs := shiftN p (Circuit.pad m (P.rhs a))
  proof := derivable_shiftN p (Derivable.of (Lift.rule (Padded.pad m (PropPresentation.Base.ax a ha))))

/-- A law of the symmetry, placed like `inst`. -/
def sym {P : PropPresentation Gate} {S : P.Ax → Prop} {k : ℕ} {w v : Circuit Gate k}
    (s : Sym P.swap k w v) (m p : ℕ) : DEqn (Padded (P.Base S)) (m + k + p) where
  lhs := shiftN p (Circuit.pad m w)
  rhs := shiftN p (Circuit.pad m v)
  proof := derivable_shiftN p (Derivable.of (Lift.rule (Padded.pad m (PropPresentation.Base.sym s))))

/-- A derived equation placed on the bottom of `m + k` wires, moved up `p`. -/
def place {Base : CRel Gate} {k : ℕ} (q : DEqn (Padded Base) k) (m p : ℕ) :
    DEqn (Padded Base) (m + k + p) where
  lhs := shiftN p (Circuit.pad m q.lhs)
  rhs := shiftN p (Circuit.pad m q.rhs)
  proof := derivable_shiftN p (derivable_pad m q.proof)

/-- A scalar moved up one wire is the scalar (the structural rule
`Lift.scalar`), on `m + 1` wires moved up `p`. -/
def scal {Base : CRel Gate} (c : Gate 0) (m p : ℕ) : DEqn (Padded Base) (m + 1 + p) where
  lhs := shiftN p (FreeMonoid.of (Gen.gate0 c).up)
  rhs := shiftN p (g0 c)
  proof := derivable_shiftN p (Derivable.of (Lift.scalar c))

/-- The two sides exchanged. -/
def symm {R : CRel Gate} {n : ℕ} (q : DEqn R n) : DEqn R n := ⟨q.rhs, q.lhs, q.proof.symm⟩

end DEqn

/-- A step of a derivation. -/
inductive Step
  /-- Rewrite, at position `i`, the left side of equation `e` into its right
  side (or the converse if `rev`). -/
  | rw (i e : ℕ) (rev : Bool)
  /-- Exchange the generators at positions `i` and `i + 1`. -/
  | swap (i : ℕ)
  /-- Move the generator at position `i` to position `j`, past generators it
  is apart from (a run of exchanges in one step). -/
  | slide (i j : ℕ)

section Run

variable [∀ k, DecidableEq (Gate k)] {R : CRel Gate} {n : ℕ}

/-- Rewrite the occurrence of `l` at position `i` of `w` into `r`. -/
def rwAt (l r : List (Gen Gate n)) (i : ℕ) (w : List (Gen Gate n)) : Option (List (Gen Gate n)) :=
  if (w.drop i).take l.length = l then some (w.take i ++ r ++ w.drop (i + l.length)) else none

/-- Exchange the generators at positions `i, i + 1` of `w`, if apart. -/
def swapAt (i : ℕ) (w : List (Gen Gate n)) : Option (List (Gen Gate n)) :=
  match w.drop i with
  | a :: b :: rest => if Gen.apart a b then some (w.take i ++ b :: a :: rest) else none
  | _ => none

/-- Move the generator at position `i` of `w` to position `j`, if it is apart
from every generator it passes. -/
def slideAt (i j : ℕ) (w : List (Gen Gate n)) : Option (List (Gen Gate n)) :=
  match w.drop i with
  | [] => none
  | x :: C =>
    if j < i then
      if ((w.take i).drop j).all (fun b => Gen.apart b x) then
        some (w.take j ++ x :: (w.take i).drop j ++ C)
      else none
    else
      if (C.take (j - i)).all (fun b => Gen.apart x b) ∧ j - i ≤ C.length then
        some (w.take i ++ C.take (j - i) ++ x :: C.drop (j - i))
      else none

/-- One step on a word. -/
def applyStep (eqs : List (DEqn R n)) (w : List (Gen Gate n)) : Step → Option (List (Gen Gate n))
  | .rw i e rev =>
    match eqs[e]? with
    | none => none
    | some q =>
      if rev then rwAt (FreeMonoid.toList q.rhs) (FreeMonoid.toList q.lhs) i w
      else rwAt (FreeMonoid.toList q.lhs) (FreeMonoid.toList q.rhs) i w
  | .swap i => swapAt i w
  | .slide i j => slideAt i j w

/-- The steps replayed on a word. -/
def run (eqs : List (DEqn R n)) : List Step → List (Gen Gate n) → Option (List (Gen Gate n))
  | [], w => some w
  | s :: ss, w =>
    match applyStep eqs w s with
    | none => none
    | some w' => run eqs ss w'

omit [∀ k, DecidableEq (Gate k)] in
theorem derivable_slice (A l r C : List (Gen Gate n))
    (h : Derivable (Lift R n) (FreeMonoid.ofList l) (FreeMonoid.ofList r)) :
    Derivable (Lift R n) (FreeMonoid.ofList (A ++ l ++ C)) (FreeMonoid.ofList (A ++ r ++ C)) := by
  simp only [FreeMonoid.ofList_append]
  exact ((Derivable.refl _).mul h).mul (Derivable.refl _)

theorem rwAt_sound {l r : List (Gen Gate n)} {i : ℕ} {w w' : List (Gen Gate n)}
    (hlr : Derivable (Lift R n) (FreeMonoid.ofList l) (FreeMonoid.ofList r))
    (h : rwAt l r i w = some w') :
    Derivable (Lift R n) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold rwAt at h
  split_ifs at h with hl
  cases h
  have eq : w.take i ++ l ++ w.drop (i + l.length) = w := by
    generalize hk : l.length = k at hl ⊢
    subst hl
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have e2 : FreeMonoid.ofList w = FreeMonoid.ofList (w.take i ++ l ++ w.drop (i + l.length)) := by
    rw [eq]
  rw [e2]
  exact derivable_slice _ _ _ _ hlr

omit [∀ k, DecidableEq (Gate k)] in
theorem swapAt_sound (hsc : ∀ c c' : Gate 0, c = c') {i : ℕ} {w w' : List (Gen Gate n)}
    (h : swapAt i w = some w') :
    Derivable (Lift R n) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold swapAt at h
  split at h
  · rename_i a b rest hd
    split_ifs at h with hab
    cases h
    have eq : w.take i ++ [a, b] ++ rest = w := by
      calc w.take i ++ [a, b] ++ rest = w.take i ++ w.drop i := by rw [hd]; simp
        _ = w := List.take_append_drop i w
    have e2 : FreeMonoid.ofList w = FreeMonoid.ofList (w.take i ++ [a, b] ++ rest) := by rw [eq]
    rw [e2, show w.take i ++ b :: a :: rest = w.take i ++ [b, a] ++ rest by simp]
    apply derivable_slice
    exact comm_apart hsc a b hab
  · cases h

omit [∀ k, DecidableEq (Gate k)] in
/-- A generator passes a list of generators it is apart from, leftwards. -/
theorem slide_left (hsc : ∀ c c' : Gate 0, c = c') (x : Gen Gate n) :
    ∀ B : List (Gen Gate n), B.all (fun b => Gen.apart b x) = true →
      Derivable (Lift R n) (FreeMonoid.ofList (B ++ [x])) (FreeMonoid.ofList (x :: B))
  | [], _ => Derivable.refl _
  | b :: B, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := slide_left hsc x B h.2
    have e1 : FreeMonoid.ofList (b :: B ++ [x]) =
        FreeMonoid.of b * FreeMonoid.ofList (B ++ [x]) := by
      rw [List.cons_append, FreeMonoid.ofList_cons]
    have e2 : FreeMonoid.ofList (x :: b :: B) =
        FreeMonoid.of x * FreeMonoid.of b * FreeMonoid.ofList B := by
      rw [FreeMonoid.ofList_cons, FreeMonoid.ofList_cons, mul_assoc]
    rw [e1, e2]
    refine ((Derivable.refl _).mul ih).trans ?_
    rw [FreeMonoid.ofList_cons, ← mul_assoc]
    exact (comm_apart hsc b x h.1).mul (Derivable.refl _)

omit [∀ k, DecidableEq (Gate k)] in
/-- A generator passes a list of generators it is apart from, rightwards. -/
theorem slide_right (hsc : ∀ c c' : Gate 0, c = c') (x : Gen Gate n) :
    ∀ B : List (Gen Gate n), B.all (fun b => Gen.apart x b) = true →
      Derivable (Lift R n) (FreeMonoid.ofList (x :: B)) (FreeMonoid.ofList (B ++ [x]))
  | [], _ => Derivable.refl _
  | b :: B, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := slide_right hsc x B h.2
    have e1 : FreeMonoid.ofList (x :: b :: B) =
        FreeMonoid.of x * FreeMonoid.of b * FreeMonoid.ofList B := by
      rw [FreeMonoid.ofList_cons, FreeMonoid.ofList_cons, mul_assoc]
    have e2 : FreeMonoid.ofList (b :: B ++ [x]) =
        FreeMonoid.of b * FreeMonoid.ofList (B ++ [x]) := by
      rw [List.cons_append, FreeMonoid.ofList_cons]
    rw [e1, e2]
    refine ((comm_apart hsc x b h.1).mul (Derivable.refl _)).trans ?_
    rw [mul_assoc, ← FreeMonoid.ofList_cons]
    exact (Derivable.refl _).mul ih

omit [∀ k, DecidableEq (Gate k)] in
theorem slideAt_sound (hsc : ∀ c c' : Gate 0, c = c') {i j : ℕ} {w w' : List (Gen Gate n)}
    (h : slideAt i j w = some w') :
    Derivable (Lift R n) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold slideAt at h
  split at h
  · cases h
  · rename_i x C hd
    have hw : w = w.take i ++ x :: C := by rw [← hd, List.take_append_drop]
    split_ifs at h with hji hall hall'
    · cases h
      have ht : w.take j ++ (w.take i).drop j = w.take i := by
        conv_rhs => rw [← List.take_append_drop j (w.take i)]
        rw [List.take_take, Nat.min_eq_left hji.le]
      have e : FreeMonoid.ofList w =
          FreeMonoid.ofList (w.take j ++ ((w.take i).drop j ++ [x]) ++ C) := by
        conv_lhs => rw [hw, ← ht]
        simp
      have e' : FreeMonoid.ofList (w.take j ++ x :: (w.take i).drop j ++ C) =
          FreeMonoid.ofList (w.take j ++ (x :: (w.take i).drop j) ++ C) := by simp
      rw [e, e']
      exact derivable_slice _ _ _ _ (slide_left hsc x _ hall)
    · cases h
      obtain ⟨hall', _⟩ := hall'
      have e : FreeMonoid.ofList w =
          FreeMonoid.ofList (w.take i ++ (x :: C.take (j - i)) ++ C.drop (j - i)) := by
        conv_lhs => rw [hw, ← List.take_append_drop (j - i) C]
        simp
      have e' : FreeMonoid.ofList (w.take i ++ C.take (j - i) ++ x :: C.drop (j - i)) =
          FreeMonoid.ofList (w.take i ++ (C.take (j - i) ++ [x]) ++ C.drop (j - i)) := by simp
      rw [e, e']
      exact derivable_slice _ _ _ _ (slide_right hsc x _ hall')

theorem applyStep_sound (hsc : ∀ c c' : Gate 0, c = c') (eqs : List (DEqn R n))
    (w w' : List (Gen Gate n)) (s : Step) (h : applyStep eqs w s = some w') :
    Derivable (Lift R n) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  cases s with
  | rw i e rev =>
    simp only [applyStep] at h
    split at h
    · cases h
    · rename_i q _
      cases rev
      · exact rwAt_sound (by simpa using q.proof) h
      · exact rwAt_sound (by simpa using q.proof.symm) h
  | swap i => exact swapAt_sound hsc h
  | slide i j => exact slideAt_sound hsc h

theorem run_sound (hsc : ∀ c c' : Gate 0, c = c') (eqs : List (DEqn R n)) :
    ∀ (steps : List Step) (w w' : List (Gen Gate n)), run eqs steps w = some w' →
      Derivable (Lift R n) (FreeMonoid.ofList w) (FreeMonoid.ofList w')
  | [], w, w', h => by simp only [run, Option.some.injEq] at h; subst h; rfl
  | s :: ss, w, w', h => by
    simp only [run] at h
    split at h
    · exact absurd h (by simp)
    · rename_i w₁ h₁
      exact (applyStep_sound hsc eqs w w₁ s h₁).trans (run_sound hsc eqs ss w₁ w' h)

/-- A derivation, checked by replaying its steps. -/
theorem derive (hsc : ∀ c c' : Gate 0, c = c') (eqs : List (DEqn R n)) (steps : List Step)
    {w v : Circuit Gate n} (h : run eqs steps (FreeMonoid.toList w) = some (FreeMonoid.toList v)) :
    Derivable (Lift R n) w v := by
  simpa using run_sound hsc eqs steps _ _ h

end Run

end QCert.Minimality
