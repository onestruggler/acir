/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): a checker for chains in a congruence

A chain between two words of Hadamard-Π's generators on concrete indices
`Fin m` is a list of steps (`CS`), each rewriting a segment of the current
word:

* `rel`: by an instance of a relation (a1)–(d2) of Figure 6 (`ruleG`), in
  either direction;
* `sem`: by a semantic identity on at most `K` indices: a pair of words on
  `Fin K` with the same matrix (decided over `ℤ√2`), pushed along a strictly
  increasing `e : Fin K → Fin m`;
* `ext`: by one of a list of extra equations, in either direction.

`run_sound` says that a successful run is a relation of any congruence that
contains the instances of (a1)–(d2), the semantic identities on `K` indices
and the extra equations (`Sound`).  The congruences used are pullbacks of
the congruence of Claim B, which contain the semantic identities on few
indices by the completeness of Figure 6 on those indices.
-/
import QCert.HadamardPi.Check
import QCert.HadamardPi.Theorem

namespace QCert.RealCliffordCH.Sec8.Chk

open QCert.HadamardPi FreeMonoid

variable {m K : ℕ}

/-- The relations (d3) and (d4), which `rel` steps exclude. -/
def bigTag : Tag → Bool
  | .d3 => true
  | .d4 => true
  | _ => false

/-- A generator of `Fin K` moved along `e`, if `e` keeps its order. -/
def pushG (e : Fin K → Fin m) : Gen K → Option (Gen m)
  | .Z a => some (.Z (e a))
  | .X a b _ => if h : e a < e b then some (.X (e a) (e b) h) else none
  | .H a b _ => if h : e a < e b then some (.H (e a) (e b) h) else none

/-- A word of `Fin K` moved along `e`. -/
def pushL (e : Fin K → Fin m) : List (Gen K) → Option (List (Gen m))
  | [] => some []
  | g :: l =>
    match pushG e g, pushL e l with
    | some x, some l' => some (x :: l')
    | _, _ => none

theorem pushL_eq {e : Fin K → Fin m} (he : StrictMono e) :
    ∀ l : List (Gen K), pushL e l = some (l.map (Gen.map e he))
  | [] => rfl
  | g :: l => by
    have hg : pushG e g = some (Gen.map e he g) := by
      cases g with
      | Z a => rfl
      | X a b h => simp only [pushG, dif_pos (he h)]; rfl
      | H a b h => simp only [pushG, dif_pos (he h)]; rfl
    simp only [pushL, hg, pushL_eq he l, List.map_cons]

/-- Two words on `Fin K` with the same matrix, decided over `ℤ√2`. -/
def SemOK (W R : List (Gen K)) : Prop :=
  rt2 ^ R.length • sprod rt2 (W.map Gen.toL) = rt2 ^ W.length • sprod rt2 (R.map Gen.toL)

instance (W R : List (Gen K)) : Decidable (SemOK W R) := by unfold SemOK; infer_instance

instance (e : Fin K → Fin m) : Decidable (StrictMono e) := by
  unfold StrictMono; infer_instance

/-- A step of a chain. -/
inductive CS (m K : ℕ)
  | rel (t : Tag) (ix : List (Fin m)) (pos : ℕ) (fwd : Bool)
  | sem (e : Fin K → Fin m) (W R : List (Gen K)) (pos : ℕ)
  | ext (i : ℕ) (pos : ℕ) (fwd : Bool)

/-- The equation a step rewrites by. -/
def CS.pair (E : List (List (Gen m) × List (Gen m))) : CS m K → Option (List (Gen m) × List (Gen m))
  | .rel t ix _ fwd =>
    if bigTag t then none else (ruleG t ix).map fun p => if fwd then p else p.swap
  | .sem e W R _ =>
    if StrictMono e ∧ SemOK W R then
      match pushL e W, pushL e R with
      | some P, some Q => some (P, Q)
      | _, _ => none
    else none
  | .ext i _ fwd => (E[i]?).map fun p => if fwd then p else p.swap

/-- The position of a step. -/
def CS.pos : CS m K → ℕ
  | .rel _ _ pos _ => pos
  | .sem _ _ _ pos => pos
  | .ext _ pos _ => pos

/-- Run a chain. -/
def run (E : List (List (Gen m) × List (Gen m))) : List (CS m K) → List (Gen m) →
    Option (List (Gen m))
  | [], w => some w
  | st :: sts, w =>
    match st.pair E with
    | some (P, Q) =>
      match rewriteAt P Q st.pos w with
      | some w' => run E sts w'
      | none => none
    | none => none

/-- What a congruence needs for chains to be sound in it. -/
structure Sound (c : Con (Word (Gen m))) (K : ℕ) (E : List (List (Gen m) × List (Gen m))) :
    Prop where
  rel : ∀ (t : Tag) (ix : List (Fin m)) (P Q : List (Gen m)), bigTag t = false →
    ruleG t ix = some (P, Q) → c (ofList P) (ofList Q)
  sem : ∀ (f : Fin K → Fin m) (hf : StrictMono f) (W R : List (Gen K)),
    wordMat invSqrt2 (ofList W) = wordMat invSqrt2 (ofList R) →
      c (ofList (W.map (Gen.map f hf))) (ofList (R.map (Gen.map f hf)))
  ext : ∀ p ∈ E, c (ofList p.1) (ofList p.2)

theorem rewriteAt_con {c : Con (Word (Gen m))} {P Q : List (Gen m)} (hd : c (ofList P) (ofList Q))
    {pos : ℕ} {w w' : List (Gen m)} (h : rewriteAt P Q pos w = some w') :
    c (ofList w) (ofList w') := by
  unfold rewriteAt at h
  split_ifs at h with hm
  cases h
  have hw : w = w.take pos ++ P ++ w.drop (pos + P.length) := by
    conv_lhs => rw [← List.take_append_drop pos w, ← List.take_append_drop P.length (w.drop pos)]
    rw [hm, List.drop_drop, List.append_assoc]
  conv_lhs => rw [hw]
  simp only [ofList_append]
  exact c.mul (c.mul (c.refl _) hd) (c.refl _)

theorem semOK_wordMat {W R : List (Gen K)} (h : SemOK W R) :
    wordMat invSqrt2 (ofList W) = wordMat invSqrt2 (ofList R) := by
  rw [wordMat_eq, wordMat_eq, toList_ofList, toList_ofList]
  exact lprod_eq_of_check _ _ (by simpa [SemOK] using h)

theorem pair_sound {c : Con (Word (Gen m))} {E : List (List (Gen m) × List (Gen m))}
    (hc : Sound c K E) {st : CS m K} {P Q : List (Gen m)} (h : st.pair E = some (P, Q)) :
    c (ofList P) (ofList Q) := by
  cases st with
  | rel t ix pos fwd =>
    by_cases hb : bigTag t = true
    · simp [CS.pair, hb] at h
    · rw [CS.pair, if_neg hb] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨P', Q'⟩, h1, h2⟩ := h
      have := hc.rel t ix P' Q' (by simpa using hb) h1
      cases fwd
      · simp only [Bool.false_eq_true, if_false, Prod.swap_prod_mk, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2; exact c.symm this
      · simp only [if_true, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2; exact this
  | sem e W R pos =>
    by_cases hb : StrictMono e ∧ SemOK W R
    · rw [CS.pair, if_pos hb, pushL_eq hb.1, pushL_eq hb.1] at h
      dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc.sem e hb.1 W R (semOK_wordMat hb.2)
    · simp [CS.pair, hb] at h
  | ext i pos fwd =>
    simp only [CS.pair, Option.map_eq_some_iff] at h
    obtain ⟨⟨P', Q'⟩, h1, h2⟩ := h
    have := hc.ext (P', Q') (List.mem_of_getElem? h1)
    cases fwd
    · simp only [Bool.false_eq_true, if_false, Prod.swap_prod_mk, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2; exact c.symm this
    · simp only [if_true, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2; exact this

/-- A successful run is a relation of every sound congruence. -/
theorem run_sound {c : Con (Word (Gen m))} {E : List (List (Gen m) × List (Gen m))}
    (hc : Sound c K E) : ∀ (sts : List (CS m K)) {w w' : List (Gen m)},
    run E sts w = some w' → c (ofList w) (ofList w')
  | [], w, w', h => by
    simp only [run, Option.some.injEq] at h; subst h; exact c.refl _
  | st :: sts, w, w', h => by
    simp only [run] at h
    split at h
    · rename_i P Q hp
      split at h
      · rename_i w1 hw1
        exact c.trans (rewriteAt_con (pair_sound hc hp) hw1) (run_sound hc sts h)
      · cases h
    · cases h

end QCert.RealCliffordCH.Sec8.Chk
