/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clément's relations and Figure 6 of Hadamard-Π generate the same congruence

A syntactic theorem, proved without either presentation theorem.  The
generators of Figure 6 (`QCert.HadamardPi.Gen`, two-level generators on
increasing indices) are among Clément's (`Gen`, any two distinct indices),
`ι` being the inclusion, and `tr` writes a Clément word over `𝒢ₙ`
(`Translate.lean`).  Then, in every dimension:

* every relation of Figure 6 is derivable from Clément's (`fig6_rel`,
  `FromFig6.lean`), and every relation of Clément's, written over `𝒢ₙ`, is
  derivable in Figure 6 (`rel_fig6`, `ToFig6.lean`);
* every Clément generator is equal, by Clément's relations, to its writing
  over `𝒢ₙ` (`rel_trg`: Lemma 1.7 of the notes, through Lemma 3.5 when
  `n ≥ 3` and through (22) when `n = 2`), and `tr ∘ ι` is the identity.

So two words over `𝒢ₙ` are equal by Figure 6 exactly when they are equal by
Clément's relations (`fig6_iff_clement`), two Clément words are equal by
Clément's relations exactly when their writings over `𝒢ₙ` are equal by
Figure 6 (`clement_iff_fig6`), and every Clément word equals its writing
over `𝒢ₙ` (`clement_tr`): each congruence is the pullback of the other
(`conGen_fig6`, `conGen_rel`), and `ι` induces an isomorphism of the
presented monoids.
-/
import QCert.Clement2019.FromFig6
import QCert.Clement2019.ToFig6

namespace QCert.Clement2019

open FreeMonoid
open HadamardPi (Fig6)

variable {n : ℕ}

/-- A rewriting step on lists, with its result. -/
theorem stepR {w w' : List (Gen n)} (k : ℕ) {L R : List (Gen n)}
    (h : Derivable Rel (ofList L) (ofList R)) (hm : (w.drop k).take L.length = L)
    (he : w.take k ++ R ++ w.drop (k + L.length) = w') : Derivable Rel (ofList w) (ofList w') :=
  he ▸ HadamardPi.rw_at w k h hm

section Two

variable (hn : n = 2) {a b : Fin n} (hab : a ≠ b)
include hn hab

/-- When `n = 2`: `H[b,a] ≈ X[a,b] H[a,b] X[a,b]`, by (22) and (3). -/
theorem hrev22 : Derivable Rel H_[b,a] (X_[a,b] * H_[a,b] * X_[a,b]) := by
  show Derivable Rel (ofList [.H b a hab.symm]) (ofList [.X a b hab, .H a b hab, .X a b hab])
  have L22 : Derivable Rel (ofList [.X a b hab, .H a b hab]) (ofList [.H b a hab.symm, .X a b hab]) :=
    Derivable.of (Rel.r22 hn hab)
  have L3 : Derivable Rel (ofList [.X a b hab, .X a b hab]) (ofList []) := Derivable.of (Rel.r3 hab)
  exact (stepR (w := [.H b a hab.symm]) (w' := [.H b a hab.symm, .X a b hab, .X a b hab]) 1 L3.symm
    rfl rfl).trans (stepR (w' := [.X a b hab, .H a b hab, .X a b hab]) 0 L22.symm rfl rfl)

/-- When `n = 2`: `X[a,b] ≈ X[b,a]`, by (22), (18), (11), (2), (3). -/
theorem xsym22 : Derivable Rel X_[a,b] X_[b,a] := by
  show Derivable Rel (ofList [.X a b hab]) (ofList [.X b a hab.symm])
  have L2 : Derivable Rel (ofList [.H a b hab, .H a b hab]) (ofList []) := Derivable.of (Rel.r2 hab)
  have L2' : Derivable Rel (ofList [.H b a hab.symm, .H b a hab.symm]) (ofList []) :=
    Derivable.of (Rel.r2 hab.symm)
  have L3' : Derivable Rel (ofList [.X b a hab.symm, .X b a hab.symm]) (ofList []) :=
    Derivable.of (Rel.r3 hab.symm)
  have L18 : Derivable Rel (ofList [.H a b hab, .X a b hab]) (ofList [.Z b, .H a b hab]) :=
    Derivable.of (Rel.r18 hab)
  have L18' : Derivable Rel (ofList [.H b a hab.symm, .X b a hab.symm])
      (ofList [.Z a, .H b a hab.symm]) := Derivable.of (Rel.r18 hab.symm)
  have L11' : Derivable Rel (ofList [.X b a hab.symm, .Z b]) (ofList [.Z a, .X b a hab.symm]) :=
    Derivable.of (Rel.r11 hab.symm)
  have hr : Derivable Rel (ofList [.H a b hab])
      (ofList [.X b a hab.symm, .H b a hab.symm, .X b a hab.symm]) := hrev22 hn hab.symm
  exact (stepR (w := [.X a b hab]) (w' := [.H a b hab, .H a b hab, .X a b hab]) 0 L2.symm
    rfl rfl).trans <|
    (stepR (w' := [.H a b hab, .Z b, .H a b hab]) 1 L18 rfl rfl).trans <|
    (stepR (w' := [.X b a hab.symm, .H b a hab.symm, .X b a hab.symm, .Z b, .H a b hab]) 0 hr
      rfl rfl).trans <|
    (stepR (w' := [.X b a hab.symm, .H b a hab.symm, .X b a hab.symm, .Z b, .X b a hab.symm,
      .H b a hab.symm, .X b a hab.symm]) 4 hr rfl rfl).trans <|
    (stepR (w' := [.X b a hab.symm, .H b a hab.symm, .Z a, .X b a hab.symm, .X b a hab.symm,
      .H b a hab.symm, .X b a hab.symm]) 2 L11' rfl rfl).trans <|
    (stepR (w' := [.X b a hab.symm, .H b a hab.symm, .Z a, .H b a hab.symm, .X b a hab.symm])
      3 L3' rfl rfl).trans <|
    (stepR (w' := [.X b a hab.symm, .H b a hab.symm, .H b a hab.symm, .X b a hab.symm,
      .X b a hab.symm]) 2 L18'.symm rfl rfl).trans <|
    (stepR (w' := [.X b a hab.symm, .X b a hab.symm, .X b a hab.symm]) 1 L2' rfl rfl).trans <|
    stepR (w' := [.X b a hab.symm]) 0 L3' rfl rfl

end Two

theorem two_of_lt_three {a b : Fin n} (hab : a ≠ b) (hn : ¬ 3 ≤ n) : n = 2 := by
  have := a.isLt; have := b.isLt; have := Fin.val_ne_of_ne hab; omega

/-- Lemma 1.7: `X[a,b] ≈ X[b,a]`. -/
theorem xsymR {a b : Fin n} (hab : a ≠ b) : Derivable Rel X_[a,b] X_[b,a] := by
  by_cases hn : 3 ≤ n
  · obtain ⟨o, hoa, hob⟩ := exists_third hn a b
    exact relK_false_rel (derC_map ![b, a, o] (by vec_inj) xsym)
  · exact xsym22 (two_of_lt_three hab hn) hab

/-- Lemma 1.7: `H[b,a] ≈ X[a,b] H[a,b] X[a,b]`. -/
theorem hrevR {a b : Fin n} (hab : a ≠ b) : Derivable Rel H_[b,a] (X_[a,b] * H_[a,b] * X_[a,b]) := by
  by_cases hn : 3 ≤ n
  · obtain ⟨o, hoa, hob⟩ := exists_third hn a b
    exact relK_false_rel (derC_map ![a, b, o] (by vec_inj) hrev)
  · exact hrev22 (two_of_lt_three hab hn) hab

/-- Every generator equals its writing over `𝒢ₙ`. -/
theorem rel_trg (g : Gen n) : Derivable Rel (of g) (ι (trg g)) := by
  cases g with
  | Z j => exact Derivable.refl _
  | X j k h =>
    by_cases hjk : j < k
    · simp only [trg, dif_pos hjk]; exact Derivable.refl _
    · simp only [trg, dif_neg hjk]; exact xsymR h
  | H j k h =>
    by_cases hjk : j < k
    · simp only [trg, dif_pos hjk]; exact Derivable.refl _
    · simp only [trg, dif_neg hjk]; exact hrevR h.symm

/-- Every Clément word equals, by Clément's relations, its writing over `𝒢ₙ`. -/
theorem clement_tr (w : Word (Gen n)) : Derivable Rel w (ι (tr w)) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of g w ih =>
    rw [map_mul, map_mul]
    exact (rel_trg g).mul ih

/-- Figure 6 derivations are Clément derivations. -/
theorem fig6_to_rel {w v : Word (HadamardPi.Gen n)} (h : Derivable Fig6 w v) :
    Derivable Rel (ι w) (ι v) := by
  have : conGen (Fig6 (n := n)) ≤ (conGen (Rel (n := n))).comap ι (map_mul ι) :=
    Con.conGen_le fun x y hxy => fig6_rel hxy
  exact this h

/-- Clément derivations, written over `𝒢ₙ`, are Figure 6 derivations. -/
theorem rel_to_fig6 {w v : Word (Gen n)} (h : Derivable Rel w v) :
    Derivable Fig6 (tr w) (tr v) := by
  have : conGen (Rel (n := n)) ≤ (conGen (Fig6 (n := n))).comap tr (map_mul tr) :=
    Con.conGen_le fun x y hxy => rel_fig6 hxy
  exact this h

/-- Figure 6 and Clément's relations agree on words over `𝒢ₙ`. -/
theorem fig6_iff_clement (w v : Word (HadamardPi.Gen n)) :
    Derivable Fig6 w v ↔ Derivable Rel (ι w) (ι v) := by
  refine ⟨fig6_to_rel, fun h => ?_⟩
  have := rel_to_fig6 h
  rwa [tr_ι, tr_ι] at this

/-- Clément's relations and Figure 6 agree on Clément words written over `𝒢ₙ`. -/
theorem clement_iff_fig6 (w v : Word (Gen n)) :
    Derivable Rel w v ↔ Derivable Fig6 (tr w) (tr v) :=
  ⟨rel_to_fig6, fun h => (clement_tr w).trans ((fig6_to_rel h).trans (clement_tr v).symm)⟩

/-- The congruence of Figure 6 is the pullback of Clément's along `ι`. -/
theorem conGen_fig6 :
    conGen (Fig6 (n := n)) = (conGen (Rel (n := n))).comap ι (map_mul ι) :=
  Con.ext fun w v => fig6_iff_clement w v

/-- The congruence of Clément's relations is the pullback of Figure 6's along `tr`. -/
theorem conGen_rel :
    conGen (Rel (n := n)) = (conGen (Fig6 (n := n))).comap tr (map_mul tr) :=
  Con.ext fun w v => clement_iff_fig6 w v

end QCert.Clement2019
