/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The circuits that keep wire 3 are faithful

Translation of `KFaithful.agda`.  `K`, the group of the four-wire circuits
whose letters do not target wire 3, is `C ⋊ P`: `P` the circuits of the
lower three wires and `C` the group of the controlled matchings (on the half
where wire 3 is 1).  Every letter of `K` is a word in the letters of the
lower wires and `G = CX₃₀` (`expand`: `CX₃₁` and `CX₃₂` are `CX₃₀` under a
swap, and a Toffoli controlled by wire 3 is equation (8) and the commutation
E3 under a relabelling, `expand_ok`).  A letter of the lower wires carries a
controlled matching to another (`push`: the frame of `G` by the letter's
Coxeter word, decided for the 105 labels by the frame lemma `W'`), and `G` is
the label `μ₀`, so every word of `K` is a word of labels followed by a word
of the lower wires (`nf`).  Two words of `K` with the same function: the
labels fix the lower half, so the two lower words agree there, hence
everywhere (they do not see wire 3), and are equal by completeness on three
wires; cancelling them, the two words of labels have the same function and
are equal by `CFaithful`.  That is `Faithful 3`, the hypothesis of `Four`.

Names.  The Agda's `rev-cancel`, `low-ok`, `push*`, `nf-ok`, `nf-low`,
`expand-ok`, `expand*`, `expand*-ok`, `expand*-basic`, `flip-comm`,
`mF*-low`, `Xs-low`, `faithful₃` are `rev_cancel`, `low_ok`, `push_s`,
`nf_ok`, `nf_low`, `expand_ok`, `expands`, `expands_ok`, `expands_basic`,
`flip_comm`, `mFs_low`, `Xs_low`, `faithful₃`; the Agda's `by` is `by_`.

**Deviations from the Agda.**  Words are multiplied left-associatively and
the Agda's associativity steps are reasoning in the quotient monoid
(`CircuitProp.cl`).  The Agda's `low-check` (one decision over all
letters) is decided letter by letter for the twelve letters of the lower
wires (`low_X₀`, …, `low_CCX₁₂₀`), with `low_mem` saying that they are the
letters that avoid wire 3: with one check over all letters the module
peaked at 6.7 GB of memory, 4.1 GB in this form.  `faithful₃` goes
through a lemma `core` that takes the two normal forms as variables (the
Agda's `where` block).
-/
import QCert.XCXCCX4bit.CFaithful
import QCert.XCXCCX4bit.KData
import QCert.XCXCCX4bit.Faithful

namespace QCert.XCXCCX4bit.KFaithful

open QCert QCert.Circuit CircuitProp IndepProp
open Placed ToPlaced PFrames PlacedEngine Faithful CRel CSem CCerts CFaithful KData CFrame
open CBase (G)

/-! ## Every letter is an involution -/

private theorem inv_check : forallPG (fun g => narrowCheck [g, g] []) = true := by
  decide +kernel

theorem gg (g : PG) : 4 ⊢ ι g * ι g ≈ 1 := by
  have h : 4 ⊢ ι g * (ι g * 1) ≈ 1 := narrow_sound [g, g] [] (forallPG_sound _ inv_check g)
  rwa [mul_one] at h

/-- A word of letters followed by its reverse. -/
theorem rev_cancel : ∀ p : List PG, 4 ⊢ ιs p * ιs p.reverse ≈ 1
  | [] => by
    show 4 ⊢ 1 * 1 ≈ 1
    rw [one_mul]
  | g :: p => by
    rw [List.reverse_cons, ιs_append]
    apply cl_eq.1
    have e1 := cl_eq.2 (rev_cancel p)
    have e2 := cl_eq.2 (gg g)
    simp only [ιs, cl_mul, cl_one, mul_one] at e1 e2 ⊢
    rw [mul_assoc, ← mul_assoc (cl (PropRel SRel) 4 (ιs p)), e1, one_mul, e2]

/-! ## The letters of the lower wires push across the controlled matchings -/

/-- The label of a matching conjugated by a letter of the lower wires. -/
def ρ (g : PG) (ν : L) : L := (find (matchF (rg g * frm ν))).getD ν

/-- A letter of the lower wires is the circuit of its Coxeter word and of the
inverse word (three-wire identities), and carries every label `ν` to `ρ g ν`
(the frame lemma's condition). -/
def low_ok (g : PG) : Bool :=
  (every (avoids 3) (pg (Pc 0 (rg g))) && eqF 4 (semPs (pg (Pc 0 (rg g)))) (semPs [g])) &&
    ((every (avoids 3) (pg (Pc 0 (inv (rg g)))) &&
        eqF 4 (semPs (pg (Pc 0 (inv (rg g))))) (semPs [g])) &&
      allFin 105 (fun ν => eqMatch (rg g * frm ν) (frm (ρ g ν))))

/-- The twelve letters of the lower wires. -/
private def lowL : List PG :=
  [PG.Xₚ 0, PG.Xₚ 1, PG.Xₚ 2, PG.CXₚ 0 1, PG.CXₚ 0 2, PG.CXₚ 1 0, PG.CXₚ 1 2, PG.CXₚ 2 0,
   PG.CXₚ 2 1, PG.CCXₚ 0 1 2, PG.CCXₚ 0 2 1, PG.CCXₚ 1 2 0]

private theorem low_mem : forallPG (fun g => !avoids 3 g || lowL.any (eqPG g)) = true := by
  decide +kernel

private theorem low_X₀ : low_ok (PG.Xₚ 0) = true := by decide +kernel
private theorem low_X₁ : low_ok (PG.Xₚ 1) = true := by decide +kernel
private theorem low_X₂ : low_ok (PG.Xₚ 2) = true := by decide +kernel
private theorem low_CX₀₁ : low_ok (PG.CXₚ 0 1) = true := by decide +kernel
private theorem low_CX₀₂ : low_ok (PG.CXₚ 0 2) = true := by decide +kernel
private theorem low_CX₁₀ : low_ok (PG.CXₚ 1 0) = true := by decide +kernel
private theorem low_CX₁₂ : low_ok (PG.CXₚ 1 2) = true := by decide +kernel
private theorem low_CX₂₀ : low_ok (PG.CXₚ 2 0) = true := by decide +kernel
private theorem low_CX₂₁ : low_ok (PG.CXₚ 2 1) = true := by decide +kernel
private theorem low_CCX₀₁₂ : low_ok (PG.CCXₚ 0 1 2) = true := by decide +kernel
private theorem low_CCX₀₂₁ : low_ok (PG.CCXₚ 0 2 1) = true := by decide +kernel
private theorem low_CCX₁₂₀ : low_ok (PG.CCXₚ 1 2 0) = true := by decide +kernel

/-- The Agda's `low-check`, letter by letter. -/
private theorem low_sound (g : PG) (a : avoids 3 g = true) : low_ok g = true := by
  have h := forallPG_sound _ low_mem g
  rw [a] at h
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at h
  obtain ⟨g', hg', e⟩ := h
  rw [eqPG_sound g g' e]
  simp only [lowL, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [low_X₀, low_X₁, low_X₂, low_CX₀₁, low_CX₀₂, low_CX₁₀, low_CX₁₂, low_CX₂₀, low_CX₂₁,
    low_CCX₀₁₂, low_CCX₀₂₁, low_CCX₁₂₀]

private theorem one (g : PG) (a : avoids 3 g = true) : every (avoids 3) [g] = true := by
  simp only [every, a, Bool.and_true]

private theorem ιg_Pc (g : PG) (a : avoids 3 g = true) : 4 ⊢ ι g ≈ Pc 0 (rg g) := by
  have h := low_sound g a
  simp only [low_ok, Bool.and_eq_true] at h
  have e : 4 ⊢ ιs (pg (Pc 0 (rg g))) ≈ ιs [g] :=
    Narrow3.narrowP 3 _ _ h.1.1 (one g a) (eqF_sound 4 _ _ h.1.2)
  have e' : 4 ⊢ Pc 0 (rg g) ≈ ι g * 1 := (pg_ok _).trans e
  rw [mul_one] at e'
  exact e'.symm

private theorem ιg_Pcinv (g : PG) (a : avoids 3 g = true) : 4 ⊢ ι g ≈ Pc 0 (inv (rg g)) := by
  have h := low_sound g a
  simp only [low_ok, Bool.and_eq_true] at h
  have e : 4 ⊢ ιs (pg (Pc 0 (inv (rg g)))) ≈ ιs [g] :=
    Narrow3.narrowP 3 _ _ h.2.1.1 (one g a) (eqF_sound 4 _ _ h.2.1.2)
  have e' : 4 ⊢ Pc 0 (inv (rg g)) ≈ ι g * 1 := (pg_ok _).trans e
  rw [mul_one] at e'
  exact e'.symm

private theorem match_ok (g : PG) (a : avoids 3 g = true) (ν : L) :
    eqMatch (rg g * frm ν) (frm (ρ g ν)) = true := by
  have h := low_sound g a
  simp only [low_ok, Bool.and_eq_true] at h
  exact allFin_sound 105 _ h.2.2 ν

theorem push (g : PG) (a : avoids 3 g = true) (ν : L) :
    4 ⊢ ι g * Xm ν ≈ Xm (ρ g ν) * ι g := by
  have s1 : 4 ⊢ ι g * Xm ν ≈ ι g * Xm ν * ι g * ι g := by
    apply cl_eq.1
    have h := cl_eq.2 (gg g)
    simp only [cl_mul, cl_one] at h ⊢
    rw [mul_assoc (cl (PropRel SRel) 4 (ι g) * cl (PropRel SRel) 4 (Xm ν)), h, mul_one]
  have s2 : 4 ⊢ ι g * Xm ν * ι g * ι g ≈ Pc 0 (rg g) * Xm ν * Pc 0 (inv (rg g)) * ι g :=
    (((ιg_Pc g a).mul (Derivable.refl _)).mul (ιg_Pcinv g a)).mul (Derivable.refl _)
  have e3 : Pc 0 (rg g) * Xm ν * Pc 0 (inv (rg g)) = Fr G (rg g * frm ν) :=
    Fr_conj G (rg g) (frm ν)
  rw [e3] at s2
  exact s1.trans (s2.trans ((W' _ _ (match_ok g a ν)).mul (Derivable.refl _)))

theorem push_s (g : PG) (a : avoids 3 g = true) :
    ∀ as : List L, 4 ⊢ ι g * Xs as ≈ Xs (as.map (ρ g)) * ι g
  | [] => by
    show 4 ⊢ ι g * 1 ≈ 1 * ι g
    rw [mul_one, one_mul]
  | ν :: as => by
    apply cl_eq.1
    have e1 := cl_eq.2 (push g a ν)
    have e2 := cl_eq.2 (push_s g a as)
    simp only [Xs, LabelEngine.Xs, List.map_cons, cl_mul] at e1 e2 ⊢
    rw [← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]

/-! ## The normal form over the lower letters and G -/

def isG (g : PG) : Bool := eqPG g (PG.CXₚ 3 0)

def basic (g : PG) : Bool := isG g || avoids 3 g

abbrev NF : Type := List L × List PG

def cons : Bool → PG → NF → NF
  | true, _, (a, p) => (μ₀ :: a, p)
  | false, g, (a, p) => (a.map (ρ g), g :: p)

def nf : List PG → NF
  | [] => ([], [])
  | g :: u => cons (isG g) g (nf u)

/-- `G` is the label `μ₀`, whose frame word is `ε`. -/
private theorem Xμ₀ : 4 ⊢ Xm μ₀ ≈ G := by
  have e : frm μ₀ = 1 := rfl
  show 4 ⊢ Fr G (frm μ₀) ≈ G
  rw [e, Fr_one]

private theorem cons_ok : ∀ (b : Bool) (g : PG), isG g = b → (b || avoids 3 g) = true →
    ∀ r : NF, 4 ⊢ ι g * (Xs r.1 * ιs r.2) ≈ Xs (cons b g r).1 * ιs (cons b g r).2
  | true, g, e, _, (a, p) => by
    obtain rfl := eqPG_sound g (PG.CXₚ 3 0) e
    show 4 ⊢ G * (Xs a * ιs p) ≈ Xm μ₀ * Xs a * ιs p
    rw [mul_assoc]
    exact Xμ₀.symm.mul (Derivable.refl _)
  | false, g, _, h, (a, p) => by
    show 4 ⊢ ι g * (Xs a * ιs p) ≈ Xs (a.map (ρ g)) * (ι g * ιs p)
    rw [← mul_assoc, ← mul_assoc]
    exact (push_s g h a).mul (Derivable.refl _)

private theorem cons_low : ∀ (b : Bool) (g : PG), (b || avoids 3 g) = true → ∀ r : NF,
    every (avoids 3) r.2 = true → every (avoids 3) (cons b g r).2 = true
  | true, _, _, (_, _), hp => hp
  | false, g, h, (_, _), hp => by
    simp only [Bool.false_or] at h
    show (avoids 3 g && every (avoids 3) _) = true
    rw [h, hp]
    rfl

theorem nf_ok : ∀ u : List PG, every basic u = true →
    4 ⊢ ιs u ≈ Xs (nf u).1 * ιs (nf u).2
  | [], _ => by
    show 4 ⊢ 1 ≈ 1 * 1
    rw [one_mul]
  | g :: u, h => by
    simp only [every, Bool.and_eq_true] at h
    exact ((Derivable.refl (ι g)).mul (nf_ok u h.2)).trans
      (cons_ok (isG g) g rfl h.1 (nf u))

theorem nf_low : ∀ u : List PG, every basic u = true → every (avoids 3) (nf u).2 = true
  | [], _ => rfl
  | g :: u, h => by
    simp only [every, Bool.and_eq_true] at h
    exact cons_low (isG g) g h.1 (nf u) (nf_low u h.2)

/-! ## Every letter of K in the lower letters and G -/

private def SW01 : List PG := [PG.CXₚ 0 1, PG.CXₚ 1 0, PG.CXₚ 0 1]
private def SW02 : List PG := [PG.CXₚ 0 2, PG.CXₚ 2 0, PG.CXₚ 0 2]
private def E31 : List PG := SW01 ++ PG.CXₚ 3 0 :: SW01
private def E32 : List PG := SW02 ++ PG.CXₚ 3 0 :: SW02

/-- `CX₃ₜ` is `CX₃₀` under the swap of wires 0 and `t`; `CCX` from wires
`a, 3` onto `t` is `CX₃ᵦ CCXᵦₐₜ CX₃ᵦ CCXᵦₐₜ`, `b` the third lower wire. -/
def expand : PG → List PG
  | .CXₚ 3 1 _ => E31
  | .CXₚ 3 2 _ => E32
  | .CCXₚ 0 3 1 _ => E32 ++ PG.CCXₚ 0 2 1 :: (E32 ++ [PG.CCXₚ 0 2 1])
  | .CCXₚ 0 3 2 _ => E31 ++ PG.CCXₚ 0 1 2 :: (E31 ++ [PG.CCXₚ 0 1 2])
  | .CCXₚ 1 3 0 _ => E32 ++ PG.CCXₚ 1 2 0 :: (E32 ++ [PG.CCXₚ 1 2 0])
  | .CCXₚ 1 3 2 _ => [PG.CXₚ 3 0, PG.CCXₚ 0 1 2, PG.CXₚ 3 0, PG.CCXₚ 0 1 2]
  | .CCXₚ 2 3 0 _ => E31 ++ PG.CCXₚ 1 2 0 :: (E31 ++ [PG.CCXₚ 1 2 0])
  | .CCXₚ 2 3 1 _ => [PG.CXₚ 3 0, PG.CCXₚ 0 2 1, PG.CXₚ 3 0, PG.CCXₚ 0 2 1]
  | g => [g]

private def d31 : Eqnp := derive E31 [PG.CXₚ 3 1] [Step.narrow 0 7 [PG.CXₚ 3 1]] (by decide +kernel)
private def d32 : Eqnp := derive E32 [PG.CXₚ 3 2] [Step.narrow 0 7 [PG.CXₚ 3 2]] (by decide +kernel)

/-- Equation (8) and E3 with wires 0, 1, 2, 3 on `t, 3, b, a`. -/
private def d031 : Eqnp := derive (expand (PG.CCXₚ 0 3 1)) [PG.CCXₚ 0 3 1]
  [Step.narrow 0 7 [PG.CXₚ 3 2], Step.narrow 2 7 [PG.CXₚ 3 2],
   Step.rw 0 (relabelE (ρ4 1 3 2 0) Equations4.eq8E),
   Step.rw 1 (symE (relabelE (ρ4 1 3 2 0) Equations4.E3E)), Step.narrow 0 2 []]
  (by decide +kernel)
private def d032 : Eqnp := derive (expand (PG.CCXₚ 0 3 2)) [PG.CCXₚ 0 3 2]
  [Step.narrow 0 7 [PG.CXₚ 3 1], Step.narrow 2 7 [PG.CXₚ 3 1],
   Step.rw 0 (relabelE (ρ4 2 3 1 0) Equations4.eq8E),
   Step.rw 1 (symE (relabelE (ρ4 2 3 1 0) Equations4.E3E)), Step.narrow 0 2 []]
  (by decide +kernel)
private def d130 : Eqnp := derive (expand (PG.CCXₚ 1 3 0)) [PG.CCXₚ 1 3 0]
  [Step.narrow 0 7 [PG.CXₚ 3 2], Step.narrow 2 7 [PG.CXₚ 3 2],
   Step.rw 0 (relabelE (ρ4 0 3 2 1) Equations4.eq8E),
   Step.rw 1 (symE (relabelE (ρ4 0 3 2 1) Equations4.E3E)), Step.narrow 0 2 []]
  (by decide +kernel)
private def d132 : Eqnp := derive (expand (PG.CCXₚ 1 3 2)) [PG.CCXₚ 1 3 2]
  [Step.rw 0 (relabelE (ρ4 2 3 0 1) Equations4.eq8E),
   Step.rw 1 (symE (relabelE (ρ4 2 3 0 1) Equations4.E3E)), Step.narrow 0 2 []]
  (by decide +kernel)
private def d230 : Eqnp := derive (expand (PG.CCXₚ 2 3 0)) [PG.CCXₚ 2 3 0]
  [Step.narrow 0 7 [PG.CXₚ 3 1], Step.narrow 2 7 [PG.CXₚ 3 1],
   Step.rw 0 (relabelE (ρ4 0 3 1 2) Equations4.eq8E),
   Step.rw 1 (symE (relabelE (ρ4 0 3 1 2) Equations4.E3E)), Step.narrow 0 2 []]
  (by decide +kernel)
private def d231 : Eqnp := derive (expand (PG.CCXₚ 2 3 1)) [PG.CCXₚ 2 3 1]
  [Step.rw 0 (relabelE (ρ4 1 3 0 2) Equations4.eq8E),
   Step.rw 1 (symE (relabelE (ρ4 1 3 0 2) Equations4.E3E)), Step.narrow 0 2 []]
  (by decide +kernel)

/-- From a derivation of a letter's expansion. -/
private theorem by_ (g : PG) (e : 4 ⊢ ιs (expand g) ≈ ι g * 1) : 4 ⊢ ι g ≈ ιs (expand g) := by
  rw [mul_one] at e
  exact e.symm

/-- A letter whose expansion is itself. -/
private theorem self (g : PG) (e : expand g = [g]) : 4 ⊢ ι g ≈ ιs (expand g) := by
  rw [e]
  show 4 ⊢ ι g ≈ ι g * 1
  rw [mul_one]

theorem expand_ok : ∀ g : PG, 4 ⊢ ι g ≈ ιs (expand g)
  | .Xₚ _ => self _ rfl
  | .CXₚ 0 _ _ => self _ rfl
  | .CXₚ 1 _ _ => self _ rfl
  | .CXₚ 2 _ _ => self _ rfl
  | .CXₚ 3 0 _ => self _ rfl
  | .CXₚ 3 1 _ => by_ _ d31.prf
  | .CXₚ 3 2 _ => by_ _ d32.prf
  | .CXₚ 3 3 _ => self _ rfl
  | .CCXₚ 0 0 _ _ => self _ rfl
  | .CCXₚ 0 1 _ _ => self _ rfl
  | .CCXₚ 0 2 _ _ => self _ rfl
  | .CCXₚ 0 3 0 _ => self _ rfl
  | .CCXₚ 0 3 1 _ => by_ _ d031.prf
  | .CCXₚ 0 3 2 _ => by_ _ d032.prf
  | .CCXₚ 0 3 3 _ => self _ rfl
  | .CCXₚ 1 0 _ _ => self _ rfl
  | .CCXₚ 1 1 _ _ => self _ rfl
  | .CCXₚ 1 2 _ _ => self _ rfl
  | .CCXₚ 1 3 0 _ => by_ _ d130.prf
  | .CCXₚ 1 3 1 _ => self _ rfl
  | .CCXₚ 1 3 2 _ => by_ _ d132.prf
  | .CCXₚ 1 3 3 _ => self _ rfl
  | .CCXₚ 2 0 _ _ => self _ rfl
  | .CCXₚ 2 1 _ _ => self _ rfl
  | .CCXₚ 2 2 _ _ => self _ rfl
  | .CCXₚ 2 3 0 _ => by_ _ d230.prf
  | .CCXₚ 2 3 1 _ => by_ _ d231.prf
  | .CCXₚ 2 3 2 _ => self _ rfl
  | .CCXₚ 2 3 3 _ => self _ rfl
  | .CCXₚ 3 _ _ _ => self _ rfl

private theorem basic_check :
    forallPG (fun g => imp (keeps 3 g) (every basic (expand g))) = true := by
  decide +kernel

def expands : List PG → List PG
  | [] => []
  | g :: u => expand g ++ expands u

theorem expands_ok : ∀ u : List PG, 4 ⊢ ιs u ≈ ιs (expands u)
  | [] => Derivable.refl _
  | g :: u => by
    rw [expands, ιs_append]
    exact (expand_ok g).mul (expands_ok u)

theorem expands_basic : ∀ u : List PG, every (keeps 3) u = true → every basic (expands u) = true
  | [], _ => rfl
  | g :: u, h => by
    simp only [every, Bool.and_eq_true] at h
    exact every_append basic _ _ (imp_sound (forallPG_sound _ basic_check g) h.1)
      (expands_basic u h.2)

/-! ## Semantics -/

/-- Wire 3 flipped. -/
def flip3 : Bits 4 → Bits 4
  | a ∷ b ∷ c ∷ d ∷ .nil => a ∷ b ∷ c ∷ (!d) ∷ .nil

private theorem flip_check :
    forallPG (fun g => imp (avoids 3 g)
      (allB 4 (fun x => eqV (semP g (flip3 x)) (flip3 (semP g x))))) = true := by
  decide +kernel

/-- A word that avoids wire 3 does not see it. -/
theorem flip_comm : ∀ p : List PG, every (avoids 3) p = true →
    ∀ x, semPs p (flip3 x) = flip3 (semPs p x)
  | [], _, _ => rfl
  | g :: p, h, x => by
    simp only [every, Bool.and_eq_true] at h
    have h1 : semP g (flip3 x) = flip3 (semP g x) :=
      eqV_sound _ _ (allB_sound 4 _ (imp_sound (forallPG_sound _ flip_check g) h.1) x)
    show semPs p (semP g (flip3 x)) = flip3 (semPs p (semP g x))
    rw [h1]
    exact flip_comm p h.2 _

/-- The controlled matchings fix the lower half. -/
theorem mFs_low : ∀ (ws : List L) (a b c : Bool),
    mFs ws (a ∷ b ∷ c ∷ false ∷ .nil) = a ∷ b ∷ c ∷ false ∷ .nil
  | [], _, _, _ => rfl
  | _ :: ws, a, b, c => mFs_low ws a b c

theorem Xs_low (ws : List L) (a b c : Bool) :
    sem (Xs ws) (a ∷ b ∷ c ∷ false ∷ .nil) = a ∷ b ∷ c ∷ false ∷ .nil :=
  (Xs_sem ws _).trans (mFs_low ws a b c)

/-! ## Faithfulness of K -/

/-- Two words with the same function, each a word of labels followed by a
lower word. -/
private theorem core (u v : List PG) (e : semPs u ≐ semPs v) (a b : List L) (p q : List PG)
    (eu : 4 ⊢ ιs u ≈ Xs a * ιs p) (ev : 4 ⊢ ιs v ≈ Xs b * ιs q)
    (hp : every (avoids 3) p = true) (hq : every (avoids 3) q = true) : 4 ⊢ ιs u ≈ ιs v := by
  have sem' : sem (Xs a * ιs p) ≐ sem (Xs b * ιs q) := fun x =>
    (sound eu x).symm.trans
      ((ιs_sem u x).trans ((e x).trans ((ιs_sem v x).symm.trans (sound ev x))))
  -- The lower words agree on the lower half, where the labels act
  -- trivially, and so everywhere.
  have low : ∀ a₀ a₁ a₂ : Bool, semPs p (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ .nil) =
      semPs q (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ .nil) := by
    intro a₀ a₁ a₂
    have h := sem' (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ .nil)
    rw [sem_mul, sem_mul, Xs_low, Xs_low, ιs_sem, ιs_sem] at h
    exact h
  have pq : semPs p ≐ semPs q := fun x => match x with
    | a₀ ∷ a₁ ∷ a₂ ∷ false ∷ .nil => low a₀ a₁ a₂
    | a₀ ∷ a₁ ∷ a₂ ∷ true ∷ .nil =>
      (flip_comm p hp (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ .nil)).trans
        ((congrArg flip3 (low a₀ a₁ a₂)).trans (flip_comm q hq (a₀ ∷ a₁ ∷ a₂ ∷ false ∷ .nil)).symm)
  have ιpq : 4 ⊢ ιs p ≈ ιs q := Narrow3.narrowP 3 p q hp hq pq
  -- Cancelling the lower words, the labels have the same function.
  have l1 : 4 ⊢ Xs a ≈ Xs a * ιs p * ιs p.reverse := by
    apply cl_eq.1
    have h := cl_eq.2 (rev_cancel p)
    simp only [cl_mul, cl_one] at h ⊢
    rw [mul_assoc, h, mul_one]
  have l2 : 4 ⊢ Xs b * ιs q * ιs p.reverse ≈ Xs b := by
    apply cl_eq.1
    have h := cl_eq.2 (rev_cancel p)
    have h2 := cl_eq.2 ιpq
    simp only [cl_mul, cl_one] at h h2 ⊢
    rw [← h2, mul_assoc, h, mul_one]
  have Xab : sem (Xs a) ≐ sem (Xs b) := fun x =>
    (sound l1 x).trans ((sem_mul _ _ x).trans ((congrArg (sem (ιs p.reverse)) (sem' x)).trans
      ((sem_mul _ _ x).symm.trans (sound l2 x))))
  exact eu.trans (((cfaith a b Xab).mul ιpq).trans ev.symm)

theorem faithful₃ : Faithful 3 := fun u v hu hv e =>
  core u v e _ _ _ _ ((expands_ok u).trans (nf_ok _ (expands_basic u hu)))
    ((expands_ok v).trans (nf_ok _ (expands_basic v hv)))
    (nf_low _ (expands_basic u hu)) (nf_low _ (expands_basic v hv))

end QCert.XCXCCX4bit.KFaithful
