/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The controlled matchings are faithful

Translation of `CFaithful.agda`.  Two words of labels whose controlled
matchings have the same function are equal circuits.  As `ByEvenRS` does on
four wires, at eight states: the words of the symbols of `EvenRS 8`
(`CCerts`' `Φ`) act on the upper half as the even permutations `f (γ c d)`
(`Φs_act`, from the functions of the labels, `CSem`), the relations of
`EvenRS 8` hold for them (`R_rel`), and every label is a word of symbols
(`ψ`, along the closure tree: a label is its parent conjugated by the word
of a symbol, `conj_list`).  So two words of labels with the same function
translate to words of symbols with the same permutation, which `EvenRS 8`'s
completeness relates, and the relations carry over.

Names.  The Agda's `conj-list`, `ψ*`, `ψ*-ok`, `Φ*-cong`, `Xs-sem`, `Φ-act`,
`Φ*-act` are `conj_list`, `ψs`, `ψs_ok`, `Φs_cong`, `Xs_sem`, `Φ_act`,
`Φs_act`; its `cl` (a label as the word of symbols along the tree) is
`cl_tree`, `CircuitProp.cl` being the class of a circuit.

**Deviation from the Agda.**  Words are multiplied left-associatively and
the Agda's associativity steps are reasoning in the quotient monoid
(`CircuitProp.cl`); `Φs_cong` is by `Con.conGen_le` (the Agda's induction on
the congruence).
-/
import QCert.XCXCCX4bit.CCerts

namespace QCert.XCXCCX4bit.CFaithful

open QCert QCert.Circuit CircuitProp IndepProp
open EvenRS CRel CSem CCerts

/-! ## Conjugation by a word of labels -/

/-- `Xs ws • Xm ν • Xs (reverse ws)` is the label of the conjugate. -/
theorem conj_list : ∀ (ws : List L) (ν : L), conjs_ok ws ν = true →
    4 ⊢ Xs ws * (Xm ν * Xs ws.reverse) ≈ Xm (star ws ν)
  | [], ν, _ => by
    show 4 ⊢ 1 * (Xm ν * 1) ≈ Xm ν
    rw [one_mul, mul_one]
  | w :: ws, ν, h => by
    simp only [conjs_ok, Bool.and_eq_true] at h
    have ih := conj_list ws ν h.2
    have hc := CBC.X_conj w (star ws ν) h.1
    rw [List.reverse_cons, Xs_append]
    show 4 ⊢ Xm w * Xs ws * (Xm ν * (Xs ws.reverse * (Xm w * 1))) ≈ Xm (c3 w (star ws ν))
    apply cl_eq.1
    have e1 := cl_eq.2 ih
    have e2 := cl_eq.2 hc
    simp only [cl_mul, mul_one] at e1 e2 ⊢
    rw [← e2, ← e1]
    simp only [mul_assoc]

/-! ## Every label is a word of symbols -/

/-- The word of symbols of a label, along the closure tree (with fuel for its
depth). -/
def ψf : ℕ → L → Word (Sch 8)
  | 0, _ => base_word
  | n + 1, μ => FreeMonoid.of (sym_of μ) * (ψf n (par μ) * FreeMonoid.of (inv_sym (sym_of μ)))

def ψ (μ : L) : Word (Sch 8) := ψf (dep μ) μ

private theorem closure_sound (μ : L) : cstep μ (dep μ) = true :=
  allFin_sound 105 closure_ok closure_all μ

/-- A label along the tree (the Agda's `cl`). -/
theorem cl_tree : ∀ (n : ℕ) (μ : L), dep μ = n → 4 ⊢ Xm μ ≈ Xs (Φs (ψf n μ))
  | 0, μ, e => by
    have h := closure_sound μ
    rw [e] at h
    have hμ : μ = μ₀ := eqLab_sound μ μ₀ h
    subst hμ
    refine Derivable.trans ?_ base_ok.symm
    show 4 ⊢ Xm μ₀ ≈ Xm μ₀ * 1
    rw [mul_one]
  | n + 1, μ, e => by
    have h := closure_sound μ
    rw [e] at h
    simp only [cstep, Bool.and_eq_true] at h
    obtain ⟨hd, hc, hs⟩ := h
    have hμ : Xm μ = Xm (star (Φ (sym_of μ)) (par μ)) := by
      rw [eqLab_sound _ _ hs]
    have ih := cl_tree n (par μ) (Nat.eq_of_beq_eq_true hd)
    rw [hμ, ψf, Φs_mul, Φs_mul, Φs_of, Φs_of, Xs_append, Xs_append]
    exact (conj_list _ _ hc).symm.trans ((Derivable.refl _).mul (ih.mul (rev_ok _)))

/-- A word of labels as a word of symbols (the Agda's `ψ*`). -/
def ψs : List L → Word (Sch 8)
  | [] => 1
  | μ :: ws => ψ μ * ψs ws

theorem ψs_ok : ∀ ws : List L, 4 ⊢ Xs ws ≈ Xs (Φs (ψs ws))
  | [] => Derivable.refl _
  | μ :: ws => by
    rw [ψs, Φs_mul, Xs_append]
    exact (cl_tree (dep μ) μ rfl).mul (ψs_ok ws)

/-! ## The relations of EvenRS 8 carry over -/

theorem Φs_cong {u v : Word (Sch 8)} (h : Derivable (RSRel 8) u v) :
    4 ⊢ Xs (Φs u) ≈ Xs (Φs v) := by
  let c : Con (Word (Sch 8)) :=
    { r := fun u v => 4 ⊢ Xs (Φs u) ≈ Xs (Φs v)
      iseqv := ⟨fun _ => Derivable.refl _, Derivable.symm, Derivable.trans⟩
      mul' := fun {u u' v v'} hu hv => by
        show 4 ⊢ Xs (Φs (u * v)) ≈ Xs (Φs (u' * v'))
        rw [Φs_mul, Φs_mul, Xs_append, Xs_append]
        exact hu.mul hv }
  have : conGen (RSRel 8) ≤ c := Con.conGen_le fun _ _ r => R_rel r
  exact this h

/-! ## Semantics -/

theorem Xs_sem : ∀ ws : List L, sem (Xs ws) ≐ mFs ws
  | [] => fun _ => rfl
  | l :: ws => fun x => by
    show sem (Xm l * Xs ws) x = mFs (l :: ws) x
    rw [sem_mul, Xm_sem l x, Xs_sem ws]
    rfl

theorem Φ_act (x : Sch 8) (i : Fin 8) :
    mFs (Φ x) (enc8 i) = enc8 (Symmetric.perm (f 8 x) i) :=
  eqV_sound _ _ (allFin_sound 8 _ (Φ_act_ok x) i)

theorem Φs_act (w : Word (Sch 8)) (i : Fin 8) :
    mFs (Φs w) (enc8 i) = enc8 (Symmetric.perm (FreeMonoid.lift (f 8) w) i) := by
  induction w using FreeMonoid.inductionOn' generalizing i with
  | one => rfl
  | mul_of x w ih =>
    rw [Φs_mul, Φs_of, mFs_append, seqF, Φ_act, ih, map_mul, FreeMonoid.lift_eval_of,
      Symmetric.perm_mul_apply]

/-! ## Faithfulness -/

/-- Two words of labels with the same function are equal. -/
theorem cfaith (a b : List L) (e : sem (Xs a) ≐ sem (Xs b)) : 4 ⊢ Xs a ≈ Xs b := by
  have at_ : ∀ (ws : List L) (i : Fin 8),
      sem (Xs ws) (enc8 i) = enc8 (Symmetric.perm (FreeMonoid.lift (f 8) (ψs ws)) i) :=
    fun ws i => ((sound (ψs_ok ws)) (enc8 i)).trans ((Xs_sem _ (enc8 i)).trans (Φs_act _ i))
  have same : ∀ i, Symmetric.perm (FreeMonoid.lift (f 8) (ψs a)) i =
      Symmetric.perm (FreeMonoid.lift (f 8) (ψs b)) i := fun i =>
    enc8_injective ((at_ a i).symm.trans ((e (enc8 i)).trans (at_ b i)))
  exact (ψs_ok a).trans ((Φs_cong (rs_complete 8 (ψs a) (ψs b) same)).trans (ψs_ok b).symm)

end QCert.XCXCCX4bit.CFaithful
