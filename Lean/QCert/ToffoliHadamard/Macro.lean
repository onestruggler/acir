/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): the macro alphabet

The encodings of Li–Ross–Selinger's generators (`enc`, Sections 5.3 and
5.6) are products of the paper's words `xAdj i` for `X_[i,i+1]`, of the
alias `neg0` of `(−1)_[0]` and of `K_[0,1,2,3]`.  Over the alphabet
`ML = {T i, N, K}` read through `phi` (`T i ↦ xAdj i`, `N ↦ neg0`,
`K ↦ K_[0,1,2,3]`) each encoding is a word `encM g`, and Figure 7 is
literally the image of equations over `ML` (`fig7M`).

`MRel`, the relations over `ML`: the Coxeter relations of `S₈` on the `T i`
and Figure 7.  `mrel_sound`: their images are derivable from `R₁` (the
Coxeter relations by `Micro.lean`), so every derivation over `ML` gives one
in `R₁` (`toR1`).
-/
import QCert.ToffoliHadamard.Micro
import QCert.ToffoliHadamard.Encode

namespace QCert.ToffoliHadamard.Macro

open Engine

/-- The macro letters: `T i` is `X_[i,i+1]`, `N` is `(−1)_[0]`, `K` is
`K_[0,1,2,3]`. -/
inductive ML : Type
  | T (i : ℕ)
  | N
  | K
  deriving DecidableEq

/-- A macro letter as a word over `Σ₁`. -/
def phiL : ML → List Sym1
  | .T i => xAdj i
  | .N => neg0
  | .K => [.Kc]

/-- Macro words as words over `Σ₁`. -/
def phi : Word ML →* Word Sym1 := FreeMonoid.lift fun x => FreeMonoid.ofList (phiL x)

theorem phi_ofList (l : List ML) : phi (FreeMonoid.ofList l) = FreeMonoid.ofList (l.flatMap phiL) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [FreeMonoid.ofList_cons, map_mul, ih, phi, FreeMonoid.lift_eval_of, List.flatMap_cons,
      FreeMonoid.ofList_append]

/-! ## Encodings -/

/-- `X_[a,a+g+1]` over `ML`. -/
def xGapM : ℕ → ℕ → List ML
  | 0, a => [.T a]
  | g + 1, a => [.T a] ++ xGapM g (a + 1) ++ [.T a]

/-- `X_[a,b]` over `ML`. -/
def xabM (a b : ℕ) : List ML := xGapM (b - a - 1) a

/-- `(−1)_[c]` over `ML`. -/
def negM (c : ℕ) : List ML := if c = 0 then [.N] else xabM 0 c ++ [.N] ++ xabM 0 c

/-- Conjugation by `X_[i,j]` over `ML`. -/
def conjXM (i j : ℕ) (u : List ML) : List ML := if i = j then u else xabM i j ++ u ++ xabM i j

/-- `K_[a,b,c,d]` over `ML`. -/
def kwM (a b c d : ℕ) : List ML := conjXM 0 a (conjXM 1 b (conjXM 2 c (conjXM 3 d [.K])))

theorem flat_xGapM (g a : ℕ) : (xGapM g a).flatMap phiL = xGap g a := by
  induction g generalizing a with
  | zero => simp [xGapM, xGap, phiL]
  | succ g ih => simp [xGapM, xGap, ih, phiL]

theorem flat_xabM (a b : ℕ) : (xabM a b).flatMap phiL = xab a b := flat_xGapM _ _

theorem flat_negM (c : ℕ) : (negM c).flatMap phiL = negw c := by
  unfold negM negw
  split_ifs <;> simp [flat_xabM, phiL]

theorem flat_conjXM (i j : ℕ) (u : List ML) :
    (conjXM i j u).flatMap phiL = conjX i j (u.flatMap phiL) := by
  unfold conjXM conjX
  split_ifs <;> simp [flat_xabM]

theorem flat_kwM (a b c d : ℕ) : (kwM a b c d).flatMap phiL = kw a b c d := by
  simp [kwM, kw, flat_conjXM, phiL]

/-- A generator of `𝒢₈` over `ML`. -/
def encM : LiRossSelinger.Gen 8 → List ML
  | .neg a => negM a
  | .x a b _ => xabM a b
  | .k a b c d _ _ _ => kwM a b c d

theorem flat_encM (g : LiRossSelinger.Gen 8) : (encM g).flatMap phiL = enc g := by
  cases g <;> simp [encM, enc, flat_negM, flat_xabM, flat_kwM]

/-- Words over `𝒢₈` as macro words. -/
def encMW : Word (LiRossSelinger.Gen 8) →* Word ML :=
  FreeMonoid.lift fun g => FreeMonoid.ofList (encM g)

theorem phi_encMW (u : Word (LiRossSelinger.Gen 8)) : phi (encMW u) = encW u := by
  have : phi.comp encMW = encW := by
    apply FreeMonoid.hom_eq
    intro g
    simp only [MonoidHom.coe_comp, Function.comp_apply, encMW, FreeMonoid.lift_eval_of, encW,
      phi_ofList, flat_encM]
  exact DFunLike.congr_fun this u

/-! ## The macro relations -/

/-- `ρ` of Figure 6 over `ML`. -/
def rhoM : List ML := kwM 4 5 6 7 ++ [.K] ++ xabM 3 4 ++ [.K] ++ kwM 4 5 6 7

/-- Figure 7 over `ML` ((83)–(101), (97) and (100) corrected). -/
def fig7M : List (Eqn ML) :=
  [(negM 0 ++ negM 0, []), ([.K, .K], []),
   (xabM 1 2 ++ negM 0, negM 0 ++ xabM 1 2), (xabM 2 3 ++ negM 0, negM 0 ++ xabM 2 3),
   (xabM 3 4 ++ negM 0, negM 0 ++ xabM 3 4), (xabM 4 5 ++ negM 0, negM 0 ++ xabM 4 5),
   (xabM 5 6 ++ negM 0, negM 0 ++ xabM 5 6), (xabM 6 7 ++ negM 0, negM 0 ++ xabM 6 7),
   (xabM 4 5 ++ [.K], [.K] ++ xabM 4 5), (xabM 5 6 ++ [.K], [.K] ++ xabM 5 6),
   (xabM 6 7 ++ [.K], [.K] ++ xabM 6 7), (negM 4 ++ [.K], [.K] ++ negM 4),
   (negM 0 ++ negM 4, negM 4 ++ negM 0), ([.K] ++ kwM 4 5 6 7, kwM 4 5 6 7 ++ [.K]),
   (xabM 0 1 ++ [.K], [.K] ++ xabM 1 3 ++ negM 1 ++ negM 3),
   (xabM 1 2 ++ [.K], negM 0 ++ [.K] ++ negM 0 ++ [.K] ++ negM 0),
   (xabM 2 3 ++ [.K], [.K] ++ xabM 1 3),
   ([.K] ++ kwM 1 3 4 5, kwM 2 3 4 5 ++ kwM 0 1 2 4),
   (negM 0 ++ negM 4 ++ xabM 0 4 ++ rhoM, rhoM ++ xabM 0 4 ++ negM 4 ++ negM 0)]

/-- The Coxeter relations of `S₈` on the `T i`, in the order of the tables:
`T i T i = ε`, then `T i T j = T j T i` (`i + 2 ≤ j`), then the braids. -/
def coxM : List (Eqn ML) :=
  ((List.range 7).map fun i => ([.T i, .T i], [])) ++
  ((List.range 7).flatMap fun i =>
    ((List.range 7).filter fun j => i + 2 ≤ j).map fun j => ([.T i, .T j], [.T j, .T i])) ++
  ((List.range 6).map fun i => ([.T i, .T (i + 1), .T i], [.T (i + 1), .T i, .T (i + 1)]))

/-- The relations over `ML`: Coxeter and Figure 7. -/
inductive MRel : WRel ML
  | ax {e : Eqn ML} (h : e ∈ coxM ++ fig7M) : MRel (FreeMonoid.ofList e.1) (FreeMonoid.ofList e.2)

/-- The base of the macro tables. -/
def baseM : List (Eqn ML) := coxM ++ fig7M

theorem baseM_valid : Valid MRel baseM := fun _ h => Derivable.of (MRel.ax h)

/-! ## Soundness in `R₁` -/

/-- The image of an equation over `ML`. -/
def phiE (e : Eqn ML) : Eqn Sym1 := (e.1.flatMap phiL, e.2.flatMap phiL)

set_option maxRecDepth 100000 in
theorem fig7M_phi : fig7M.map phiE = (Micro.base.drop 46).take 19 := by decide +kernel

set_option maxRecDepth 10000 in
theorem coxM_cases : ∀ e ∈ coxM,
    (∃ i, i < 7 ∧ e = ([.T i, .T i], [])) ∨
    (∃ i j, j < 7 ∧ i + 2 ≤ j ∧ e = ([.T i, .T j], [.T j, .T i])) ∨
    (∃ i, i < 6 ∧ e = ([.T i, .T (i + 1), .T i], [.T (i + 1), .T i, .T (i + 1)])) := by
  intro e he
  simp only [coxM, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap,
    List.mem_filter, decide_eq_true_eq] at he
  rcases he with (⟨i, hi, rfl⟩ | ⟨i, _, j, ⟨hj, hij⟩, rfl⟩) | ⟨i, hi, rfl⟩
  · exact Or.inl ⟨i, hi, rfl⟩
  · exact Or.inr (Or.inl ⟨i, j, hj, hij, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)

theorem xAdj_palin : ∀ i : Fin 7, (xAdj i).reverse = xAdj i := by decide

theorem mrel_sound : ∀ u v, MRel u v → Derivable R1 (phi u) (phi v) := by
  rintro _ _ ⟨he⟩
  rw [phi_ofList, phi_ofList]
  rcases List.mem_append.1 he with h | h
  · rcases coxM_cases _ h with ⟨i, hi, rfl⟩ | ⟨i, j, hj, hij, rfl⟩ | ⟨i, hi, rfl⟩
    · have := reverse_mul Micro.involution (xAdj i)
      rw [xAdj_palin ⟨i, hi⟩] at this
      simpa [phiL] using this
    · simpa [phiL] using Micro.far_micro hj hij
    · simpa [phiL] using Micro.braid_micro hi
  · have h2 : phiE _ ∈ fig7M.map phiE := List.mem_map_of_mem h
    rw [fig7M_phi] at h2
    have := Micro.base_valid _ (List.mem_of_mem_drop (List.mem_of_mem_take h2))
    simpa [phiE] using this

/-- A derivation over `ML` gives one in `R₁`. -/
theorem toR1 {u v : Word ML} (h : Derivable MRel u v) : Derivable R1 (phi u) (phi v) :=
  Derivable.map phi mrel_sound h

end QCert.ToffoliHadamard.Macro
