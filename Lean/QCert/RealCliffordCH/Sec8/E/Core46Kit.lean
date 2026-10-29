/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5, rule (46): the kit of the core

The core of the rule (46) is (147) with every wire above `2` a white control
(`Rule46.Core46`).  From four wires on, the paper's chain (pages 269–277) uses
the wires `0, 1, 2, 3`, every gate white on the wires `4, …`.  Here:

* gate descriptions (`GD`): the multi-controlled gate `mc N K tg (c4 a)`, `a`
  the colours of the wires `0, …, 3` and white above (`c4`), and `P ⊗ P` on
  two of the wires `0, …, 3`; a word `wI N l` is their drawn product;
* a rewriting checker (`runW`): a step rewrites a window with an equation of
  a table, and a run that the checker accepts is a derivation (`run_sound`);
* frames (`fr_eq`): an equation between gate descriptions moved by a
  permutation `σ` of the wires `0, …, 3` (`perms4`, `GD.fr`, from `frameAt'`);
* the canonical equations of Appendix D in this form, with their colours:
  (111), (112), (130), (274), (277), (308)–(312), (335)–(345).
-/
import QCert.RealCliffordCH.Sec8.E.Rule46
import QCert.RealCliffordCH.Sec8.E.Rule43
import QCert.RealCliffordCH.Sec8.E.Merge
import QCert.RealCliffordCH.Sec8.E.MergeHg
import QCert.RealCliffordCH.Sec8.E.Step84

namespace QCert.RealCliffordCH.Sec8.E.C46

open Circuit Net

/-! ## Gate descriptions -/

/-- Colours of the wires `0, …, 3` (`none`: idle or special), white above. -/
def c4 (a : List (Option Bool)) : ℕ → Option Bool :=
  fun j => if j < 4 then a.getD j none else some false

/-- Gate descriptions. -/
inductive GD
  /-- `mc N K tg (c4 a)` -/
  | g (K : Kind) (tg : List ℕ) (a : List (Option Bool))
  /-- `P ⊗ P` on the wires `i`, `j` -/
  | p (i j : ℕ)
  deriving DecidableEq, Repr

/-- The gate on `N` wires. -/
def GD.circ (N : ℕ) : GD → Circ N
  | .g K tg a => mc N K tg (c4 a)
  | .p i j => ppAt N i j

/-- A word of gate descriptions, in drawn order. -/
def wI (N : ℕ) (l : List GD) : Circ N := drawn (l.map (GD.circ N))

theorem wI_ctx {N : ℕ} (L R : List GD) {a b : List GD}
    (h : Derivable (theory N) (wI N a) (wI N b)) :
    Derivable (theory N) (wI N (L ++ a ++ R)) (wI N (L ++ b ++ R)) := by
  simp only [wI, List.map_append]
  exact D.N15.rw_at _ _ h

/-! ## The rewriting checker -/

/-- An equation between words. -/
abbrev Eqn := List GD × List GD

/-- Every equation of the table is derivable on `N` wires. -/
def AllT (N : ℕ) (T : List Eqn) : Prop :=
  T.Forall fun e => Derivable (theory N) (wI N e.1) (wI N e.2)

/-- Rewrite the window at `i` with the equation `k` of the table, forwards or
backwards. -/
def stepW (T : List Eqn) (w : List GD) (i k : ℕ) (fwd : Bool) : Option (List GD) :=
  match T[k]? with
  | none => none
  | some e =>
    if (w.drop i).take (cond fwd e.1 e.2).length = cond fwd e.1 e.2 then
      some (w.take i ++ cond fwd e.2 e.1 ++ (w.drop i).drop (cond fwd e.1 e.2).length)
    else none

/-- A run of steps. -/
def runW (T : List Eqn) : List GD → List (ℕ × ℕ × Bool) → Option (List GD)
  | w, [] => some w
  | w, (i, k, f) :: ss =>
    match stepW T w i k f with
    | none => none
    | some w' => runW T w' ss

theorem stepW_sound {N : ℕ} {T : List Eqn} (hT : AllT N T) {w w' : List GD} {i k : ℕ}
    {f : Bool} (h : stepW T w i k f = some w') : Derivable (theory N) (wI N w) (wI N w') := by
  unfold stepW at h
  cases he : T[k]? with
  | none => rw [he] at h; exact absurd h (by simp)
  | some e =>
    rw [he] at h
    simp only at h
    split_ifs at h with hm
    cases h
    have hd := (List.forall_iff_forall_mem.1 hT) e (List.mem_of_getElem? he)
    have hd' : Derivable (theory N) (wI N (cond f e.1 e.2)) (wI N (cond f e.2 e.1)) := by
      cases f
      · exact hd.symm
      · exact hd
    have hw : w = w.take i ++ cond f e.1 e.2 ++ (w.drop i).drop (cond f e.1 e.2).length := by
      conv_lhs => rw [← List.take_append_drop i w,
        ← List.take_append_drop (cond f e.1 e.2).length (w.drop i)]
      rw [hm, List.append_assoc]
    exact (der_of_eq (congrArg (wI N) hw)).trans (wI_ctx _ _ hd')

theorem run_sound {N : ℕ} {T : List Eqn} (hT : AllT N T) :
    ∀ {w v : List GD} {ss : List (ℕ × ℕ × Bool)}, runW T w ss = some v →
      Derivable (theory N) (wI N w) (wI N v)
  | w, v, [], h => by
    simp only [runW, Option.some.injEq] at h
    subst h; exact Derivable.refl _
  | w, v, (i, k, f) :: ss, h => by
    simp only [runW] at h
    cases hs : stepW T w i k f with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some w' =>
      rw [hs] at h
      exact (stepW_sound hT hs).trans (run_sound hT h)

/-! ## Frames -/

/-- The permutations of the wires `0, …, 3`. -/
def perms4 : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1], [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3],
    [1, 0, 3, 2], [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0], [2, 0, 1, 3], [2, 0, 3, 1],
    [2, 1, 0, 3], [2, 1, 3, 0], [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1], [3, 1, 0, 2],
    [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]]

/-- The image of a wire under `σ` (fixing the wires `4, …`). -/
def sg (σ : List ℕ) (i : ℕ) : ℕ := σ.getD i i

/-- A gate moved by the frame `σ`: its wire `j` goes to `σ j`. -/
def GD.fr (σ : List ℕ) : GD → GD
  | .g K tg a => .g K (tg.map (sg σ)) ((List.range 4).map fun k => a.getD (σ.idxOf k) none)
  | .p i j => .p (min (sg σ i) (sg σ j)) (max (sg σ i) (sg σ j))

/-- A well formed gate description. -/
def GD.ok : GD → Bool
  | .g K tg a => decide tg.Nodup && tg.all (· < 4) && (tg.length == kindSp K) && (a.length == 4)
  | .p i j => decide (i < j ∧ j < 4)

theorem perms4_props : ∀ σ ∈ perms4, σ.Nodup ∧ σ.length = 4 ∧ (∀ x ∈ σ, x < 4) ∧
    (∀ x ∈ netOf σ, x ≤ 2) ∧ (∀ j < 4, σ.idxOf (σ.getD j 0) = j) := by
  decide

theorem frm_sg {σ : List ℕ} (hσ : σ ∈ perms4) (j : ℕ) : frm σ j = sg σ j := by
  obtain ⟨hnd, hl, hlt, hnet, -⟩ := perms4_props σ hσ
  by_cases hj : j < 4
  · rw [frm_getD (N := 4) hnd hlt (by omega)]
    simp [sg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < σ.length by omega)]
  · have h1 : frm σ j = j := pos_below_gt _ _ (fun x hx => by
      have := hnet x (List.mem_reverse.1 hx); omega)
    rw [h1, sg, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem sg_lt {σ : List ℕ} (hσ : σ ∈ perms4) {j : ℕ} (hj : j < 4) : sg σ j < 4 := by
  obtain ⟨-, hl, hlt, -, -⟩ := perms4_props σ hσ
  have : sg σ j ∈ σ := by
    simp only [sg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < σ.length by omega),
      Option.getD_some]
    exact List.getElem_mem _
  exact hlt _ this

theorem getD_map_range (f : ℕ → Option Bool) {k : ℕ} (hk : k < 4) :
    ((List.range 4).map f).getD k none = f k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

section Frames

variable {n : ℕ} (ih : IH (n + 4))
include ih

theorem fr_g {σ : List ℕ} (hσ : σ ∈ perms4) (K : Kind) (tg : List ℕ) (a : List (Option Bool))
    (hok : (GD.g K tg a).ok = true) :
    Derivable (theory (n + 4)) (placedBy (n + 4) (netOf σ) ((GD.g K tg a).circ (n + 4)))
      (((GD.g K tg a).fr σ).circ (n + 4)) := by
  obtain ⟨hnd, hl, hlt, -, hidx⟩ := perms4_props σ hσ
  simp only [GD.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨htnd, htlt⟩, htl⟩, hal⟩ := hok
  refine D.N15.frameAt' ih hnd (fun p hp => by have := hlt p hp; omega) K tg _ _ _ htl htnd
    (fun t ht => by have := htlt t ht; omega)
    (List.map_congr_left (fun t _ => frm_sg hσ t)) ?_
  intro j hj
  rw [frm_sg hσ]
  by_cases h4 : j < 4
  · have hs := sg_lt hσ h4
    have e1 : sg σ j = σ.getD j 0 := by
      simp [sg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < σ.length by omega)]
    simp only [c4, if_pos h4, if_pos hs]
    rw [getD_map_range _ hs, e1, hidx j h4]
  · have e1 : sg σ j = j := by
      rw [sg, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    simp only [c4, e1, if_neg h4]

theorem fr_p_raw {σ : List ℕ} (hσ : σ ∈ perms4) {i j : ℕ} (hij : i ≠ j) (hi : i < 4) (hj : j < 4) :
    Derivable (theory (n + 4)) (placedBy (n + 4) (netOf σ) (ppAt (n + 4) i j))
      (ppAt (n + 4) (sg σ i) (sg σ j)) := by
  obtain ⟨hnd, hl, hlt, -, -⟩ := perms4_props σ hσ
  have h := placeG_net (N := n + 4) (pp : Circ 2) (ps := [i, j]) (by simp [hij])
    (by intro p hp; simp at hp; omega) rfl (netOf σ)
    (netOf_ok hnd (fun p hp => by have := hlt p hp; omega))
  have e : [i, j].map (pos (netOf σ).reverse) = [sg σ i, sg σ j] := by
    simp only [List.map_cons, List.map_nil]
    rw [show pos (netOf σ).reverse i = frm σ i from rfl, show pos (netOf σ).reverse j = frm σ j from rfl,
      frm_sg hσ, frm_sg hσ]
  rw [e] at h
  exact h

theorem pp_sym01 : Derivable (theory (n + 4)) (ppAt (n + 4) 1 0) (ppAt (n + 4) 0 1) := by
  have h := placeG_swap (N := n + 4) (pp : Circ 2) (ps := [0, 1]) (by decide)
    (by intro p hp; simp at hp; omega) rfl 0 (by omega)
  have e : [0, 1].map (Net.tau 0) = [1, 0] := by decide
  rw [e, D.N15.drawn_three'] at h
  exact h.symm.trans (sw_pp44 (M := n + 1) ih)

theorem pp_sym {a b : ℕ} (hab : a ≠ b) (ha : a < 4) (hb : b < 4) :
    Derivable (theory (n + 4)) (ppAt (n + 4) b a) (ppAt (n + 4) a b) := by
  have hex : ∀ a < 4, ∀ b < 4, a ≠ b → ∃ σ ∈ perms4, sg σ 0 = a ∧ sg σ 1 = b := by decide
  obtain ⟨σ, hσ, h0, h1⟩ := hex a ha b hb hab
  have k1 := fr_p_raw ih hσ (i := 1) (j := 0) (by omega) (by omega) (by omega)
  have k2 := fr_p_raw ih hσ (i := 0) (j := 1) (by omega) (by omega) (by omega)
  rw [h0, h1] at k1 k2
  exact k1.symm.trans ((placedBy_cong _ (pp_sym01 ih)).trans k2)

theorem fr_p {σ : List ℕ} (hσ : σ ∈ perms4) (i j : ℕ) (hok : (GD.p i j).ok = true) :
    Derivable (theory (n + 4)) (placedBy (n + 4) (netOf σ) ((GD.p i j).circ (n + 4)))
      (((GD.p i j).fr σ).circ (n + 4)) := by
  simp only [GD.ok, decide_eq_true_eq] at hok
  have k := fr_p_raw ih hσ (i := i) (j := j) (by omega) (by omega) (by omega)
  have hinj : sg σ i ≠ sg σ j := by
    intro e
    rw [← frm_sg hσ, ← frm_sg hσ] at e
    have := frm_injective σ e
    omega
  simp only [GD.circ, GD.fr]
  rcases Nat.lt_or_gt_of_ne hinj with hlt | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le]; exact k
  · rw [min_eq_right hlt.le, max_eq_left hlt.le]
    exact k.trans (pp_sym ih (Ne.symm hinj) (sg_lt hσ (by omega)) (sg_lt hσ (by omega)))

theorem fr_one {σ : List ℕ} (hσ : σ ∈ perms4) (g : GD) (hok : g.ok = true) :
    Derivable (theory (n + 4)) (placedBy (n + 4) (netOf σ) (g.circ (n + 4))) ((g.fr σ).circ (n + 4)) := by
  cases g with
  | g K tg a => exact fr_g ih hσ K tg a hok
  | p i j => exact fr_p ih hσ i j hok

theorem fr_list {σ : List ℕ} (hσ : σ ∈ perms4) :
    ∀ l : List GD, l.all GD.ok = true →
      List.Forall₂ (fun A B => Derivable (theory (n + 4)) (placedBy (n + 4) (netOf σ) A) B)
        (l.map (GD.circ (n + 4))) ((l.map (GD.fr σ)).map (GD.circ (n + 4)))
  | [], _ => List.Forall₂.nil
  | g :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact List.Forall₂.cons (fr_one ih hσ g h.1) (fr_list hσ l h.2)

/-- An equation between gate descriptions, moved by the frame `σ`. -/
theorem fr_eq {σ : List ℕ} (hσ : σ ∈ perms4) {l r L R : List GD} (hl : l.all GD.ok = true)
    (hr : r.all GD.ok = true) (hL : l.map (GD.fr σ) = L) (hR : r.map (GD.fr σ) = R)
    (h : Derivable (theory (n + 4)) (wI (n + 4) l) (wI (n + 4) r)) :
    Derivable (theory (n + 4)) (wI (n + 4) L) (wI (n + 4) R) := by
  obtain ⟨hnd, hl4, hlt, -, -⟩ := perms4_props σ hσ
  subst hL hR
  exact via_frame hnd (fun p hp => by have := hlt p hp; omega) (fr_list ih hσ l hl)
    (fr_list ih hσ r hr) h

end Frames

end QCert.RealCliffordCH.Sec8.E.C46
