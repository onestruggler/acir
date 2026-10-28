/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemmas D.14–D.15: transport of multi-controlled gates

With (353) proved (`E353c`), every multi-controlled gate moves along swap
networks (`mcSwapAll'`, Net's `mc_swap_sym` with (307), (313), (353)), so the
equations of Appendix D move to any wires by a frame (`frameAt'`).  Also:
rewriting inside a drawn product (`rw_at`).
-/
import QCert.RealCliffordCH.Sec8.D.N15.E353c

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net E Eng

/-- Naturality of `mc` for one swap at any wires, from (307), (313) and (353). -/
theorem mcSwapAll' {N : ℕ} (ih : IH N) : McSwapAll N :=
  mcSwapOf ih fun k hk h3 a j hj1 hj2 => eq353 (k + 1) h3 (ih.mono hk) a j hj1 hj2

/-- A frame, with the canonical colours given pointwise. -/
theorem frameAt' {N : ℕ} (ih : IH N) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) (K : Kind) (tg tg' : List ℕ) (c d : ℕ → Option Bool)
    (hl : tg.length = kindSp K) (htnd : tg.Nodup) (htN : ∀ t ∈ tg, t < N)
    (htg : tg.map (frm ps) = tg') (h : ∀ j < N, d j = c (frm ps j)) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg d)) (mc N K tg' c) :=
  frameAtK ((mcSwapAll' ih).toK (fun _ => True)) hnd hps K trivial tg tg' c d hl htnd htN htg h

/-- Rewriting a factor of a drawn product. -/
theorem rw_at {N : ℕ} (L R : List (Circ N)) {M M' : List (Circ N)}
    (h : Derivable (theory N) (drawn M) (drawn M')) :
    Derivable (theory N) (drawn (L ++ M ++ R)) (drawn (L ++ M' ++ R)) := by
  rw [SE.drawn_append, SE.drawn_append, SE.drawn_append, SE.drawn_append]
  rw [← mul_assoc, ← mul_assoc]; exact dctx _ _ h

/-- Exchanging two commuting factors of a drawn product. -/
theorem sw_at {N : ℕ} (L R : List (Circ N)) {a b : Circ N} (h : D.Comm N a b) :
    Derivable (theory N) (drawn (L ++ [a, b] ++ R)) (drawn (L ++ [b, a] ++ R)) :=
  rw_at L R h

/-- A commutation moved by a frame. -/
theorem comm_frame {N : ℕ} {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N)
    {A B A' B' : Circ N} (hA : Derivable (theory N) (placedBy N (netOf ps) A) A')
    (hB : Derivable (theory N) (placedBy N (netOf ps) B) B') (h : D.Comm N A B) :
    D.Comm N A' B' :=
  via_frame hnd hps (List.Forall₂.cons hA (List.Forall₂.cons hB List.Forall₂.nil))
    (List.Forall₂.cons hB (List.Forall₂.cons hA List.Forall₂.nil)) h

/-- `setCtl` composed with a frame. -/
theorem setCtl_frm' (ps : List ℕ) (c : ℕ → Option Bool) (w : ℕ) (v : Option Bool) (j : ℕ) :
    setCtl c w v (frm ps j) = setCtl (c ∘ frm ps) (pos (netOf ps) w) v j := by
  have := congrFun (setCtl_frm ps c w v) j
  simpa using this

/-- In an inverse pair, merging is inherited (Lemma B.5): if `a b = c` with
inverses `a'`, `b'`, `c'`, then `b' a' = c'`. -/
theorem inv_merge {N : ℕ} {a b c a' b' c' : Circ N} (h : Derivable (theory N) (a * b) c)
    (ha : Derivable (theory N) (a' * a) 1) (hb : Derivable (theory N) (b' * b) 1)
    (hc : Derivable (theory N) (c * c') 1) :
    Derivable (theory N) (b' * a') c' := by
  -- `b' a' = b' a' (a b c') = b' (a' a) b c' = b' b c' = c'`
  have h1 : Derivable (theory N) (b' * a') (b' * a' * (a * b * c')) := by
    have := dleft (b' * a') ((dright c' h).trans hc)
    rw [mul_one] at this
    exact this.symm
  have e : b' * a' * (a * b * c') = b' * (a' * a) * b * c' := by simp only [mul_assoc]
  have h2 : Derivable (theory N) (b' * (a' * a) * b * c') (b' * b * c') := by
    have := dright c' (dright b (dleft b' ha))
    simpa only [mul_one] using this
  have h3 : Derivable (theory N) (b' * b * c') c' := by
    have := dright c' hb
    simpa only [one_mul] using this
  exact h1.trans ((der_of_eq e).trans (h2.trans h3))

/-! ## Frames: wires outside the special ones -/

/-- The colours, read on canonical wires, of a frame whose wire `m + 3` is `b`. -/
def colT (ps : List ℕ) (T : ℕ) (b : Bool) : ℕ → Bool := fun j => if frm ps j = T then b else true

theorem pos_ge {N : ℕ} {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {w : ℕ}
    (hw : w < N) (hwp : w ∉ ps) : ps.length ≤ pos (netOf ps) w ∧ pos (netOf ps) w < N := by
  refine ⟨?_, pos_lt _ (netOf_ok hnd hps) w hw⟩
  by_contra hlt
  push Not at hlt
  apply hwp
  rw [← frm_pos ps w, frm_getD hnd hps hlt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlt]
  exact List.getElem_mem hlt

/-- Wires of a frame outside its special wires stay outside them. -/
theorem frm_ge {N : ℕ} {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) (k : ℕ)
    (hk : ∀ i, i < k ↔ i ∈ ps) {j : ℕ} (hj : ps.length ≤ j) (hjN : j < N) :
    k ≤ frm ps j ∧ frm ps j < N := by
  obtain ⟨hm, hl⟩ := frm_out' hnd hps hj hjN
  refine ⟨?_, hl⟩
  by_contra h
  exact hm ((hk _).1 (by omega))

end QCert.RealCliffordCH.Sec8.D.N15
