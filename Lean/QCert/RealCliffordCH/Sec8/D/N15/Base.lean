/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemmas D.14–D.15: tools

Conjugation by an involution (`conj_drawn`, `comm_of_conj`, `conj_of_comm`),
drawn products of up to four gates, and frames with the canonical colours
given pointwise (`frameAtK`).  The modules `D/N15/*` do not import
`D/N15.lean`: they prove its statements (package (vi)).
-/
import QCert.RealCliffordCH.Sec8.E.TransportCore
import QCert.RealCliffordCH.Sec8.D.N13

namespace QCert.RealCliffordCH.Sec8.D.N15

open Circuit Net

section Conj

variable {N : ℕ}

theorem drawn_one' (a : Circ N) : drawn [a] = a := by simp [drawn]

theorem drawn_two' (a b : Circ N) : drawn [a, b] = b * a := by simp [drawn]

theorem drawn_three' (a b c : Circ N) : drawn [a, b, c] = c * b * a := by
  simp [drawn, mul_assoc]

theorem drawn_four' (a b c d : Circ N) : drawn [a, b, c, d] = d * c * b * a := by
  simp [drawn, mul_assoc]

/-- Conjugating a drawn product by an involution conjugates each factor. -/
theorem conj_drawn {u : Circ N} (hu : Derivable (theory N) (u * u) 1) :
    ∀ l : List (Circ N), Derivable (theory N) (u * drawn l * u) (drawn (l.map fun g => u * g * u))
  | [] => by simpa [drawn] using hu
  | a :: l => by
    rw [Net.drawn_cons, List.map_cons, Net.drawn_cons]
    exact (conj_mul hu).trans (dmul (conj_drawn hu l) (Derivable.refl _))

/-- A gate fixed by conjugation with an involution commutes with it. -/
theorem comm_of_conj {u a : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (h : Derivable (theory N) (u * a * u) a) : D.Comm N a u := by
  unfold D.Comm
  rw [drawn_two', drawn_two']
  have h1 : Derivable (theory N) (u * a * (u * u)) (u * a) := by
    have := dleft (u * a) hu; rwa [mul_one] at this
  have h2 : Derivable (theory N) ((u * a * u) * u) (a * u) := dright u h
  rw [show u * a * (u * u) = (u * a * u) * u by simp only [mul_assoc]] at h1
  exact h1.symm.trans h2

/-- Conversely, a gate commuting with an involution is fixed by conjugation. -/
theorem conj_of_comm {u a : Circ N} (hu : Derivable (theory N) (u * u) 1)
    (h : D.Comm N a u) : Derivable (theory N) (u * a * u) a := by
  unfold D.Comm at h
  rw [drawn_two', drawn_two'] at h
  have := dright u h
  refine this.trans ?_
  have e : a * u * u = a * (u * u) := by simp only [mul_assoc]
  rw [e]
  have := dleft a hu
  rwa [mul_one] at this

/-- Conjugation by an involution, written as a drawn product. -/
theorem conj3 (u a : Circ N) : drawn [u, a, u] = u * a * u := by simp [drawn, mul_assoc]

end Conj

/-! ## Frames with pointwise colours -/

section Frames

open E

variable {N : ℕ}

theorem frm_not_mem' {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {j : ℕ}
    (hj : ps.length ≤ j) : frm ps j ∉ ps := by
  intro hm
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  have h1 : frm ps i = ps[i] := by
    rw [frm_getD hnd hps hi]; simp [List.getD_eq_getElem?_getD, hi]
  have := frm_injective ps (h1.trans he)
  omega

/-- Outside the special wires `ps` the frame stays outside `ps`. -/
theorem frm_out' {ps : List ℕ} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p < N) {j : ℕ}
    (hj : ps.length ≤ j) (hjN : j < N) : frm ps j ∉ ps ∧ frm ps j < N :=
  ⟨frm_not_mem' hnd hps hj, frm_lt hnd hps hjN⟩

/-- A frame, with the canonical colours given pointwise. -/
theorem frameAtK {P : Kind → Prop} (hsw : McSwapK N P) {ps : List ℕ} (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p < N) (K : Kind) (hK : P K) (tg tg' : List ℕ) (c d : ℕ → Option Bool)
    (hl : tg.length = kindSp K) (htnd : tg.Nodup) (htN : ∀ t ∈ tg, t < N)
    (htg : tg.map (frm ps) = tg') (h : ∀ j < N, d j = c (frm ps j)) :
    Derivable (theory N) (placedBy N (netOf ps) (mc N K tg d)) (mc N K tg' c) := by
  rw [Net.mc_congr N K tg (c := d) (c' := c ∘ frm ps) h, ← htg]
  exact frameK hsw hnd hps K hK tg c hl htnd htN

end Frames

end QCert.RealCliffordCH.Sec8.D.N15
