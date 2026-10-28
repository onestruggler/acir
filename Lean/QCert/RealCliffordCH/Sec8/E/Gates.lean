/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4: the merged gates are the gates

After merging, the decoding of the encoding of `Z` (resp. `CZ`) is the box
controlled by the gate's wire (resp. wires) alone.  The box with one
control is `Z` on the control and the box with two controls is `CZ` on them
(Definition 2.4: `box 1 = shift z`, `box 2 = shift cz`), placed: a gate
placed with an idle wire first is the gate placed on the other wires
(`placeG_shift_cons`).
-/
import QCert.RealCliffordCH.Sec8.E.Transport

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

theorem atBot_atBot {m k : ℕ} (g : Circ m) (hmk : m ≤ k) :
    ∀ d, atBot (k + d) (atBot k g) = atBot (k + d) g
  | 0 => by rw [Nat.add_zero, atBot_self]
  | d + 1 => by
    rw [show k + (d + 1) = (k + d) + 1 by omega, atBot_succ _ _ (by omega : k ≠ k + d + 1),
      atBot_succ _ g (by omega : m ≠ k + d + 1), atBot_atBot g hmk d]

theorem atBot_placeG {k m : ℕ} (g : Circ m) {qs : List ℕ} (hnd : qs.Nodup)
    (hqs : ∀ q ∈ qs, q < k) (hm : qs.length = m) (N : ℕ) (hkN : k ≤ N) :
    atBot N (placeG k g qs) = placeG N g qs := by
  have hmk : m ≤ k := hm ▸ length_le_of_lt hnd hqs
  have hok := (netK_spec hnd hqs qs.length le_rfl).1
  have hnet : (netL k qs).map (atBot N) = netL N qs := by
    rw [netL_eq, netL_eq, List.map_map]
    apply List.map_congr_left
    intro j hj
    exact atBot_swAt j (hok j hj) N hkN
  have hgg : atBot N (atBot k g) = atBot N g := by
    have := atBot_atBot g hmk (N - k)
    rwa [show k + (N - k) = N by omega] at this
  unfold placeG
  rw [atBot_drawn, List.map_append, List.map_append, List.map_reverse, hnet, List.map_cons,
    List.map_nil, hgg]

/-- A gate placed with an idle wire first is the gate placed on the other wires. -/
theorem placeG_shift_cons {n m : ℕ} (g : Circ m) {p : ℕ} {ps : List ℕ}
    (hnd : (p :: ps).Nodup) (hps : ∀ q ∈ p :: ps, q < n) (hm : ps.length = m) :
    Derivable (theory n) (placeG n (shift g) (p :: ps)) (placeG n g ps) := by
  have hm1 : m + 1 ≤ n := by
    have := length_le_of_lt hnd hps; simp at this; omega
  have h1 : Derivable (theory n) (atBot n (shift g)) (placeG n g (List.range' 1 m)) := by
    have := der_atBot (shift_placeG_id m g) n hm1
    rwa [atBot_placeG g (List.nodup_range' (step := 1) (by omega)) (by intro q hq; simp at hq; omega)
      (by simp) n hm1] at this
  have hok : Ok n (netOf (p :: ps)) := netOf_ok hnd hps
  have h2 := placeG_net g (ps := List.range' 1 m) (List.nodup_range' (step := 1) (by omega))
    (by intro q hq; simp at hq; omega) (by simp) (netOf (p :: ps)) hok
  have e : (List.range' 1 m).map (pos (netOf (p :: ps)).reverse) = ps := by
    apply List.ext_getElem (by simp [hm])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
    have := frm_getD hnd hps (i := 1 + i) (by simp at h1 ⊢; omega)
    unfold frm at this
    rw [this]
    simp [List.getD_eq_getElem?_getD, Nat.add_comm 1 i, List.getElem?_eq_getElem h2]
  rw [e] at h2
  rw [placeG_eq]
  exact (placedBy_cong _ h1).trans h2

/-- The controls black on the wires `F`, idle elsewhere. -/
def blackL (F : List ℕ) : ℕ → Option Bool := fun j => if j ∈ F then some true else none

theorem mc_black {n : ℕ} (K : Kind) {t : ℕ} {F : List ℕ} (hF : F.Pairwise (· < ·))
    (hFn : ∀ a ∈ F, a < n) (htF : t ∉ F) :
    mc n K [t] (blackL F) = canonAt n K F.length (t :: F) := by
  have hcw : ctrlWires n [t] (blackL F) = F := by
    apply eq_of_lt_mem (List.Pairwise.filter _ List.pairwise_lt_range) hF
    intro x
    show x ∈ ctrlWires n [t] (blackL F) ↔ x ∈ F
    rw [MS.mem_ctrlWires]
    simp only [blackL, List.mem_singleton]
    constructor
    · rintro ⟨_, h, _⟩; by_contra hx; simp [hx] at h
    · intro hx; exact ⟨hFn x hx, by simp [hx], fun e => htF (e ▸ hx)⟩
  have hww : whiteWires n [t] (blackL F) = [] := by
    unfold whiteWires
    rw [List.filter_eq_nil_iff]
    intro j _
    unfold blackL; split_ifs <;> simp
  unfold mc colourW
  rw [hcw, hww]
  simp [drawn]

/-- The box with one black control is `Z` on the control. -/
theorem box1_z {n : ℕ} {t a : ℕ} (hta : t ≠ a) (ht : t < n) (ha : a < n) :
    Derivable (theory n) (mc n .box [t] (blackL [a])) (place1 n a z) := by
  rw [mc_black .box (by simp) (by simp [ha]) (by simp [hta])]
  exact (placeG_shift_cons (n := n) (z : Circ 1) (p := t) (ps := [a]) (by simp [hta])
    (by simp [ht, ha]) rfl).trans (place1_placeG z n a ha).symm

/-- The box with two adjacent black controls is `CZ` on them. -/
theorem box2_cz {n : ℕ} {t a : ℕ} (hta : t ≠ a) (hta' : t ≠ a + 1) (ht : t < n) (ha : a + 1 < n) :
    Derivable (theory n) (mc n .box [t] (blackL [a, a + 1])) (place2 n a cz) := by
  rw [mc_black .box (by simp) (by intro x hx; simp at hx; omega) (by simp; omega)]
  exact (placeG_shift_cons (n := n) (cz : Circ 2) (p := t) (ps := [a, a + 1]) (by simp; omega)
    (by intro q hq; simp at hq; omega) rfl).trans (place2_placeG cz n a (by omega)).symm

end QCert.RealCliffordCH.Sec8.E
