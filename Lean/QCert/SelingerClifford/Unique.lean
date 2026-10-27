/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): uniqueness of normal forms

Lemmas 5.1–5.4 and Proposition 5.5 of Selinger's paper: two normal forms
with the same matrix are equal.  The matrix determines the action on Pauli
operators (`actC_eq_of_sem`), and a normal form is read off its action:
the Z-normal circuit `L` is the unique one sending a certain Pauli operator
`encL L` to `Z` on the top wire (Lemma 5.1), the X-normal circuit `M` is the
unique one sending `encDC M` to `X` on the bottom wire (Lemma 5.2), every
X-normal circuit sends `Z` on the top wire to `Z` on the bottom one
(Lemma 5.3), and the rest is a normal form on one wire less (Lemma 5.4,
Proposition 5.5); the scalar is then fixed by the matrix.

The action of the boxes `A`–`E` on the Pauli operators they meet
(Figure 6 of the paper) is decided on two wires (`fA` … `fEZ`) and moved to
any position (`box_at`).
-/
import QCert.SelingerClifford.PauliWires
import QCert.SelingerClifford.NormalForm
import Mathlib.Tactic.IntervalCases

namespace QCert.SelingerClifford

/-! ### Words at a position -/

/-- The data from the wire `c` up, moved down to the wire `0`. -/
def pick (c : ℕ) (P : PS) : PS := ⟨P.c, fun x => P.a (c + x), fun x => P.b (c + x)⟩

/-- `Q` moved up to the wire `c`, below which `P` stays. -/
def place (c : ℕ) (P Q : PS) : PS :=
  ⟨Q.c, fun x => if x < c then P.a x else Q.a (x - c),
    fun x => if x < c then P.b x else Q.b (x - c)⟩

theorem place_pick (c : ℕ) (P : PS) : place c P (pick c P) = P := by
  ext x <;> simp only [place, pick] <;> split_ifs <;> first | rfl | (congr 2; omega)

theorem pick_place (c : ℕ) (P Q : PS) : pick c (place c P Q) = Q := by
  ext x <;> simp [place, pick]

theorem place_place (c : ℕ) (P Q R : PS) : place c (place c P Q) R = place c P R := by
  ext x <;> simp only [place] <;> split_ifs <;> rfl

theorem act1PS_upBy (f : PD 1 → PD 1) (c i : ℕ) (P : PS) :
    act1PS f (c + i) P = place c P (act1PS f i (pick c P)) := by
  ext x <;> simp only [act1PS, place, pick, Function.update_apply] <;>
    split_ifs <;> first | rfl | omega | (congr 2; omega)

theorem act2PS_upBy (f : PD 2 → PD 2) (c i : ℕ) (P : PS) :
    act2PS f (c + i) P = place c P (act2PS f i (pick c P)) := by
  ext x <;> simp only [act2PS, place, pick, Function.update_apply, Nat.add_assoc] <;>
    split_ifs <;> first | rfl | omega | (congr 2; omega)

theorem actLt_upBy (a : Lt) (c : ℕ) (P : PS) :
    actLt (a.upBy c) P = place c P (actLt a (pick c P)) := by
  cases a with
  | om => exact (place_pick c P).symm
  | H i => exact act1PS_upBy _ c i P
  | S i => exact act1PS_upBy _ c i P
  | CZ i => exact act2PS_upBy _ c i P

/-- A word moved up to the wire `c` acts on the data from `c` up. -/
theorem actW_upN (c : ℕ) : ∀ (w : List Lt) (P : PS),
    actW (upN c w) P = place c P (actW w (pick c P))
  | [], P => by rw [upN_nil]; exact (place_pick c P).symm
  | a :: w, P => by
    rw [upN_cons]
    show actW (upN c w) (actLt (a.upBy c) P) = _
    rw [actW_upN c w, actLt_upBy, pick_place, place_place]
    rfl

/-! ### Words on the bottom wires -/

/-- The data `R` on the wires below `k`, and `Q` above. -/
def merge (k : ℕ) (Q R : PS) : PS :=
  ⟨R.c, fun x => if x < k then R.a x else Q.a x, fun x => if x < k then R.b x else Q.b x⟩

/-- The data on the bottom `k` wires. -/
def toPD (k : ℕ) (Q : PS) : PD k := ⟨Q.c, fun x => Q.a x, fun x => Q.b x⟩

theorem merge_toPD (k : ℕ) (Q : PS) : merge k Q (toPS (toPD k Q)) = Q := by
  ext x <;> simp only [merge, toPS, toPD] <;> split_ifs <;> rfl

theorem act1PS_merge (f : PD 1 → PD 1) {i k : ℕ} (hi : i + 1 ≤ k) (Q R : PS) :
    act1PS f i (merge k Q R) = merge k Q (act1PS f i R) := by
  ext x <;> simp only [act1PS, merge, Function.update_apply] <;>
    split_ifs <;> first | rfl | omega

theorem act2PS_merge (f : PD 2 → PD 2) {i k : ℕ} (hi : i + 2 ≤ k) (Q R : PS) :
    act2PS f i (merge k Q R) = merge k Q (act2PS f i R) := by
  ext x <;> simp only [act2PS, merge, Function.update_apply] <;>
    split_ifs <;> first | rfl | omega

theorem actLt_merge {k : ℕ} (a : Lt) (ha : a.hi ≤ k) (Q R : PS) :
    actLt a (merge k Q R) = merge k Q (actLt a R) := by
  cases a with
  | om => rfl
  | H i => exact act1PS_merge _ ha Q R
  | S i => exact act1PS_merge _ ha Q R
  | CZ i => exact act2PS_merge _ ha Q R

theorem actW_merge {k : ℕ} : ∀ (w : List Lt), (∀ a ∈ w, a.hi ≤ k) → ∀ Q R : PS,
    actW w (merge k Q R) = merge k Q (actW w R)
  | [], _, _, _ => rfl
  | a :: w, hw, Q, R => by
    show actW w (actLt a (merge k Q R)) = _
    rw [actLt_merge a (hw a (by simp)), actW_merge w (fun b hb => hw b (by simp [hb]))]
    rfl

/-- **A box at the wire `c`**: its action, decided on its own wires. -/
theorem box_at {k : ℕ} (w : List Lt) (hw : ∀ a ∈ w, a.hi ≤ k) (c : ℕ) (P : PS)
    {D D' : PD k} (hD : toPD k (pick c P) = D) (hact : actC k (wc k w) D = D') :
    actW (upN c w) P = place c P (merge k (pick c P) (toPS D')) := by
  rw [actW_upN]
  congr 1
  calc actW w (pick c P) = actW w (merge k (pick c P) (toPS (toPD k (pick c P)))) := by
        rw [merge_toPD]
    _ = merge k (pick c P) (actW w (toPS (toPD k (pick c P)))) := actW_merge w hw _ _
    _ = merge k (pick c P) (toPS (actC k (wc k w) (toPD k (pick c P)))) := by
        rw [toPS_actC_wc w hw]
    _ = _ := by rw [hD, hact]

/-! ### The boxes on Pauli operators (Figure 6) -/

/-- The data on the wire `c` set to `X^x Z^z`, and the phase to `p`. -/
def set1 (P : PS) (c : ℕ) (x z : Fin 2) (p : Fin 4) : PS :=
  ⟨p, Function.update P.a c x, Function.update P.b c z⟩

/-- The data on the wires `c`, `c + 1` set, and the phase to `p`. -/
def set2 (P : PS) (c : ℕ) (x0 z0 x1 z1 : Fin 2) (p : Fin 4) : PS :=
  ⟨p, Function.update (Function.update P.a c x0) (c + 1) x1,
    Function.update (Function.update P.b c z0) (c + 1) z1⟩

theorem place_merge1 (c : ℕ) (P : PS) (p : Fin 4) (x z : Fin 2) :
    place c P (merge 1 (pick c P) (toPS (⟨p, ![x], ![z]⟩ : PD 1))) = set1 P c x z p := by
  ext y
  · rfl
  all_goals
    simp only [place, merge, pick, toPS, set1, Function.update_apply]
    rcases lt_trichotomy y c with h | rfl | h
    · simp [h, show y ≠ c by omega]
    · simp
    · simp [show ¬ y < c by omega, show ¬ y - c < 1 by omega, show y ≠ c by omega,
        show c + (y - c) = y by omega]

theorem place_merge2 (c : ℕ) (P : PS) (p : Fin 4) (x0 z0 x1 z1 : Fin 2) :
    place c P (merge 2 (pick c P) (toPS (⟨p, ![x0, x1], ![z0, z1]⟩ : PD 2))) =
      set2 P c x0 z0 x1 z1 p := by
  ext y
  · rfl
  all_goals
    simp only [place, merge, pick, toPS, set2, Function.update_apply]
    rcases lt_trichotomy y c with h | rfl | h
    · simp [h, show y ≠ c by omega, show y ≠ c + 1 by omega]
    · simp
    · rcases Nat.lt_or_ge y (c + 2) with h' | h'
      · obtain rfl : y = c + 1 := by omega
        simp
      · simp [show ¬ y < c by omega, show ¬ y - c < 2 by omega, show y ≠ c by omega,
          show y ≠ c + 1 by omega, show c + (y - c) = y by omega]

/-- The Pauli operator `A_{i+1}` sends to `Z`, and its phase. -/
def xA : Fin 3 → Fin 2 := ![0, 1, 1]
def zA : Fin 3 → Fin 2 := ![1, 0, 1]
def cA : Fin 3 → Fin 4 := ![0, 0, 1]
/-- The Pauli operator on the upper wire that `B_{j+1}` sends, with `Z` on
the lower wire, to `Z` on the upper wire, and its phase; the same for the
lower wire of `D_{j+1}`. -/
def xB : Fin 4 → Fin 2 := ![0, 1, 1, 0]
def zB : Fin 4 → Fin 2 := ![0, 0, 1, 1]
def cB : Fin 4 → Fin 4 := ![0, 0, 1, 0]
/-- The phase of `C_{k+1}`. -/
def cC : Fin 2 → Fin 4 := ![0, 2]
/-- The Pauli operator that `E_{h+1}` sends to `X`, and its phase. -/
def zE : Fin 4 → Fin 2 := ![0, 1, 0, 1]
def cE : Fin 4 → Fin 4 := ![0, 3, 2, 1]

theorem fA : ∀ (i : Fin 3) (p : Fin 4), actC 1 (wc 1 (bA (i.val + 1) 0))
    ⟨p + cA i, ![xA i], ![zA i]⟩ = ⟨p, ![0], ![1]⟩ := by decide +kernel
theorem fB : ∀ (j p : Fin 4), actC 2 (wc 2 (bB (j.val + 1) 0))
    ⟨p + cB j, ![0, xB j], ![1, zB j]⟩ = ⟨p, ![0, 0], ![0, 1]⟩ := by decide +kernel
theorem fC : ∀ (k : Fin 2) (p : Fin 4), actC 1 (wc 1 (bC (k.val + 1) 0))
    ⟨p + cC k, ![0], ![1]⟩ = ⟨p, ![0], ![1]⟩ := by decide +kernel
theorem fD : ∀ (l p : Fin 4) (t : Fin 2), actC 2 (wc 2 (bD (l.val + 1) 0))
    ⟨p + cB l, ![xB l, 1], ![zB l, t]⟩ = ⟨p, ![1, 0], ![t, 0]⟩ := by decide +kernel
theorem fDZ : ∀ (l p : Fin 4), actC 2 (wc 2 (bD (l.val + 1) 0))
    ⟨p, ![0, 0], ![0, 1]⟩ = ⟨p, ![0, 0], ![1, 0]⟩ := by decide +kernel
theorem fE : ∀ (h p : Fin 4), actC 1 (wc 1 (bE (h.val + 1) 0))
    ⟨p + cE h, ![1], ![zE h]⟩ = ⟨p, ![1], ![0]⟩ := by decide +kernel
theorem fEZ : ∀ (h p : Fin 4), actC 1 (wc 1 (bE (h.val + 1) 0))
    ⟨p, ![0], ![1]⟩ = ⟨p, ![0], ![1]⟩ := by decide +kernel

theorem toPD1_pick (c : ℕ) (P : PS) (p : Fin 4) (x z : Fin 2) (hp : P.c = p)
    (hx : P.a c = x) (hz : P.b c = z) : toPD 1 (pick c P) = ⟨p, ![x], ![z]⟩ := by
  refine PD.ext hp (funext fun i => ?_) (funext fun i => ?_) <;>
    (rw [Fin.fin_one_eq_zero i]; simpa [toPD, pick])

theorem toPD2_pick (c : ℕ) (P : PS) (p : Fin 4) (x0 z0 x1 z1 : Fin 2) (hp : P.c = p)
    (hx0 : P.a c = x0) (hz0 : P.b c = z0) (hx1 : P.a (c + 1) = x1) (hz1 : P.b (c + 1) = z1) :
    toPD 2 (pick c P) = ⟨p, ![x0, x1], ![z0, z1]⟩ := by
  refine PD.ext hp (funext fun i => ?_) (funext fun i => ?_) <;>
    fin_cases i <;> simpa [toPD, pick]

theorem hi_box1 {f : ℕ → ℕ → List Lt} (hf : ∀ i a, Within a (a + 1) (f i a)) (i : ℕ) :
    ∀ x ∈ f i 0, x.hi ≤ 1 := fun x hx => (hf i 0).2 x hx

theorem hi_box2 {f : ℕ → ℕ → List Lt} (hf : ∀ i a, Within a (a + 2) (f i a)) (i : ℕ) :
    ∀ x ∈ f i 0, x.hi ≤ 2 := fun x hx => (hf i 0).2 x hx

theorem boxA (i : Fin 3) (a : ℕ) (P : PS) (h1 : P.a a = xA i) (h2 : P.b a = zA i) :
    actW (bA (i.val + 1) a) P = set1 P a 0 1 (P.c - cA i) := by
  have e : bA (i.val + 1) a = upN a (bA (i.val + 1) 0) := (upN_bA a _ 0).symm
  rw [e, box_at _ (hi_box1 within_bA _) a P
    (toPD1_pick a P _ _ _ (sub_add_cancel P.c (cA i)).symm h1 h2) (fA i _), place_merge1]

theorem boxB (j : Fin 4) (c : ℕ) (P : PS) (h1 : P.a c = 0) (h2 : P.b c = 1)
    (h3 : P.a (c + 1) = xB j) (h4 : P.b (c + 1) = zB j) :
    actW (bB (j.val + 1) c) P = set2 P c 0 0 0 1 (P.c - cB j) := by
  have e : bB (j.val + 1) c = upN c (bB (j.val + 1) 0) := (upN_bB c _ 0).symm
  rw [e, box_at _ (hi_box2 within_bB _) c P
    (toPD2_pick c P _ _ _ _ _ (sub_add_cancel P.c (cB j)).symm h1 h2 h3 h4) (fB j _),
    place_merge2]

theorem boxC (k : Fin 2) (c : ℕ) (P : PS) (h1 : P.a c = 0) (h2 : P.b c = 1) :
    actW (bC (k.val + 1) c) P = set1 P c 0 1 (P.c - cC k) := by
  have e : bC (k.val + 1) c = upN c (bC (k.val + 1) 0) := (upN_bC c _ 0).symm
  rw [e, box_at _ (hi_box1 within_bC _) c P
    (toPD1_pick c P _ _ _ (sub_add_cancel P.c (cC k)).symm h1 h2) (fC k _), place_merge1]

theorem boxD (l : Fin 4) (d : ℕ) (P : PS) (h1 : P.a d = xB l) (h2 : P.b d = zB l)
    (h3 : P.a (d + 1) = 1) :
    actW (bD (l.val + 1) d) P = set2 P d 1 (P.b (d + 1)) 0 0 (P.c - cB l) := by
  have e : bD (l.val + 1) d = upN d (bD (l.val + 1) 0) := (upN_bD d _ 0).symm
  rw [e, box_at _ (hi_box2 within_bD _) d P
    (toPD2_pick d P _ _ _ _ _ (sub_add_cancel P.c (cB l)).symm h1 h2 h3 rfl) (fD l _ _),
    place_merge2]

theorem boxDZ (l : Fin 4) (d : ℕ) (P : PS) (h1 : P.a d = 0) (h2 : P.b d = 0)
    (h3 : P.a (d + 1) = 0) (h4 : P.b (d + 1) = 1) :
    actW (bD (l.val + 1) d) P = set2 P d 0 1 0 0 P.c := by
  have e : bD (l.val + 1) d = upN d (bD (l.val + 1) 0) := (upN_bD d _ 0).symm
  rw [e, box_at _ (hi_box2 within_bD _) d P
    (toPD2_pick d P _ _ _ _ _ rfl h1 h2 h3 h4) (fDZ l _), place_merge2]

theorem boxE (h : Fin 4) (P : PS) (h1 : P.a 0 = 1) (h2 : P.b 0 = zE h) :
    actW (bE (h.val + 1) 0) P = set1 P 0 1 0 (P.c - cE h) := by
  have e : bE (h.val + 1) 0 = upN 0 (bE (h.val + 1) 0) := rfl
  rw [e, box_at _ (hi_box1 within_bE _) 0 P
    (toPD1_pick 0 P _ _ _ (sub_add_cancel P.c (cE h)).symm h1 h2) (fE h _), place_merge1]

theorem boxEZ (h : Fin 4) (P : PS) (h1 : P.a 0 = 0) (h2 : P.b 0 = 1) :
    actW (bE (h.val + 1) 0) P = set1 P 0 0 1 P.c := by
  have e : bE (h.val + 1) 0 = upN 0 (bE (h.val + 1) 0) := rfl
  rw [e, box_at _ (hi_box1 within_bE _) 0 P (toPD1_pick 0 P _ _ _ rfl h1 h2) (fEZ h _),
    place_merge1]

/-! ### Setting wires -/

theorem set1_set1 (P : PS) (c : ℕ) (x z x' z' : Fin 2) (p q : Fin 4) :
    set1 (set1 P c x z p) c x' z' q = set1 P c x' z' q := by
  ext y <;> simp only [set1, Function.update_apply] <;> split_ifs <;> rfl

theorem set1_self {P : PS} {c : ℕ} {x z : Fin 2} (hx : P.a c = x) (hz : P.b c = z) :
    set1 P c x z P.c = P := by
  ext y <;> simp only [set1, Function.update_apply] <;> split_ifs with h <;> subst_vars <;> rfl

theorem set2_set2 (P : PS) (c : ℕ) (x0 z0 x1 z1 x0' z0' x1' z1' : Fin 2) (p q : Fin 4) :
    set2 (set2 P c x0 z0 x1 z1 p) c x0' z0' x1' z1' q = set2 P c x0' z0' x1' z1' q := by
  ext y <;> simp only [set2, Function.update_apply] <;> split_ifs <;> rfl

theorem set2_self {P : PS} {c : ℕ} {x0 z0 x1 z1 : Fin 2} (hx0 : P.a c = x0) (hz0 : P.b c = z0)
    (hx1 : P.a (c + 1) = x1) (hz1 : P.b (c + 1) = z1) : set2 P c x0 z0 x1 z1 P.c = P := by
  ext y <;> simp only [set2, Function.update_apply] <;> split_ifs <;> subst_vars <;> rfl

@[simp] theorem set1_c (P : PS) (c : ℕ) (x z : Fin 2) (p : Fin 4) : (set1 P c x z p).c = p := rfl
@[simp] theorem set2_c (P : PS) (c : ℕ) (x0 z0 x1 z1 : Fin 2) (p : Fin 4) :
    (set2 P c x0 z0 x1 z1 p).c = p := rfl

theorem set2_a0 (P : PS) (c : ℕ) (x0 z0 x1 z1 : Fin 2) (p : Fin 4) :
    (set2 P c x0 z0 x1 z1 p).a c = x0 := by simp [set2]
theorem set2_b0 (P : PS) (c : ℕ) (x0 z0 x1 z1 : Fin 2) (p : Fin 4) :
    (set2 P c x0 z0 x1 z1 p).b c = z0 := by simp [set2]
theorem set2_a1 (P : PS) (c : ℕ) (x0 z0 x1 z1 : Fin 2) (p : Fin 4) :
    (set2 P c x0 z0 x1 z1 p).a (c + 1) = x1 := by simp [set2]
theorem set2_b1 (P : PS) (c : ℕ) (x0 z0 x1 z1 : Fin 2) (p : Fin 4) :
    (set2 P c x0 z0 x1 z1 p).b (c + 1) = z1 := by simp [set2]
theorem set2_a (P : PS) (c : ℕ) (x0 z0 x1 z1 : Fin 2) (p : Fin 4) {y : ℕ} (h0 : y ≠ c)
    (h1 : y ≠ c + 1) : (set2 P c x0 z0 x1 z1 p).a y = P.a y := by simp [set2, h0, h1]
theorem set2_b (P : PS) (c : ℕ) (x0 z0 x1 z1 : Fin 2) (p : Fin 4) {y : ℕ} (h0 : y ≠ c)
    (h1 : y ≠ c + 1) : (set2 P c x0 z0 x1 z1 p).b y = P.b y := by simp [set2, h0, h1]

/-! ### Lemma 5.1: the Z-normal circuits -/

/-- `Z` on the wire `w`. -/
def ZPS (w : ℕ) : PS := ⟨0, fun _ => 0, fun x => if x = w then 1 else 0⟩

/-- `X` on the wire `0`. -/
def X0PS : PS := ⟨0, fun x => if x = 0 then 1 else 0, fun _ => 0⟩

/-- The Pauli operator that the ladder `BC c js k` sends to `Z` on its top
wire: `Z` on the wire `c` and, above it, the operators of Figure 6(a). -/
def encBC : ℕ → List (Fin 4) → Fin 2 → PS
  | c, [], k => ⟨cC k, fun _ => 0, fun x => if x = c then 1 else 0⟩
  | c, j :: js, k => set2 (encBC (c + 1) js k) c 0 1 (xB j) (zB j) ((encBC (c + 1) js k).c + cB j)

theorem encBC_below : ∀ (js : List (Fin 4)) (c : ℕ) (k : Fin 2) (x : ℕ), x < c →
    (encBC c js k).a x = 0 ∧ (encBC c js k).b x = 0
  | [], c, k, x, h => by simp [encBC, show x ≠ c by omega]
  | j :: js, c, k, x, h => by
    simp only [encBC]
    rw [set2_a _ _ _ _ _ _ _ (by omega) (by omega), set2_b _ _ _ _ _ _ _ (by omega) (by omega)]
    exact encBC_below js (c + 1) k x (by omega)

theorem encBC_at (js : List (Fin 4)) (c : ℕ) (k : Fin 2) :
    (encBC c js k).a c = 0 ∧ (encBC c js k).b c = 1 := by
  cases js with
  | nil => simp [encBC]
  | cons j js => exact ⟨set2_a0 _ _ _ _ _ _ _, set2_b0 _ _ _ _ _ _ _⟩

theorem encBC_spec : ∀ (js : List (Fin 4)) (c : ℕ) (k : Fin 2),
    actW (BC c js k) (encBC c js k) = ZPS (c + js.length)
  | [], c, k => by
    simp only [BC]
    rw [boxC k c _ (encBC_at [] c k).1 (encBC_at [] c k).2]
    ext y <;> simp only [set1, encBC, ZPS, Function.update_apply, sub_self, List.length_nil,
      Nat.add_zero] <;> split_ifs <;> rfl
  | j :: js, c, k => by
    simp only [BC, actW_append, encBC]
    rw [boxB j c _ (set2_a0 _ _ _ _ _ _ _) (set2_b0 _ _ _ _ _ _ _) (set2_a1 _ _ _ _ _ _ _)
      (set2_b1 _ _ _ _ _ _ _), set2_set2, set2_c, add_sub_cancel_right]
    have hb := encBC_below js (c + 1) k c (by omega)
    have ha := encBC_at js (c + 1) k
    rw [set2_self hb.1 hb.2 ha.1 ha.2, encBC_spec js (c + 1) k]
    congr 1; simp; omega

/-- The Pauli operator a Z-normal circuit sends to `Z` on the top wire. -/
def encL {n : ℕ} (L : ZNormal n) : PS :=
  set1 (encBC L.a L.js L.k) L.a (xA L.i) (zA L.i) ((encBC L.a L.js L.k).c + cA L.i)

/-- **Lemma 5.1, existence**: `L • encL L = Z` on the top wire. -/
theorem encL_spec {n : ℕ} (L : ZNormal n) : actW L.word (encL L) = ZPS (n - 1) := by
  simp only [ZNormal.word, actW_append, encL]
  rw [boxA L.i L.a _ (by simp [set1]) (by simp [set1]), set1_set1, set1_c, add_sub_cancel_right]
  have ha := encBC_at L.js L.a L.k
  rw [set1_self ha.1 ha.2, encBC_spec]
  congr 1; have := L.h; omega

theorem cC_inj : ∀ k k' : Fin 2, cC k = cC k' → k = k' := by decide
theorem B_inj : ∀ j j' : Fin 4, xB j = xB j' → zB j = zB j' → j = j' := by decide
theorem A_inj : ∀ i i' : Fin 3, xA i = xA i' → zA i = zA i' → i = i' := by decide
theorem A_ne : ∀ i : Fin 3, ¬ (xA i = 0 ∧ zA i = 0) := by decide
theorem E_inj : ∀ h h' : Fin 4, zE h = zE h' → cE h = cE h' → h = h' := by decide

theorem encBC_inj : ∀ (js js' : List (Fin 4)) (c : ℕ) (k k' : Fin 2),
    js.length = js'.length → encBC c js k = encBC c js' k' → js = js' ∧ k = k'
  | [], [], c, k, k', _, h => ⟨rfl, cC_inj k k' (congrArg PS.c h)⟩
  | j :: js, j' :: js', c, k, k', hl, h => by
    simp only [encBC] at h
    have hj : j = j' := B_inj j j'
      (by have := congrArg (fun P => P.a (c + 1)) h; simpa [set2_a1] using this)
      (by have := congrArg (fun P => P.b (c + 1)) h; simpa [set2_b1] using this)
    subst hj
    have e : ∀ (js : List (Fin 4)) (k : Fin 2),
        set2 (set2 (encBC (c + 1) js k) c 0 1 (xB j) (zB j) ((encBC (c + 1) js k).c + cB j))
          c 0 0 0 1 ((encBC (c + 1) js k).c + cB j - cB j) = encBC (c + 1) js k := by
      intro js k
      have hb := encBC_below js (c + 1) k c (by omega)
      have ha := encBC_at js (c + 1) k
      rw [set2_set2, add_sub_cancel_right]
      exact set2_self hb.1 hb.2 ha.1 ha.2
    have h' := congrArg (fun P => set2 P c 0 0 0 1 (P.c - cB j)) h
    simp only [set2_c] at h'
    rw [e, e] at h'
    obtain ⟨h1, h2⟩ := encBC_inj js js' (c + 1) k k' (by simpa using hl) h'
    exact ⟨by rw [h1], h2⟩
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl

/-- **Lemma 5.1, uniqueness**: a Z-normal circuit is determined by the
operator it sends to `Z` on the top wire. -/
theorem encL_inj {n : ℕ} {L L' : ZNormal n} (h : encL L = encL L') : L = L' := by
  obtain ⟨a, i, js, k, hn⟩ := L
  obtain ⟨a', i', js', k', hn'⟩ := L'
  simp only [encL] at h
  -- the lowest wire that is not the identity
  have key : ∀ {a a' : ℕ} {i i' : Fin 3} {js js' : List (Fin 4)} {k k' : Fin 2},
      a < a' → set1 (encBC a js k) a (xA i) (zA i) ((encBC a js k).c + cA i) ≠
        set1 (encBC a' js' k') a' (xA i') (zA i') ((encBC a' js' k').c + cA i') := by
    intro a a' i i' js js' k k' hlt he
    have h1 := congrArg (fun P => P.a a) he
    have h2 := congrArg (fun P => P.b a) he
    simp only [set1, Function.update_apply, if_true, show a ≠ a' by omega, if_false] at h1 h2
    exact A_ne i ⟨h1.trans (encBC_below js' a' k' a hlt).1, h2.trans (encBC_below js' a' k' a hlt).2⟩
  obtain rfl : a = a' := by
    rcases lt_trichotomy a a' with hlt | heq | hlt
    · exact absurd h (key hlt)
    · exact heq
    · exact absurd h.symm (key hlt)
  have hi : i = i' := A_inj i i'
    (by have := congrArg (fun P => P.a a) h; simpa [set1] using this)
    (by have := congrArg (fun P => P.b a) h; simpa [set1] using this)
  subst hi
  have e : ∀ (js : List (Fin 4)) (k : Fin 2),
      set1 (set1 (encBC a js k) a (xA i) (zA i) ((encBC a js k).c + cA i)) a 0 1
        ((encBC a js k).c + cA i - cA i) = encBC a js k := by
    intro js k
    have ha := encBC_at js a k
    rw [set1_set1, add_sub_cancel_right]
    exact set1_self ha.1 ha.2
  have h' := congrArg (fun P => set1 P a 0 1 (P.c - cA i)) h
  simp only [set1_c] at h'
  rw [e, e] at h'
  obtain ⟨rfl, rfl⟩ := encBC_inj js js' a k k' (by omega) h'
  rfl

/-! ### Lemmas 5.2 and 5.3: the X-normal circuits -/

/-- The Pauli operator that the ladder `DC ls h` sends to `X` on the wire `0`:
on its top wire `X` or `XZ`, below it the operators of Figure 6(b). -/
def encDC : List (Fin 4) → Fin 4 → PS
  | [], h => ⟨cE h, fun x => if x = 0 then 1 else 0, fun x => if x = 0 then zE h else 0⟩
  | l :: ls, h => set2 (encDC ls h) ls.length (xB l) (zB l) 1 ((encDC ls h).b ls.length)
      ((encDC ls h).c + cB l)

theorem encDC_top (ls : List (Fin 4)) (h : Fin 4) : (encDC ls h).a ls.length = 1 := by
  cases ls with
  | nil => simp [encDC]
  | cons l ls => exact set2_a1 _ _ _ _ _ _ _

theorem encDC_above : ∀ (ls : List (Fin 4)) (h : Fin 4) (x : ℕ), ls.length < x →
    (encDC ls h).a x = 0 ∧ (encDC ls h).b x = 0
  | [], h, x, hx => by simp [encDC, show x ≠ 0 by simp at hx; omega]
  | l :: ls, h, x, hx => by
    simp only [encDC]
    simp only [List.length_cons] at hx
    rw [set2_a _ _ _ _ _ _ _ (by omega) (by omega), set2_b _ _ _ _ _ _ _ (by omega) (by omega)]
    exact encDC_above ls h x (by omega)

/-- Undoing a step of `encDC`. -/
def recD (d : ℕ) (l : Fin 4) (P : PS) : PS := set2 P d 1 (P.b (d + 1)) 0 0 (P.c - cB l)

theorem unD (ls : List (Fin 4)) (h : Fin 4) (l : Fin 4) (d : ℕ) (hd : d = ls.length) :
    recD d l (set2 (encDC ls h) d (xB l) (zB l) 1 ((encDC ls h).b d)
      ((encDC ls h).c + cB l)) = encDC ls h := by
  subst hd
  have ht := encDC_top ls h
  have hab := encDC_above ls h (ls.length + 1) (by omega)
  simp only [recD, set2_b1, set2_c]
  rw [set2_set2, add_sub_cancel_right]
  exact set2_self ht rfl hab.1 hab.2

/-- **Lemma 5.2, existence**: `M • encDC = X` on the wire `0`. -/
theorem encDC_spec : ∀ (ls : List (Fin 4)) (h : Fin 4), actW (DC ls h) (encDC ls h) = X0PS
  | [], h => by
    simp only [DC]
    rw [boxE h _ (by simp [encDC]) (by simp [encDC])]
    ext y <;> simp only [set1, encDC, X0PS, Function.update_apply, sub_self] <;>
      split_ifs <;> simp_all
  | l :: ls, h => by
    simp only [DC, actW_append, encDC]
    rw [boxD l ls.length _ (set2_a0 _ _ _ _ _ _ _) (set2_b0 _ _ _ _ _ _ _)
      (set2_a1 _ _ _ _ _ _ _)]
    have := unD ls h l ls.length rfl
    simp only [recD, set2_b1, set2_c] at this
    rw [set2_b1, set2_c, this, encDC_spec ls h]

/-- **Lemma 5.3**: an X-normal circuit sends `Z` on the top wire to `Z` on
the wire `0`. -/
theorem DC_Z : ∀ (ls : List (Fin 4)) (h : Fin 4), actW (DC ls h) (ZPS ls.length) = ZPS 0
  | [], h => by
    simp only [DC, List.length_nil]
    rw [boxEZ h _ (by simp [ZPS]) (by simp [ZPS])]
    exact set1_self (by simp [ZPS]) (by simp [ZPS])
  | l :: ls, h => by
    simp only [DC, actW_append, List.length_cons]
    rw [boxDZ l ls.length _ (by simp [ZPS]) (by simp [ZPS]) (by simp [ZPS]) (by simp [ZPS])]
    have e : set2 (ZPS (ls.length + 1)) ls.length 0 1 0 0 (ZPS (ls.length + 1)).c =
        ZPS ls.length := by
      ext y <;> simp only [set2, ZPS, Function.update_apply] <;> split_ifs <;> first | rfl | omega
    rw [e, DC_Z ls h]

theorem encDC_inj : ∀ (ls ls' : List (Fin 4)) (h h' : Fin 4),
    ls.length = ls'.length → encDC ls h = encDC ls' h' → ls = ls' ∧ h = h'
  | [], [], h, h', _, he => by
    refine ⟨rfl, E_inj h h' ?_ (congrArg PS.c he)⟩
    have := congrArg (fun P => P.b 0) he
    simpa [encDC] using this
  | l :: ls, l' :: ls', h, h', hl, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [encDC] at he
    have hl' : l = l' := B_inj l l'
      (by have := congrArg (fun P => P.a ls.length) he; simpa [set2_a0, hl] using this)
      (by have := congrArg (fun P => P.b ls.length) he; simpa [set2_b0, hl] using this)
    subst hl'
    rw [← hl] at he
    have hr := congrArg (recD ls.length l) he
    rw [unD ls h l ls.length rfl, unD ls' h' l ls.length hl] at hr
    obtain ⟨h1, h2⟩ := encDC_inj ls ls' h h' hl hr
    exact ⟨by rw [h1], h2⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- **Lemma 5.2, uniqueness**: an X-normal circuit is determined by the
operator it sends to `X` on the wire `0`. -/
theorem encM_inj {n : ℕ} {M M' : XNormal n} (h : encDC M.ls M.h = encDC M'.ls M'.h) :
    M = M' := by
  obtain ⟨ls, hh, hl⟩ := M
  obtain ⟨ls', hh', hl'⟩ := M'
  obtain ⟨rfl, rfl⟩ := encDC_inj ls ls' hh hh' (by omega) h
  rfl

/-! ### Injectivity and surjectivity of the action -/

/-- A circuit acts injectively: its matrix is invertible. -/
theorem actC_inj {n : ℕ} (w : Circ n) : Function.Injective (actC n w) := by
  intro P Q h
  apply PD.op_inj
  have hP := sem_conj w P
  have hQ := sem_conj w Q
  rw [h] at hP
  have e := hP.trans hQ.symm
  have hu : star (S.sem n w).1 * (S.sem n w).1 = 1 := (S.sem n w).2.1
  calc P.op = (star (S.sem n w).1 * (S.sem n w).1) * P.op := by rw [hu, one_mul]
    _ = star (S.sem n w).1 * ((S.sem n w).1 * P.op) := mul_assoc _ _ _
    _ = star (S.sem n w).1 * ((S.sem n w).1 * Q.op) := by rw [e]
    _ = Q.op := by rw [← mul_assoc, hu, one_mul]

/-- Data on the bottom `n` wires. -/
def Supp (n : ℕ) (X : PS) : Prop := ∀ x, n ≤ x → X.a x = 0 ∧ X.b x = 0

theorem toPS_toPD {n : ℕ} {X : PS} (h : Supp n X) : toPS (toPD n X) = X := by
  ext x <;> simp only [toPS, toPD] <;> split_ifs with hx
  · rfl
  · rw [(h x (by omega)).1]
  · rfl
  · rw [(h x (by omega)).2]

theorem supp_toPS {n : ℕ} (P : PD n) : Supp n (toPS P) := fun x hx => by
  simp [toPS, show ¬ x < n by omega]

theorem actW_inj {n : ℕ} {l : List Lt} (hl : ∀ a ∈ l, a.hi ≤ n) {X Y : PS} (hX : Supp n X)
    (hY : Supp n Y) (h : actW l X = actW l Y) : X = Y := by
  rw [← toPS_toPD hX, ← toPS_toPD hY, ← toPS_actC_wc l hl, ← toPS_actC_wc l hl] at h
  rw [← toPS_toPD hX, ← toPS_toPD hY, actC_inj (wc n l) (toPS_inj h)]

theorem actW_surj {n : ℕ} {l : List Lt} (hl : ∀ a ∈ l, a.hi ≤ n) {Y : PS} (hY : Supp n Y) :
    ∃ P : PD n, actW l (toPS P) = Y := by
  obtain ⟨P, hP⟩ := (Finite.injective_iff_surjective.mp (actC_inj (wc n l))) (toPD n Y)
  exact ⟨P, by rw [← toPS_actC_wc l hl, hP, toPS_toPD hY]⟩

theorem actLt_supp {n : ℕ} (a : Lt) (ha : a.hi ≤ n) {X : PS} (h : Supp n X) :
    Supp n (actLt a X) := by
  intro x hx
  cases a with
  | om => exact h x hx
  | H i =>
    have hxi : x ≠ i := by simp [Lt.hi] at ha; omega
    simp only [actLt, act1PS]
    rw [Function.update_of_ne hxi, Function.update_of_ne hxi]; exact h x hx
  | S i =>
    have hxi : x ≠ i := by simp [Lt.hi] at ha; omega
    simp only [actLt, act1PS]
    rw [Function.update_of_ne hxi, Function.update_of_ne hxi]; exact h x hx
  | CZ i =>
    have hxi : x ≠ i := by simp [Lt.hi] at ha; omega
    have hxi' : x ≠ i + 1 := by simp [Lt.hi] at ha; omega
    simp only [actLt, act2PS]
    rw [Function.update_of_ne hxi', Function.update_of_ne hxi, Function.update_of_ne hxi',
      Function.update_of_ne hxi]; exact h x hx

theorem actW_supp {n : ℕ} : ∀ {l : List Lt}, (∀ a ∈ l, a.hi ≤ n) → ∀ {X : PS}, Supp n X →
    Supp n (actW l X)
  | [], _, _, h => h
  | a :: l, hl, X, h =>
    actW_supp (l := l) (fun b hb => hl b (by simp [hb])) (actLt_supp a (hl a (by simp)) h)

/-! ### Circuits moved up -/

/-- The identity. -/
def IPS : PS := ⟨0, fun _ => 0, fun _ => 0⟩

theorem actLt_IPS (a : Lt) : actLt a IPS = IPS := by
  cases a <;> ext x <;> simp [actLt, act1PS, act2PS, IPS, actH, actS, actCZ, dbl, lft]

theorem actW_IPS : ∀ l : List Lt, actW l IPS = IPS
  | [] => rfl
  | a :: l => by show actW l (actLt a IPS) = IPS; rw [actLt_IPS, actW_IPS l]

theorem actLt_up (a : Lt) (x z : Fin 2) (Q : PS) :
    actLt a.up (consPS x z Q) = consPS x z (actLt a Q) := by
  cases a with
  | om => rfl
  | H i => exact act1PS_cons _ i x z Q
  | S i => exact act1PS_cons _ i x z Q
  | CZ i => exact act2PS_cons _ i x z Q

theorem actW_up : ∀ (l : List Lt) (x z : Fin 2) (Q : PS),
    actW (l.map Lt.up) (consPS x z Q) = consPS x z (actW l Q)
  | [], _, _, _ => rfl
  | a :: l, x, z, Q => by
    show actW (l.map Lt.up) (actLt a.up (consPS x z Q)) = _
    rw [actLt_up, actW_up l]
    rfl

theorem consPS_inj {x z : Fin 2} {Q Q' : PS} (h : consPS x z Q = consPS x z Q') : Q = Q' := by
  have h1 := congrArg PS.c h
  have h2 := congrArg PS.a h
  have h3 := congrArg PS.b h
  exact PS.ext h1 (funext fun w => congrFun h2 (w + 1)) (funext fun w => congrFun h3 (w + 1))

theorem ZPS_zero : ZPS 0 = consPS 0 1 IPS :=
  PS.ext rfl (funext fun w => by cases w <;> rfl)
    (funext fun w => by cases w <;> simp [ZPS, consPS, IPS])

theorem X0PS_eq : X0PS = consPS 1 0 IPS :=
  PS.ext rfl (funext fun w => by cases w <;> simp [X0PS, consPS, IPS])
    (funext fun w => by cases w <;> rfl)

/-! ### Where things lie -/

theorem encBC_above : ∀ (js : List (Fin 4)) (c : ℕ) (k : Fin 2) (x : ℕ), c + js.length < x →
    (encBC c js k).a x = 0 ∧ (encBC c js k).b x = 0
  | [], c, k, x, h => by simp [encBC, show x ≠ c by simp at h; omega]
  | j :: js, c, k, x, h => by
    simp only [encBC]
    simp only [List.length_cons] at h
    rw [set2_a _ _ _ _ _ _ _ (by omega) (by omega), set2_b _ _ _ _ _ _ _ (by omega) (by omega)]
    exact encBC_above js (c + 1) k x (by omega)

theorem supp_encL {n : ℕ} (L : ZNormal n) : Supp n (encL L) := by
  intro x hx
  have h := L.h
  simp only [encL, set1, Function.update, show x ≠ L.a by omega, dif_neg, not_false_eq_true]
  exact encBC_above L.js L.a L.k x (by omega)

theorem supp_encDC (ls : List (Fin 4)) (h : Fin 4) : Supp (ls.length + 1) (encDC ls h) :=
  fun x hx => encDC_above ls h x (by omega)

theorem supp_ZPS {n w : ℕ} (hw : w < n) : Supp n (ZPS w) := fun x hx => by
  simp [ZPS, show x ≠ w by omega]

theorem supp_X0PS {n : ℕ} (hn : 0 < n) : Supp n X0PS := fun x hx => by
  simp [X0PS, show x ≠ 0 by omega]

theorem supp_cons {n : ℕ} (P : PD n) : Supp (n + 1) (consPS 0 0 (toPS P)) := by
  intro x hx
  cases x with
  | zero => omega
  | succ x => exact supp_toPS P x (by omega)

theorem hi_of_within {lo hi : ℕ} {u : List Lt} (h : Within lo hi u) : ∀ a ∈ u, a.hi ≤ hi :=
  h.2

theorem ZNormal.hi {n : ℕ} (L : ZNormal n) : ∀ a ∈ L.word, a.hi ≤ n := by
  intro x hx
  have h := L.h
  rcases List.mem_append.1 hx with hx | hx
  · exact ((within_bA _ _).2 x hx).trans (by omega)
  · exact ((within_BC _ _ _).2 x hx).trans (by omega)

theorem XNormal.hi {n : ℕ} (M : XNormal n) : ∀ a ∈ M.word, a.hi ≤ n := by
  intro x hx
  exact ((within_DC _ _).2 x hx).trans (by have := M.hl; omega)

theorem up_hi (a : Lt) : a.up.hi = a.hi + 1 ∨ a = .om := by
  cases a <;> simp [Lt.up, Lt.hi]

theorem NF.word_hi : ∀ {n : ℕ} (N : NF n), ∀ a ∈ N.word, a.hi ≤ n
  | _, .scalar p, a, ha => by
    simp only [NF.word, List.mem_replicate] at ha
    rw [ha.2]; simp [Lt.hi]
  | n + 1, .cons L M N, a, ha => by
    simp only [NF.word, List.mem_append, List.mem_map] at ha
    rcases ha with (ha | ha) | ⟨b, hb, rfl⟩
    · exact L.hi a ha
    · exact M.hi a ha
    · rcases up_hi b with h | h
      · rw [h]; have := NF.word_hi N b hb; omega
      · subst h; simp [Lt.up, Lt.hi]

/-! ### Proposition 5.5 -/

/-- The scalar of a normal form. -/
def NF.sc : {n : ℕ} → NF n → Fin 8
  | _, .scalar p => p
  | _, .cons _ _ N => N.sc

/-- The normal form with another scalar. -/
def NF.setSc : {n : ℕ} → NF n → Fin 8 → NF n
  | _, .scalar _, q => .scalar q
  | _, .cons L M N, q => .cons L M (N.setSc q)

theorem NF.setSc_sc : ∀ {n : ℕ} (N : NF n), N.setSc N.sc = N
  | _, .scalar _ => rfl
  | _, .cons L M N => by simp only [NF.setSc, NF.sc, NF.setSc_sc N]

theorem NF.sc_setSc : ∀ {n : ℕ} (N : NF n) (q : Fin 8), (N.setSc q).sc = q
  | _, .scalar _, _ => rfl
  | _, .cons _ _ N, q => NF.sc_setSc N q

theorem NF.word_setSc : ∀ {n : ℕ} (N : NF n) (q : Fin 8),
    (N.setSc q).word = (N.setSc 0).word ++ List.replicate q.val .om
  | _, .scalar _, q => by simp [NF.setSc, NF.word]
  | _, .cons L M N, q => by
    simp only [NF.setSc, NF.word, NF.word_setSc N q, List.map_append, List.append_assoc]
    simp [List.map_replicate, Lt.up]

/-- **Proposition 5.5, uniqueness up to the scalar**: two normal forms that
act alike on Pauli operators differ at most in their scalar. -/
theorem nf_act_unique : ∀ (n : ℕ) (N N' : NF n),
    (∀ P : PD n, actW N.word (toPS P) = actW N'.word (toPS P)) → N' = N.setSc N'.sc
  | 0, .scalar _, .scalar _, _ => rfl
  | n + 1, .cons L M N, .cons L' M' N', h => by
    have hN := NF.word_hi N
    have hN' := NF.word_hi N'
    have hup : ∀ (N : NF n), ∀ a ∈ N.word.map Lt.up, a.hi ≤ n + 1 := by
      intro N a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      rcases up_hi b with e | e
      · rw [e]; have := NF.word_hi N b hb; omega
      · subst e; simp [Lt.up, Lt.hi]
    have hML : M.ls.length = n := by have := M.hl; omega
    have hML' : M'.ls.length = n := by have := M'.hl; omega
    have split3 : ∀ (L : ZNormal (n + 1)) (M : XNormal (n + 1)) (N : NF n) (X : PS),
        actW (NF.cons L M N).word X = actW (N.word.map Lt.up) (actW M.word (actW L.word X)) := by
      intro L M N X
      simp only [NF.word, actW_append]
    have fixZ : ∀ N : NF n, actW (N.word.map Lt.up) (ZPS 0) = ZPS 0 := by
      intro N; rw [ZPS_zero, actW_up, actW_IPS]
    have fixX : ∀ N : NF n, actW (N.word.map Lt.up) X0PS = X0PS := by
      intro N; rw [X0PS_eq, actW_up, actW_IPS]
    -- Lemma 5.1: the Z-normal parts agree
    obtain rfl : L = L' := by
      have h1 := h (toPD (n + 1) (encL L))
      rw [toPS_toPD (supp_encL L), split3, split3, encL_spec, Nat.add_sub_cancel] at h1
      have hZ : actW M.word (ZPS n) = ZPS 0 := by
        have := DC_Z M.ls M.h; rw [hML] at this; exact this
      rw [hZ, fixZ] at h1
      have h2 : actW M'.word (actW L'.word (encL L)) = ZPS 0 := by
        refine actW_inj (hup N') (actW_supp M'.hi (actW_supp L'.hi (supp_encL L)))
          (supp_ZPS (by omega)) ?_
        rw [← h1, fixZ]
      have hZ' : actW M'.word (ZPS n) = ZPS 0 := by
        have := DC_Z M'.ls M'.h; rw [hML'] at this; exact this
      have h3 : actW L'.word (encL L) = ZPS n :=
        actW_inj M'.hi (actW_supp L'.hi (supp_encL L)) (supp_ZPS (by omega)) (h2.trans hZ'.symm)
      have h4 := encL_spec L'
      rw [Nat.add_sub_cancel] at h4
      exact encL_inj (actW_inj L'.hi (supp_encL L) (supp_encL L') (h3.trans h4.symm))
    -- Lemma 5.2: the X-normal parts agree
    obtain rfl : M = M' := by
      obtain ⟨Q, hQ⟩ := actW_surj L.hi (n := n + 1) (Y := encDC M.ls M.h)
        (by have := supp_encDC M.ls M.h; rwa [hML] at this)
      have h1 := h Q
      rw [split3, split3, hQ] at h1
      have h1' : actW (N.word.map Lt.up) (actW M.word (encDC M.ls M.h)) = X0PS := by
        rw [show actW M.word (encDC M.ls M.h) = X0PS from encDC_spec M.ls M.h, fixX]
      rw [h1'] at h1
      have h2 : actW M'.word (encDC M.ls M.h) = X0PS := by
        refine actW_inj (hup N') (actW_supp M'.hi (by
          have := supp_encDC M.ls M.h; rwa [hML] at this)) (supp_X0PS (by omega)) ?_
        rw [← h1, fixX]
      have h3 := encDC_spec M'.ls M'.h
      have h4 : encDC M.ls M.h = encDC M'.ls M'.h :=
        actW_inj M'.hi (by have := supp_encDC M.ls M.h; rwa [hML] at this)
          (by have := supp_encDC M'.ls M'.h; rwa [hML'] at this)
          (h2.trans h3.symm)
      exact encM_inj h4
    -- the rest is a normal form on the top `n` wires
    have hrest : ∀ P : PD n, actW N.word (toPS P) = actW N'.word (toPS P) := by
      intro P
      have hLM : ∀ a ∈ L.word ++ M.word, a.hi ≤ n + 1 := by
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        exacts [L.hi a ha, M.hi a ha]
      obtain ⟨Q, hQ⟩ := actW_surj hLM (supp_cons P)
      have hQ' : actW M.word (actW L.word (toPS Q)) = consPS 0 0 (toPS P) := by
        rw [← actW_append]; exact hQ
      have h1 := h Q
      rw [split3, split3, hQ', actW_up, actW_up] at h1
      exact consPS_inj h1
    have := nf_act_unique n N N' hrest
    show NF.cons L M N' = NF.cons L M (N.setSc N'.sc)
    exact congrArg (NF.cons L M) this

/-! ### The scalar -/

theorem ω_pow_ne_one {d : ℕ} (h0 : 0 < d) (h8 : d < 8) : ω ^ d ≠ 1 := by
  have h2 := ω_sq
  have h4 := ω_pow_four
  have hI : Complex.I ≠ 1 := by intro h; have := congrArg Complex.im h; simp at this
  have hm : (-1 : ℂ) ≠ 1 := by norm_num
  intro h
  interval_cases d
  · exact hI (by rw [← h2, show ω ^ 2 = ω ^ 1 * ω ^ 1 by ring, h, one_mul])
  · exact hI (by rw [← h2, h])
  · exact hI (by
      have e : ω = -1 := by rw [← h4, show ω ^ 4 = ω ^ 3 * ω by ring, h, one_mul]
      rw [← h2, e]; norm_num)
  · exact hm (by rw [← h4, h])
  · exact hI (by
      have e : ω = -1 := by
        have : ω ^ 5 = ω ^ 4 * ω := by ring
        rw [h, h4] at this
        linear_combination this
      rw [← h2, e]; norm_num)
  · have : ω ^ 6 = ω ^ 4 * ω ^ 2 := by ring
    rw [h, h4, h2] at this
    have := congrArg Complex.re this
    simp at this
  · exact hI (by
      have e : ω = 1 := by
        have : ω ^ 8 = ω ^ 7 * ω := by ring
        rw [h, one_mul, show ω ^ 8 = (ω ^ 4) ^ 2 by ring, h4] at this
        rw [← this]; norm_num
      rw [← h2, e]; norm_num)

theorem ω_pow_inj {p q : ℕ} (hp : p < 8) (hq : q < 8) (h : ω ^ p = ω ^ q) : p = q := by
  have hω : ω ≠ 0 := by
    intro h0; have := ω_sq; rw [h0] at this; simp at this; exact Complex.I_ne_zero this.symm
  rcases le_total p q with hpq | hpq
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
    rw [pow_add] at h
    have : ω ^ d = 1 := by
      have := mul_left_cancel₀ (pow_ne_zero p hω) (h.symm.trans (mul_one _).symm)
      exact this
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · exact absurd this (ω_pow_ne_one hd (by omega))
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
    rw [pow_add] at h
    have : ω ^ d = 1 := mul_left_cancel₀ (pow_ne_zero q hω) (h.trans (mul_one _).symm)
    rcases Nat.eq_zero_or_pos d with hd | hd
    · omega
    · exact absurd this (ω_pow_ne_one hd (by omega))

theorem sem_om_pow {n : ℕ} (q : ℕ) : (S.sem n (wc n (List.replicate q .om))).1 = ω ^ q • 1 := by
  induction q with
  | zero => simp [wc]
  | succ q ih =>
    rw [List.replicate_succ, wc, map_mul, Submonoid.coe_mul, ih]
    show (ω ^ q • 1) * (S.gen (Gen.gate0 Gate.ω)).1 = _
    show (ω ^ q • 1) * ((S.scalar Gate.ω : ℂ) • 1) = _
    simp only [smul_mul_smul_comm, mul_one, pow_succ]
    rfl

/-- **Proposition 5.5**: distinct normal forms denote distinct operators. -/
theorem normal_unique' {n : ℕ} (N N' : NF n) (h : S.sem n N.circ = S.sem n N'.circ) : N = N' := by
  have hact : ∀ P : PD n, actW N.word (toPS P) = actW N'.word (toPS P) := by
    intro P
    rw [← toPS_actC_wc _ (NF.word_hi N), ← toPS_actC_wc _ (NF.word_hi N')]
    exact congrArg toPS (actC_eq_of_sem h P)
  have e := nf_act_unique n N N' hact
  -- the two differ at most in the scalar, which the matrix fixes
  have hw : ∀ q : Fin 8, S.sem n (N.setSc q).circ =
      S.sem n (wc n (List.replicate q.val .om)) * S.sem n (N.setSc 0).circ := by
    intro q
    simp only [NF.circ, NF.word_setSc N q, wc_append, map_mul]
  have h' : S.sem n (N.setSc N.sc).circ = S.sem n (N.setSc N'.sc).circ := by
    rw [NF.setSc_sc, ← e]; exact h
  rw [hw N.sc, hw N'.sc] at h'
  have h'' := mul_right_cancel h'
  have hv := congrArg Subtype.val h''
  rw [sem_om_pow, sem_om_pow] at hv
  have hq := congrFun (congrFun hv (fun _ => 0)) (fun _ => 0)
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hq
  have := ω_pow_inj N.sc.2 N'.sc.2 hq
  have hsc : N.sc = N'.sc := Fin.ext this
  rw [e, ← hsc, NF.setSc_sc]

end QCert.SelingerClifford
