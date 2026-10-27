/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): dirty gates and ladders

The material for Section 6 (Lemma 6.2, Proposition 6.3).  A *dirty gate*
(`Dg`) is one of `ω`, `H`, `S`, `X = HSSH` or `CZ` at an absolute position;
dirty gates travel through a normal form from left to right.  The normal
forms of Definition 4.3 are built from two ladders: `BC c js k` is
`B_{j₁} … B_{j_r}` going up from the wire `c`, then `C_k` on the top wire, and
`DC ls h` is `D_{ℓ₁} … D_{ℓ_r}` going down to the bottom wire, then `E_h` on
it.  The labels ①–④ of the dirty normal forms (Section 6) say which dirty
gates may stand where: `okB c` inside a `B`-ladder whose current wire (label
②) is `c`, `okD top c` inside a `D`-ladder whose current wire (label ④, or
③ before the first `D` when `top`) is `c`, and `okN` after the ladders.

`Holds.at` moves an equation of `Tables` into place, and `Holds.swap`
commutes words on disjoint wires.
-/
import QCert.SelingerClifford.Boxes
import QCert.SelingerClifford.Rewrite

namespace QCert.SelingerClifford

/-! ### Dirty gates -/

/-- A dirty gate at an absolute position (`CZ w` on the wires `w, w + 1`). -/
inductive Dg
  | om
  | H (w : ℕ)
  | S (w : ℕ)
  | X (w : ℕ)
  | CZ (w : ℕ)
  deriving DecidableEq, Repr

namespace Dg

/-- The letters of a dirty gate. -/
def word : Dg → List Lt
  | om => [.om]
  | H w => [.H w]
  | S w => [.S w]
  | X w => bX w
  | CZ w => [.CZ w]

/-- The dirty gate `s` wires up. -/
def shift (s : ℕ) : Dg → Dg
  | om => om
  | H w => H (s + w)
  | S w => S (s + w)
  | X w => X (s + w)
  | CZ w => CZ (s + w)

/-- One more than the highest wire (`0` for the scalar). -/
def hi : Dg → ℕ
  | om => 0
  | H w => w + 1
  | S w => w + 1
  | X w => w + 1
  | CZ w => w + 2

end Dg

/-- The letters of a word of dirty gates. -/
def dw (l : List Dg) : List Lt := l.flatMap Dg.word

@[simp] theorem dw_nil : dw [] = [] := rfl
@[simp] theorem dw_cons (g : Dg) (l : List Dg) : dw (g :: l) = g.word ++ dw l := rfl
@[simp] theorem dw_append (l l' : List Dg) : dw (l ++ l') = dw l ++ dw l' := by
  simp [dw, List.flatMap_append]

/-- Every gate of `r` satisfies `p` and lies on the bottom `n` wires. -/
def OkL (p : Dg → Bool) (n : ℕ) (r : List Dg) : Prop := ∀ x ∈ r, p x = true ∧ x.hi ≤ n

instance (p : Dg → Bool) (n : ℕ) (r : List Dg) : Decidable (OkL p n r) := by
  unfold OkL; infer_instance

theorem OkL.nil (p : Dg → Bool) (n : ℕ) : OkL p n [] := by simp [OkL]

theorem OkL.append {p : Dg → Bool} {n : ℕ} {r r' : List Dg} (h : OkL p n r) (h' : OkL p n r') :
    OkL p n (r ++ r') := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  exacts [h x hx, h' x hx]

theorem OkL.single {p : Dg → Bool} {n : ℕ} {g : Dg} (h : p g = true) (h' : g.hi ≤ n) :
    OkL p n [g] := by
  simp [OkL, h, h']

theorem OkL.mono {p q : Dg → Bool} {n n' : ℕ} {r : List Dg} (h : OkL p n r)
    (hpq : ∀ x, p x = true → x.hi ≤ n → q x = true) (hn : n ≤ n') : OkL q n' r :=
  fun x hx => ⟨hpq x (h x hx).1 (h x hx).2, (h x hx).2.trans hn⟩

/-! ### The labels -/

/-- Allowed inside a `B`-ladder whose current wire (label ②) is `c`: `H` on
the other wires, `S` anywhere, `X` on `c`, `CZ` whose lower wire is not `c`. -/
def okB (c : ℕ) : Dg → Bool
  | .om => true
  | .H w => w != c
  | .S _ => true
  | .X w => w == c
  | .CZ w => w != c

/-- Allowed inside a `D`-ladder whose current wire is `c` (label ④, or ③
before the first `D` when `top`): `H` on the other wires, `S` anywhere, no
`X`, `CZ` whose lower wire is not `c` and, below the first `D` only, whose
upper wire may be `c`. -/
def okD (top : Bool) (c : ℕ) : Dg → Bool
  | .om => true
  | .H w => w != c
  | .S _ => true
  | .X _ => false
  | .CZ w => w != c && (top || w + 1 != c)

/-- Allowed after the ladders: not on the bottom wire, and no `X`. -/
def okN : Dg → Bool
  | .om => true
  | .H w => w != 0
  | .S w => w != 0
  | .X _ => false
  | .CZ w => w != 0

/-- Allowed before a normal form: no `X` (all wires are labelled ①). -/
def okA : Dg → Bool
  | .X _ => false
  | _ => true

theorem okB_shift (s c : ℕ) (g : Dg) : okB (s + c) (g.shift s) = okB c g := by
  cases g <;> simp only [okB, Dg.shift] <;> rw [Bool.eq_iff_iff] <;> simp

theorem okD_shift (top : Bool) (s c : ℕ) (g : Dg) :
    okD top (s + c) (g.shift s) = okD top c g := by
  cases g <;> cases top <;> simp only [okD, Dg.shift] <;> rw [Bool.eq_iff_iff] <;> simp
  intro _
  constructor <;> (intro h h'; apply h; omega)

theorem hi_shift (s : ℕ) (g : Dg) : (g.shift s).hi ≤ s + g.hi := by
  cases g <;> simp only [Dg.shift, Dg.hi] <;> omega

theorem OkL.shiftB {c k s : ℕ} {r : List Dg} (h : OkL (okB c) k r) :
    OkL (okB (s + c)) (s + k) (r.map (Dg.shift s)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact ⟨by rw [okB_shift]; exact (h y hy).1, (hi_shift s y).trans (by have := (h y hy).2; omega)⟩

theorem OkL.shiftD {top : Bool} {c k s : ℕ} {r : List Dg} (h : OkL (okD top c) k r) :
    OkL (okD top (s + c)) (s + k) (r.map (Dg.shift s)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact ⟨by rw [okD_shift]; exact (h y hy).1, (hi_shift s y).trans (by have := (h y hy).2; omega)⟩

/-! ### Moving words up -/

/-- A letter `s` wires up. -/
def Lt.upBy (s : ℕ) : Lt → Lt
  | .om => .om
  | .H i => .H (s + i)
  | .S i => .S (s + i)
  | .CZ i => .CZ (s + i)

theorem upN_eq : ∀ (s : ℕ) (l : List Lt), upN s l = l.map (Lt.upBy s)
  | 0, l => by
    simp only [upN]
    conv_lhs => rw [← List.map_id l]
    congr 1; funext a; cases a <;> simp [Lt.upBy]
  | s + 1, l => by
    simp only [upN, upN_eq s l, List.map_map]
    congr 1; funext a; cases a <;> simp [Lt.upBy, Lt.up] <;> omega

@[simp] theorem upN_append (s : ℕ) (l l' : List Lt) : upN s (l ++ l') = upN s l ++ upN s l' := by
  simp [upN_eq]

theorem upN_nil (s : ℕ) : upN s [] = [] := by simp [upN_eq]

theorem upN_cons (s : ℕ) (a : Lt) (l : List Lt) : upN s (a :: l) = a.upBy s :: upN s l := by
  simp [upN_eq]

theorem upN_word (s : ℕ) (g : Dg) : upN s g.word = (g.shift s).word := by
  cases g <;> simp [upN_eq, Dg.word, Dg.shift, Lt.upBy, bX]

theorem upN_dw (s : ℕ) (l : List Dg) : upN s (dw l) = dw (l.map (Dg.shift s)) := by
  induction l with
  | nil => simp [upN_eq]
  | cons g l ih => simp [upN_word, ih]

theorem upN_bA (s i a : ℕ) : upN s (bA i a) = bA i (s + a) := by
  unfold bA; split <;> simp [upN_eq, Lt.upBy]

theorem upN_bB (s j a : ℕ) : upN s (bB j a) = bB j (s + a) := by
  unfold bB; split <;> simp [upN_eq, Lt.upBy] <;> omega

theorem upN_bC (s k a : ℕ) : upN s (bC k a) = bC k (s + a) := by
  unfold bC; split <;> simp [upN_eq, Lt.upBy]

theorem upN_bD (s l a : ℕ) : upN s (bD l a) = bD l (s + a) := by
  unfold bD; split <;> simp [upN_eq, Lt.upBy] <;> omega

theorem upN_bE (s h a : ℕ) : upN s (bE h a) = bE h (s + a) := by
  unfold bE; split <;> simp [upN_eq, Lt.upBy]

theorem upN_bX (s a : ℕ) : upN s (bX a) = bX (s + a) := by
  simp [upN_eq, Lt.upBy, bX]

/-! ### Equations in place -/

namespace Holds

variable {k : ℕ} {l r l' r' : List Lt}

theorem app (h : Holds k l r) (h' : Holds k l' r') : Holds k (l ++ l') (r ++ r') := by
  have a := congr [] l' h
  have b := congr r [] h'
  simp only [List.nil_append, List.append_nil] at a b
  exact a.trans b

/-- An equation of a table, `s` wires up, inside `n` wires. -/
theorem «at» (h : Holds k l r) (s n : ℕ) (hn : s + k ≤ n) : Holds n (upN s l) (upN s r) :=
  (holds_upN h s).mono (by omega)

/-- Words whose letters are pairwise on disjoint wires commute. -/
theorem swap : ∀ {u v : List Lt}, (∀ a ∈ u, ∀ b ∈ v, a.disj b = true) →
    Holds 0 (u ++ v) (v ++ u)
  | [], v, _ => by simpa using refl 0 v
  | a :: u, v, h => by
    have h1 : Holds 0 (a :: (u ++ v)) (a :: (v ++ u)) := by
      simpa using congr [a] [] (swap (fun x hx y hy => h x (by simp [hx]) y hy))
    have h2 : Holds 0 (a :: (v ++ u)) (v ++ [a] ++ u) := by
      have := congr [] u (allDisj_move (a := a) (u := v)
        (by simpa [allDisj] using fun y hy => h a (by simp) y hy))
      simpa using this
    simpa using h1.trans h2

end Holds

/-! ### Letters below and above a wire -/

/-- All letters of `u` lie below the wire `c` (or are scalars). -/
def Below (c : ℕ) (u : List Lt) : Prop := ∀ a ∈ u, a.hi ≤ c

/-- All letters of `u` lie on or above the wire `c` (and are not scalars). -/
def Above (c : ℕ) (u : List Lt) : Prop := ∀ a ∈ u, a ≠ .om ∧ c ≤ a.lo

theorem disj_of_below {c : ℕ} {u v : List Lt} (hu : Below c u) (hv : Above c v) :
    ∀ a ∈ u, ∀ b ∈ v, a.disj b = true := by
  intro a ha b hb
  have h1 := hu a ha
  have h2 := (hv b hb).2
  simp only [Lt.disj, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl (Or.inr (by omega))

theorem disj_of_above {c : ℕ} {u v : List Lt} (hu : Above c u) (hv : Below c v) :
    ∀ a ∈ u, ∀ b ∈ v, a.disj b = true := by
  intro a ha b hb
  have h1 := (hu a ha).2
  have h2 := hv b hb
  simp only [Lt.disj, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (by omega)

/-- A word below `c` commutes past a word above `c`. -/
theorem Holds.pass_up {c n : ℕ} {u v : List Lt} (hu : Below c u) (hv : Above c v) :
    Holds n (u ++ v) (v ++ u) :=
  (Holds.swap (disj_of_below hu hv)).mono (Nat.zero_le _)

/-- A word above `c` commutes past a word below `c`. -/
theorem Holds.pass_down {c n : ℕ} {u v : List Lt} (hu : Above c u) (hv : Below c v) :
    Holds n (u ++ v) (v ++ u) :=
  (Holds.swap (disj_of_above hu hv)).mono (Nat.zero_le _)

/-- The scalar commutes with everything. -/
theorem Holds.om_pass {n : ℕ} (u : List Lt) : Holds n (Lt.om :: u) (u ++ [Lt.om]) :=
  (allDisj_move (by simp [allDisj, Lt.disj])).mono (Nat.zero_le _)

theorem Below.append {c : ℕ} {u v : List Lt} (hu : Below c u) (hv : Below c v) :
    Below c (u ++ v) := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  exacts [hu a h, hv a h]

theorem Above.append {c : ℕ} {u v : List Lt} (hu : Above c u) (hv : Above c v) :
    Above c (u ++ v) := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  exacts [hu a h, hv a h]

theorem Below.mono {c c' : ℕ} {u : List Lt} (h : Below c u) (hc : c ≤ c') : Below c' u :=
  fun a ha => (h a ha).trans hc

theorem Above.mono {c c' : ℕ} {u : List Lt} (h : Above c u) (hc : c' ≤ c) : Above c' u :=
  fun a ha => ⟨(h a ha).1, hc.trans (h a ha).2⟩

/-! ### Where the boxes are -/

/-- The letters of a box lie on its wires. -/
def Within (lo hi : ℕ) (u : List Lt) : Prop := Above lo u ∧ Below hi u

theorem Within.append {a b : ℕ} {u v : List Lt} (hu : Within a b u) (hv : Within a b v) :
    Within a b (u ++ v) := ⟨hu.1.append hv.1, hu.2.append hv.2⟩

theorem Within.mono {a b a' b' : ℕ} {u : List Lt} (h : Within a b u) (ha : a' ≤ a)
    (hb : b ≤ b') : Within a' b' u := ⟨h.1.mono ha, h.2.mono hb⟩

theorem within_bA (i a : ℕ) : Within a (a + 1) (bA i a) := by
  unfold bA; split <;> simp [Within, Above, Below, Lt.lo, Lt.hi]

theorem within_bB (j a : ℕ) : Within a (a + 2) (bB j a) := by
  unfold bB; split <;> simp [Within, Above, Below, Lt.lo, Lt.hi]

theorem within_bC (k a : ℕ) : Within a (a + 1) (bC k a) := by
  unfold bC; split <;> simp [Within, Above, Below, Lt.lo, Lt.hi]

theorem within_bD (l a : ℕ) : Within a (a + 2) (bD l a) := by
  unfold bD; split <;> simp [Within, Above, Below, Lt.lo, Lt.hi]

theorem within_bE (h a : ℕ) : Within a (a + 1) (bE h a) := by
  unfold bE; split <;> simp [Within, Above, Below, Lt.lo, Lt.hi]

/-- The letters of a dirty gate. -/
theorem below_word (g : Dg) : Below g.hi g.word := by
  cases g <;> simp [Below, Dg.word, Dg.hi, Lt.hi, bX]

theorem above_word {g : Dg} (hg : g ≠ .om) {c : ℕ} (hc : ∀ w, (g = .H w ∨ g = .S w ∨
    g = .X w ∨ g = .CZ w) → c ≤ w) : Above c g.word := by
  cases g with
  | om => exact absurd rfl hg
  | H w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, this]
  | S w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, this]
  | X w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, bX, this]
  | CZ w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, this]

/-! ### The ladders -/

/-- `B_{j₁}` on the wires `c, c + 1`, …, `B_{j_r}` on `c + r - 1, c + r`,
then `C_k` on the wire `c + r`. -/
def BC : ℕ → List (Fin 4) → Fin 2 → List Lt
  | c, [], k => bC (k.val + 1) c
  | c, j :: js, k => bB (j.val + 1) c ++ BC (c + 1) js k

/-- `D_{ℓ₁}` on the wires `r - 1, r`, …, `D_{ℓ_r}` on `0, 1`, then `E_h` on
the wire `0` (`r` the length). -/
def DC : List (Fin 4) → Fin 4 → List Lt
  | [], h => bE (h.val + 1) 0
  | l :: ls, h => bD (l.val + 1) ls.length ++ DC ls h

theorem within_BC : ∀ (c : ℕ) (js : List (Fin 4)) (k : Fin 2),
    Within c (c + js.length + 1) (BC c js k)
  | c, [], k => by simpa [BC] using within_bC (k.val + 1) c
  | c, j :: js, k => by
    simp only [BC, List.length_cons]
    exact ((within_bB _ c).mono le_rfl (by omega)).append
      ((within_BC (c + 1) js k).mono (by omega) (by omega))

theorem within_DC : ∀ (ls : List (Fin 4)) (h : Fin 4), Within 0 (ls.length + 1) (DC ls h)
  | [], h => by simpa [DC] using within_bE (h.val + 1) 0
  | l :: ls, h => by
    simp only [DC, List.length_cons]
    exact ((within_bD _ _).mono (Nat.zero_le _) le_rfl).append
      ((within_DC ls h).mono le_rfl (by omega))

theorem upN_BC (s : ℕ) : ∀ (c : ℕ) (js : List (Fin 4)) (k : Fin 2),
    upN s (BC c js k) = BC (s + c) js k
  | c, [], k => by simp [BC, upN_bC]
  | c, j :: js, k => by
    simp only [BC, upN_append, upN_bB, upN_BC s (c + 1) js k]
    rfl

end QCert.SelingerClifford
