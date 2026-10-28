/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: dirty gates and their labels

The material for Section 5.1 (Definition 5.3, Lemma 5.4, Proposition 5.7),
adapted from `SelingerClifford/Dirty.lean`.  A *dirty gate* (`Dg`) is one of
`-1`, `H`, `Z`, `X = HZH`, `CZ` or `CXZ` (`XZ` on the upper wire, controlled
by the lower one) at an absolute position; dirty gates travel through a
normal form from left to right.

The labels of Definition 5.3 say which dirty gates may stand where.  In a
`B`-ladder whose current wire (label ②) is `c`, of type `t`, `okB t c`
allows: `H` on another wire, or on `c` if it is double; `Z` anywhere; `X`
on `c`; `CZ` whose lower wire is not `c` and, if its upper wire is `c`, a
simple `c`; `CXZ` on the wires `c - 1, c` with `c` double.  (Definition 5.3
asks for a *double* top wire for both `CZ` and `CXZ`; the relations of
Figure 5 and the rules that produce these gates have `CZ` with a simple and
`CXZ` with a double top wire, which is what is used here.)  An `X` or `CXZ`
elsewhere is written as its letters `H Z H`, `H CZ H CZ`, each allowed where
it stands.  `okD top c` holds inside a `D`-ladder whose current wire is `c`
(label ④, or ③ before the first `D` when `top`), `okN` after the ladders,
and `okA` before a normal form (all wires labelled ①).

`Holds.at` moves an equation of `Tables` into place, and `Holds.swap`
commutes words on disjoint wires.
-/
import QCert.RealStabilizer.Unique

namespace QCert.RealStabilizer

/-! ### Dirty gates -/

/-- A dirty gate at an absolute position (`CZ w`, `CXZ w` on the wires
`w, w + 1`). -/
inductive Dg
  | neg
  | H (w : ℕ)
  | Z (w : ℕ)
  | X (w : ℕ)
  | CZ (w : ℕ)
  | CXZ (w : ℕ)
  deriving DecidableEq, Repr

namespace Dg

/-- The letters of a dirty gate. -/
def word : Dg → List Lt
  | neg => [.neg]
  | H w => [.H w]
  | Z w => [.Z w]
  | X w => bX w
  | CZ w => [.CZ w]
  | CXZ w => [.H (w + 1), .CZ w, .H (w + 1), .CZ w]

/-- The dirty gate `s` wires up. -/
def shift (s : ℕ) : Dg → Dg
  | neg => neg
  | H w => H (s + w)
  | Z w => Z (s + w)
  | X w => X (s + w)
  | CZ w => CZ (s + w)
  | CXZ w => CXZ (s + w)

/-- One more than the highest wire (`0` for the scalar). -/
def hi : Dg → ℕ
  | neg => 0
  | H w => w + 1
  | Z w => w + 1
  | X w => w + 1
  | CZ w => w + 2
  | CXZ w => w + 2

end Dg

theorem bCXZ_succ (w : ℕ) : bCXZ (w + 1) w = (Dg.CXZ w).word := by
  simp [bCXZ, Dg.word]

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

/-- Allowed inside a `B`-ladder whose current wire (label ②) is `c`, of
type `t`. -/
def okB (t : Ty) (c : ℕ) : Dg → Bool
  | .neg => true
  | .H w => w != c || t
  | .Z _ => true
  | .X w => w == c
  | .CZ w => w != c && (w + 1 != c || !t)
  | .CXZ w => w + 1 == c && t

/-- Allowed inside a `D`-ladder whose current wire is `c` (label ④, or ③
before the first `D` when `top`): `H` on the other wires, `Z` anywhere, no
`X` or `CXZ`, `CZ` whose lower wire is not `c` and, below the first `D`
only, whose upper wire may be `c`. -/
def okD (top : Bool) (c : ℕ) : Dg → Bool
  | .neg => true
  | .H w => w != c
  | .Z _ => true
  | .X _ => false
  | .CZ w => w != c && (top || w + 1 != c)
  | .CXZ _ => false

/-- Allowed after the ladders: not on the bottom wire, and no `X` or
`CXZ`. -/
def okN : Dg → Bool
  | .neg => true
  | .H w => w != 0
  | .Z w => w != 0
  | .X _ => false
  | .CZ w => w != 0
  | .CXZ _ => false

/-- Allowed before a normal form (all wires labelled ①): no `X` or `CXZ`. -/
def okA : Dg → Bool
  | .X _ => false
  | .CXZ _ => false
  | _ => true

theorem okB_shift (t : Ty) (s c : ℕ) (g : Dg) : okB t (s + c) (g.shift s) = okB t c g := by
  cases g <;> cases t <;> simp only [okB, Dg.shift] <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem okD_shift (top : Bool) (s c : ℕ) (g : Dg) :
    okD top (s + c) (g.shift s) = okD top c g := by
  cases g <;> cases top <;> simp only [okD, Dg.shift] <;> rw [Bool.eq_iff_iff] <;> simp
  intro _
  constructor <;> (intro h h'; apply h; omega)

theorem hi_shift (s : ℕ) (g : Dg) : (g.shift s).hi ≤ s + g.hi := by
  cases g <;> simp only [Dg.shift, Dg.hi] <;> omega

theorem OkL.shiftB {t : Ty} {c k s : ℕ} {r : List Dg} (h : OkL (okB t c) k r) :
    OkL (okB t (s + c)) (s + k) (r.map (Dg.shift s)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact ⟨by rw [okB_shift]; exact (h y hy).1, (hi_shift s y).trans (by have := (h y hy).2; omega)⟩

theorem OkL.shiftD {top : Bool} {c k s : ℕ} {r : List Dg} (h : OkL (okD top c) k r) :
    OkL (okD top (s + c)) (s + k) (r.map (Dg.shift s)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  exact ⟨by rw [okD_shift]; exact (h y hy).1, (hi_shift s y).trans (by have := (h y hy).2; omega)⟩

/-! ### Moving words up -/

@[simp] theorem upN_append (s : ℕ) (l l' : List Lt) : upN s (l ++ l') = upN s l ++ upN s l' := by
  simp [upN_eq]

theorem upN_nil (s : ℕ) : upN s [] = [] := by simp [upN_eq]

theorem upN_cons (s : ℕ) (a : Lt) (l : List Lt) : upN s (a :: l) = a.upBy s :: upN s l := by
  simp [upN_eq]

theorem upN_bX (s a : ℕ) : upN s (bX a) = bX (s + a) := by
  simp [upN_eq, Lt.upBy, bX]

theorem upN_bE (s h a : ℕ) : upN s (bE h a) = bE h (s + a) := by
  unfold bE; split <;> simp [upN_eq, Lt.upBy]

theorem upN_word (s : ℕ) (g : Dg) : upN s g.word = (g.shift s).word := by
  cases g <;> simp [upN_eq, Dg.word, Dg.shift, Lt.upBy, bX]
  omega

theorem upN_dw (s : ℕ) (l : List Dg) : upN s (dw l) = dw (l.map (Dg.shift s)) := by
  induction l with
  | nil => simp [upN_eq]
  | cons g l ih => simp [upN_word, ih]

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
def Above (c : ℕ) (u : List Lt) : Prop := ∀ a ∈ u, a ≠ .neg ∧ c ≤ a.lo

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

theorem above_word {g : Dg} (hg : g ≠ .neg) {c : ℕ} (hc : ∀ w, (g = .H w ∨ g = .Z w ∨
    g = .X w ∨ g = .CZ w ∨ g = .CXZ w) → c ≤ w) : Above c g.word := by
  cases g with
  | neg => exact absurd rfl hg
  | H w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, this]
  | Z w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, this]
  | X w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, bX, this]
  | CZ w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, this]
  | CXZ w => have := hc w (by simp); simp [Above, Dg.word, Lt.lo, this]; omega

/-! ### The ladders -/

theorem within_BC : ∀ (t : Ty) (c : ℕ) (js : List (Fin 4)) (k : Fin 2),
    Within c (c + js.length + 1) (BC t c js k)
  | _, c, [], k => by simpa [BC] using within_bC (k.val + 1) c
  | t, c, j :: js, k => by
    simp only [BC, List.length_cons]
    exact ((within_bB _ c).mono le_rfl (by omega)).append
      ((within_BC (tB t j) (c + 1) js k).mono (by omega) (by omega))

theorem within_DC : ∀ (ls : List (Fin 4)) (h : Fin 2), Within 0 (ls.length + 1) (DC ls h)
  | [], h => by simpa [DC] using within_bE (h.val + 1) 0
  | l :: ls, h => by
    simp only [DC, List.length_cons]
    exact ((within_bD _ _).mono (Nat.zero_le _) le_rfl).append
      ((within_DC ls h).mono le_rfl (by omega))

theorem upN_BC (s : ℕ) : ∀ (t : Ty) (c : ℕ) (js : List (Fin 4)) (k : Fin 2),
    upN s (BC t c js k) = BC t (s + c) js k
  | _, c, [], k => by simp [BC, upN_bC]
  | t, c, j :: js, k => by
    simp only [BC, upN_append, upN_bB, upN_BC s (tB t j) (c + 1) js k]
    rfl

end QCert.RealStabilizer
