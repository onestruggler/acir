/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A proof engine for equations between concrete circuits of a fragment

Translation of `Examples/Independence/Engine.agda`, with the canonical forms
modulo commutation of `Presentation/Tactics/Words.agda`'s `Commuting` that it
uses.

An equation is a pair of letter lists with a derivation (`Eqn`, the Agda's
record with constructor `eqn` and fields `lhs⁼`, `rhs⁼`, `prf`).  A
derivation of a new equation is a list of steps run on the letters:
`Step.perm ys` replaces the current list by `ys`, which must be the same word
up to the commutation of letters on disjoint wires (the canonical forms
`canon` agree), and `Step.rw i e` rewrites the occurrence of `e.lhs` at
position `i` to `e.rhs`.  `run` executes the steps and `run_sound` turns a
successful run into a derivation.  Equations are transformed by `symE` and
`liftE` (one wire up; the Agda's `sym⁼`, `lift⁼`), and built from equations
between words by `eqnW` (the Agda's `eqnʷ`).  Lists are in the order of
words: diagram order, the head first.

The engine needs a decidable equality on gates and a code for their order,
and that the fragment has one scalar (`Gates`, the Agda's module
parameters).

**Deviations from the Agda.**

* The Agda closes `derive l r steps refl`, the type checker running the
  steps.  Here the run is one Boolean (`check`) with a soundness lemma, and a
  derivation is `derive l r steps (by decide +kernel)`.
* The kernel decides closed propositions only, while the Agda's derivations
  are at symbolic widths (`Eqn (₂₊ n)`).  So a derivation is checked at the
  width it is drawn on and put on the bottom wires of any wider circuit by
  `Eqn.pad` (`CircuitProp.pad`, the Agda's `ax-at` for equations): the
  Agda's `x⁼ : Eqn (₂₊ n)` is `Eqn.pad n (derive …)` at width `2`.
* Two letters commute when they act on disjoint wires
  (`QCert.Minimality.Gen.apart`, with its soundness
  `QCert.Minimality.comm_apart`).  The Agda's `comm?` decides the same for
  letters other than scalars; it lets a scalar shifted up commute only with
  what the unshifted scalar does, while `apart` lets it commute with
  everything (both are sound).  The four-bit development has no scalars.
* Words are `FreeMonoid`, which is `List`: the Agda's `⟪_⟫` (a list as a
  word) is `FreeMonoid.ofList`, and `⟪++⟫`, `⟪≈⟫`, `⟪map↥⟫` hold by `rfl`.
-/
import QCert.XCXCCX4bit.Lib.IProp
import QCert.Minimality.Comm

namespace QCert.XCXCCX4bit.Engine

open QCert QCert.Circuit CircuitProp IndepProp

/-- The engine's parameters (the Agda's module parameters `gate-eq`,
`gate-eq-sound`, `code`, `one`). -/
class Gates (Gate : ℕ → Type) where
  gateEq : ∀ {k : ℕ}, Gate k → Gate k → Bool
  gateEq_sound : ∀ {k : ℕ} (a b : Gate k), gateEq a b = true → a = b
  code : ∀ {k : ℕ}, Gate k → ℕ
  one : ∀ h h' : Gate 0, h = h'

variable {Gate : ℕ → Type} [Gates Gate]

/-! ## Equality and order of letters -/

def eqP : {k : ℕ} → PGate Gate k → PGate Gate k → Bool
  | _, .gate a, .gate b => Gates.gateEq a b
  | _, .gate _, .swap => false
  | _, .swap, .gate _ => false
  | _, .swap, .swap => true

theorem eqP_sound : ∀ {k : ℕ} (a b : PGate Gate k), eqP a b = true → a = b
  | _, .gate a, .gate b, h => congrArg PGate.gate (Gates.gateEq_sound a b h)
  | _, .swap, .swap, _ => rfl
  | _, .gate _, .swap, h => by simp [eqP] at h
  | _, .swap, .gate _, h => by simp [eqP] at h

/-- Letters compared constructor by constructor. -/
def eqG : {n : ℕ} → Gen (PGate Gate) n → Gen (PGate Gate) n → Bool
  | _, .gate0 a, .gate0 b => eqP a b
  | _, .gate0 _, .gate1 _ => false
  | _, .gate0 _, .gate2 _ => false
  | _, .gate0 _, .gate3 _ => false
  | _, .gate0 _, .up _ => false
  | _, .gate1 _, .gate0 _ => false
  | _, .gate1 a, .gate1 b => eqP a b
  | _, .gate1 _, .gate2 _ => false
  | _, .gate1 _, .gate3 _ => false
  | _, .gate1 _, .up _ => false
  | _, .gate2 _, .gate0 _ => false
  | _, .gate2 _, .gate1 _ => false
  | _, .gate2 a, .gate2 b => eqP a b
  | _, .gate2 _, .gate3 _ => false
  | _, .gate2 _, .up _ => false
  | _, .gate3 _, .gate0 _ => false
  | _, .gate3 _, .gate1 _ => false
  | _, .gate3 _, .gate2 _ => false
  | _, .gate3 a, .gate3 b => eqP a b
  | _, .gate3 _, .up _ => false
  | _, .up _, .gate0 _ => false
  | _, .up _, .gate1 _ => false
  | _, .up _, .gate2 _ => false
  | _, .up _, .gate3 _ => false
  | _, .up x, .up y => eqG x y

theorem eqG_sound : ∀ {n : ℕ} (x y : Gen (PGate Gate) n), eqG x y = true → x = y
  | _, .gate0 a, .gate0 b, h => congrArg Gen.gate0 (eqP_sound a b h)
  | _, .gate1 a, .gate1 b, h => congrArg Gen.gate1 (eqP_sound a b h)
  | _, .gate2 a, .gate2 b, h => congrArg Gen.gate2 (eqP_sound a b h)
  | _, .gate3 a, .gate3 b, h => congrArg Gen.gate3 (eqP_sound a b h)
  | _, .up x, .up y, h => congrArg Gen.up (eqG_sound x y h)
  | _, .gate0 _, .gate1 _, h => by simp [eqG] at h
  | _, .gate0 _, .gate2 _, h => by simp [eqG] at h
  | _, .gate0 _, .gate3 _, h => by simp [eqG] at h
  | _, .gate0 _, .up _, h => by simp [eqG] at h
  | _, .gate1 _, .gate0 _, h => by simp [eqG] at h
  | _, .gate1 _, .gate2 _, h => by simp [eqG] at h
  | _, .gate1 _, .gate3 _, h => by simp [eqG] at h
  | _, .gate1 _, .up _, h => by simp [eqG] at h
  | _, .gate2 _, .gate0 _, h => by simp [eqG] at h
  | _, .gate2 _, .gate1 _, h => by simp [eqG] at h
  | _, .gate2 _, .gate3 _, h => by simp [eqG] at h
  | _, .gate2 _, .up _, h => by simp [eqG] at h
  | _, .gate3 _, .gate0 _, h => by simp [eqG] at h
  | _, .gate3 _, .gate1 _, h => by simp [eqG] at h
  | _, .gate3 _, .gate2 _, h => by simp [eqG] at h
  | _, .gate3 _, .up _, h => by simp [eqG] at h
  | _, .up _, .gate0 _, h => by simp [eqG] at h
  | _, .up _, .gate1 _, h => by simp [eqG] at h
  | _, .up _, .gate2 _, h => by simp [eqG] at h
  | _, .up _, .gate3 _, h => by simp [eqG] at h

/-- Letter lists compared letter by letter. -/
def eqL {n : ℕ} : List (Gen (PGate Gate) n) → List (Gen (PGate Gate) n) → Bool
  | [], [] => true
  | x :: xs, y :: ys => eqG x y && eqL xs ys
  | _, _ => false

theorem eqL_sound {n : ℕ} : ∀ (xs ys : List (Gen (PGate Gate) n)), eqL xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [eqG_sound x y h.1, eqL_sound xs ys h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

/-- The order of a gate in the canonical forms: the swap first. -/
def codeP : {k : ℕ} → PGate Gate k → ℕ
  | _, .gate a => Gates.code a + 1
  | _, .swap => 0

/-- The order of the canonical forms: by height, then by arity, then by the
code of the gate. -/
def less : {n : ℕ} → Gen (PGate Gate) n → Gen (PGate Gate) n → Bool
  | _, .up x, .up y => less x y
  | _, .up _, _ => false
  | _, .gate0 _, .up _ => true
  | _, .gate1 _, .up _ => true
  | _, .gate2 _, .up _ => true
  | _, .gate3 _, .up _ => true
  | _, .gate0 a, .gate0 b => Nat.blt (codeP a) (codeP b)
  | _, .gate0 _, _ => true
  | _, .gate1 _, .gate0 _ => false
  | _, .gate1 a, .gate1 b => Nat.blt (codeP a) (codeP b)
  | _, .gate1 _, .gate2 _ => true
  | _, .gate1 _, .gate3 _ => true
  | _, .gate2 a, .gate2 b => Nat.blt (codeP a) (codeP b)
  | _, .gate2 _, .gate3 _ => true
  | _, .gate2 _, _ => false
  | _, .gate3 a, .gate3 b => Nat.blt (codeP a) (codeP b)
  | _, .gate3 _, _ => false

/-- Letters on disjoint wires commute: the decision. -/
abbrev comm {n : ℕ} (x y : Gen (PGate Gate) n) : Bool := Minimality.Gen.apart x y

/-- The one scalar, at `PGate`. -/
theorem one' : ∀ h h' : PGate Gate 0, h = h'
  | .gate a, .gate b => congrArg PGate.gate (Gates.one a b)

/-! ## Canonical forms modulo commutation

The canonical form of a word is the least equivalent one in the reverse
lexicographic order (`Commuting.comm-canonical`): the canonical form of
`x :: xs` inserts `x` into that of `xs`. -/

section Canon

variable {X : Type} (comm : X → X → Bool) (less : X → X → Bool)

/-- `split ys x zs`: `(reverse zs₁ ++ ys, zs₂)` for `zs = zs₁ ++ zs₂`, `zs₁` the
longest prefix of letters commuting with `x`. -/
def split : List X → X → List X → List X × List X
  | ys, _, [] => (ys, [])
  | ys, x, z :: zs => bif comm x z then split (z :: ys) x zs else (ys, z :: zs)

/-- `unsplit ys x zs`: `reverse ys' ++ zs`, `ys'` the least word obtained by
inserting `x` in `ys`. -/
def unsplit : List X → X → List X → List X
  | [], x, zs => x :: zs
  | y :: ys, x, zs => bif less x y then unsplit ys x (y :: zs) else List.reverseAux (y :: ys) (x :: zs)

/-- The canonical form of `x :: xs`, given that of `xs`. -/
def insert (x : X) (xs : List X) : List X :=
  unsplit less (split comm [] x xs).1 x (split comm [] x xs).2

/-- The canonical form of a word modulo commutation (the Agda's
`comm-canonical`). -/
def canon : List X → List X
  | [] => []
  | x :: xs => insert comm less x (canon xs)

variable {Γ : WRel X}
  (hc : ∀ x y, comm x y = true →
    Derivable Γ (FreeMonoid.of x * FreeMonoid.of y) (FreeMonoid.of y * FreeMonoid.of x))
include hc

omit hc in
theorem split1 : ∀ (ys : List X) (x : X) (zs : List X),
    List.reverseAux ys zs =
      List.reverseAux (split comm ys x zs).1 (split comm ys x zs).2
  | _, _, [] => rfl
  | ys, x, z :: zs => by
    unfold split
    cases comm x z
    · rfl
    · exact split1 (z :: ys) x zs

omit hc in
theorem split2 : ∀ (ys : List X) (x : X) (zs : List X), (∀ y ∈ ys, comm x y = true) →
    ∀ y ∈ (split comm ys x zs).1, comm x y = true
  | ys, _, [], h => h
  | ys, x, z :: zs, h => by
    unfold split
    cases hz : comm x z
    · exact h
    · exact split2 (z :: ys) x zs (by
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hz
        · exact h y hy)

omit hc in
theorem reverseAux_cong (ys : List X) {zs zs' : List X}
    (h : Derivable Γ (FreeMonoid.ofList zs) (FreeMonoid.ofList zs')) :
    Derivable Γ (FreeMonoid.ofList (List.reverseAux ys zs))
      (FreeMonoid.ofList (List.reverseAux ys zs')) := by
  rw [List.reverseAux_eq, List.reverseAux_eq, FreeMonoid.ofList_append, FreeMonoid.ofList_append]
  exact (Derivable.refl _).mul h

theorem reverse_append : ∀ (ys : List X) (x : X) (zs : List X), (∀ y ∈ ys, comm x y = true) →
    Derivable Γ (FreeMonoid.ofList (x :: List.reverseAux ys zs))
      (FreeMonoid.ofList (List.reverseAux ys (x :: zs)))
  | [], _, _, _ => Derivable.refl _
  | y :: ys, x, zs, h => by
    have ih := reverse_append ys x (y :: zs) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have claim : Derivable Γ (FreeMonoid.ofList (x :: y :: zs)) (FreeMonoid.ofList (y :: x :: zs)) := by
      rw [FreeMonoid.ofList_cons, FreeMonoid.ofList_cons, FreeMonoid.ofList_cons,
        FreeMonoid.ofList_cons, ← mul_assoc, ← mul_assoc]
      exact (hc x y (h y (List.mem_cons_self))).mul (Derivable.refl _)
    exact ih.trans (reverseAux_cong ys claim)

theorem unsplit_sound : ∀ (ys : List X) (x : X) (zs : List X), (∀ y ∈ ys, comm x y = true) →
    Derivable Γ (FreeMonoid.ofList (x :: List.reverseAux ys zs))
      (FreeMonoid.ofList (unsplit less ys x zs))
  | [], _, _, _ => Derivable.refl _
  | y :: ys, x, zs, h => by
    unfold unsplit
    cases less x y
    · exact reverse_append comm hc (y :: ys) x zs h
    · exact unsplit_sound ys x (y :: zs) (fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem insert_sound (x : X) (xs : List X) :
    Derivable Γ (FreeMonoid.ofList (x :: xs)) (FreeMonoid.ofList (insert comm less x xs)) := by
  have e := split1 comm [] x xs
  have h := split2 comm [] x xs (by simp)
  unfold insert
  rw [show x :: xs = x :: List.reverseAux [] xs from rfl, e]
  exact unsplit_sound comm less hc _ x _ h

theorem canon_sound : ∀ xs : List X,
    Derivable Γ (FreeMonoid.ofList xs) (FreeMonoid.ofList (canon comm less xs))
  | [] => Derivable.refl _
  | x :: xs => by
    have ih := canon_sound xs
    refine Derivable.trans ?_ (insert_sound comm less hc x (canon comm less xs))
    rw [FreeMonoid.ofList_cons, FreeMonoid.ofList_cons]
    exact (Derivable.refl _).mul ih

end Canon

/-! ## Equations -/

section Kit

variable (SRel : CRel (PGate Gate))

/-- An equation between letter lists, with its derivation. -/
structure Eqn (n : ℕ) where
  eqn ::
  lhs : List (Gen (PGate Gate) n)
  rhs : List (Gen (PGate Gate) n)
  prf : Der SRel n (FreeMonoid.ofList lhs) (FreeMonoid.ofList rhs)

variable {SRel}

/-- Both sides exchanged (the Agda's `sym⁼`). -/
def symE {n : ℕ} (e : Eqn SRel n) : Eqn SRel n := ⟨e.rhs, e.lhs, e.prf.symm⟩

/-- An equation between words, read as one between letter lists: the lists
are the words' letters (the Agda's `eqnʷ`; the words being lists here, both
side conditions are `rfl`). -/
def eqnW {n : ℕ} {w v : Circuit (PGate Gate) n} (l r : List (Gen (PGate Gate) n))
    (p : Der SRel n w v) (e₁ : FreeMonoid.ofList l = w) (e₂ : v = FreeMonoid.ofList r) :
    Eqn SRel n :=
  ⟨l, r, by rw [e₁, ← e₂]; exact p⟩

/-- One wire up.  The scalar stays the scalar of the wider circuit (`ω↑=ω`),
so that lifted equations still match the letters of a word. -/
def liftGen {n : ℕ} : Gen (PGate Gate) n → Gen (PGate Gate) (n + 1)
  | .gate0 h => .gate0 h
  | g => g.up

omit [Gates Gate] in
theorem map_liftGen {n : ℕ} (xs : List (Gen (PGate Gate) n)) :
    Der SRel (n + 1) (FreeMonoid.ofList (xs.map liftGen)) (shift (FreeMonoid.ofList xs)) := by
  induction xs with
  | nil => exact Derivable.refl _
  | cons x xs ih =>
    rw [List.map_cons, FreeMonoid.ofList_cons, FreeMonoid.ofList_cons, map_mul, shift_of]
    refine Derivable.mul ?_ ih
    cases x with
    | gate0 h => exact (Derivable.of (Lift.scalar h)).symm
    | gate1 _ => exact Derivable.refl _
    | gate2 _ => exact Derivable.refl _
    | gate3 _ => exact Derivable.refl _
    | up _ => exact Derivable.refl _

/-- The equation one wire up (the Agda's `lift⁼`). -/
def liftE {n : ℕ} (e : Eqn SRel n) : Eqn SRel (n + 1) :=
  ⟨e.lhs.map liftGen, e.rhs.map liftGen,
    (map_liftGen e.lhs).trans ((lemma_cong_up e.prf).trans (map_liftGen e.rhs).symm)⟩

/-- An equation of `k ≤ 4` wires on the bottom wires of a circuit of `n + k`
wires (`CircuitProp.pad`). -/
def Eqn.pad {k : ℕ} (n : ℕ) (e : Eqn SRel k) (hk : k ≤ 4 := by decide) : Eqn SRel (n + k) :=
  ⟨e.lhs.map (Gen.pad n), e.rhs.map (Gen.pad n), CircuitProp.pad hk e.prf n⟩

/-! ## Running a derivation -/

/-- A step: `perm ys`, the same word up to commutations, or `rw i e`. -/
inductive Step (SRel : CRel (PGate Gate)) (n : ℕ) where
  | perm : List (Gen (PGate Gate) n) → Step SRel n
  | rw : ℕ → Eqn SRel n → Step SRel n

/-- The occurrence of `e.lhs` at position `i` replaced by `e.rhs`. -/
def rewriteAt {n : ℕ} (i : ℕ) (e : Eqn SRel n) (xs : List (Gen (PGate Gate) n)) :
    List (Gen (PGate Gate) n) :=
  xs.take i ++ (e.rhs ++ (xs.drop i).drop e.lhs.length)

/-- Whether `e.lhs` occurs at position `i`. -/
def matchesAt {n : ℕ} (i : ℕ) (e : Eqn SRel n) (xs : List (Gen (PGate Gate) n)) : Bool :=
  eqL ((xs.drop i).take e.lhs.length) e.lhs

/-- The canonical form of a letter list modulo commutation. -/
abbrev canonG {n : ℕ} (xs : List (Gen (PGate Gate) n)) : List (Gen (PGate Gate) n) :=
  canon comm less xs

/-- Run the steps. -/
def run {n : ℕ} : List (Step SRel n) → List (Gen (PGate Gate) n) → Option (List (Gen (PGate Gate) n))
  | [], xs => some xs
  | .perm ys :: ss, xs => bif eqL (canonG xs) (canonG ys) then run ss ys else none
  | .rw i e :: ss, xs => bif matchesAt i e xs then run ss (rewriteAt i e xs) else none

/-- The steps turn `l` into `r`. -/
def check {n : ℕ} (ss : List (Step SRel n)) (l r : List (Gen (PGate Gate) n)) : Bool :=
  match run ss l with
  | some y => eqL y r
  | none => false

theorem comm_sound {n : ℕ} (x y : Gen (PGate Gate) n) (h : comm x y = true) :
    Der SRel n (FreeMonoid.of x * FreeMonoid.of y) (FreeMonoid.of y * FreeMonoid.of x) :=
  Minimality.comm_apart one' x y h

theorem perm_sound {n : ℕ} (xs ys : List (Gen (PGate Gate) n)) (h : canonG xs = canonG ys) :
    Der SRel n (FreeMonoid.ofList xs) (FreeMonoid.ofList ys) := by
  have a := canon_sound comm less (Γ := VRel SRel n) comm_sound xs
  have b := canon_sound comm less (Γ := VRel SRel n) comm_sound ys
  have h' : canon comm less xs = canon comm less ys := h
  rw [h'] at a
  exact a.trans b.symm

theorem rw_sound {n : ℕ} (i : ℕ) (e : Eqn SRel n) (xs : List (Gen (PGate Gate) n))
    (h : matchesAt i e xs = true) :
    Der SRel n (FreeMonoid.ofList xs) (FreeMonoid.ofList (rewriteAt i e xs)) := by
  have hm : (xs.drop i).take e.lhs.length = e.lhs := eqL_sound _ _ h
  have hx : xs = xs.take i ++ (e.lhs ++ (xs.drop i).drop e.lhs.length) := by
    conv_lhs => rw [← List.take_append_drop i xs, ← List.take_append_drop e.lhs.length (xs.drop i)]
    rw [hm]
  rw [rewriteAt]
  conv_lhs => rw [hx]
  simp only [FreeMonoid.ofList_append]
  exact (Derivable.refl _).mul (e.prf.mul (Derivable.refl _))

theorem run_sound {n : ℕ} : ∀ (ss : List (Step SRel n)) (xs ys : List (Gen (PGate Gate) n)),
    run ss xs = some ys → Der SRel n (FreeMonoid.ofList xs) (FreeMonoid.ofList ys)
  | [], xs, ys, h => by
    simp only [run, Option.some.injEq] at h; subst h; exact Derivable.refl _
  | .perm zs :: ss, xs, ys, h => by
    simp only [run] at h
    cases hc : eqL (canonG xs) (canonG zs)
    · rw [hc] at h; simp at h
    · rw [hc] at h
      exact (perm_sound xs zs (eqL_sound _ _ hc)).trans (run_sound ss zs ys h)
  | .rw i e :: ss, xs, ys, h => by
    simp only [run] at h
    cases hm : matchesAt i e xs
    · rw [hm] at h; simp at h
    · rw [hm] at h
      exact (rw_sound i e xs hm).trans (run_sound ss _ ys h)

theorem check_sound {n : ℕ} {ss : List (Step SRel n)} {l r : List (Gen (PGate Gate) n)}
    (h : check ss l r = true) : Der SRel n (FreeMonoid.ofList l) (FreeMonoid.ofList r) := by
  unfold check at h
  split at h
  · rename_i y hy
    rw [← eqL_sound _ _ h]; exact run_sound ss l y hy
  · simp at h

/-- A derivation: an equation from the steps that turn `l` into `r`. -/
def derive {n : ℕ} (l r : List (Gen (PGate Gate) n)) (ss : List (Step SRel n))
    (h : check ss l r = true) : Eqn SRel n :=
  ⟨l, r, check_sound h⟩

end Kit

end QCert.XCXCCX4bit.Engine
