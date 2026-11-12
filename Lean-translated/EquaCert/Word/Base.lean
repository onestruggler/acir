/-
# Words over a set of generators

Translation of `Word/Base.agda`.

**Representation.**  The Agda's `Word X` is a binary tree (`[_]ʷ`, `ε`,
`_•_`) compared up to the monoid laws by every congruence of the library;
here `Word X` is Mathlib's free monoid `FreeMonoid X` (lists), so the monoid
laws hold on the nose (`mul_assoc`, `one_mul`, `mul_one`) and the Agda's
`assoc`, `left-unit` and `right-unit` steps are rewrites.  The Agda's
`_•_` is `*` (infixl here, infixr in the Agda: Agda's `a • b • c` is
`a * (b * c)`, which is `a * b * c` up to `mul_assoc`), `ε` is `1`, and
`[ x ]ʷ` is `FreeMonoid.of x`, with notation `[x]ʷ`.

The functorial operations are Mathlib's: `wmap f` is `FreeMonoid.map f`,
`(f ʷ)` (the Agda's `wconcatmap`) is `FreeMonoid.lift f`, a monoid
homomorphism.  The folds and the stateful traversals that drive coset
enumeration are defined by recursion on the list.
-/
import Mathlib.Algebra.FreeMonoid.Basic

namespace EquaCert

universe u v w

/-- Words over the generators `X` (the Agda's `Word X`): the free monoid. -/
abbrev Word (X : Type u) := FreeMonoid X

/-- A relation on words, read as a set of axioms (the Agda's `WRel X`). -/
abbrev WRel (X : Type u) := Word X → Word X → Prop

namespace Word

variable {A : Type u} {B : Type v} {C : Type w} {X Y : Type u}

/-- A generator as a word (the Agda's `[ x ]ʷ`). -/
abbrev gen (x : X) : Word X := FreeMonoid.of x

@[inherit_doc gen]
scoped notation "[" x "]ʷ" => FreeMonoid.of x

/-- The empty word (the Agda's `ε`). -/
scoped notation "ε" => (1 : FreeMonoid _)

/-- The functorial map (the Agda's `wmap`). -/
abbrev wmap (f : A → B) : Word A →* Word B := FreeMonoid.map f

/-- The extension of `f : X → Word Y` to words (the Agda's `wconcatmap`,
written `(f ʷ)`). -/
abbrev wconcatmap (f : A → Word B) : Word A →* Word B := FreeMonoid.lift f

@[inherit_doc wconcatmap]
scoped postfix:max "ʷ" => FreeMonoid.lift

/-- Flatten a word of words (the Agda's `wconcat`). -/
abbrev wconcat : Word (Word A) →* Word A := FreeMonoid.lift id

/-- The Agda's right-associative power `w ^ n` is the monoid power. -/
theorem pow_succ_eq (w : Word A) (n : ℕ) : w ^ (n + 1) = w * w ^ n := pow_succ' w n

/-! ## Folds -/

/-- Right fold over a word (the Agda's `wfoldr`). -/
def wfoldr (f : A → B → B) (w : Word A) (b : B) : B := List.foldr f b w.toList

/-- Left fold over a word (the Agda's `wfoldl`). -/
def wfoldl (f : B → A → B) (b : B) (w : Word A) : B := List.foldl f b w.toList

@[simp] theorem wfoldr_one (f : A → B → B) (b : B) : wfoldr f 1 b = b := rfl
@[simp] theorem wfoldr_of (f : A → B → B) (x : A) (b : B) : wfoldr f [x]ʷ b = f x b := rfl
@[simp] theorem wfoldr_mul (f : A → B → B) (w w' : Word A) (b : B) :
    wfoldr f (w * w') b = wfoldr f w (wfoldr f w' b) := by
  simp [wfoldr, FreeMonoid.toList_mul, List.foldr_append]

@[simp] theorem wfoldl_one (f : B → A → B) (b : B) : wfoldl f b 1 = b := rfl
@[simp] theorem wfoldl_of (f : B → A → B) (x : A) (b : B) : wfoldl f b [x]ʷ = f b x := rfl
@[simp] theorem wfoldl_mul (f : B → A → B) (w w' : Word A) (b : B) :
    wfoldl f b (w * w') = wfoldl f (wfoldl f b w) w' := by
  simp [wfoldl, FreeMonoid.toList_mul, List.foldl_append]

/-! ## Stateful traversals (coset enumeration)

A coset action `h : C → Y → Word X × C` consumes one letter of `Y`,
returning an output word and a successor state; `trav h` (the Agda's
`h ᵗ`) extends it to words, threading the state left to right and
concatenating the outputs.  `travR` (the Agda's `h ᵗ'`) is the right-to-left
mirror for left coset actions. -/

/-- Left-to-right stateful traversal on a list of letters. -/
def travList (h : C → Y → Word X × C) : C → List Y → Word X × C
  | c, [] => (1, c)
  | c, y :: ys =>
    let p := h c y
    let q := travList h p.2 ys
    (p.1 * q.1, q.2)

/-- Left-to-right stateful traversal (the Agda's `_ᵗ`). -/
def trav (h : C → Y → Word X × C) (c : C) (w : Word Y) : Word X × C :=
  travList h c w.toList

@[simp] theorem trav_one (h : C → Y → Word X × C) (c : C) : trav h c 1 = (1, c) := rfl

@[simp] theorem trav_of (h : C → Y → Word X × C) (c : C) (y : Y) :
    trav h c [y]ʷ = h c y := by
  simp [trav, travList]

theorem travList_append (h : C → Y → Word X × C) (c : C) (l l' : List Y) :
    travList h c (l ++ l') =
      ((travList h c l).1 * (travList h (travList h c l).2 l').1,
        (travList h (travList h c l).2 l').2) := by
  induction l generalizing c with
  | nil => simp [travList]
  | cons y ys ih => simp [travList, ih, mul_assoc]

@[simp] theorem trav_mul (h : C → Y → Word X × C) (c : C) (w u : Word Y) :
    trav h c (w * u) =
      ((trav h c w).1 * (trav h (trav h c w).2 u).1, (trav h (trav h c w).2 u).2) :=
  travList_append h c w.toList u.toList

/-- Right-to-left stateful traversal on a list (the Agda's `_ᵗ'`). -/
def travRList (h : Y → C → C × Word X) : List Y → C → C × Word X
  | [], c => (c, 1)
  | y :: ys, c =>
    let q := travRList h ys c
    let p := h y q.1
    (p.1, p.2 * q.2)

/-- Right-to-left stateful traversal (the Agda's `_ᵗ'`). -/
def travR (h : Y → C → C × Word X) (w : Word Y) (c : C) : C × Word X :=
  travRList h w.toList c

/-! ## Conjugation helpers -/

/-- Apply a word of group elements, the last first (the Agda's `_ʰ`). -/
abbrev conjH {H N : Type u} (conj : H → N → N) (w : Word H) (n : N) : N := wfoldr conj w n

/-- A conjugation action applied letter by letter to a word of normals
(the Agda's `_ⁿ`). -/
abbrev conjN {H N : Type u} (conj : H → N → N) (h : H) : Word N →* Word N :=
  FreeMonoid.map (conj h)

/-- A word-valued conjugation action applied to a word of normals (the
Agda's `_ⁿ'`). -/
abbrev conjN' {H N : Type u} (conj : H → N → Word N) (h : H) : Word N →* Word N :=
  FreeMonoid.lift (conj h)

/-- A word-valued conjugation action by a word of group elements, the last
first (the Agda's `_ʰ'`). -/
def conjH' {H N : Type u} (conj : H → N → Word N) (hs : Word H) (ns : Word N) : Word N :=
  wfoldr (fun h ns => conjN' conj h ns) hs ns

end Word

end EquaCert
