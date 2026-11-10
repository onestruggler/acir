/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of {X, CX, CCX} circuits: permutations of bit vectors

Translation of `Semantics.agda`.  A circuit on `n` wires denotes a function
on bit vectors of length `n`, wire 0 first, read in diagram order:
`sem (w * v)` applies `sem w` first (`sem_mul`).  Functions are compared
pointwise (`f ≐ g`), and on a fixed width the comparison is decided by
running over all `2ⁿ` vectors (`eqF`, `eqF_sound`).  Every relation of the
theory, and every swap and structural rule, is sound (`sound`): the seven
rules by evaluation at the width they are drawn on, the rest at every width
by computation on the first bits.

A state of the paper, `x₁x₂…xₙ` with `x₁` the most significant bit, is the
vector whose entry on wire `w` is `x_{n−w}`: the paper's wire 1 is our top
wire.

Representation.  A state is `Bits n`, an inductive vector of Booleans (the
Agda's `Vec Bool n`, with `a ∷ x` its cons, wire 0 at the head), so that
gates are defined, and states taken apart, by pattern matching as in the
Agda, and the kernel decides equations by structural evaluation.  The
Agda's `⟦_⟧` and `⟦_⟧ᵍ` are `sem` and `semG` (`⟦ ⟧` is Mathlib's quotient
notation), `⟦↑⟧` is `sem_up`, `_⨾_` is `f ⨾ g` (diagram-order composition),
`≐-refl` is `feq_refl`, and so on.
-/
import QCert.XCXCCX4bit.Syntactics

namespace QCert.XCXCCX4bit

open QCert QCert.Circuit CircuitProp IndepProp

/-! ## Functions on bit vectors -/

/-- Bit vectors of length `n`, wire 0 first (the Agda's `Vec Bool n`). -/
inductive Bits : ℕ → Type
  /-- The empty vector. -/
  | nil : Bits 0
  /-- A bit on wire 0 below a vector on the wires above it. -/
  | cons {n : ℕ} (a : Bool) (x : Bits n) : Bits (n + 1)
  deriving DecidableEq

@[inherit_doc] scoped infixr:67 " ∷ " => Bits.cons

/-! ### Vector operations on states

`Data.Vec`'s operations that the development applies to states, for `Bits`:
`head`, `tail`, `lookup` (`Bits.get`), `x [ t ]%= f` (`Bits.update`) and
`_++_` (`Bits.append`, written `x ++ y`; `x ++ (b ∷ .nil)` puts `b` on a new
top wire, the state of `Circuit.pad 1 w`, and has width `1 + n`, as `pad`'s
circuits). -/

namespace Bits

def head {n : ℕ} : Bits (n + 1) → Bool
  | a ∷ _ => a

def tail {n : ℕ} : Bits (n + 1) → Bits n
  | _ ∷ x => x

/-- The bit on wire `i` (`Data.Vec`'s `lookup`). -/
def get : {n : ℕ} → Bits n → Fin n → Bool
  | _, a ∷ _, ⟨0, _⟩ => a
  | _, _ ∷ x, ⟨i + 1, h⟩ => get x ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- The bit on wire `i` changed by `f` (`Data.Vec`'s `x [ i ]%= f`). -/
def update : {n : ℕ} → Bits n → Fin n → (Bool → Bool) → Bits n
  | _, a ∷ x, ⟨0, _⟩, f => f a ∷ x
  | _, a ∷ x, ⟨i + 1, h⟩, f => a ∷ update x ⟨i, Nat.lt_of_succ_lt_succ h⟩ f

/-- `x` below `y`: the wires of `y` on top of those of `x`. -/
def append : {m k : ℕ} → Bits m → Bits k → Bits (k + m)
  | _, _, .nil, y => y
  | _, _, a ∷ x, y => a ∷ append x y

instance {m k : ℕ} : HAppend (Bits m) (Bits k) (Bits (k + m)) := ⟨append⟩

theorem cons_append {m k : ℕ} (a : Bool) (x : Bits m) (y : Bits k) :
    (a ∷ x) ++ y = a ∷ (x ++ y) := rfl

theorem nil_append {k : ℕ} (y : Bits k) : (Bits.nil ++ y : Bits (k + 0)) = y := rfl

/-- `++-injectiveˡ`. -/
theorem append_inj_left : ∀ {m k : ℕ} (x x' : Bits m) (y y' : Bits k),
    x ++ y = x' ++ y' → x = x'
  | _, _, .nil, .nil, _, _, _ => rfl
  | _, _, a ∷ x, a' ∷ x', y, y', h => by
    rw [cons_append, cons_append] at h
    injection h with _ h₁ h₂
    rw [h₁, append_inj_left x x' y y' h₂]

end Bits

/-- Functions on bit vectors. -/
abbrev Fun (n : ℕ) : Type := Bits n → Bits n

variable {n : ℕ}

/-- Pointwise equality of functions (the Agda's `_≐_`). -/
def Feq (f g : Fun n) : Prop := ∀ x, f x = g x

@[inherit_doc] scoped infix:50 " ≐ " => Feq

theorem feq_refl {f : Fun n} : f ≐ f := fun _ => rfl

theorem feq_sym {f g : Fun n} (e : f ≐ g) : g ≐ f := fun x => (e x).symm

theorem feq_trans {f g h : Fun n} (e : f ≐ g) (e' : g ≐ h) : f ≐ h := fun x => (e x).trans (e' x)

/-- Composition in diagram order: `f` first, then `g`. -/
def seqF (f g : Fun n) : Fun n := fun x => g (f x)

@[inherit_doc] scoped infixr:90 " ⨾ " => seqF

theorem seq_cong {f f' g g' : Fun n} (e : f ≐ f') (e' : g ≐ g') : (f ⨾ g) ≐ (f' ⨾ g') :=
  fun x => (congrArg g (e x)).trans (e' (f' x))

/-- A function on the wires above the bottom one. -/
def up (f : Fun n) : Fun (n + 1)
  | a ∷ x => a ∷ f x

theorem up_cong {f g : Fun n} (e : f ≐ g) : up f ≐ up g
  | a ∷ x => congrArg (a ∷ ·) (e x)

/-! ## Deciding pointwise equality -/

/-- Every vector satisfies `p`, checked on all `2ⁿ` of them. -/
def allB : (n : ℕ) → (Bits n → Bool) → Bool
  | 0, p => p .nil
  | n + 1, p => allB n (fun x => p (false ∷ x)) && allB n (fun x => p (true ∷ x))

theorem allB_sound : ∀ (n : ℕ) (p : Bits n → Bool), allB n p = true → ∀ x, p x = true
  | 0, _, h, .nil => h
  | n + 1, p, h, false ∷ x => by
    simp only [allB, Bool.and_eq_true] at h
    exact allB_sound n (fun x => p (false ∷ x)) h.1 x
  | n + 1, p, h, true ∷ x => by
    simp only [allB, Bool.and_eq_true] at h
    exact allB_sound n (fun x => p (true ∷ x)) h.2 x

def eqB : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem eqB_sound : ∀ a b : Bool, eqB a b = true → a = b
  | true, true, _ => rfl
  | false, false, _ => rfl
  | true, false, h => by simp [eqB] at h
  | false, true, h => by simp [eqB] at h

def eqV : {n : ℕ} → Bits n → Bits n → Bool
  | _, .nil, .nil => true
  | _, a ∷ x, b ∷ y => eqB a b && eqV x y

theorem eqV_sound : ∀ {n : ℕ} (x y : Bits n), eqV x y = true → x = y
  | _, .nil, .nil, _ => rfl
  | _, a ∷ x, b ∷ y, h => by
    simp only [eqV, Bool.and_eq_true] at h
    rw [eqB_sound a b h.1, eqV_sound x y h.2]

def eqF (n : ℕ) (f g : Fun n) : Bool := allB n (fun x => eqV (f x) (g x))

theorem eqF_sound (n : ℕ) (f g : Fun n) (h : eqF n f g = true) : f ≐ g :=
  fun x => eqV_sound (f x) (g x) (allB_sound n _ h x)

/-! ## The gates -/

/-- The function of a generator. -/
def semG : {n : ℕ} → Gn n → Fun n
  | _, .gate0 (.gate g), _ => nomatch g
  | _, .gate1 (.gate .X_gate), a ∷ x => (!a) ∷ x
  | _, .gate2 (.gate .CX_gate), a ∷ b ∷ x => (a ^^ b) ∷ b ∷ x
  | _, .gate2 .swap, a ∷ b ∷ x => b ∷ a ∷ x
  | _, .gate3 (.gate .CCX_gate), a ∷ b ∷ c ∷ x => (a ^^ (b && c)) ∷ b ∷ c ∷ x
  | _, .up g, a ∷ x => a ∷ semG g x

/-- The function of a letter list, its letters in diagram order. -/
def semL : List (Gn n) → Fun n
  | [], x => x
  | g :: w, x => semL w (semG g x)

/-- The function of a circuit, its letters in diagram order (the Agda's
`⟦_⟧`). -/
def sem (w : Circ n) : Fun n := semL (FreeMonoid.toList w)

theorem semL_append (l l' : List (Gn n)) (x : Bits n) :
    semL (l ++ l') x = semL l' (semL l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons g l ih => exact ih (semG g x)

/-- `⟦ w • v ⟧ = ⟦ w ⟧ ⨾ ⟦ v ⟧`. -/
theorem sem_mul (w v : Circ n) (x : Bits n) : sem (w * v) x = sem v (sem w x) :=
  semL_append _ _ x

theorem sem_one (x : Bits n) : sem (1 : Circ n) x = x := rfl

theorem sem_of (g : Gn n) (x : Bits n) : sem (FreeMonoid.of g) x = semG g x := rfl

/-- Two circuits on `n` wires with the same function, decided. -/
def same (n : ℕ) (w v : Circ n) : Bool := eqF n (sem w) (sem v)

theorem same_sound (w v : Circ n) (h : same n w v = true) : sem w ≐ sem v :=
  eqF_sound n (sem w) (sem v) h

/-! ## Shifting -/

/-- The Agda's `⟦↑⟧`. -/
theorem sem_up (w : Circ n) : sem (shift w) ≐ up (sem w) := by
  intro x
  cases x with
  | cons a x =>
    show semL ((FreeMonoid.toList w).map Gen.up) (a ∷ x) = a ∷ semL (FreeMonoid.toList w) x
    generalize FreeMonoid.toList w = l
    induction l generalizing x with
    | nil => rfl
    | cons g l ih => exact ih (semG g x)

/-! ## Soundness -/

/-- The seven rules, at the widths they are drawn on. -/
private theorem srel_sound : ∀ {n : ℕ} {w v : Circ n}, SRel n w v → sem w ≐ sem v
  | _, _, _, .r1 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r2 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r3 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r4 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r5 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r6 => same_sound _ _ (by decide +kernel)
  | _, _, _, .r7 => same_sound _ _ (by decide +kernel)

/-- The swap rules, at every width. -/
private theorem sym_sound : ∀ {n : ℕ} {w v : Circ n}, Sym n w v → sem w ≐ sem v
  | _, _, _, .σ_inv, _ ∷ _ ∷ _ => rfl
  | _, _, _, .σ_nat₁ (.gate .X_gate), _ ∷ _ ∷ _ => rfl
  | _, _, _, .σ_nat₂ (.gate .CX_gate), _ ∷ _ ∷ _ ∷ _ => rfl
  | _, _, _, .σ_nat₂ .swap, _ ∷ _ ∷ _ ∷ _ => rfl
  | _, _, _, .σ_nat₃ (.gate .CCX_gate), _ ∷ _ ∷ _ ∷ _ ∷ _ => rfl

/-- The structural rules. -/
private theorem ax_sound : ∀ {n : ℕ} {w v : Circ n}, VRel SRel n w v → sem w ≐ sem v
  | _, _, _, .rule (.srel r), x => srel_sound r x
  | _, _, _, .rule (.σrel s), x => sym_sound s x
  | _, _, _, .shift a, x =>
    feq_trans (sem_up _) (feq_trans (up_cong (ax_sound a)) (feq_sym (sem_up _))) x
  | _, _, _, .comm1 (.gate .X_gate) _, _ ∷ _ => rfl
  | _, _, _, .comm2 (.gate .CX_gate) _, _ ∷ _ ∷ _ => rfl
  | _, _, _, .comm2 .swap _, _ ∷ _ ∷ _ => rfl
  | _, _, _, .comm3 (.gate .CCX_gate) _, _ ∷ _ ∷ _ ∷ _ => rfl
  | _, _, _, .scalar (.gate g), _ => nomatch g

/-- The theory, with the swap and structural rules, is sound. -/
theorem sound {w v : Circ n} (d : n ⊢ w ≈ v) : sem w ≐ sem v := by
  let c : Con (Circ n) :=
    { r := fun w v => sem w ≐ sem v
      iseqv := ⟨fun _ => feq_refl, feq_sym, feq_trans⟩
      mul' := fun {w w' v v'} e e' x => by
        rw [sem_mul, sem_mul, e x, e' (sem w' x)] }
  have : conGen (VRel SRel n) ≤ c := Con.conGen_le fun _ _ r => ax_sound r
  exact this d

end QCert.XCXCCX4bit
