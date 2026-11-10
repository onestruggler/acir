/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of the circuits over X, CX, CCX and Ex: functions on bit vectors

Translation of `Semantics.agda`.  A circuit on `n` wires denotes a function
on bit vectors of length `n`, the bit of wire 0 first, read in diagram
order: `sem (w * v)` applies `sem w` first (`sem_mul`).  Functions are
compared pointwise (`f ≐ g`), and on a fixed width the comparison is decided
by running over all `2ⁿ` vectors (`eqF`, `eqF_sound`).  Every rule of the
theory is sound (`sound`).  The rules of `Syntactics` live on four wires and
are decided there on the sixteen states; those with indices, Lafont's
relations between the cycles `Ω i`, are decided for all their indices at
once, by one Boolean that runs over the indices within the bounds.  The laws
of the swap and the structural rules hold at every width, by computation on
the first bits.

Representation.  A state is `Bits n`, an inductive vector of Booleans (the
Agda's `Vec Bool n`, with `a ∷ x` its cons, wire 0 at the head), so that
gates are defined, and states taken apart, by pattern matching as in the
Agda.  The Agda's `⟦_⟧` and `⟦_⟧ᵍ` are `sem` and `semG` (`⟦ ⟧` is Mathlib's
quotient notation), `⟦↑⟧` is `sem_up`, `_⨾_` is `f ⨾ g` (diagram-order
composition), `≐-refl` is `feq_refl`, and so on.

**Deviations from the Agda.**  A circuit is a list of letters here, so `sem`
runs down the list (`semL`), where the Agda's follows the brackets of the
word; `sound` is the inclusion of the generated congruence in the kernel of
`sem` (`con_sound`), where the Agda's is an induction on derivations, and
the structural rules are sound over any relation (`lift_sound`, which
`Theory` reuses).  The Agda's `refl` on a Boolean is `decide +kernel`, and
for the kernel's sake the four-wire rules are decided on the states as
numbers (`same₄`, with `same₄_sound`; see "Deciding on numbered states").
-/
import QCert.Alt16RevCir.Syntactics

namespace QCert.Alt16RevCir

open QCert QCert.Circuit CircuitProp

/-! ## Functions on bit vectors -/

/-- Bit vectors of length `n`, wire 0 first (the Agda's `Vec Bool n`). -/
inductive Bits : ℕ → Type
  /-- The empty vector. -/
  | nil : Bits 0
  /-- A bit on wire 0 below a vector on the wires above it. -/
  | cons {n : ℕ} (a : Bool) (x : Bits n) : Bits (n + 1)
  deriving DecidableEq

@[inherit_doc] scoped infixr:67 " ∷ " => Bits.cons

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

/-- The function of a generator (the Agda's `⟦_⟧ᵍ`). -/
def semG : {n : ℕ} → Gn n → Fun n
  | _, .gate0 g, _ => nomatch g
  | _, .gate1 .X_gate, a ∷ x => (!a) ∷ x
  | _, .gate2 .CX_gate, a ∷ b ∷ x => (a ^^ b) ∷ b ∷ x
  | _, .gate2 .Ex_gate, a ∷ b ∷ x => b ∷ a ∷ x
  | _, .gate3 .CCX_gate, a ∷ b ∷ c ∷ x => (a ^^ (b && c)) ∷ b ∷ c ∷ x
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

/-! ## Deciding on numbered states

The kernel pays several hundred reductions for one application of `semG` to
a state: both `Gn n` and `Bits n` are indexed families.  So a comparison of
two long circuits is decided on the states as numbers instead: a letter is
read once as an operation on numbers (`Op`), a word is run on the `2ⁿ`
numbers (`runOps`), and `sameOps_sound` carries the result to `sem`, given
that each letter's operation is its function (checked once per letter, on
`Bits`).  The Agda decides `same` itself everywhere. -/

/-- The number of a state: bit `k` is the bit of wire `k`. -/
def num : {n : ℕ} → Bits n → ℕ
  | _, .nil => 0
  | _, a ∷ x => (bif a then 1 else 0) + 2 * num x

theorem num_inj : ∀ {n : ℕ} (x y : Bits n), num x = num y → x = y
  | _, .nil, .nil, _ => rfl
  | _, a ∷ x, b ∷ y, h => by
    have h' : (bif a then 1 else 0) + 2 * num x = (bif b then 1 else 0) + 2 * num y := h
    have e : a = b ∧ num x = num y := by
      cases a <;> cases b <;> simp only [cond_true, cond_false] at h' <;>
        refine ⟨?_, ?_⟩ <;> first | rfl | omega
    rw [e.1, num_inj x y e.2]

theorem num_lt : ∀ {n : ℕ} (x : Bits n), num x < 2 ^ n
  | _, .nil => Nat.one_pos
  | n + 1, a ∷ x => by
    have h := num_lt x
    have e : num (a ∷ x) = (bif a then 1 else 0) + 2 * num x := rfl
    rw [e, Nat.pow_succ]
    cases a <;> simp only [cond_true, cond_false] <;> omega

/-- A gate as an operation on numbers: the bits `t` are flipped when the
bits `c` are `v₁` or `v₂`. -/
structure Op where
  c : ℕ
  v₁ : ℕ
  v₂ : ℕ
  t : ℕ

def Op.app (o : Op) (x : ℕ) : ℕ :=
  bif Nat.beq (Nat.land x o.c) o.v₁ || Nat.beq (Nat.land x o.c) o.v₂ then Nat.xor x o.t else x

def runOps : List Op → ℕ → ℕ
  | [], x => x
  | o :: os, x => runOps os (o.app x)

/-- Every `x < m` satisfies `p`. -/
def allLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | m + 1, p => p m && allLt m p

theorem allLt_sound : ∀ (m : ℕ) (p : ℕ → Bool), allLt m p = true → ∀ x, x < m → p x = true
  | 0, _, _, _, l => absurd l (Nat.not_lt_zero _)
  | m + 1, p, h, x, l => by
    simp only [allLt, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 l with l' | rfl
    · exact allLt_sound m p h.2 x l'
    · exact h.1

/-- Two lists of operations agree on the numbers below `m`. -/
def sameOps (m : ℕ) (l r : List Op) : Bool := allLt m fun x => Nat.beq (runOps l x) (runOps r x)

section Ops

variable {α : Type} (gen : α → Gn n) (op : α → Op)
  (h : ∀ a x, num (semG (gen a) x) = (op a).app (num x))
include h

theorem runOps_sem : ∀ (l : List α) (x : Bits n),
    num (semL (l.map gen) x) = runOps (l.map op) (num x)
  | [], _ => rfl
  | a :: l, x => by
    show num (semL (l.map gen) (semG (gen a) x)) = runOps (l.map op) ((op a).app (num x))
    rw [runOps_sem l, h]

/-- Letters named by `α`, each with its operation: two words whose
operations agree on the numbers of the states have the same function. -/
theorem sameOps_sound (l r : List α) (e : sameOps (2 ^ n) (l.map op) (r.map op) = true) :
    semL (l.map gen) ≐ semL (r.map gen) := fun x =>
  num_inj _ _ (by
    rw [runOps_sem gen op h, runOps_sem gen op h]
    exact Nat.eq_of_beq_eq_true (allLt_sound _ _ e (num x) (num_lt x)))

end Ops

/-- The operation of a generator `d` wires up. -/
def opAt : {n : ℕ} → Gn n → ℕ → Op
  | _, .gate0 g, _ => nomatch g
  | _, .gate1 .X_gate, d => ⟨0, 0, 0, Nat.pow 2 d⟩
  | _, .gate2 .CX_gate, d => ⟨Nat.pow 2 (d + 1), Nat.pow 2 (d + 1), Nat.pow 2 (d + 1), Nat.pow 2 d⟩
  | _, .gate2 .Ex_gate, d =>
    ⟨Nat.mul 3 (Nat.pow 2 d), Nat.pow 2 d, Nat.pow 2 (d + 1), Nat.mul 3 (Nat.pow 2 d)⟩
  | _, .gate3 .CCX_gate, d =>
    ⟨Nat.mul 6 (Nat.pow 2 d), Nat.mul 6 (Nat.pow 2 d), Nat.mul 6 (Nat.pow 2 d), Nat.pow 2 d⟩
  | _, .up g, d => opAt g (d + 1)

private theorem opAt_ok (g : Gn 4)
    (h : allB 4 (fun x => Nat.beq (num (semG g x)) ((opAt g 0).app (num x))) = true)
    (x : Bits 4) : num (semG g x) = (opAt g 0).app (num x) :=
  Nat.eq_of_beq_eq_true (allB_sound 4 _ h x)

/-- On four wires the operation of each of the twelve generators is its
function. -/
theorem opAt_sem : ∀ (g : Gn 4) (x : Bits 4), num (semG g x) = (opAt g 0).app (num x)
  | .gate0 g => nomatch g
  | .gate1 .X_gate => opAt_ok _ (by decide +kernel)
  | .gate2 .CX_gate => opAt_ok _ (by decide +kernel)
  | .gate2 .Ex_gate => opAt_ok _ (by decide +kernel)
  | .gate3 .CCX_gate => opAt_ok _ (by decide +kernel)
  | .up (.gate0 g) => nomatch g
  | .up (.gate1 .X_gate) => opAt_ok _ (by decide +kernel)
  | .up (.gate2 .CX_gate) => opAt_ok _ (by decide +kernel)
  | .up (.gate2 .Ex_gate) => opAt_ok _ (by decide +kernel)
  | .up (.gate3 .CCX_gate) => opAt_ok _ (by decide +kernel)
  | .up (.up (.gate0 g)) => nomatch g
  | .up (.up (.gate1 .X_gate)) => opAt_ok _ (by decide +kernel)
  | .up (.up (.gate2 .CX_gate)) => opAt_ok _ (by decide +kernel)
  | .up (.up (.gate2 .Ex_gate)) => opAt_ok _ (by decide +kernel)
  | .up (.up (.up (.gate0 g))) => nomatch g
  | .up (.up (.up (.gate1 .X_gate))) => opAt_ok _ (by decide +kernel)
  | .up (.up (.up (.up (.gate0 g)))) => nomatch g

/-- Two four-wire circuits with the same function, decided on the sixteen
numbers. -/
def same₄ (w v : Circ 4) : Bool :=
  sameOps 16 ((FreeMonoid.toList w).map (opAt · 0)) ((FreeMonoid.toList v).map (opAt · 0))

theorem same₄_sound (w v : Circ 4) (h : same₄ w v = true) : sem w ≐ sem v := by
  have e := sameOps_sound id (opAt · 0) opAt_sem (FreeMonoid.toList w) (FreeMonoid.toList v) h
  simpa only [List.map_id] using e

/-! ## Deciding a rule for all its indices -/

/-- Every `i ≤ n` satisfies `p` (the Agda's `all≤`). -/
def allLe : ℕ → (ℕ → Bool) → Bool
  | 0, p => p 0
  | n + 1, p => p 0 && allLe n (fun i => p (i + 1))

theorem allLe_sound : ∀ (n : ℕ) (p : ℕ → Bool), allLe n p = true → ∀ i, i ≤ n → p i = true
  | 0, _, h, 0, _ => h
  | n + 1, p, h, 0, _ => by
    simp only [allLe, Bool.and_eq_true] at h
    exact h.1
  | n + 1, p, h, i + 1, l => by
    simp only [allLe, Bool.and_eq_true] at h
    exact allLe_sound n (fun i => p (i + 1)) h.2 i (Nat.le_of_succ_le_succ l)

/-- A condition under a guard (the Agda's `_⇒_`). -/
def imp : Bool → Bool → Bool
  | true, b => b
  | false, _ => true

theorem imp_sound : ∀ {a b : Bool}, a = true → imp a b = true → b = true
  | true, _, _, h => h

/-! ## Soundness -/

/-! The rules of `Syntactics`, on the sixteen states.  The two sides of
Lafont's relations at position `i`, and of the commutation of the cycles at
`i` and `j`, are named so that the Boolean decided and the one used are the
same term. -/

private def orderB (i : ℕ) : Bool := same₄ (Ω i * Ω i * Ω i) 1

private def nearB (i : ℕ) : Bool := same₄ (Ω i * Ω (i + 1) * Ω i) (Ω (i + 1) * Ω (i + 1))

private def farB (i : ℕ) : Bool :=
  same₄ (Ω i * Ω (i + 2) * Ω i) (Ω (i + 2) * Ω i * Ω (i + 1))

private def apartB (i j : ℕ) : Bool := imp (Nat.ble (i + 3) j) (same₄ (Ω j * Ω i) (Ω i * Ω j))

private theorem order_all : allLe 13 orderB = true := by decide +kernel

private theorem near_all : allLe 12 nearB = true := by decide +kernel

private theorem far_all : allLe 11 farB = true := by decide +kernel

private theorem apart_all : allLe 10 (fun i => allLe 13 (apartB i)) = true := by decide +kernel

private theorem srel_sound : ∀ {n : ℕ} {w v : Circ n}, SRel n w v → sem w ≐ sem v
  | _, _, _, .order i l => same₄_sound _ _ (allLe_sound 13 orderB order_all i l)
  | _, _, _, .near i l => same₄_sound _ _ (allLe_sound 12 nearB near_all i l)
  | _, _, _, .far i l => same₄_sound _ _ (allLe_sound 11 farB far_all i l)
  | _, _, _, .apart i j l l' =>
    same₄_sound _ _ (imp_sound (Nat.ble_eq_true_of_le l)
      (allLe_sound 13 (apartB i)
        (allLe_sound 10 (fun i => allLe 13 (apartB i)) apart_all i (by omega)) j l'))
  | _, _, _, .gate_X => same₄_sound _ _ (by decide +kernel)
  | _, _, _, .gate_CX => same₄_sound _ _ (by decide +kernel)
  | _, _, _, .gate_CCX => same₄_sound _ _ (by decide +kernel)
  | _, _, _, .gate_Ex₀ => same₄_sound _ _ (by decide +kernel)
  | _, _, _, .gate_Ex₁ => same₄_sound _ _ (by decide +kernel)
  | _, _, _, .gate_Ex₂ => same₄_sound _ _ (by decide +kernel)

/-- The laws of the swap, at every width. -/
theorem sym_sound : ∀ {n : ℕ} {w v : Circ n}, Sym n w v → sem w ≐ sem v
  | _, _, _, .σ_inv, _ ∷ _ ∷ _ => rfl
  | _, _, _, .σ_nat₁ .X_gate, _ ∷ _ ∷ _ => rfl
  | _, _, _, .σ_nat₂ .CX_gate, _ ∷ _ ∷ _ ∷ _ => rfl
  | _, _, _, .σ_nat₂ .Ex_gate, _ ∷ _ ∷ _ ∷ _ => rfl
  | _, _, _, .σ_nat₃ .CCX_gate, _ ∷ _ ∷ _ ∷ _ ∷ _ => rfl

/-- The structural rules, over any relation whose own rules are sound
(`ax_sound` is the instance for `Syntactics`' relation, and `Theory` uses it
for the rules (1)–(7)). -/
theorem lift_sound {R : CRel Gate}
    (hR : ∀ {n : ℕ} {w v : Circ n}, R n w v → sem w ≐ sem v) :
    ∀ {n : ℕ} {w v : Circ n}, Lift R n w v → sem w ≐ sem v
  | _, _, _, .rule r, x => hR r x
  | _, _, _, .shift a, x =>
    feq_trans (sem_up _) (feq_trans (up_cong (lift_sound hR a)) (feq_sym (sem_up _))) x
  | _, _, _, .comm1 .X_gate _, _ ∷ _ => rfl
  | _, _, _, .comm2 .CX_gate _, _ ∷ _ ∷ _ => rfl
  | _, _, _, .comm2 .Ex_gate _, _ ∷ _ ∷ _ => rfl
  | _, _, _, .comm3 .CCX_gate _, _ ∷ _ ∷ _ ∷ _ => rfl
  | _, _, _, .scalar g, _ => nomatch g

/-- Every rule: those of `Syntactics`, the laws of the swap and the
structural rules. -/
theorem ax_sound {w v : Circ n} (a : VRel SRel n w v) : sem w ≐ sem v :=
  lift_sound (fun r => match r with
    | .srel r => srel_sound r
    | .σrel s => sym_sound s) a

/-- A congruence generated by sound rules is sound. -/
theorem con_sound {Γ : WRel (Gn n)} (h : ∀ {w v : Circ n}, Γ w v → sem w ≐ sem v)
    {w v : Circ n} (d : Derivable Γ w v) : sem w ≐ sem v := by
  let c : Con (Circ n) :=
    { r := fun w v => sem w ≐ sem v
      iseqv := ⟨fun _ => feq_refl, feq_sym, feq_trans⟩
      mul' := fun {w w' v v'} e e' x => by
        rw [sem_mul, sem_mul, e x, e' (sem w' x)] }
  have : conGen Γ ≤ c := Con.conGen_le fun _ _ r => h r
  exact this d

/-- The theory is sound. -/
theorem sound {w v : Circ n} (d : n ⊢ w ≈ v) : sem w ≐ sem v :=
  con_sound ax_sound d

end QCert.Alt16RevCir
