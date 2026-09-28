------------------------------------------------------------------------
-- Presentations of groups
--
-- Boolean formulas compiled into reversible netlists over NOT, CNOT and
-- Toffoli gates (Amy, QPL 2018, section 4, footnote 2)
--
-- The reduction behind footnote 2 (the plan is in the header of
-- PathSum.Hardness.CNF), at the level of reversible circuits: for every
-- Boolean formula e over n variables, a netlist computing
--
--    |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ e(x)⟩
--
-- on n + s + 2 wires (s = nodes e): the inputs, the ancillas -- a wire
-- that holds the constant 1 while the netlist runs, then one scratch
-- wire per node of e -- and the target, in the paper's order |x⟩|0⟩|t⟩.
--
-- Compiling.  A formula is compiled into Toffoli and CNOT gates
-- (PathSum.Reversible) inside a Frame: the input wires, the constant
-- wire, and the formula's own ancillas, one per node, the node's first.
-- A node writes its value into its ancilla, which starts at 0, after
-- its operands have written theirs into their own:
--
--    x_v       CNOT from the input;
--    1, 0      a CNOT from the constant wire, or nothing;
--    ¬e        CNOTs from e's ancilla and from the constant wire;
--    e₁ ∧ e₂   a Toffoli gate on the operands' ancillas;
--    e₁ ∨ e₂   two CNOTs and a Toffoli gate: e₁ ⊕ e₂ ⊕ e₁e₂ = e₁ ∨ e₂.
--
-- The operands' ancillas are carved out of the node's by the Frame
-- (below, left, right), distinct because the ancilla map is injective.
-- By induction on the formula, from a state where the constant wire
-- reads 1 and the ancillas 0, the netlist leaves the node's value in
-- its ancilla (compile-correct); it writes nothing but its ancillas
-- (compile-frame) and touches only its inputs, the constant wire and
-- its ancillas (compile-within).
--
-- Copying the value out.  Bennett's compute-copy-uncompute
-- (PathSum.Reversible.bennett-work and bennett-out, with the set of
-- wires "not the target"): the compiled netlist, a CNOT from the
-- formula's ancilla into the target, and the compiled netlist
-- reversed (core) restores every wire but the target, on every input,
-- and xors e(x) into the target when the constant wire reads 1 and the
-- scratch wires 0 (core-correct).
--
-- The constant.  The constant wire is an ancilla too, so it enters at
-- 0: a NOT gate sets it before the core and another clears it after.
-- These are the only two NOT gates, and a netlist over {NOT, CNOT,
-- Toffoli} (NCT, run by runᴺ) is what results (oracle).  From every
-- input whose ancillas read 0 it computes |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ e(x)⟩
-- (oracle-correct), so it is the identity on those inputs exactly when
-- e is false everywhere (oracle-identity⇔: if it is not, the input
-- |x⟩|0⟩|0⟩ at a point where e holds comes out with its target
-- flipped).  NOT is not a Toffoli or CNOT gate, and it is needed: a
-- netlist of Toffoli and CNOT gates maps 0 to 0 (run-zero), so none
-- computes |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ e(x)⟩ on the clean inputs, on any
-- wires, for a formula e true at 0 (needs-NOT).
--
-- CNF formulas.  netlist φ is the oracle of cnf φ, on wires φ =
-- n + 2 lits + negs + 2 clauses + 3 wires (wires-exact), and
-- netlist-identity⇔unsat says that it is the identity on the inputs
-- whose ancillas are 0 exactly when φ is unsatisfiable.  Its gates:
-- two NOT gates, 2‖φ‖ Toffoli gates and 6 lits + 4 negs + 3 CNOTs,
-- 8 lits + 4 negs + 2 clauses + 5 in all (netlist-nots,
-- netlist-toffolis, netlist-cnots, netlist-length); since negs ≤ lits,
-- at most n + 3‖φ‖ + 3 wires and 12‖φ‖ + 5 gates (wires-bound,
-- netlist-length-bound): linear in the formula.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Hardness.Netlist where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _∨_; _xor_; if_then_else_)
open import Data.Bool.Properties using (not-involutive; xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.List.Base using (List; []; _∷_; _++_; map; reverse; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (+-identityʳ; m≤m+n; m≤n⇒∃[o]m+o≡n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂; [_,_]′)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)

import Data.Fin.Properties as Fin

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

open import PathSum.Assign using (_[_≔_]; ≔-here; ≔-there; ≔-self; ≔-≔; ≔-cong)
open import PathSum.Hardness.CNF using
  (Assignment; Formula; var; cst; ¬ᶠ_; _∧ᶠ_; _∨ᶠ_; ⟦_⟧ᵇ; ⟦⟧ᵇ-cong; nodes;
   Literal; pos; neg; Clause; CNF; ⟦_⟧ᶠ; literal; clause; cnf; ⟦cnf⟧;
   Unsatisfiable; unsat⇔cnf; negsᶜ; lits; negs; clauses; ‖_‖; negs≤lits;
   nodes-cnf)
open import PathSum.Reversible using
  (Gate; ccx; cx; target; control; Within; ⟪_⟫; ⟪⟫-here; ⟪⟫-there; run;
   run-++; run-cong; run-frame; bennett-work; bennett-out; count;
   count-++; count-reverse; is-ccx; is-cx; toffolis; cnots)

private
  variable
    n N s j : ℕ


------------------------------------------------------------------------
-- Bits

private
  xor-true : ∀ b → b xor true ≡ not b
  xor-true true  = refl
  xor-true false = refl

  or-xor : ∀ a b → (a xor b) xor (a ∧ b) ≡ a ∨ b
  or-xor true  true  = refl
  or-xor true  false = refl
  or-xor false true  = refl
  or-xor false false = refl

  or-value : ∀ {a b c a′ b′} → a ≡ false → b ≡ a′ → c ≡ b′ →
             ((a xor b) xor c) xor (b ∧ c) ≡ a′ ∨ b′
  or-value {a′ = a′} {b′} refl refl refl = or-xor a′ b′

  xor-cancel : ∀ a b → a xor b ≡ a → b ≡ false
  xor-cancel true  true  ()
  xor-cancel true  false _ = refl
  xor-cancel false b     h = h

-- A state that reads b at t and agrees with u elsewhere is u [ t ≔ b ].

≔-ext : (f u : Assignment N) (t : Fin N) (b : Bool) → f t ≡ b →
        (∀ w → w ≢ t → f w ≡ u w) → ∀ w → f w ≡ (u [ t ≔ b ]) w
≔-ext f u t b h₁ h₂ w with w Fin.≟ t
... | yes refl = h₁
... | no w≢t   = h₂ w w≢t

-- Every ancilla reads 0.

Clean : (Fin j → Fin N) → Assignment N → Set
Clean a x = ∀ i → x (a i) ≡ false


------------------------------------------------------------------------
-- Frames

-- Where a compiled formula lives: its n input wires, the wire holding
-- the constant 1, and its own s ancillas, one per node, the node's
-- first -- distinct from one another and from the other wires.

record Frame (n N s : ℕ) : Set where
  field
    inp     : Fin n → Fin N
    one     : Fin N
    anc     : Fin s → Fin N
    anc-inj : ∀ i i′ → anc i ≡ anc i′ → i ≡ i′
    inp≢anc : ∀ v i → inp v ≢ anc i
    one≢anc : ∀ i → one ≢ anc i

open Frame public

anc-≢ : (F : Frame n N s) {i i′ : Fin s} → i ≢ i′ → anc F i ≢ anc F i′
anc-≢ F ne eq = ne (anc-inj F _ _ eq)

private
  ↑ˡ≢↑ʳ : ∀ {m k} (i : Fin m) (i′ : Fin k) → i ↑ˡ k ≢ m ↑ʳ i′
  ↑ˡ≢↑ʳ {m} {k} i i′ eq = absurd
    (trans (sym (Fin.splitAt-↑ˡ m i k))
           (trans (cong (splitAt m) eq) (Fin.splitAt-↑ʳ m k i′)))
    where
    absurd : ∀ {A : Set} → inj₁ i ≡ inj₂ i′ → A
    absurd ()

-- The operands' ancillas, after the node's own: the one operand's
-- (below), or the first operand's and then the second's (left, right).

below : Frame n N (suc s) → Frame n N s
below F = record
  { inp     = inp F
  ; one     = one F
  ; anc     = λ i → anc F (suc i)
  ; anc-inj = λ i i′ eq → Fin.suc-injective (anc-inj F (suc i) (suc i′) eq)
  ; inp≢anc = λ v i → inp≢anc F v (suc i)
  ; one≢anc = λ i → one≢anc F (suc i)
  }

left : ∀ s₁ s₂ → Frame n N (suc (s₁ + s₂)) → Frame n N s₁
left s₁ s₂ F = record
  { inp     = inp F
  ; one     = one F
  ; anc     = λ i → anc F (suc (i ↑ˡ s₂))
  ; anc-inj = λ i i′ eq → Fin.↑ˡ-injective s₂ i i′ (Fin.suc-injective
                (anc-inj F (suc (i ↑ˡ s₂)) (suc (i′ ↑ˡ s₂)) eq))
  ; inp≢anc = λ v i → inp≢anc F v (suc (i ↑ˡ s₂))
  ; one≢anc = λ i → one≢anc F (suc (i ↑ˡ s₂))
  }

right : ∀ s₁ s₂ → Frame n N (suc (s₁ + s₂)) → Frame n N s₂
right s₁ s₂ F = record
  { inp     = inp F
  ; one     = one F
  ; anc     = λ i → anc F (suc (s₁ ↑ʳ i))
  ; anc-inj = λ i i′ eq → Fin.↑ʳ-injective s₁ i i′ (Fin.suc-injective
                (anc-inj F (suc (s₁ ↑ʳ i)) (suc (s₁ ↑ʳ i′)) eq))
  ; inp≢anc = λ v i → inp≢anc F v (suc (s₁ ↑ʳ i))
  ; one≢anc = λ i → one≢anc F (suc (s₁ ↑ʳ i))
  }

-- The operands' ancillas differ from each other and from the node's.

sep₁ : ∀ s₁ s₂ (F : Frame n N (suc (s₁ + s₂))) (i : Fin s₁) →
       anc F (suc (i ↑ˡ s₂)) ≢ anc F zero
sep₁ s₁ s₂ F i = anc-≢ F {suc (i ↑ˡ s₂)} {zero} λ ()

sep₂ : ∀ s₁ s₂ (F : Frame n N (suc (s₁ + s₂))) (i : Fin s₂) →
       anc F (suc (s₁ ↑ʳ i)) ≢ anc F zero
sep₂ s₁ s₂ F i = anc-≢ F {suc (s₁ ↑ʳ i)} {zero} λ ()

sep₁₂ : ∀ s₁ s₂ (F : Frame n N (suc (s₁ + s₂))) (i : Fin s₁) (i′ : Fin s₂) →
        anc F (suc (i ↑ˡ s₂)) ≢ anc F (suc (s₁ ↑ʳ i′))
sep₁₂ s₁ s₂ F i i′ = anc-≢ F {suc (i ↑ˡ s₂)} {suc (s₁ ↑ʳ i′)}
  (λ eq → ↑ˡ≢↑ʳ i i′ (Fin.suc-injective eq))


------------------------------------------------------------------------
-- Compiling a formula

-- The node's ancilla: the first of the formula's.

res : (e : Formula n) → Fin (nodes e)
res (var _)  = zero
res (cst _)  = zero
res (¬ᶠ _)   = zero
res (_ ∧ᶠ _) = zero
res (_ ∨ᶠ _) = zero

out : (e : Formula n) → Frame n N (nodes e) → Fin N
out e F = anc F (res e)

-- The gates of each kind of node, writing into the node's ancilla:
-- a copy of an input, the constant 1, a negation, a conjunction and a
-- disjunction.

copy : Frame n N (suc s) → Fin n → Gate N
copy F v = cx (inp F v) (anc F zero) (inp≢anc F v zero)

set1 : Frame n N (suc s) → Gate N
set1 F = cx (one F) (anc F zero) (one≢anc F zero)

gates¬ : Frame n N (suc s) → Fin s → List (Gate N)
gates¬ F i =
  cx (anc F (suc i)) (anc F zero) (anc-≢ F {suc i} {zero} λ ()) ∷ set1 F ∷ []

gate∧ : ∀ s₁ s₂ → Frame n N (suc (s₁ + s₂)) → Fin s₁ → Fin s₂ → Gate N
gate∧ s₁ s₂ F i i′ =
  ccx (anc F (suc (i ↑ˡ s₂))) (anc F (suc (s₁ ↑ʳ i′))) (anc F zero)
      (sep₁₂ s₁ s₂ F i i′) (sep₁ s₁ s₂ F i) (sep₂ s₁ s₂ F i′)

gates∨ : ∀ s₁ s₂ → Frame n N (suc (s₁ + s₂)) → Fin s₁ → Fin s₂ →
         List (Gate N)
gates∨ s₁ s₂ F i i′ =
  cx (anc F (suc (i ↑ˡ s₂))) (anc F zero) (sep₁ s₁ s₂ F i) ∷
  cx (anc F (suc (s₁ ↑ʳ i′))) (anc F zero) (sep₂ s₁ s₂ F i′) ∷
  gate∧ s₁ s₂ F i i′ ∷ []

-- The operands first, then the node.

compile : (e : Formula n) → Frame n N (nodes e) → List (Gate N)
compile (var v)     F = copy F v ∷ []
compile (cst false) F = []
compile (cst true)  F = set1 F ∷ []
compile (¬ᶠ e)      F = compile e (below F) ++ gates¬ F (res e)
compile (e₁ ∧ᶠ e₂)  F =
  compile e₁ (left (nodes e₁) (nodes e₂) F) ++
  compile e₂ (right (nodes e₁) (nodes e₂) F) ++
  gate∧ (nodes e₁) (nodes e₂) F (res e₁) (res e₂) ∷ []
compile (e₁ ∨ᶠ e₂)  F =
  compile e₁ (left (nodes e₁) (nodes e₂) F) ++
  compile e₂ (right (nodes e₁) (nodes e₂) F) ++
  gates∨ (nodes e₁) (nodes e₂) F (res e₁) (res e₂)


------------------------------------------------------------------------
-- What the compiled netlist writes and reads

-- It writes only the formula's ancillas ...

compile-targets : (e : Formula n) (F : Frame n N (nodes e)) {w : Fin N} →
                  (∀ i → w ≢ anc F i) → All (λ g → w ≢ target g) (compile e F)
compile-targets (var v)     F h = h zero ∷ []
compile-targets (cst false) F h = []
compile-targets (cst true)  F h = h zero ∷ []
compile-targets (¬ᶠ e)      F h =
  ++⁺ (compile-targets e (below F) (λ i → h (suc i))) (h zero ∷ h zero ∷ [])
compile-targets (e₁ ∧ᶠ e₂)  F h =
  ++⁺ (compile-targets e₁ (left (nodes e₁) (nodes e₂) F)
                       (λ i → h (suc (i ↑ˡ nodes e₂))))
      (++⁺ (compile-targets e₂ (right (nodes e₁) (nodes e₂) F)
                            (λ i → h (suc (nodes e₁ ↑ʳ i))))
           (h zero ∷ []))
compile-targets (e₁ ∨ᶠ e₂)  F h =
  ++⁺ (compile-targets e₁ (left (nodes e₁) (nodes e₂) F)
                       (λ i → h (suc (i ↑ˡ nodes e₂))))
      (++⁺ (compile-targets e₂ (right (nodes e₁) (nodes e₂) F)
                            (λ i → h (suc (nodes e₁ ↑ʳ i))))
           (h zero ∷ h zero ∷ h zero ∷ []))

compile-frame : (e : Formula n) (F : Frame n N (nodes e))
                (u : Assignment N) {w : Fin N} →
                (∀ i → w ≢ anc F i) → run (compile e F) u w ≡ u w
compile-frame e F u h = run-frame (compile e F) u (compile-targets e F h)

-- ... and lies within any set of wires holding its inputs, the
-- constant wire and its ancillas.

compile-within : (Q : Fin N → Set) (e : Formula n) (F : Frame n N (nodes e)) →
                 (∀ v → Q (inp F v)) → Q (one F) → (∀ i → Q (anc F i)) →
                 All (Within Q) (compile e F)
compile-within Q (var v)     F qi qo qa = (qi v , qa zero) ∷ []
compile-within Q (cst false) F qi qo qa = []
compile-within Q (cst true)  F qi qo qa = (qo , qa zero) ∷ []
compile-within Q (¬ᶠ e)      F qi qo qa =
  ++⁺ (compile-within Q e (below F) qi qo (λ i → qa (suc i)))
      ((qa (suc (res e)) , qa zero) ∷ (qo , qa zero) ∷ [])
compile-within Q (e₁ ∧ᶠ e₂)  F qi qo qa =
  ++⁺ (compile-within Q e₁ (left (nodes e₁) (nodes e₂) F) qi qo
                      (λ i → qa (suc (i ↑ˡ nodes e₂))))
      (++⁺ (compile-within Q e₂ (right (nodes e₁) (nodes e₂) F) qi qo
                           (λ i → qa (suc (nodes e₁ ↑ʳ i))))
           ((qa (suc (res e₁ ↑ˡ nodes e₂)) , qa (suc (nodes e₁ ↑ʳ res e₂)) ,
             qa zero) ∷ []))
compile-within Q (e₁ ∨ᶠ e₂)  F qi qo qa =
  ++⁺ (compile-within Q e₁ (left (nodes e₁) (nodes e₂) F) qi qo
                      (λ i → qa (suc (i ↑ˡ nodes e₂))))
      (++⁺ (compile-within Q e₂ (right (nodes e₁) (nodes e₂) F) qi qo
                           (λ i → qa (suc (nodes e₁ ↑ʳ i))))
           ((qa (suc (res e₁ ↑ˡ nodes e₂)) , qa zero) ∷
            (qa (suc (nodes e₁ ↑ʳ res e₂)) , qa zero) ∷
            (qa (suc (res e₁ ↑ˡ nodes e₂)) , qa (suc (nodes e₁ ↑ʳ res e₂)) ,
             qa zero) ∷ []))


------------------------------------------------------------------------
-- The compiled netlist computes the formula

-- From a state where the constant wire reads 1 and the ancillas 0, the
-- formula's value is left in its ancilla.

Correct : (e : Formula n) → Frame n N (nodes e) → Set
Correct {N = N} e F =
  (u : Assignment N) → u (one F) ≡ true → (∀ i → u (anc F i) ≡ false) →
  run (compile e F) u (out e F) ≡ ⟦ e ⟧ᵇ (λ v → u (inp F v))

private
  -- The three gates of a disjunction leave x ⊕ a ⊕ b ⊕ ab in the node's
  -- ancilla, x its old value and a, b the operands' values.

  or-step : ∀ s₁ s₂ (F : Frame n N (suc (s₁ + s₂))) (i : Fin s₁) (i′ : Fin s₂)
            (v : Assignment N) →
            run (gates∨ s₁ s₂ F i i′) v (anc F zero) ≡
            ((v (anc F zero) xor v (anc F (suc (i ↑ˡ s₂)))) xor
             v (anc F (suc (s₁ ↑ʳ i′)))) xor
            (v (anc F (suc (i ↑ˡ s₂))) ∧ v (anc F (suc (s₁ ↑ʳ i′))))
  or-step {N = N} s₁ s₂ F i i′ v =
    trans (⟪⟫-here g₃ v₂)
      (cong₂ _xor_
        (trans (⟪⟫-here g₂ v₁)
               (cong₂ _xor_ (⟪⟫-here g₁ v) (⟪⟫-there g₁ v p₂)))
        (cong₂ _∧_ (trans (⟪⟫-there g₂ v₁ p₁) (⟪⟫-there g₁ v p₁))
                   (trans (⟪⟫-there g₂ v₁ p₂) (⟪⟫-there g₁ v p₂))))
    where
    p₁ : anc F (suc (i ↑ˡ s₂)) ≢ anc F zero
    p₁ = sep₁ s₁ s₂ F i
    p₂ : anc F (suc (s₁ ↑ʳ i′)) ≢ anc F zero
    p₂ = sep₂ s₁ s₂ F i′
    g₁ g₂ g₃ : Gate N
    g₁ = cx (anc F (suc (i ↑ˡ s₂))) (anc F zero) p₁
    g₂ = cx (anc F (suc (s₁ ↑ʳ i′))) (anc F zero) p₂
    g₃ = gate∧ s₁ s₂ F i i′
    v₁ v₂ : Assignment N
    v₁ = ⟪ g₁ ⟫ v
    v₂ = ⟪ g₂ ⟫ v₁

  -- After the two operands of a binary node have run: the node's
  -- ancilla still reads 0 and each operand's ancilla its value.

  binary : (e₁ e₂ : Formula n)
           (F : Frame n N (suc (nodes e₁ + nodes e₂))) →
           Correct e₁ (left (nodes e₁) (nodes e₂) F) →
           Correct e₂ (right (nodes e₁) (nodes e₂) F) →
           (u : Assignment N) → u (one F) ≡ true →
           (∀ i → u (anc F i) ≡ false) →
           let u₂ = run (compile e₂ (right (nodes e₁) (nodes e₂) F))
                        (run (compile e₁ (left (nodes e₁) (nodes e₂) F)) u)
           in (u₂ (anc F zero) ≡ false) ×
              (u₂ (anc F (suc (res e₁ ↑ˡ nodes e₂))) ≡
               ⟦ e₁ ⟧ᵇ (λ v → u (inp F v))) ×
              (u₂ (anc F (suc (nodes e₁ ↑ʳ res e₂))) ≡
               ⟦ e₂ ⟧ᵇ (λ v → u (inp F v)))
  binary {n = n} {N = N} e₁ e₂ F ok₁ ok₂ u o cl =
    trans (fr₂ (λ i → anc-≢ F {zero} {suc (s₁ ↑ʳ i)} λ ()))
          (trans (fr₁ u (λ i → anc-≢ F {zero} {suc (i ↑ˡ s₂)} λ ()))
                 (cl zero)) ,
    trans (fr₂ (λ i → sep₁₂ s₁ s₂ F (res e₁) i))
          (ok₁ u o (λ i → cl (suc (i ↑ˡ s₂)))) ,
    trans (ok₂ u₁ o₁ cl₁)
          (⟦⟧ᵇ-cong e₂ (λ v → fr₁ u (λ i → inp≢anc F v (suc (i ↑ˡ s₂)))))
    where
    s₁ s₂ : ℕ
    s₁ = nodes e₁
    s₂ = nodes e₂

    F₁ : Frame n N s₁
    F₁ = left s₁ s₂ F

    F₂ : Frame n N s₂
    F₂ = right s₁ s₂ F

    u₁ : Assignment N
    u₁ = run (compile e₁ F₁) u

    fr₁ : (u′ : Assignment N) {w : Fin N} → (∀ i → w ≢ anc F₁ i) →
          run (compile e₁ F₁) u′ w ≡ u′ w
    fr₁ u′ h = compile-frame e₁ F₁ u′ h

    fr₂ : {w : Fin N} → (∀ i → w ≢ anc F₂ i) →
          run (compile e₂ F₂) u₁ w ≡ u₁ w
    fr₂ h = compile-frame e₂ F₂ u₁ h

    o₁ : u₁ (one F) ≡ true
    o₁ = trans (fr₁ u (λ i → one≢anc F (suc (i ↑ˡ s₂)))) o

    cl₁ : ∀ i → u₁ (anc F₂ i) ≡ false
    cl₁ i = trans (fr₁ u (λ i′ eq → sep₁₂ s₁ s₂ F i′ i (sym eq)))
                  (cl (suc (s₁ ↑ʳ i)))

  not-correct : (e : Formula n) (F : Frame n N (suc (nodes e))) →
                Correct e (below F) → Correct (¬ᶠ e) F
  not-correct {N = N} e F ok u o cl =
    trans (cong (λ f → f (anc F zero)) (run-++ c (gates¬ F (res e)) u))
    (trans (⟪⟫-here (set1 F) v₁)
    (trans (cong₂ _xor_ (trans (⟪⟫-here g v) (cong₂ _xor_ v-r v-w))
                        (trans (⟪⟫-there g v (one≢anc F zero)) v-one))
           (xor-true (⟦ e ⟧ᵇ (λ w → u (inp F w))))))
    where
    c : List (Gate N)
    c = compile e (below F)

    g : Gate N
    g = cx (anc F (suc (res e))) (anc F zero)
           (anc-≢ F {suc (res e)} {zero} λ ())

    v v₁ : Assignment N
    v  = run c u
    v₁ = ⟪ g ⟫ v

    v-r : v (anc F zero) ≡ false
    v-r = trans (compile-frame e (below F) u
                   (λ i → anc-≢ F {zero} {suc i} λ ()))
                (cl zero)

    v-w : v (anc F (suc (res e))) ≡ ⟦ e ⟧ᵇ (λ w → u (inp F w))
    v-w = ok u o (λ i → cl (suc i))

    v-one : v (one F) ≡ true
    v-one = trans (compile-frame e (below F) u (λ i → one≢anc F (suc i))) o

  and-correct : (e₁ e₂ : Formula n)
                (F : Frame n N (suc (nodes e₁ + nodes e₂))) →
                Correct e₁ (left (nodes e₁) (nodes e₂) F) →
                Correct e₂ (right (nodes e₁) (nodes e₂) F) →
                Correct (e₁ ∧ᶠ e₂) F
  and-correct {N = N} e₁ e₂ F ok₁ ok₂ u o cl =
    trans (cong (λ f → f (anc F zero)) (run-++ c₁ (c₂ ++ g ∷ []) u))
    (trans (cong (λ f → f (anc F zero)) (run-++ c₂ (g ∷ []) (run c₁ u)))
    (trans (⟪⟫-here g (run c₂ (run c₁ u)))
           (cong₂ _xor_ (proj₁ b)
                  (cong₂ _∧_ (proj₁ (proj₂ b)) (proj₂ (proj₂ b))))))
    where
    c₁ c₂ : List (Gate N)
    c₁ = compile e₁ (left (nodes e₁) (nodes e₂) F)
    c₂ = compile e₂ (right (nodes e₁) (nodes e₂) F)

    g : Gate N
    g = gate∧ (nodes e₁) (nodes e₂) F (res e₁) (res e₂)

    b = binary e₁ e₂ F ok₁ ok₂ u o cl

  or-correct : (e₁ e₂ : Formula n)
               (F : Frame n N (suc (nodes e₁ + nodes e₂))) →
               Correct e₁ (left (nodes e₁) (nodes e₂) F) →
               Correct e₂ (right (nodes e₁) (nodes e₂) F) →
               Correct (e₁ ∨ᶠ e₂) F
  or-correct {N = N} e₁ e₂ F ok₁ ok₂ u o cl =
    trans (cong (λ f → f (anc F zero)) (run-++ c₁ (c₂ ++ gs) u))
    (trans (cong (λ f → f (anc F zero)) (run-++ c₂ gs (run c₁ u)))
    (trans (or-step (nodes e₁) (nodes e₂) F (res e₁) (res e₂)
                    (run c₂ (run c₁ u)))
           (or-value (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)))))
    where
    c₁ c₂ gs : List (Gate N)
    c₁ = compile e₁ (left (nodes e₁) (nodes e₂) F)
    c₂ = compile e₂ (right (nodes e₁) (nodes e₂) F)
    gs = gates∨ (nodes e₁) (nodes e₂) F (res e₁) (res e₂)

    b = binary e₁ e₂ F ok₁ ok₂ u o cl

compile-correct : (e : Formula n) (F : Frame n N (nodes e)) → Correct e F
compile-correct (var v)     F u o cl =
  trans (⟪⟫-here (copy F v) u) (cong (_xor u (inp F v)) (cl zero))
compile-correct (cst false) F u o cl = cl zero
compile-correct (cst true)  F u o cl =
  trans (⟪⟫-here (set1 F) u) (cong₂ _xor_ (cl zero) o)
compile-correct (¬ᶠ e)      F u o cl =
  not-correct e F (compile-correct e (below F)) u o cl
compile-correct (e₁ ∧ᶠ e₂)  F u o cl =
  and-correct e₁ e₂ F (compile-correct e₁ (left (nodes e₁) (nodes e₂) F))
                      (compile-correct e₂ (right (nodes e₁) (nodes e₂) F))
                      u o cl
compile-correct (e₁ ∨ᶠ e₂)  F u o cl =
  or-correct e₁ e₂ F (compile-correct e₁ (left (nodes e₁) (nodes e₂) F))
                     (compile-correct e₂ (right (nodes e₁) (nodes e₂) F))
                     u o cl


------------------------------------------------------------------------
-- Gate counts of the compiled netlist

-- Toffoli gates: one per conjunction and per disjunction.  CNOTs: one
-- per variable and per constant 1, two per negation and per
-- disjunction.

tofs cxs : Formula n → ℕ
tofs (var _)    = 0
tofs (cst _)    = 0
tofs (¬ᶠ e)     = tofs e
tofs (e₁ ∧ᶠ e₂) = suc (tofs e₁ + tofs e₂)
tofs (e₁ ∨ᶠ e₂) = suc (tofs e₁ + tofs e₂)

cxs (var _)     = 1
cxs (cst false) = 0
cxs (cst true)  = 1
cxs (¬ᶠ e)      = 2 + cxs e
cxs (e₁ ∧ᶠ e₂)  = cxs e₁ + cxs e₂
cxs (e₁ ∨ᶠ e₂)  = 2 + (cxs e₁ + cxs e₂)

toffolis-compile : (e : Formula n) (F : Frame n N (nodes e)) →
                   toffolis (compile e F) ≡ tofs e
toffolis-compile (var v)     F = refl
toffolis-compile (cst false) F = refl
toffolis-compile (cst true)  F = refl
toffolis-compile (¬ᶠ e)      F =
  trans (count-++ is-ccx (compile e (below F)) (gates¬ F (res e)))
        (trans (cong (_+ 0) (toffolis-compile e (below F)))
               (+-identityʳ (tofs e)))
toffolis-compile (e₁ ∧ᶠ e₂)  F =
  trans (count-++ is-ccx c₁ (c₂ ++ gate∧ s₁ s₂ F (res e₁) (res e₂) ∷ []))
  (trans (cong (count is-ccx c₁ +_)
               (count-++ is-ccx c₂ (gate∧ s₁ s₂ F (res e₁) (res e₂) ∷ [])))
  (trans (cong₂ (λ a b → a + (b + 1)) (toffolis-compile e₁ (left s₁ s₂ F))
                                      (toffolis-compile e₂ (right s₁ s₂ F)))
         (solve 2 (λ a b → a :+ (b :+ con 1) := con 1 :+ (a :+ b)) refl
                (tofs e₁) (tofs e₂))))
  where
  s₁ = nodes e₁
  s₂ = nodes e₂
  c₁ = compile e₁ (left s₁ s₂ F)
  c₂ = compile e₂ (right s₁ s₂ F)
toffolis-compile (e₁ ∨ᶠ e₂)  F =
  trans (count-++ is-ccx c₁ (c₂ ++ gates∨ s₁ s₂ F (res e₁) (res e₂)))
  (trans (cong (count is-ccx c₁ +_)
               (count-++ is-ccx c₂ (gates∨ s₁ s₂ F (res e₁) (res e₂))))
  (trans (cong₂ (λ a b → a + (b + 1)) (toffolis-compile e₁ (left s₁ s₂ F))
                                      (toffolis-compile e₂ (right s₁ s₂ F)))
         (solve 2 (λ a b → a :+ (b :+ con 1) := con 1 :+ (a :+ b)) refl
                (tofs e₁) (tofs e₂))))
  where
  s₁ = nodes e₁
  s₂ = nodes e₂
  c₁ = compile e₁ (left s₁ s₂ F)
  c₂ = compile e₂ (right s₁ s₂ F)

cnots-compile : (e : Formula n) (F : Frame n N (nodes e)) →
                cnots (compile e F) ≡ cxs e
cnots-compile (var v)     F = refl
cnots-compile (cst false) F = refl
cnots-compile (cst true)  F = refl
cnots-compile (¬ᶠ e)      F =
  trans (count-++ is-cx (compile e (below F)) (gates¬ F (res e)))
        (trans (cong (_+ 2) (cnots-compile e (below F)))
               (solve 1 (λ a → a :+ con 2 := con 2 :+ a) refl (cxs e)))
cnots-compile (e₁ ∧ᶠ e₂)  F =
  trans (count-++ is-cx c₁ (c₂ ++ gate∧ s₁ s₂ F (res e₁) (res e₂) ∷ []))
  (trans (cong (count is-cx c₁ +_)
               (count-++ is-cx c₂ (gate∧ s₁ s₂ F (res e₁) (res e₂) ∷ [])))
  (trans (cong₂ (λ a b → a + (b + 0)) (cnots-compile e₁ (left s₁ s₂ F))
                                      (cnots-compile e₂ (right s₁ s₂ F)))
         (solve 2 (λ a b → a :+ (b :+ con 0) := a :+ b) refl
                (cxs e₁) (cxs e₂))))
  where
  s₁ = nodes e₁
  s₂ = nodes e₂
  c₁ = compile e₁ (left s₁ s₂ F)
  c₂ = compile e₂ (right s₁ s₂ F)
cnots-compile (e₁ ∨ᶠ e₂)  F =
  trans (count-++ is-cx c₁ (c₂ ++ gates∨ s₁ s₂ F (res e₁) (res e₂)))
  (trans (cong (count is-cx c₁ +_)
               (count-++ is-cx c₂ (gates∨ s₁ s₂ F (res e₁) (res e₂))))
  (trans (cong₂ (λ a b → a + (b + 2)) (cnots-compile e₁ (left s₁ s₂ F))
                                      (cnots-compile e₂ (right s₁ s₂ F)))
         (solve 2 (λ a b → a :+ (b :+ con 2) := con 2 :+ (a :+ b)) refl
                (cxs e₁) (cxs e₂))))
  where
  s₁ = nodes e₁
  s₂ = nodes e₂
  c₁ = compile e₁ (left s₁ s₂ F)
  c₂ = compile e₂ (right s₁ s₂ F)


------------------------------------------------------------------------
-- Netlists with NOT gates

-- NOT (X), or a Toffoli or CNOT gate.

data NCT (N : ℕ) : Set where
  X    : Fin N → NCT N
  gate : Gate N → NCT N

flip : Fin N → Assignment N → Assignment N
flip w x = x [ w ≔ not (x w) ]

⟦_⟧ᴺ : NCT N → Assignment N → Assignment N
⟦ X w    ⟧ᴺ x = flip w x
⟦ gate g ⟧ᴺ x = ⟪ g ⟫ x

-- The head first, like a circuit.

runᴺ : List (NCT N) → Assignment N → Assignment N
runᴺ []       x = x
runᴺ (g ∷ gs) x = runᴺ gs (⟦ g ⟧ᴺ x)

runᴺ-++ : (gs hs : List (NCT N)) (x : Assignment N) →
          runᴺ (gs ++ hs) x ≡ runᴺ hs (runᴺ gs x)
runᴺ-++ []       hs x = refl
runᴺ-++ (g ∷ gs) hs x = runᴺ-++ gs hs (⟦ g ⟧ᴺ x)

runᴺ-gates : (gs : List (Gate N)) (x : Assignment N) →
             runᴺ (map gate gs) x ≡ run gs x
runᴺ-gates []       x = refl
runᴺ-gates (g ∷ gs) x = runᴺ-gates gs (⟪ g ⟫ x)

-- NOT only reads values, and is an involution.

flip-cong : (w : Fin N) {x x′ : Assignment N} → (∀ u → x u ≡ x′ u) →
            ∀ u → flip w x u ≡ flip w x′ u
flip-cong w {x} {x′} h u =
  trans (cong (λ b → (x [ w ≔ b ]) u) (cong not (h w)))
        (≔-cong w (not (x′ w)) h u)

flip-flip : (w : Fin N) (x : Assignment N) → ∀ u → flip w (flip w x) u ≡ x u
flip-flip w x u =
  trans (cong (λ b → ((x [ w ≔ not (x w) ]) [ w ≔ b ]) u)
              (trans (cong not (≔-here x w (not (x w))))
                     (not-involutive (x w))))
        (trans (≔-≔ x w (not (x w)) (x w) u) (≔-self x w u))

-- Gate counts by kind.

countᴺ : (NCT N → ℕ) → List (NCT N) → ℕ
countᴺ f []       = 0
countᴺ f (g ∷ gs) = f g + countᴺ f gs

countᴺ-++ : (f : NCT N → ℕ) (gs hs : List (NCT N)) →
            countᴺ f (gs ++ hs) ≡ countᴺ f gs + countᴺ f hs
countᴺ-++ f []       hs = refl
countᴺ-++ f (g ∷ gs) hs =
  trans (cong (f g +_) (countᴺ-++ f gs hs))
        (solve 3 (λ a b c → a :+ (b :+ c) := a :+ b :+ c) refl
               (f g) (countᴺ f gs) (countᴺ f hs))

countᴺ-gates : (f : NCT N → ℕ) (gs : List (Gate N)) →
               countᴺ f (map gate gs) ≡ count (λ g → f (gate g)) gs
countᴺ-gates f []       = refl
countᴺ-gates f (g ∷ gs) = cong (f (gate g) +_) (countᴺ-gates f gs)

is-X is-ccxᴺ is-cxᴺ : NCT N → ℕ
is-X (X _)       = 1
is-X (gate _)    = 0
is-ccxᴺ (X _)    = 0
is-ccxᴺ (gate g) = is-ccx g
is-cxᴺ (X _)     = 0
is-cxᴺ (gate g)  = is-cx g

nots toffolisᴺ cnotsᴺ : List (NCT N) → ℕ
nots      = countᴺ is-X
toffolisᴺ = countᴺ is-ccxᴺ
cnotsᴺ    = countᴺ is-cxᴺ

-- Every gate is of one of the three kinds.

length-countᴺ : (gs : List (NCT N)) →
                length gs ≡ nots gs + toffolisᴺ gs + cnotsᴺ gs
length-countᴺ []                           = refl
length-countᴺ (X _ ∷ gs)                   = cong suc (length-countᴺ gs)
length-countᴺ (gate (ccx _ _ _ _ _ _) ∷ gs) =
  trans (cong suc (length-countᴺ gs))
        (solve 3 (λ a b c → con 1 :+ (a :+ b :+ c) := a :+ (con 1 :+ b) :+ c)
               refl (nots gs) (toffolisᴺ gs) (cnotsᴺ gs))
length-countᴺ (gate (cx _ _ _) ∷ gs)       =
  trans (cong suc (length-countᴺ gs))
        (solve 3 (λ a b c → con 1 :+ (a :+ b :+ c) := a :+ b :+ (con 1 :+ c))
               refl (nots gs) (toffolisᴺ gs) (cnotsᴺ gs))

private
  count-zero : (gs : List (Gate N)) → count (λ _ → 0) gs ≡ 0
  count-zero []       = refl
  count-zero (g ∷ gs) = count-zero gs


------------------------------------------------------------------------
-- Why NOT gates

-- A netlist of Toffoli and CNOT gates maps the input 0 to itself: each
-- gate xors a conjunction of zeros, or a zero, into its target.

private
  z0 : Assignment N
  z0 _ = false

  control-zero : (g : Gate N) → control g z0 ≡ false
  control-zero (ccx _ _ _ _ _ _) = refl
  control-zero (cx _ _ _)        = refl

  ≔-zero : (t w : Fin N) → (z0 [ t ≔ false ]) w ≡ false
  ≔-zero t w = go ⌊ w Fin.≟ t ⌋
    where
    go : ∀ d → (if d then false else false) ≡ false
    go true  = refl
    go false = refl

  ⟪⟫-zero : (g : Gate N) → ∀ w → ⟪ g ⟫ z0 w ≡ false
  ⟪⟫-zero g w =
    trans (cong (λ b → (z0 [ target g ≔ b ]) w) (control-zero g))
          (≔-zero (target g) w)

run-zero : (gs : List (Gate N)) → ∀ w → run gs (λ _ → false) w ≡ false
run-zero []       w = refl
run-zero (g ∷ gs) w = trans (run-cong gs (⟪⟫-zero g) w) (run-zero gs w)

-- So none computes |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ e(x)⟩ on the inputs whose
-- ancillas are 0, on any wires, when e is true at 0: the input 0 is
-- one of them, and its target would come out as e(0).

needs-NOT : (e : Formula n) (gs : List (Gate N)) (ι : Fin n → Fin N)
            (a : Fin j → Fin N) (t : Fin N) →
            (∀ x → Clean a x → run gs x t ≡ x t xor ⟦ e ⟧ᵇ (λ v → x (ι v))) →
            ⟦ e ⟧ᵇ (λ _ → false) ≡ false
needs-NOT e gs ι a t h = trans (sym (h z0 (λ _ → refl))) (run-zero gs t)


------------------------------------------------------------------------
-- The standard layout

-- n inputs, then the ancillas -- the constant wire, then s scratch
-- wires -- then the target: the paper's |x⟩|0⟩|t⟩.

Width : ℕ → ℕ → ℕ
Width n s = n + (suc s + 1)

inpʷ : ∀ n s → Fin n → Fin (Width n s)
inpʷ n s v = v ↑ˡ (suc s + 1)

ancʷ : ∀ n s → Fin (suc s) → Fin (Width n s)
ancʷ n s i = n ↑ʳ (i ↑ˡ 1)

tgtʷ : ∀ n s → Fin (Width n s)
tgtʷ n s = n ↑ʳ (suc s ↑ʳ zero)

ancʷ-inj : ∀ n s (i i′ : Fin (suc s)) → ancʷ n s i ≡ ancʷ n s i′ → i ≡ i′
ancʷ-inj n s i i′ eq =
  Fin.↑ˡ-injective 1 i i′ (Fin.↑ʳ-injective n (i ↑ˡ 1) (i′ ↑ˡ 1) eq)

inp≢ancʷ : ∀ n s (v : Fin n) (i : Fin (suc s)) → inpʷ n s v ≢ ancʷ n s i
inp≢ancʷ n s v i = ↑ˡ≢↑ʳ v (i ↑ˡ 1)

inp≢tgtʷ : ∀ n s (v : Fin n) → inpʷ n s v ≢ tgtʷ n s
inp≢tgtʷ n s v = ↑ˡ≢↑ʳ v (suc s ↑ʳ zero)

anc≢tgtʷ : ∀ n s (i : Fin (suc s)) → ancʷ n s i ≢ tgtʷ n s
anc≢tgtʷ n s i eq =
  ↑ˡ≢↑ʳ i zero (Fin.↑ʳ-injective n (i ↑ˡ 1) (suc s ↑ʳ zero) eq)

-- The frame of a formula with s nodes on it.

std : ∀ n s → Frame n (Width n s) s
std n s = record
  { inp     = inpʷ n s
  ; one     = ancʷ n s zero
  ; anc     = λ i → ancʷ n s (suc i)
  ; anc-inj = λ i i′ eq → Fin.suc-injective (ancʷ-inj n s (suc i) (suc i′) eq)
  ; inp≢anc = λ v i → inp≢ancʷ n s v (suc i)
  ; one≢anc = λ i eq → Fin.0≢1+n (ancʷ-inj n s zero (suc i) eq)
  }

-- The input |v⟩|0⟩|0⟩.

blank : ∀ {n} s → Assignment n → Assignment (Width n s)
blank {n} s v w = [ v , (λ _ → false) ]′ (splitAt n w)

blank-inp : ∀ {n} s (v : Assignment n) (u : Fin n) →
            blank s v (inpʷ n s u) ≡ v u
blank-inp {n} s v u =
  cong [ v , (λ _ → false) ]′ (Fin.splitAt-↑ˡ n u (suc s + 1))

blank-clean : ∀ {n} s (v : Assignment n) → Clean (ancʷ n s) (blank s v)
blank-clean {n} s v i =
  cong [ v , (λ _ → false) ]′ (Fin.splitAt-↑ʳ n (suc s + 1) (i ↑ˡ 1))


------------------------------------------------------------------------
-- Copying the value out: Bennett's compute-copy-uncompute

-- The CNOT from the formula's ancilla into the target.

copyout : (e : Formula n) → Gate (Width n (nodes e))
copyout {n} e = cx (out e (std n (nodes e))) (tgtʷ n (nodes e))
                   (anc≢tgtʷ n (nodes e) (suc (res e)))

core : (e : Formula n) → List (Gate (Width n (nodes e)))
core {n} e = compile e (std n (nodes e)) ++ (copyout e ∷ []) ++
             reverse (compile e (std n (nodes e)))

-- Every wire but the target is restored, from every input ...

core-there : (e : Formula n) (u : Assignment (Width n (nodes e))) →
             ∀ w → w ≢ tgtʷ n (nodes e) → run (core e) u w ≡ u w
core-there {n} e u w w≢t =
  bennett-work (λ w → w ≢ tgtʷ n sz) (compile e (std n sz)) (copyout e ∷ [])
    (compile-within (λ w → w ≢ tgtʷ n sz) e (std n sz) (inp≢tgtʷ n sz)
                    (anc≢tgtʷ n sz zero) (λ i → anc≢tgtʷ n sz (suc i)))
    (λ u′ w′ q → ⟪⟫-there (copyout e) u′ q) u w w≢t
  where
  sz : ℕ
  sz = nodes e

-- ... and the target is flipped by the formula's value, once the
-- constant wire reads 1 and the scratch wires 0.

core-here : (e : Formula n) (u : Assignment (Width n (nodes e))) →
            u (ancʷ n (nodes e) zero) ≡ true →
            (∀ i → u (ancʷ n (nodes e) (suc i)) ≡ false) →
            run (core e) u (tgtʷ n (nodes e)) ≡
            u (tgtʷ n (nodes e)) xor ⟦ e ⟧ᵇ (λ v → u (inpʷ n (nodes e) v))
core-here {n} e u o cl =
  trans (bennett-out (λ w → w ≢ tgtʷ n sz) (compile e (std n sz))
          (copyout e ∷ [])
          (compile-within (λ w → w ≢ tgtʷ n sz) e (std n sz) (inp≢tgtʷ n sz)
                          (anc≢tgtʷ n sz zero) (λ i → anc≢tgtʷ n sz (suc i)))
          u (tgtʷ n sz) (λ q → q refl))
  (trans (⟪⟫-here (copyout e) (run (compile e (std n sz)) u))
         (cong₂ _xor_
           (compile-frame e (std n sz) u
              (λ i eq → anc≢tgtʷ n sz (suc i) (sym eq)))
           (compile-correct e (std n sz) u o cl)))
  where
  sz : ℕ
  sz = nodes e

core-correct : (e : Formula n) (u : Assignment (Width n (nodes e))) →
               u (ancʷ n (nodes e) zero) ≡ true →
               (∀ i → u (ancʷ n (nodes e) (suc i)) ≡ false) →
               ∀ w → run (core e) u w ≡
                     (u [ tgtʷ n (nodes e) ≔
                          u (tgtʷ n (nodes e)) xor
                          ⟦ e ⟧ᵇ (λ v → u (inpʷ n (nodes e) v)) ]) w
core-correct {n} e u o cl =
  ≔-ext (run (core e) u) u (tgtʷ n (nodes e)) _ (core-here e u o cl)
        (core-there e u)


------------------------------------------------------------------------
-- The oracle of a formula

-- The core between the two NOT gates on the constant wire.

oracle : (e : Formula n) → List (NCT (Width n (nodes e)))
oracle {n} e = X (ancʷ n (nodes e) zero) ∷
               (map gate (core e) ++ X (ancʷ n (nodes e) zero) ∷ [])

-- From every input whose ancillas read 0 it computes
-- |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ e(x)⟩.

oracle-correct : (e : Formula n) (x : Assignment (Width n (nodes e))) →
                 Clean (ancʷ n (nodes e)) x →
                 ∀ w → runᴺ (oracle e) x w ≡
                       (x [ tgtʷ n (nodes e) ≔
                            x (tgtʷ n (nodes e)) xor
                            ⟦ e ⟧ᵇ (λ v → x (inpʷ n (nodes e) v)) ]) w
oracle-correct {n} e x cl = ≔-ext (runᴺ (oracle e) x) x t _ at-t away
  where
  sz : ℕ
  sz = nodes e

  o t : Fin (Width n sz)
  o = ancʷ n sz zero
  t = tgtʷ n sz

  x₁ x₂ : Assignment (Width n sz)
  x₁ = flip o x
  x₂ = run (core e) x₁

  -- The netlist is the core between two NOT gates.

  whole : ∀ w → runᴺ (oracle e) x w ≡ flip o x₂ w
  whole w = cong (λ f → f w)
    (trans (runᴺ-++ (map gate (core e)) (X o ∷ []) x₁)
           (cong (flip o) (runᴺ-gates (core e) x₁)))

  o≢t : o ≢ t
  o≢t = anc≢tgtʷ n sz zero

  t≢o : t ≢ o
  t≢o eq = o≢t (sym eq)

  -- After the first NOT the constant wire reads 1; nothing else moved.

  x₁-o : x₁ o ≡ true
  x₁-o = trans (≔-here x o (not (x o))) (cong not (cl zero))

  x₁-anc : ∀ i → x₁ (ancʷ n sz (suc i)) ≡ false
  x₁-anc i = trans (≔-there x (not (x o))
                      (λ eq → Fin.0≢1+n (sym (ancʷ-inj n sz (suc i) zero eq))))
                   (cl (suc i))

  x₁-inp : ∀ v → x₁ (inpʷ n sz v) ≡ x (inpʷ n sz v)
  x₁-inp v = ≔-there x (not (x o)) (inp≢ancʷ n sz v zero)

  at-t : runᴺ (oracle e) x t ≡
         x t xor ⟦ e ⟧ᵇ (λ v → x (inpʷ n sz v))
  at-t = trans (whole t)
    (trans (≔-there x₂ (not (x₂ o)) t≢o)
    (trans (core-here e x₁ x₁-o x₁-anc)
           (cong₂ _xor_ (≔-there x (not (x o)) t≢o) (⟦⟧ᵇ-cong e x₁-inp))))

  -- Off the target: the second NOT undoes the first.

  off : ∀ w → Dec (w ≡ o) → w ≢ t → flip o x₂ w ≡ x w
  off w (yes refl) w≢t =
    trans (≔-here x₂ o (not (x₂ o)))
          (trans (cong not (trans (core-there e x₁ o o≢t)
                                  (≔-here x o (not (x o)))))
                 (not-involutive (x o)))
  off w (no w≢o)   w≢t =
    trans (≔-there x₂ (not (x₂ o)) w≢o)
          (trans (core-there e x₁ w w≢t) (≔-there x (not (x o)) w≢o))

  away : ∀ w → w ≢ t → runᴺ (oracle e) x w ≡ x w
  away w w≢t = trans (whole w) (off w (w Fin.≟ o) w≢t)

-- So on those inputs it is the identity exactly when e is false
-- everywhere: if e holds at v, the input |v⟩|0⟩|0⟩ comes out with its
-- target flipped.

oracle-identity⇔ : (e : Formula n) →
                   (∀ x → Clean (ancʷ n (nodes e)) x →
                    ∀ w → runᴺ (oracle e) x w ≡ x w) ⇔
                   (∀ v → ⟦ e ⟧ᵇ v ≡ false)
oracle-identity⇔ {n} e = mk⇔ to from
  where
  sz : ℕ
  sz = nodes e

  t : Fin (Width n sz)
  t = tgtʷ n sz

  to : (∀ x → Clean (ancʷ n sz) x → ∀ w → runᴺ (oracle e) x w ≡ x w) →
       ∀ v → ⟦ e ⟧ᵇ v ≡ false
  to same v =
    trans (sym (⟦⟧ᵇ-cong e (blank-inp sz v)))
          (xor-cancel (x t) _
             (trans (sym (trans (oracle-correct e x cl t) (≔-here x t _)))
                    (same x cl t)))
    where
    x : Assignment (Width n sz)
    x = blank sz v

    cl : Clean (ancʷ n sz) x
    cl = blank-clean sz v

  from : (∀ v → ⟦ e ⟧ᵇ v ≡ false) →
         ∀ x → Clean (ancʷ n sz) x → ∀ w → runᴺ (oracle e) x w ≡ x w
  from u x cl w =
    trans (oracle-correct e x cl w)
    (trans (cong (λ c → (x [ t ≔ x t xor c ]) w) (u (λ v → x (inpʷ n sz v))))
    (trans (cong (λ c → (x [ t ≔ c ]) w) (xor-identityʳ (x t)))
           (≔-self x t w)))

-- Its gates: two NOT gates, the compiled netlist's Toffoli gates twice,
-- and its CNOTs twice with the copying CNOT.

private
  countᴺ-oracle : (e : Formula n) (f : NCT (Width n (nodes e)) → ℕ) →
                  countᴺ f (oracle e) ≡
                  f (X (ancʷ n (nodes e) zero)) +
                  (count (λ g → f (gate g)) (core e) +
                   (f (X (ancʷ n (nodes e) zero)) + 0))
  countᴺ-oracle {n} e f =
    cong (f (X o) +_)
      (trans (countᴺ-++ f (map gate (core e)) (X o ∷ []))
             (cong (_+ (f (X o) + 0)) (countᴺ-gates f (core e))))
    where
    o : Fin (Width n (nodes e))
    o = ancʷ n (nodes e) zero

  count-core : (e : Formula n) (f : Gate (Width n (nodes e)) → ℕ) →
               count f (core e) ≡
               count f (compile e (std n (nodes e))) +
               (f (copyout e) + count f (compile e (std n (nodes e))))
  count-core {n} e f =
    trans (count-++ f F (copyout e ∷ reverse F))
          (cong (λ c → count f F + (f (copyout e) + c)) (count-reverse f F))
    where
    F : List (Gate (Width n (nodes e)))
    F = compile e (std n (nodes e))

oracle-nots : (e : Formula n) → nots (oracle e) ≡ 2
oracle-nots e =
  trans (countᴺ-oracle e is-X) (cong (λ c → suc (c + 1)) (count-zero (core e)))

oracle-toffolis : (e : Formula n) → toffolisᴺ (oracle e) ≡ 2 * tofs e
oracle-toffolis {n} e =
  trans (countᴺ-oracle e is-ccxᴺ)
  (trans (cong (_+ 0) (trans (count-core e is-ccx)
                             (cong (λ c → c + c)
                                   (toffolis-compile e (std n (nodes e))))))
         (solve 1 (λ a → a :+ a :+ con 0 := con 2 :* a) refl (tofs e)))

oracle-cnots : (e : Formula n) → cnotsᴺ (oracle e) ≡ 2 * cxs e + 1
oracle-cnots {n} e =
  trans (countᴺ-oracle e is-cxᴺ)
  (trans (cong (_+ 0) (trans (count-core e is-cx)
                             (cong (λ c → c + suc c)
                                   (cnots-compile e (std n (nodes e))))))
         (solve 1 (λ a → a :+ (con 1 :+ a) :+ con 0 := con 2 :* a :+ con 1)
                refl (cxs e)))


------------------------------------------------------------------------
-- CNF formulas

-- The wires, and their roles, for a CNF formula φ.

wires : CNF n → ℕ
wires {n} φ = Width n (nodes (cnf φ))

inputs : (φ : CNF n) → Fin n → Fin (wires φ)
inputs {n} φ = inpʷ n (nodes (cnf φ))

ancillas : (φ : CNF n) → Fin (suc (nodes (cnf φ))) → Fin (wires φ)
ancillas {n} φ = ancʷ n (nodes (cnf φ))

tgt : (φ : CNF n) → Fin (wires φ)
tgt {n} φ = tgtʷ n (nodes (cnf φ))

-- The reduction: φ ↦ the oracle of φ.

netlist : (φ : CNF n) → List (NCT (wires φ))
netlist φ = oracle (cnf φ)

-- It computes |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ φ(x)⟩ ...

netlist-correct : (φ : CNF n) (x : Assignment (wires φ)) →
                  Clean (ancillas φ) x →
                  ∀ w → runᴺ (netlist φ) x w ≡
                        (x [ tgt φ ≔ x (tgt φ) xor
                                     ⟦ φ ⟧ᶠ (λ v → x (inputs φ v)) ]) w
netlist-correct φ x cl w =
  trans (oracle-correct (cnf φ) x cl w)
        (cong (λ c → (x [ tgt φ ≔ x (tgt φ) xor c ]) w)
              (⟦cnf⟧ φ (λ v → x (inputs φ v))))

-- ... so it is the identity on the inputs whose ancillas are 0 exactly
-- when φ is unsatisfiable.

netlist-identity⇔unsat : (φ : CNF n) →
                         (∀ x → Clean (ancillas φ) x →
                          ∀ w → runᴺ (netlist φ) x w ≡ x w) ⇔
                         Unsatisfiable φ
netlist-identity⇔unsat φ = mk⇔
  (λ h → Equivalence.from (unsat⇔cnf φ)
           (Equivalence.to (oracle-identity⇔ (cnf φ)) h))
  (λ u → Equivalence.from (oracle-identity⇔ (cnf φ))
           (Equivalence.to (unsat⇔cnf φ) u))


------------------------------------------------------------------------
-- The size of the reduction

-- The compiled netlist of cnf φ: a Toffoli gate per disjunction and
-- per conjunction, one per literal occurrence and one per clause; a
-- CNOT per positive literal, three per negative one, two per
-- disjunction, one for the final true.

tofs-clause : (c : Clause n) → tofs (clause c) ≡ length c
tofs-clause []          = refl
tofs-clause (pos _ ∷ c) = cong suc (tofs-clause c)
tofs-clause (neg _ ∷ c) = cong suc (tofs-clause c)

tofs-cnf : (φ : CNF n) → tofs (cnf φ) ≡ ‖ φ ‖
tofs-cnf []      = refl
tofs-cnf (c ∷ φ) =
  trans (cong suc (cong₂ _+_ (tofs-clause c) (tofs-cnf φ)))
        (solve 3 (λ k L m → con 1 :+ (k :+ (L :+ m))
                            := k :+ L :+ (con 1 :+ m))
               refl (length c) (lits φ) (clauses φ))

cxs-clause : (c : Clause n) → cxs (clause c) ≡ 3 * length c + 2 * negsᶜ c
cxs-clause []          = refl
cxs-clause (pos _ ∷ c) =
  trans (cong (λ a → 3 + a) (cxs-clause c))
        (solve 2 (λ k q → con 3 :+ (con 3 :* k :+ con 2 :* q)
                          := con 3 :* (con 1 :+ k) :+ con 2 :* q)
               refl (length c) (negsᶜ c))
cxs-clause (neg _ ∷ c) =
  trans (cong (λ a → 5 + a) (cxs-clause c))
        (solve 2 (λ k q → con 5 :+ (con 3 :* k :+ con 2 :* q)
                          := con 3 :* (con 1 :+ k) :+ con 2 :* (con 1 :+ q))
               refl (length c) (negsᶜ c))

cxs-cnf : (φ : CNF n) → cxs (cnf φ) ≡ 3 * lits φ + 2 * negs φ + 1
cxs-cnf []      = refl
cxs-cnf (c ∷ φ) =
  trans (cong₂ _+_ (cxs-clause c) (cxs-cnf φ))
        (solve 4 (λ k q L Q → con 3 :* k :+ con 2 :* q :+
                                (con 3 :* L :+ con 2 :* Q :+ con 1)
                              := con 3 :* (k :+ L) :+ con 2 :* (q :+ Q) :+
                                 con 1)
               refl (length c) (negsᶜ c) (lits φ) (negs φ))

-- The wires: n inputs, 2 lits + negs + 2 clauses + 2 ancillas and the
-- target.

wires-exact : (φ : CNF n) →
              wires φ ≡ n + 2 * lits φ + negs φ + 2 * clauses φ + 3
wires-exact {n} φ =
  trans (cong (λ a → n + (suc a + 1)) (nodes-cnf φ))
        (solve 4 (λ n L Q m →
                    n :+ (con 1 :+ (con 2 :* L :+ Q :+ con 2 :* m :+ con 1)
                          :+ con 1)
                    := n :+ con 2 :* L :+ Q :+ con 2 :* m :+ con 3)
               refl n (lits φ) (negs φ) (clauses φ))

-- The gates.

netlist-nots : (φ : CNF n) → nots (netlist φ) ≡ 2
netlist-nots φ = oracle-nots (cnf φ)

netlist-toffolis : (φ : CNF n) → toffolisᴺ (netlist φ) ≡ 2 * ‖ φ ‖
netlist-toffolis φ =
  trans (oracle-toffolis (cnf φ)) (cong (2 *_) (tofs-cnf φ))

netlist-cnots : (φ : CNF n) →
                cnotsᴺ (netlist φ) ≡ 6 * lits φ + 4 * negs φ + 3
netlist-cnots φ =
  trans (oracle-cnots (cnf φ))
  (trans (cong (λ a → 2 * a + 1) (cxs-cnf φ))
         (solve 2 (λ L Q → con 2 :* (con 3 :* L :+ con 2 :* Q :+ con 1) :+ con 1
                           := con 6 :* L :+ con 4 :* Q :+ con 3)
                refl (lits φ) (negs φ)))

netlist-length : (φ : CNF n) →
                 length (netlist φ) ≡
                 8 * lits φ + 4 * negs φ + 2 * clauses φ + 5
netlist-length φ =
  trans (length-countᴺ (netlist φ))
  (trans (cong₂ _+_ (cong₂ _+_ (netlist-nots φ) (netlist-toffolis φ))
                    (netlist-cnots φ))
         (solve 3 (λ L Q m → con 2 :+ con 2 :* (L :+ m) :+
                               (con 6 :* L :+ con 4 :* Q :+ con 3)
                             := con 8 :* L :+ con 4 :* Q :+ con 2 :* m :+ con 5)
                refl (lits φ) (negs φ) (clauses φ)))

-- Linear bounds in ‖φ‖, since negs φ ≤ lits φ.

private
  ≤-via : ∀ {a b} c → b ≡ a + c → a ≤ b
  ≤-via {a} c refl = m≤m+n a c

  split-lits : (φ : CNF n) → ∃ λ d → negs φ + d ≡ lits φ
  split-lits φ = m≤n⇒∃[o]m+o≡n (negs≤lits φ)

wires-bound : (φ : CNF n) → wires φ ≤ n + 3 * ‖ φ ‖ + 3
wires-bound {n} φ =
  subst (_≤ n + 3 * ‖ φ ‖ + 3) (sym (wires-exact φ))
        (≤-via (d + clauses φ)
          (subst (λ L → n + 3 * (L + clauses φ) + 3 ≡
                        (n + 2 * L + negs φ + 2 * clauses φ + 3) +
                        (d + clauses φ))
                 (proj₂ (split-lits φ))
                 (solve 4 (λ n Q d m → n :+ con 3 :* ((Q :+ d) :+ m) :+ con 3
                                       := (n :+ con 2 :* (Q :+ d) :+ Q :+
                                           con 2 :* m :+ con 3) :+ (d :+ m))
                        refl n (negs φ) d (clauses φ))))
  where
  d : ℕ
  d = proj₁ (split-lits φ)

netlist-length-bound : (φ : CNF n) → length (netlist φ) ≤ 12 * ‖ φ ‖ + 5
netlist-length-bound φ =
  subst (_≤ 12 * ‖ φ ‖ + 5) (sym (netlist-length φ))
        (≤-via (4 * d + 10 * clauses φ)
          (subst (λ L → 12 * (L + clauses φ) + 5 ≡
                        (8 * L + 4 * negs φ + 2 * clauses φ + 5) +
                        (4 * d + 10 * clauses φ))
                 (proj₂ (split-lits φ))
                 (solve 3 (λ Q d m → con 12 :* ((Q :+ d) :+ m) :+ con 5
                                     := (con 8 :* (Q :+ d) :+ con 4 :* Q :+
                                         con 2 :* m :+ con 5) :+
                                        (con 4 :* d :+ con 10 :* m))
                        refl (negs φ) d (clauses φ))))
  where
  d : ℕ
  d = proj₁ (split-lits φ)
