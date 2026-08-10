------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal form for the cyclic groups ℤ/Nℤ: a word is normalised by
-- counting its generators, modulo the order.  The normal forms are ℕ
-- at order 0 (where the presented monoid is free) and Fin N at order N.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Cyclic.Normalization where

open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ ; inject₁)
open import Data.Fin.Induction using (<-weakInduction)
open import Data.Fin.Properties
  using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
open import Data.Nat using (ℕ ; zero ; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; module ≡-Reasoning)
open import Relation.Nullary.Negation.Core using (contradiction)

import Data.Nat.Properties as NP
import Relation.Binary.Reasoning.Setoid as SR

import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
open import Notations
import Presentation.Base as PB
import Presentation.Properties as PP
open import Word.Base hiding (wfoldl)

open NFBase using (NormalFormInjective ; NormalForm)

------------------------------------------------------------------------
-- Generators and relation

open import Examples.Groups.Cyclic.Syntactics public

------------------------------------------------------------------------
-- Successor modulo N

-- The successor of the largest element wraps around to zero.
sucN : ∀ {N} → Fin N → Fin N
sucN {₁₊ zero} zero   = zero
sucN {₂₊ N}    zero   = ₁₊ zero
sucN {₂₊ N}    (₁₊ f) with sucN {₁₊ N} f
... | zero  = zero
... | ₁₊ ih = ₂₊ ih

-- Below the top, sucN is the Fin successor.
sucN-inject₁ : ∀ {N} (x : Fin N) → sucN (inject₁ x) ≡ ₁₊ x
sucN-inject₁ {₁₊ N} zero   = Eq.refl
sucN-inject₁ {₂₊ N} (₁₊ x) rewrite sucN-inject₁ {₁₊ N} x = Eq.refl

-- If sucN does not wrap around then it steps the underlying numeral.
sucN≡suc⇒toℕ≡toℕ : ∀ {N} (x : Fin (₁₊ N)) (h : Fin N) →
                   sucN x ≡ ₁₊ h → toℕ x ≡ toℕ h
sucN≡suc⇒toℕ≡toℕ {₁₊ N} zero    zero   eq = Eq.refl
sucN≡suc⇒toℕ≡toℕ {₁₊ N} (₁₊ x) zero   eq with sucN x
sucN≡suc⇒toℕ≡toℕ {₁₊ N} (₁₊ x) zero   () | zero
sucN≡suc⇒toℕ≡toℕ {₁₊ N} (₁₊ x) zero   () | ₁₊ _
sucN≡suc⇒toℕ≡toℕ {₁₊ N} (₁₊ x) (₁₊ h) eq with sucN x in eqx
... | ₁₊ _ =
  Eq.cong ₁₊ (sucN≡suc⇒toℕ≡toℕ x h (Eq.trans eqx (suc-injective eq)))

-- sucN wraps around exactly at the top element.
sucN≡zero⇒toℕ≡N : ∀ {N} (x : Fin (suc N)) → sucN x ≡ zero → toℕ x ≡ N
sucN≡zero⇒toℕ≡N {zero}  zero   eq = Eq.refl
sucN≡zero⇒toℕ≡N {₁₊ N} (₁₊ x) eq with sucN x in eqx
... | zero = Eq.cong ₁₊ (sucN≡zero⇒toℕ≡N x eqx)

toℕ≡N⇒sucN≡zero : ∀ {N} (x : Fin (suc N)) → toℕ x ≡ N → sucN x ≡ zero
toℕ≡N⇒sucN≡zero {zero}  zero       eq = Eq.refl
toℕ≡N⇒sucN≡zero {₁₊ N} zero          = λ ()
toℕ≡N⇒sucN≡zero {₁₊ N} (₁₊ x) hyp
  rewrite toℕ≡N⇒sucN≡zero x (NP.suc-injective hyp) = Eq.refl

------------------------------------------------------------------------
-- Normal forms

-- The normal-form set: ℕ for the free monoid (N = 0), and Fin N for
-- the cyclic group of order N.
NF : ℕ → Set
NF zero   = ℕ
NF (₁₊ N) = Fin (₁₊ N)

-- Successor on normal forms.
succ : ∀ {N} → NF N → NF N
succ {zero}  = suc
succ {₁₊ N} = sucN

-- The normal form of the empty word.
z : ∀ {N} → NF N
z {zero}  = zero
z {₁₊ N} = zero

-- Interpret a normal form as a word: the generator raised to the
-- corresponding power.
[_] : ∀ {N} → NF N → Word X
[_] {zero}  nf = T ^' nf
[_] {₁₊ N} nf = T ^' toℕ nf

-- The zero normal form is interpreted as the empty word.
[z]=ε : ∀ {N} → [_] {N} z ≡ ε
[z]=ε {zero}  = Eq.refl
[z]=ε {₁₊ N} = Eq.refl

------------------------------------------------------------------------
-- Normalising a word

-- Iterate a step function over a word, once per generator.  This is a
-- specialised left fold: since there is only one generator, the step
-- function ignores which generator was read.  It shadows
-- Word.Base.wfoldl, which is hidden in the import above.
wfoldl : ∀ {N} → (NF N → NF N) → (NF N → Word X → NF N)
wfoldl step c [ x ]ʷ  = step c
wfoldl step c ε       = c
wfoldl step c (w • v) = wfoldl step (wfoldl step c w) v

-- The normal form of a word: count its generators from zero.
f : ∀ {N} → Word X → NF N
f = wfoldl succ z

-- The section: a normal form denotes the corresponding power of T.
g : ∀ {N} → NF N → Word X
g = [_]

-- Folding commutes with a step taken before the fold.
wfoldl-succ-comm : ∀ {N} (c : Fin (₁₊ N)) w →
                   wfoldl succ (succ c) w ≡ succ (wfoldl succ c w)
wfoldl-succ-comm c [ x ]ʷ  = Eq.refl
wfoldl-succ-comm c ε       = Eq.refl
wfoldl-succ-comm c (w • v) =
  Eq.trans (Eq.cong (λ u → wfoldl sucN u v) (wfoldl-succ-comm c w))
           (wfoldl-succ-comm (wfoldl sucN c w) v)

------------------------------------------------------------------------
-- The fold is a section of the interpretation

-- Reading one more generator is appending one more T, up to _≈_.
succ-sound : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
             ∀ c → ([ c ] • T) ≈ [ succ {N} c ]
succ-sound {zero}    zero   = PB.left-unit
succ-sound {zero}    (₁₊ c) = PB.refl
succ-sound {₁₊ zero} zero   = PB.trans PB.left-unit (PB.axiom order)
succ-sound {₂₊ N}    zero   = PB.left-unit
succ-sound {₂₊ N}    (₁₊ c) with succ c in eqc
... | zero  rewrite sucN≡zero⇒toℕ≡N c eqc      = PB.axiom order
... | ₁₊ h rewrite sucN≡suc⇒toℕ≡toℕ c h eqc  = PB.refl

-- Folding a word into an accumulator is appending it, up to _≈_.
wfoldl-sound : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
               ∀ (step : NF N → NF N)
                 (step-sound : ∀ c → ([ c ] • T) ≈ [ step c ])
                 (c : NF N) (w : Word X) →
               [ wfoldl step c w ] ≈ ([ c ] • w)
wfoldl-sound step step-sound c [ x ]ʷ = PB.sym (step-sound c)
wfoldl-sound step step-sound c ε      = PB.sym PB.right-unit
wfoldl-sound {N} step step-sound c (w • v) = PB.sym claim
  where
  open PB (pres N)
  open PP (pres N)
  open SR word-setoid

  c' : NF N
  c' = wfoldl step c w

  fold-w : [ c' ] ≈ ([ c ] • w)
  fold-w = wfoldl-sound step step-sound c w

  fold-v : [ wfoldl step c' v ] ≈ ([ c' ] • v)
  fold-v = wfoldl-sound step step-sound c' v

  claim : [ c ] • (w • v) ≈ [ wfoldl step c (w • v) ]
  claim = begin
    [ c ] • (w • v)      ≈⟨ sym assoc ⟩
    ([ c ] • w) • v      ≈⟨ cleft (sym fold-w) ⟩
    [ c' ] • v           ≈⟨ sym fold-v ⟩
    [ wfoldl step c' v ] ∎

-- The normal form of a word is congruent to the word itself.
g∘f≈id : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
         ∀ {w} → g {N} (f {N} w) ≈ w
g∘f≈id {N} {w} = begin
  g {N} (f {N} w)         ≈⟨ refl ⟩
  g {N} (wfoldl succ z w) ≈⟨ wfoldl-sound succ succ-sound z w ⟩
  g {N} z • w             ≈⟨ cleft (refl' ([z]=ε {N})) ⟩
  ε • w                   ≈⟨ left-unit ⟩
  w                       ∎
  where
  open PB (pres N)
  open PP (pres N)
  open SR word-setoid

------------------------------------------------------------------------
-- The fold is a retraction of the interpretation

f∘g : ∀ {N} → NF N → NF N
f∘g = f ∘ g

f∘g≗id : ∀ {N} (x : Fin (₁₊ N)) → f∘g x ≡ x
f∘g≗id {zero}       zero = Eq.refl
f∘g≗id {N@(₁₊ N')} =
  <-weakInduction (λ (x : Fin (₁₊ N)) → f∘g x ≡ x) Eq.refl (step N)
  where
  step : ∀ N (i : Fin N) →
         f∘g (inject₁ i) ≡ inject₁ i → f∘g (₁₊ i) ≡ ₁₊ i
  step (₁₊ zero) zero   hyp = Eq.refl
  step (₂₊ N)    zero   hyp = Eq.refl
  step (₂₊ N)    (₁₊ i) hyp with sucN (inject₁ i) in eqi
  ... | zero =
    contradiction (Eq.trans (Eq.sym (sucN-inject₁ i)) eqi) (λ ())
  ... | ₁₊ ii rewrite toℕ-inject₁ i | hyp | eqi =
    Eq.sym (Eq.cong ₁₊ top)
    where
    top : ₁₊ i ≡ ₁₊ ii
    top = Eq.trans (Eq.sym (sucN-inject₁ i)) eqi

------------------------------------------------------------------------
-- The fold respects the order axiom

-- One full turn from the top element returns to zero.
sucN-f≡zero : ∀ {N} (x : Fin (₁₊ N)) →
              toℕ x ≡ N → sucN (f {₁₊ N} [ x ]) ≡ zero
sucN-f≡zero {N} x eq = toℕ≡N⇒sucN≡zero (f {₁₊ N} [ x ])
  (Eq.trans (Eq.cong toℕ (f∘g≗id x)) eq)

f-order : ∀ {N} → f {₁₊ N} (T ^' (₁₊ N)) ≡ zero
f-order {N} = Eq.trans (unfold N) (sucN-f≡zero (fromℕ N) (toℕ-fromℕ N))
  where
  unfold : ∀ N → f {₁₊ N} (T ^' (₁₊ N)) ≡ sucN (f {₁₊ N} [ fromℕ N ])
  unfold zero                       = Eq.refl
  unfold (₁₊ N) rewrite toℕ-fromℕ N = Eq.refl

-- A full turn from any accumulator returns to that accumulator.
wfoldl-order : ∀ {N} (c : Fin (₁₊ N)) → wfoldl sucN c (T ^' (₁₊ N)) ≡ c
wfoldl-order {N} = <-weakInduction
  (λ (c : Fin (₁₊ N)) → wfoldl sucN c (T ^' (₁₊ N)) ≡ c)
  f-order (step N)
  where
  step : ∀ N (i : Fin N) →
         wfoldl sucN (inject₁ i) (T ^' ₁₊ N) ≡ inject₁ i →
         wfoldl sucN (₁₊ i) (T ^' ₁₊ N) ≡ ₁₊ i
  step N i ih = begin
    wfoldl sucN (₁₊ i) (T ^' ₁₊ N)
      ≡⟨ Eq.cong (λ u → wfoldl sucN u (T ^' ₁₊ N))
                 (Eq.sym (sucN-inject₁ i)) ⟩
    wfoldl sucN (sucN (inject₁ i)) (T ^' ₁₊ N)
      ≡⟨ wfoldl-succ-comm (inject₁ i) (T ^' ₁₊ N) ⟩
    sucN (wfoldl sucN (inject₁ i) (T ^' ₁₊ N))
      ≡⟨ Eq.cong sucN ih ⟩
    sucN (inject₁ i)
      ≡⟨ sucN-inject₁ i ⟩
    ₁₊ i ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- The fold respects the congruence

wfoldl-cong : ∀ {N} {w v} (c : NF N) → PB._≈_ (pres N) w v →
              wfoldl succ c w ≡ wfoldl succ c v
wfoldl-cong c PB.refl          = Eq.refl
wfoldl-cong c (PB.sym p)       = Eq.sym (wfoldl-cong c p)
wfoldl-cong c (PB.trans p q)   =
  Eq.trans (wfoldl-cong c p) (wfoldl-cong c q)
wfoldl-cong c (PB.cong p q)
  rewrite wfoldl-cong c p      = wfoldl-cong _ q
wfoldl-cong c PB.assoc         = Eq.refl
wfoldl-cong c PB.left-unit     = Eq.refl
wfoldl-cong c PB.right-unit    = Eq.refl
wfoldl-cong {zero}  c (PB.axiom order) = Eq.refl
wfoldl-cong {₁₊ N} c (PB.axiom order) = wfoldl-order c

f-cong : ∀ {N} {w v} → PB._≈_ (pres N) w v → f {N} w ≡ f {N} v
f-cong = wfoldl-cong z

------------------------------------------------------------------------
-- The normal form

nfp' : (n : ℕ) → NormalForm (pres n) (NF n)
nfp' n = record
  { rightInverse = record
      { to        = f
      ; from      = g
      ; to-cong   = f-cong
      ; from-cong = λ { Eq.refl → refl }
      ; inverseʳ  = λ { Eq.refl → g∘f≈id }
      }
  }
  where open PB (pres n) using (refl)

nfp : (n : ℕ) → NormalFormInjective (pres n) (NF n)
nfp n = SNF.NormalForm.normalFormInjective (nfp' n)
