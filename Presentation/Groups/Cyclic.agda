------------------------------------------------------------------------
-- Presentations of groups
--
-- Cyclic groups Z/NZ and their normal form
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Presentation.Groups.Cyclic where

open import Data.Fin using (Fin ; zero ; suc ; toℕ ; fromℕ ; inject₁)
open import Data.Fin.Induction using (<-weakInduction)
open import Data.Fin.Properties using (suc-injective ; toℕ-inject₁ ; toℕ-fromℕ)
open import Data.Nat using (ℕ ; zero ; suc)
import Data.Nat.Properties as NP
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR

open import Notations

import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Base as NFBase
open NFBase using (NormalFormWithoutInverse ; NormalForm)
open import Word.Base hiding (wfoldl)

------------------------------------------------------------------------
-- Generators and relation

-- The generating set is a singleton: the only generator is tt.
X = ⊤

-- The word consisting of the single generator.
T : Word X
T = [ tt ]ʷ

-- There is only one relation for a cyclic group: the generator has
-- order N. rel is indexed by the order of the cyclic group.
data rel (N : ℕ) : WRel X where
  order :  rel N (T ^' N) ε

-- pres 0 presents the free monoid ℕ; for N > 0, pres N presents the
-- additive group of the integers modulo N.
pres : ℕ → WRel X
pres N = rel N

------------------------------------------------------------------------
-- Successor modulo N

-- Successor modulo N: the successor of the largest element wraps
-- around to zero.
sucN : ∀ {N} → Fin N → Fin N
sucN {₁₊ zero} zero = zero
sucN {₂₊ N} zero = ₁₊ zero
sucN {₂₊ N} (₁₊ f) with sucN {₁₊ N} f
... | zero = zero
... | ₁₊ ih = ₂₊ ih

------------------------------------------------------------------------
-- Normal form

-- The normal-form set: ℕ for the free monoid (N = 0), and Fin N for
-- the cyclic group of order N.
NF : ℕ → Set
NF zero = ℕ
NF (₁₊ N) = Fin (₁₊ N)

-- Successor on normal forms.
succ : ∀ {N} → NF N → NF N
succ {zero} = suc
succ {₁₊ N} = sucN

-- The normal form of the empty word.
z : ∀ {N} → NF N
z {zero} = zero
z {₁₊ N} = zero

-- Interpret a normal form as a word: the generator raised to the
-- corresponding power.
[_] : ∀ {N} → NF N → Word X
[_] {zero} nf = T ^' nf
[_] {₁₊ N} nf = T ^' toℕ nf

-- The zero normal form is interpreted as the empty word.
[z]=ε : ∀ {N} → [_] {N} z ≡ ε
[z]=ε {zero} = Eq.refl
[z]=ε {₁₊ N} = Eq.refl

-- Iterate a step function over a word, once per generator. This is a
-- specialised left fold: since there is only one generator, the step
-- function ignores which generator was read. It shadows
-- Word.Base.wfoldl, which is hidden in the import above.
wfoldl : ∀ {N} → (NF N → NF N) → (NF N → Word X → NF N)
wfoldl {N} succ c [ x ]ʷ = succ c
wfoldl {N} succ c ε = c
wfoldl {N} succ c (w • w₁) = wfoldl {N} succ (wfoldl {N} succ c w) w₁

f : ∀ {N} → Word X → NF N
f {N} = wfoldl {N} succ z

wfoldl-sound : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
  ∀ (succ : NF N → NF N)
    (succ-sound :  ∀ c → ([ c ] • T) ≈ [ succ c ])
    (c : NF N) (w : Word X)
    →
    [ wfoldl succ c w ] ≈ ([ c ] • w)
wfoldl-sound {N} succ succ-sound c [ x ]ʷ = PB._≈_.sym (succ-sound c)
wfoldl-sound {N} succ succ-sound c ε = PB._≈_.sym PB._≈_.right-unit
wfoldl-sound {N} succ succ-sound c (w • v) = _≈_.sym claim
  where
  open PB (pres N)
  open PP (pres N)
  open SR word-setoid  

  claim : [ c ] • (w • v) ≈ [ wfoldl succ c (w • v) ]
  claim = begin
    [ c ] • (w • v) ≈⟨ sym assoc ⟩
    ([ c ] • w) • v ≈⟨ cong (sym (wfoldl-sound {N} succ succ-sound c w)) refl ⟩
    ([ wfoldl succ c w ]) • v ≈⟨ sym (wfoldl-sound {N} succ succ-sound (wfoldl succ c w) v) ⟩
    [ wfoldl succ (wfoldl succ c w) v ] ≈⟨ _≈_.refl ⟩
    [ wfoldl succ c (w • v) ] ∎

wfoldl-succ-comm : ∀ {N} (c : Fin (₁₊ N)) w → wfoldl succ (succ c) w ≡ succ (wfoldl succ c w)
wfoldl-succ-comm c [ x ]ʷ = Eq.refl
wfoldl-succ-comm c ε = Eq.refl
wfoldl-succ-comm c (w • w₁) with wfoldl-succ-comm c w
... | ih with wfoldl-succ-comm ( (wfoldl sucN c w)) w₁
... | ih2 = Eq.trans (Eq.cong (\xx → wfoldl sucN xx w₁) ih) ih2


aux-x=h : ∀ {N} (w : Fin (₁₊ N)) (h : Fin N) → sucN w ≡ ₁₊ h → toℕ w ≡ toℕ h
aux-x=h {₁₊ N} zero zero eq = Eq.refl
aux-x=h {₁₊ N} (₁₊ w) zero eq with sucN w | inspect sucN w
aux-x=h {₁₊ N} (₁₊ w) zero () | zero | [ eqh ]'
aux-x=h {₁₊ N} (₁₊ w) zero () | ₁₊ hyp | [ eqh ]'
aux-x=h {₁₊ N} (₁₊ w) (₁₊ h) eq with sucN w | inspect sucN w
... | ₁₊ hyp | [ eqh ]' with aux-x=h {N} w h (Eq.trans eqh (suc-injective eq))
... | ih = Eq.cong ₁₊ ih

aux-x=N : ∀ {N} (x : Fin (suc (N))) → sucN x ≡ zero → toℕ x ≡ N
aux-x=N {zero} zero eq = Eq.refl
aux-x=N {₁₊ N} (₁₊ x) eq with sucN x | inspect sucN x
... | zero | [ eqh ]' with aux-x=N {N} x eqh
... | ih = Eq.cong ₁₊ ih

sucN-inject₁ : ∀ {N} (x : Fin ((N))) → sucN (inject₁ x) ≡ ₁₊ x
sucN-inject₁ {₁₊ N} zero = Eq.refl
sucN-inject₁ {₂₊ N} (₁₊ x) with sucN-inject₁ {₁₊ N} x
... | ih rewrite (ih) = Eq.refl


aux-sx=0 : ∀ {N} (x : Fin (suc (N))) → toℕ x ≡ N → sucN x ≡ zero
aux-sx=0 {zero} zero eq = Eq.refl
aux-sx=0 {₁₊ N} zero = λ ()
aux-sx=0 {₁₊ N} (₁₊ x) hyp with aux-sx=0 {N} x
... | ih with ih (NP.suc-injective hyp)
... | ih' rewrite ih' = Eq.refl

succ-sound : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
  ∀ c → ([ c ] • T) ≈ [ succ {N} c ]
succ-sound {zero} zero = PB._≈_.left-unit
succ-sound {zero} (₁₊ c) = PB._≈_.refl
succ-sound {₁₊ zero} zero = PB._≈_.trans PB._≈_.left-unit (PB._≈_.axiom order)
succ-sound {₂₊ N} zero = PB._≈_.left-unit
succ-sound {₂₊ N} (₁₊ c) with succ c | inspect succ c
... | zero | [ eqc ]' rewrite aux-x=N c eqc = PB._≈_.axiom order
... | ₁₊ hyp | [ eqc ]' rewrite aux-x=h c hyp eqc = PB._≈_.refl


g : ∀ {N} → NF N → Word X
g = [_]

g∘f≈id : ∀ {N} → let _≈_ = PB._≈_ (pres N) in
  ∀ {w} → g {N} (f {N} w) ≈ w
g∘f≈id {N} {w} = begin
  g {N} (f {N} w) ≈⟨ _≈_.refl ⟩
  g {N} (wfoldl succ z w) ≈⟨ wfoldl-sound succ succ-sound z w ⟩
  g {N} z • w ≈⟨ cong (refl' ([z]=ε {N})) refl ⟩
  ε • w ≈⟨ _≈_.left-unit ⟩
  w ∎
  where
  open PB (pres N)
  open PP (pres N)
  open SR word-setoid  


comm-suc-inject₁ : ∀ {N} → (x : Fin N) → suc (inject₁ x) ≡ inject₁ (₁₊ x)
comm-suc-inject₁ {₁₊ N} x = Eq.refl

fg : ∀ {N} → NF N → NF N
fg = f ∘ g

fg=id : ∀ {N} (x : Fin (₁₊ N)) → fg x ≡ x
fg=id {N@zero} zero = Eq.refl
fg=id {N@(₁₊ N')} = <-weakInduction
  (\(x : Fin (₁₊ N)) → fg x ≡ x)
  Eq.refl
  (claim N)
  where
  claim : ∀ N → (i : Fin N) → fg (inject₁ i) ≡ inject₁ i → fg (₁₊ i) ≡ ₁₊ i
  claim (₁₊ zero) zero hyp = Eq.refl
  claim (₂₊ N) zero hyp = Eq.refl
  claim (₂₊ N) (₁₊ i) hyp with claim (₁₊ N) i (fg=id (inject₁ i))
  claim (₂₊ N) (₁₊ i) hyp | ih with sucN (inject₁ i) in eqi
  claim (₂₊ N) (₁₊ i) hyp | ih | zero rewrite toℕ-inject₁ i | hyp | eqi  with (Eq.trans (Eq.sym (sucN-inject₁ i )) eqi)
  ... | ()
  claim (₂₊ N) (₁₊ i) hyp | ih | ₁₊ ii rewrite toℕ-inject₁ i | hyp | eqi = (Eq.sym (Eq.cong ₁₊ c3))
    where
    c3 : (₁₊ i) ≡ (₁₊ ii)
    c3 = Eq.trans (Eq.sym (sucN-inject₁ i )) eqi


sucN-f≡zero : ∀ {N} (x : Fin (₁₊ N)) → toℕ x ≡ N → sucN (f {₁₊ N} ([ x ])) ≡ zero
sucN-f≡zero {N} x eq = aux-sx=0 ((f {₁₊ N} ([ x ]))) (Eq.trans (Eq.cong toℕ (fg=id x)) eq)

f-order : ∀ {N} → f {₁₊ N} (T ^' (₁₊ N)) ≡ zero
f-order {N} = Eq.trans (c1 N) (sucN-f≡zero (fromℕ N) (toℕ-fromℕ N))
  where
  c1 : ∀ N → f {₁₊ N} (T ^' (₁₊ N)) ≡ sucN (f {₁₊ N} [ fromℕ N ])
  c1 zero = Eq.refl
  c1 (₁₊ N) rewrite toℕ-fromℕ N = Eq.refl


wfoldl-order : ∀ {N} (c : Fin (₁₊ N)) → wfoldl sucN c (T ^' (₁₊ N)) ≡ c
wfoldl-order {N} = <-weakInduction
  (\ (c : Fin (₁₊ N)) → wfoldl sucN c (T ^' (₁₊ N)) ≡ c)
  f-order
  (c1 N)
  where
  c1 : ∀ N → (i : Fin N) → wfoldl sucN (inject₁ i) (T ^' ₁₊ N) ≡ inject₁ i →
    wfoldl sucN (₁₊ i) (T ^' ₁₊ N) ≡ ₁₊ i
  c1 N i ih = begin
    wfoldl sucN (₁₊ i) (T ^' ₁₊ N) ≡⟨ Eq.cong (λ xx → wfoldl sucN xx (T ^' ₁₊ N)) (Eq.sym (sucN-inject₁ i)) ⟩
    wfoldl sucN (sucN (inject₁ i)) (T ^' ₁₊ N) ≡⟨ wfoldl-succ-comm (inject₁ i) (T ^' ₁₊ N) ⟩
    sucN (wfoldl sucN ( (inject₁ i)) (T ^' ₁₊ N)) ≡⟨ Eq.cong sucN ih ⟩
    sucN (inject₁ i) ≡⟨ sucN-inject₁ i ⟩
    ₁₊ i ∎
       where open ≡-Reasoning


wfoldl-cong : ∀ {N} → let _≈_ = PB._≈_ (pres (N)) in

  ∀ {w v} → (c : NF N) → w ≈ v → wfoldl succ c w ≡ wfoldl succ c v

wfoldl-cong {N} {w} {v} c PB.refl = Eq.refl
wfoldl-cong {N} {w} {v} c (PB.sym eq) = Eq.sym (wfoldl-cong c eq)
wfoldl-cong {N} {w} {v} c (PB.trans eq eq₁) = Eq.trans (wfoldl-cong c eq) (wfoldl-cong c eq₁)
wfoldl-cong {N} {w • w'} {v • v'} c (PB.cong eq eq₁) with wfoldl succ c w | wfoldl succ c v | wfoldl-cong {N} {w} {v} c eq
... | c' | c'' | ih rewrite ih = wfoldl-cong {N} {w'} {v'} c'' eq₁
wfoldl-cong {N} {w} {v} c PB.assoc = Eq.refl
wfoldl-cong {N} {w} {v} c PB.left-unit = Eq.refl
wfoldl-cong {N} {w} {v} c PB.right-unit = Eq.refl
wfoldl-cong {zero} {w} {v} c (PB.axiom order) = Eq.refl
wfoldl-cong {₁₊ N} {w} {v} c (PB.axiom order) = wfoldl-order c


f-cong : ∀ {N} → let _≈_ = PB._≈_ (pres (N)) in

  ∀ {w v} → w ≈ v → f {N} w ≡ f {N} v

f-cong {N} {w} {v} = wfoldl-cong z


nfp' : (n : ℕ) → NormalForm (pres n)
nfp' n = record
           { NF = NF n ; nf = f ; nf-cong = f-cong ; inv-nf = g ; inv-nf∘nf=id = g∘f≈id }

nfp : (n : ℕ) → NormalFormWithoutInverse (pres n)
nfp n = NormalForm.hasNormalFormWithoutInverse (nfp' n)


