------------------------------------------------------------------------
-- Presentations of groups
--
-- A circuit under two controls, as vector operators: exchanging the two
-- control wires does not change it.
--
-- ctrl (ctrl C) acts by the operator of C on the block where bits 0
-- and 1 are both set, and by the identity on the other three
-- (`ctrl₂-block`); the swap of wires 0 1 exchanges the two bits of the
-- blocks (SwapBlocks.swap-conj), and that function of them is symmetric.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.DoubleSem where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base using (ℕ ; suc ; _^_ ; _*_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (_•_)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-cong ; parallel-id)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating)
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ ; interpret)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSem using (ctrl-sem)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (Op ; ctrlA)
open import Examples.Groups.CCX+HH.NaturalP.SwapBlocks using (block₂ ; swap-conj)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
  using (quantum ; swap ; swap-correct)
open import Examples.Groups.CCX+HH.GeneralN.ActionSemantics using (action⇒matrix)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Operators

private
  -- G where both bits are set, the identity elsewhere.
  both : ∀ k → Op (2 ^ k) → Bool → Bool → Op (2 ^ k)
  both k G true  true  = G
  both k G true  false = λ x → x
  both k G false true  = λ x → x
  both k G false false = λ x → x

  both-sym : ∀ k (G : Op (2 ^ k)) a b x → both k G b a x ≡ both k G a b x
  both-sym k G true  true  x = refl
  both-sym k G true  false x = refl
  both-sym k G false true  x = refl
  both-sym k G false false x = refl

  ctrl₂-block : ∀ k (G : Op (2 ^ k)) v →
    ctrlA (2 * 2 ^ k) (ctrlA (2 ^ k) G) v ≡ block₂ k (both k G) v
  ctrl₂-block k G v = sym
    (parallel-cong (alternating (2 * 2 ^ k))
      {f = parallel (alternating (2 ^ k)) (λ x → x) (λ x → x)} {f′ = λ x → x}
      {g = ctrlA (2 ^ k) G} {g′ = ctrlA (2 ^ k) G}
      (parallel-id (alternating (2 ^ k))) (λ _ → refl) v)

  block₂-cong : ∀ k {f g : Bool → Bool → Op (2 ^ k)} →
    (∀ a b x → f a b x ≡ g a b x) → ∀ v → block₂ k f v ≡ block₂ k g v
  block₂-cong k e v =
    parallel-cong (alternating (2 * 2 ^ k))
      (parallel-cong (alternating (2 ^ k)) (e false false) (e false true))
      (parallel-cong (alternating (2 ^ k)) (e true false) (e true true)) v

-- Exchanging the two control bits.
ctrl₂-swap : ∀ k (G : Op (2 ^ k)) v →
  swap k (ctrlA (2 * 2 ^ k) (ctrlA (2 ^ k) G) (swap k v)) ≡
  ctrlA (2 * 2 ^ k) (ctrlA (2 ^ k) G) v
ctrl₂-swap k G v =
  trans (cong (swap k) (ctrl₂-block k G (swap k v)))
  (trans (swap-conj k (both k G) v)
  (trans (block₂-cong k {f = λ a b → both k G b a} {g = both k G}
            (λ a b x → both-sym k G a b x) v)
    (sym (ctrl₂-block k G v))))

------------------------------------------------------------------------
-- Circuits

private
  -- An equation of actions, as a record, so that the words of action⇒matrix
  -- are solved from signatures (see SpareSem).
  record QEq {k} (u v : H.Circuit k) : Set where
    field eq : ∀ x → quantum u x ≡ quantum v x

  am : ∀ {k} {u v : H.Circuit k} → QEq u v → Q.interpret u ≡ Q.interpret v
  am {u = u} {v} h = action⇒matrix {u = u} {v = v} (QEq.eq h)

  -- W acts by G under two controls.
  record Ctrl₂ {k} (W : H.Circuit (suc (suc k))) (G : Op (2 ^ k)) : Set where
    field eq : ∀ x → quantum W x ≡ ctrlA (2 * 2 ^ k) (ctrlA (2 ^ k) G) x

  -- Over a variable word W, so that the swap's action is never compared
  -- with another spelling of it.
  conj-swap : ∀ {k} {W : H.Circuit (suc (suc k))} {G : Op (2 ^ k)} →
    Ctrl₂ W G → QEq (H.Ex {k} • (W • H.Ex {k})) W
  conj-swap {k} {W} {G} h = record { eq = λ v →
    trans (swap-correct k (quantum W (quantum (H.Ex {k}) v)))
    (trans (cong (λ y → swap k (quantum W y)) (swap-correct k v))
    (trans (cong (swap k) (Ctrl₂.eq h (swap k v)))
    (trans (ctrl₂-swap k G v)
      (sym (Ctrl₂.eq h v))))) }

  D2 : (C : P.Circuit (₄₊ n)) → Ctrl₂ (τ (ctrl (ctrl C))) (quantum (τ C))
  D2 {n} C = record { eq = λ x →
    trans (ctrl-sem (ctrl C) x)
      (parallel-cong (alternating (2 * 2 ^ ₄₊ n))
        {f = λ y → y} {f′ = λ y → y}
        {g = quantum (τ (ctrl C))} {g′ = ctrlA (2 ^ ₄₊ n) (quantum (τ C))}
        (λ _ → refl) (ctrl-sem C) x) }

  dact : (C : P.Circuit (₄₊ n)) →
    QEq (H.Ex {₄₊ n} • (τ (ctrl (ctrl C)) • H.Ex {₄₊ n})) (τ (ctrl (ctrl C)))
  dact C = conj-swap (D2 C)

  respell : (C : P.Circuit (₄₊ n)) →
    τ (P.σ • (ctrl (ctrl C) • P.σ)) ≡ H.Ex {₄₊ n} • (τ (ctrl (ctrl C)) • H.Ex {₄₊ n})
  respell C = refl

  respell-mat : (C : P.Circuit (₄₊ n)) →
    Q.interpret (τ (P.σ • (ctrl (ctrl C) • P.σ))) ≡
    Q.interpret (H.Ex {₄₊ n} • (τ (ctrl (ctrl C)) • H.Ex {₄₊ n}))
  respell-mat C = cong Q.interpret (respell C)

  mat : (C : P.Circuit (₄₊ n)) →
    Q.interpret (H.Ex {₄₊ n} • (τ (ctrl (ctrl C)) • H.Ex {₄₊ n})) ≡
    Q.interpret (τ (ctrl (ctrl C)))
  mat C = am (dact C)

-- The two controls of ctrl (ctrl C) exchange.
ctrl₂-sym-sem : (C : P.Circuit (₄₊ n)) →
  interpret (P.σ • (ctrl (ctrl C) • P.σ)) ≡ interpret (ctrl (ctrl C))
ctrl₂-sym-sem C = trans (respell-mat C) (mat C)
