------------------------------------------------------------------------
-- Presentations of groups
--
-- The Maslov decomposition of the n-bit Toffoli gate: layouts, and the
-- function it computes (Amy, QPL 2018, section 5.2)
--
-- Section 5.2's second implementation of
--
--    Toffoli_n : |x₁ x₂ … x_n⟩ ↦ |x₁ x₂ … (x_n ⊕ x₁ x₂ ⋯ x_(n−1))⟩
--
-- is "the Maslov decomposition [23] using relative phase Toffolis and
-- ⌈(n − 3)/2⌉ ancillas".  This module is its Boolean half: the wires,
-- the permutation of basis states the circuit computes on every input,
-- and the proof that on the inputs whose ancillas read 0 that
-- permutation is Toffoli_n and returns the ancillas to 0.  The circuit
-- and the theorems about its path-sum are in PathSum.Maslov, whose
-- header explains the plan.
--
-- The wires are given by a Layout N m: m + 1 controls, a target and
-- ⌊m/2⌋ ancillas among N wires, all distinct.  So n = m + 2 is the
-- number of wires Toffoli_n acts on, and ⌊m/2⌋ = ⌈(n − 3)/2⌉.  The
-- construction is by recursion on m:
--
--    m = 0:      one control: t ⊕= c₀ (a CNOT);
--    m = 1:      two controls: t ⊕= c₀ c₁ (a Toffoli gate);
--    m + 2:      a₀ ⊕= c₀ c₁ c₂ (a Toffoli-4 gate, three controls),
--                then the construction on the layout whose controls
--                are a₀, c₃, …, c_(m+2) and whose ancillas are a₁, …
--                (inner), then a₀ ⊕= c₀ c₁ c₂ again.
--
-- Each Toffoli-4 gate replaces three controls by one ancilla, so every
-- ancilla absorbs two controls: with ⌊m/2⌋ ancillas the m + 1
-- controls come down to one (m even, n even: a CNOT onto the target)
-- or to two (m odd, n odd: a Toffoli gate onto the target).  The
-- function applyᴹ L is the composite of the gates' Boolean functions,
-- on every input.  It changes only the target and the ancillas
-- (applyᴹ-off; so the inner construction leaves the four wires of the
-- gates around it alone, inner-c₀ … inner-a₀).  On the clean inputs --
-- every ancilla 0 -- it is Toffoli_n (applyᴹ-correct, by induction on
-- m as for the V-chain of PathSum.ToffoliN.Chain: the first gate sets
-- a₀ to x_c₀ x_c₁ x_c₂, the inner construction flips the target by the
-- conjunction of that and the remaining controls, and the last gate
-- resets a₀), which leaves the ancillas 0 (toffoliᴹ-anc).  Off the
-- clean inputs it is some other permutation (at n = 4, from the input
-- whose only 1 is on the ancilla, it flips the target:
-- applyᴹ-unclean), which is why the theorem is stated on those inputs,
-- as the paper means it.
--
-- The specification is the classical path-sum that flips the target
-- by the lift of the conjunction x_c₀ x_c₁ ⋯ x_cm (toffoliᶜˢ, on any
-- controls and target; fun-toffoliᶜˢ).  It is the specification of
-- the standard decomposition, PathSum.ToffoliN.Chain.toffoliₙˢ, as a
-- function of the controls and the target (toffoliₙ-≡, toffoliₙˢ-≡);
-- toffoliᴹ, toffoliᴹᵉ and toffoliᴹˢ are it on a layout.  Finally the
-- paper's layout: for every n ≥ 3, on n + ⌈(n − 3)/2⌉ wires, the
-- controls are wires 0 … n − 2, the target is wire n − 1 and the
-- ancillas are the ⌈(n − 3)/2⌉ wires from n on (standardᴹ,
-- standardᴹ-ctl, standardᴹ-tgt, standardᴹ-anc).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Maslov.Chain (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Bool.Properties using (∧-assoc; ∧-identityʳ; xor-same)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using
  (Fin; zero; suc; toℕ; fromℕ; inject₁; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Nat.Base using (_+_; _∸_; _≤_; z≤n; s≤s; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin

open import PathSum.Ancillas M₀ using (Clean)
open import PathSum.Assign using
  (_[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-comm; ≔-cong; ≔-self)
open import PathSum.Base using (PathSum)
open import PathSum.Classical M₀ using
  (classical; fun; setWire; fun-setWireᵉ; none)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Maslov.Gate4 M₀ using (toffoli₄)
open import PathSum.Polynomial using (x[_])
open import PathSum.Polynomial.Boolean using (BExp; var; _⊕ᵉ_; liftᵉ)
open import PathSum.Toffoli M₀ using (toffoli)

import PathSum.ToffoliN.Chain M₀ as Chain
open Chain using (⋀; ⋀-cong; ⋀ᵉ; ⟦⋀ᵉ⟧)

private
  variable
    N m j k : ℕ


------------------------------------------------------------------------
-- Layouts

-- m + 1 controls, a target and ⌊m/2⌋ ancillas, all distinct.

record Layout (N m : ℕ) : Set where
  field
    ctl     : Fin (suc m) → Fin N
    tgt     : Fin N
    anc     : Fin ⌊ m /2⌋ → Fin N
    ctl-inj : ∀ i i′ → ctl i ≡ ctl i′ → i ≡ i′
    anc-inj : ∀ i i′ → anc i ≡ anc i′ → i ≡ i′
    ctl≢tgt : ∀ i → ctl i ≢ tgt
    anc≢tgt : ∀ i → anc i ≢ tgt
    ctl≢anc : ∀ i i′ → ctl i ≢ anc i′

open Layout public

-- With two controls, they differ.

c₀≢c₁ : (L : Layout N (suc m)) → ctl L zero ≢ ctl L (suc zero)
c₀≢c₁ L e = Fin.0≢1+n (ctl-inj L zero (suc zero) e)

-- With three or more, the first gate reads the first three controls
-- and writes the first ancilla.

c₀ c₁ c₂ a₀ : Layout N (suc (suc m)) → Fin N
c₀ L = ctl L zero
c₁ L = ctl L (suc zero)
c₂ L = ctl L (suc (suc zero))
a₀ L = anc L zero

c₀≢a₀ : (L : Layout N (suc (suc m))) → c₀ L ≢ a₀ L
c₀≢a₀ L = ctl≢anc L zero zero

c₁≢a₀ : (L : Layout N (suc (suc m))) → c₁ L ≢ a₀ L
c₁≢a₀ L = ctl≢anc L (suc zero) zero

c₂≢a₀ : (L : Layout N (suc (suc m))) → c₂ L ≢ a₀ L
c₂≢a₀ L = ctl≢anc L (suc (suc zero)) zero

-- The layout of the inner construction: the first ancilla becomes the
-- first control, in place of the first three, and the other ancillas
-- remain.

inner : Layout N (suc (suc m)) → Layout N m
inner {N = N} {m = m} L = record
  { ctl     = ctl′
  ; tgt     = tgt L
  ; anc     = λ i → anc L (suc i)
  ; ctl-inj = ctl′-inj
  ; anc-inj = λ i i′ e → Fin.suc-injective (anc-inj L (suc i) (suc i′) e)
  ; ctl≢tgt = ctl′≢tgt
  ; anc≢tgt = λ i → anc≢tgt L (suc i)
  ; ctl≢anc = ctl′≢anc
  }
  where
  ctl′ : Fin (suc m) → Fin N
  ctl′ zero    = anc L zero
  ctl′ (suc i) = ctl L (suc (suc (suc i)))

  ctl′-inj : ∀ i i′ → ctl′ i ≡ ctl′ i′ → i ≡ i′
  ctl′-inj zero    zero     e = refl
  ctl′-inj zero    (suc i′) e =
    ⊥-elim (ctl≢anc L (suc (suc (suc i′))) zero (sym e))
  ctl′-inj (suc i) zero     e =
    ⊥-elim (ctl≢anc L (suc (suc (suc i))) zero e)
  ctl′-inj (suc i) (suc i′) e =
    cong suc (Fin.suc-injective (Fin.suc-injective (Fin.suc-injective
      (ctl-inj L (suc (suc (suc i))) (suc (suc (suc i′))) e))))

  ctl′≢tgt : ∀ i → ctl′ i ≢ tgt L
  ctl′≢tgt zero    = anc≢tgt L zero
  ctl′≢tgt (suc i) = ctl≢tgt L (suc (suc (suc i)))

  ctl′≢anc : ∀ i i′ → ctl′ i ≢ anc L (suc i′)
  ctl′≢anc zero    i′ e = Fin.0≢1+n (anc-inj L zero (suc i′) e)
  ctl′≢anc (suc i) i′   = ctl≢anc L (suc (suc (suc i))) (suc i′)


------------------------------------------------------------------------
-- The function computed, on every input

-- t ⊕= c₀ with one control, t ⊕= c₀ c₁ with two, and with more the
-- Toffoli-4 function a₀ ⊕= c₀ c₁ c₂ on either side of the inner
-- construction.

applyᴹ : Layout N m → Assign N → Assign N
applyᴹ {m = zero}        L x = x [ tgt L ≔ x (tgt L) xor x (ctl L zero) ]
applyᴹ {m = suc zero}    L x =
  toffoli (ctl L zero) (ctl L (suc zero)) (tgt L) x
applyᴹ {m = suc (suc m)} L x =
  toffoli₄ (c₀ L) (c₁ L) (c₂ L) (a₀ L)
    (applyᴹ (inner L) (toffoli₄ (c₀ L) (c₁ L) (c₂ L) (a₀ L) x))

-- It writes only the target and the ancillas.

applyᴹ-off : (L : Layout N m) (x : Assign N) {w : Fin N} → w ≢ tgt L →
             (∀ i → w ≢ anc L i) → applyᴹ L x w ≡ x w
applyᴹ-off {m = zero}        L x w≢t w≢a = ≔-there x _ w≢t
applyᴹ-off {m = suc zero}    L x w≢t w≢a = ≔-there x _ w≢t
applyᴹ-off {N = N} {m = suc (suc m)} L x w≢t w≢a =
  trans (≔-there y (y (a₀ L) xor ((y (c₀ L) ∧ y (c₁ L)) ∧ y (c₂ L)))
                 (w≢a zero))
    (trans (applyᴹ-off (inner L) x′ w≢t (λ i → w≢a (suc i)))
           (≔-there x (x (a₀ L) xor ((x (c₀ L) ∧ x (c₁ L)) ∧ x (c₂ L)))
                    (w≢a zero)))
  where
  x′ y : Assign N
  x′ = toffoli₄ (c₀ L) (c₁ L) (c₂ L) (a₀ L) x
  y  = applyᴹ (inner L) x′

-- So the inner construction leaves the four wires of the gate around
-- it alone.

inner-c₀ : (L : Layout N (suc (suc m))) (x : Assign N) →
           applyᴹ (inner L) x (c₀ L) ≡ x (c₀ L)
inner-c₀ L x =
  applyᴹ-off (inner L) x (ctl≢tgt L zero) (λ i → ctl≢anc L zero (suc i))

inner-c₁ : (L : Layout N (suc (suc m))) (x : Assign N) →
           applyᴹ (inner L) x (c₁ L) ≡ x (c₁ L)
inner-c₁ L x = applyᴹ-off (inner L) x (ctl≢tgt L (suc zero))
                          (λ i → ctl≢anc L (suc zero) (suc i))

inner-c₂ : (L : Layout N (suc (suc m))) (x : Assign N) →
           applyᴹ (inner L) x (c₂ L) ≡ x (c₂ L)
inner-c₂ L x = applyᴹ-off (inner L) x (ctl≢tgt L (suc (suc zero)))
                          (λ i → ctl≢anc L (suc (suc zero)) (suc i))

inner-a₀ : (L : Layout N (suc (suc m))) (x : Assign N) →
           applyᴹ (inner L) x (a₀ L) ≡ x (a₀ L)
inner-a₀ L x = applyᴹ-off (inner L) x (anc≢tgt L zero)
  (λ i e → Fin.0≢1+n (anc-inj L zero (suc i) e))


------------------------------------------------------------------------
-- The n-bit Toffoli function, on any controls and target

-- The target flipped by the conjunction of the controls
-- (PathSum.ToffoliN.Chain's ⋀), and the classical path-sum whose output
-- on the target is the lift of x_t ⊕ x_c₀ ⋯ x_ck.

toffoliᶜ : (Fin (suc k) → Fin N) → Fin N → Assign N → Assign N
toffoliᶜ c t x = x [ t ≔ x t xor ⋀ (λ i → x (c i)) ]

toffoliᶜᵉ : (Fin (suc k) → Fin N) → Fin N → BExp N 0
toffoliᶜᵉ c t = var x[ t ] ⊕ᵉ ⋀ᵉ c

toffoliᶜˢ : (Fin (suc k) → Fin N) → Fin N → PathSum N 0 0
toffoliᶜˢ c t = classical (setWire t (liftᵉ (toffoliᶜᵉ c t)))

fun-toffoliᶜˢ : (c : Fin (suc k) → Fin N) (t : Fin N) (x : Assign N) →
                ∀ w → fun (setWire t (liftᵉ (toffoliᶜᵉ c t))) x w ≡
                      toffoliᶜ c t x w
fun-toffoliᶜˢ c t x w = trans (fun-setWireᵉ t (toffoliᶜᵉ c t) x w)
  (cong (λ d → (x [ t ≔ x t xor d ]) w) (⟦⋀ᵉ⟧ c x none))

-- These are PathSum.ToffoliN.Chain's specification of the standard
-- decomposition, read off its layouts' controls and target.

toffoliₙ-≡ : (L : Chain.Layout N j) (x : Assign N) →
             Chain.toffoliₙ L x ≡ toffoliᶜ (Chain.ctl L) (Chain.tgt L) x
toffoliₙ-≡ L x = refl

toffoliₙˢ-≡ : (L : Chain.Layout N j) →
              Chain.toffoliₙˢ L ≡ toffoliᶜˢ (Chain.ctl L) (Chain.tgt L)
toffoliₙˢ-≡ L = refl

-- On a layout.

toffoliᴹ : Layout N m → Assign N → Assign N
toffoliᴹ L = toffoliᶜ (ctl L) (tgt L)

toffoliᴹᵉ : Layout N m → BExp N 0
toffoliᴹᵉ L = toffoliᶜᵉ (ctl L) (tgt L)

toffoliᴹˢ : Layout N m → PathSum N 0 0
toffoliᴹˢ L = toffoliᶜˢ (ctl L) (tgt L)

-- It leaves the ancillas as they were.

toffoliᴹ-anc : (L : Layout N m) (x : Assign N) → Clean (anc L) x →
               Clean (anc L) (toffoliᴹ L x)
toffoliᴹ-anc L x cl i = trans (≔-there x _ (anc≢tgt L i)) (cl i)


------------------------------------------------------------------------
-- The function computed, on the clean inputs

-- The conjunction of k bits, true when there are none, so that a
-- conjunction of k + 1 bits is always the first and the rest.

⋀⁰ : (Fin k → Bool) → Bool
⋀⁰ {zero}  f = true
⋀⁰ {suc k} f = ⋀ f

⋀⁰-cong : {f g : Fin k → Bool} → (∀ i → f i ≡ g i) → ⋀⁰ f ≡ ⋀⁰ g
⋀⁰-cong {zero}  h = refl
⋀⁰-cong {suc k} h = ⋀-cong h

⋀-split : (f : Fin (suc k) → Bool) → ⋀ f ≡ f zero ∧ ⋀⁰ (λ i → f (suc i))
⋀-split {zero}  f = sym (∧-identityʳ (f zero))
⋀-split {suc k} f = refl

-- On clean inputs the construction computes Toffoli_n.

applyᴹ-correct : (L : Layout N m) (x : Assign N) → Clean (anc L) x →
                 ∀ w → applyᴹ L x w ≡ toffoliᴹ L x w
applyᴹ-correct {m = zero}     L x cl w = refl
applyᴹ-correct {m = suc zero} L x cl w = refl
applyᴹ-correct {N = N} {m = suc (suc m)} L x cl w = goal
  where
  t : Fin N
  t = tgt L

  a₀≢t : a₀ L ≢ t
  a₀≢t = anc≢tgt L zero

  b v : Bool
  b = (x (c₀ L) ∧ x (c₁ L)) ∧ x (c₂ L)
  v = x t xor ⋀ (λ i → x (ctl L i))

  -- After the first gate a₀ reads x_c₀ x_c₁ x_c₂, and the other wires
  -- are as they were.

  x′ : Assign N
  x′ = toffoli₄ (c₀ L) (c₁ L) (c₂ L) (a₀ L) x

  x′-a₀ : x′ (a₀ L) ≡ b
  x′-a₀ = trans (≔-here x (a₀ L) (x (a₀ L) xor b)) (cong (_xor b) (cl zero))

  x′-there : ∀ {u} → u ≢ a₀ L → x′ u ≡ x u
  x′-there u≢a₀ = ≔-there x (x (a₀ L) xor b) u≢a₀

  cl′ : Clean (anc (inner L)) x′
  cl′ i = trans (x′-there (λ e → Fin.0≢1+n (sym (anc-inj L (suc i) zero e))))
                (cl (suc i))

  -- The inner construction flips the target by a₀ x_c₃ ⋯, which is the
  -- conjunction of all the controls.

  R : Bool
  R = ⋀⁰ (λ i → x (ctl L (suc (suc (suc i)))))

  inner-controls : ⋀ (λ i → x′ (ctl (inner L) i)) ≡ ⋀ (λ i → x (ctl L i))
  inner-controls =
    trans (⋀-split (λ i → x′ (ctl (inner L) i)))
    (trans (cong₂ _∧_ x′-a₀
             (⋀⁰-cong (λ i → x′-there (ctl≢anc L (suc (suc (suc i))) zero))))
    (trans (∧-assoc (x (c₀ L) ∧ x (c₁ L)) (x (c₂ L)) R)
    (trans (∧-assoc (x (c₀ L)) (x (c₁ L)) (x (c₂ L) ∧ R))
           (cong (λ r → x (c₀ L) ∧ (x (c₁ L) ∧ r))
                 (sym (⋀-split (λ i → x (ctl L (suc (suc i))))))))))

  y : Assign N
  y = applyᴹ (inner L) x′

  y≗ : ∀ u → y u ≡ (x′ [ t ≔ v ]) u
  y≗ u = trans (applyᴹ-correct (inner L) x′ cl′ u)
    (cong (λ d → (x′ [ t ≔ d ]) u)
          (cong₂ _xor_ (x′-there (λ e → a₀≢t (sym e))) inner-controls))

  y-off : ∀ {u} → u ≢ t → u ≢ a₀ L → y u ≡ x u
  y-off u≢t u≢a₀ =
    trans (y≗ _) (trans (≔-there x′ v u≢t) (x′-there u≢a₀))

  -- The last gate: a₀ ⊕= x_c₀ x_c₁ x_c₂ returns a₀ to 0.

  y-a₀ : y (a₀ L) ≡ b
  y-a₀ = trans (y≗ (a₀ L)) (trans (≔-there x′ v a₀≢t) x′-a₀)

  reset : y (a₀ L) xor ((y (c₀ L) ∧ y (c₁ L)) ∧ y (c₂ L)) ≡ false
  reset = trans
    (cong₂ _xor_ y-a₀
      (cong₂ _∧_ (cong₂ _∧_ (y-off (ctl≢tgt L zero) (c₀≢a₀ L))
                            (y-off (ctl≢tgt L (suc zero)) (c₁≢a₀ L)))
                 (y-off (ctl≢tgt L (suc (suc zero))) (c₂≢a₀ L))))
    (xor-same b)

  xt-a₀ : false ≡ (x [ t ≔ v ]) (a₀ L)
  xt-a₀ = sym (trans (≔-there x v a₀≢t) (cl zero))

  goal : toffoli₄ (c₀ L) (c₁ L) (c₂ L) (a₀ L) y w ≡ (x [ t ≔ v ]) w
  goal =
    trans (cong (λ d → (y [ a₀ L ≔ d ]) w) reset)
    (trans (≔-cong (a₀ L) false y≗ w)
    (trans (≔-cong (a₀ L) false (≔-comm x (x (a₀ L) xor b) v a₀≢t) w)
    (trans (≔-≔ (x [ t ≔ v ]) (a₀ L) (x (a₀ L) xor b) false w)
    (trans (cong (λ d → ((x [ t ≔ v ]) [ a₀ L ≔ d ]) w) xt-a₀)
           (≔-self (x [ t ≔ v ]) (a₀ L) w)))))

-- The specification computes the same function.

fun-toffoliᴹˢ : (L : Layout N m) (x : Assign N) →
                ∀ w → fun (setWire (tgt L) (liftᵉ (toffoliᴹᵉ L))) x w ≡
                      toffoliᴹ L x w
fun-toffoliᴹˢ L = fun-toffoliᶜˢ (ctl L) (tgt L)


------------------------------------------------------------------------
-- The paper's layout

private
  ↑ˡ≢↑ʳ : ∀ {m n} (i : Fin m) (k : Fin n) → i ↑ˡ n ≢ m ↑ʳ k
  ↑ˡ≢↑ʳ {m} {n} i k e = absurd
    (trans (sym (Fin.splitAt-↑ˡ m i n))
           (trans (cong (splitAt m) e) (Fin.splitAt-↑ʳ m n k)))
    where
    absurd : ∀ {A : Set} → inj₁ i ≡ inj₂ k → A
    absurd ()

-- For m + 1 controls, on m + 2 + ⌊m/2⌋ wires: the controls are wires
-- 0 … m, the target is wire m + 1, the ancillas are the wires from
-- m + 2 on.

layout : (m : ℕ) → Layout (suc (suc m) + ⌊ m /2⌋) m
layout m = record
  { ctl     = λ i → inject₁ i ↑ˡ ⌊ m /2⌋
  ; tgt     = fromℕ (suc m) ↑ˡ ⌊ m /2⌋
  ; anc     = λ i → suc (suc m) ↑ʳ i
  ; ctl-inj = λ i i′ e → Fin.inject₁-injective
                (Fin.↑ˡ-injective ⌊ m /2⌋ (inject₁ i) (inject₁ i′) e)
  ; anc-inj = λ i i′ e → Fin.↑ʳ-injective (suc (suc m)) i i′ e
  ; ctl≢tgt = λ i e → Fin.fromℕ≢inject₁
                (sym (Fin.↑ˡ-injective ⌊ m /2⌋ (inject₁ i) _ e))
  ; anc≢tgt = λ i e → ↑ˡ≢↑ʳ (fromℕ (suc m)) i (sym e)
  ; ctl≢anc = λ i i′ → ↑ˡ≢↑ʳ (inject₁ i) i′
  }

-- For every n ≥ 3, on n + ⌈(n − 3)/2⌉ wires: the controls are wires
-- 0 … n − 2, the target wire n − 1, the ⌈(n − 3)/2⌉ ancillas the
-- wires from n on.  (At n = m + 3 the ⌊(m + 1)/2⌋ ancillas of layout
-- (m + 1) are ⌈m/2⌉ by definition.)

standardᴹ : (n : ℕ) → 3 ≤ n → Layout (n + ⌈ n ∸ 3 /2⌉) (n ∸ 2)
standardᴹ (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) = layout (suc m)

standardᴹ-ctl : (n : ℕ) (p : 3 ≤ n) (i : Fin (suc (n ∸ 2))) →
                toℕ (ctl (standardᴹ n p) i) ≡ toℕ i
standardᴹ-ctl (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) i =
  trans (Fin.toℕ-↑ˡ (inject₁ i) ⌊ suc m /2⌋) (Fin.toℕ-inject₁ i)

standardᴹ-tgt : (n : ℕ) (p : 3 ≤ n) → toℕ (tgt (standardᴹ n p)) ≡ n ∸ 1
standardᴹ-tgt (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) =
  trans (Fin.toℕ-↑ˡ (fromℕ (suc (suc m))) ⌊ suc m /2⌋)
        (Fin.toℕ-fromℕ (suc (suc m)))

standardᴹ-anc : (n : ℕ) (p : 3 ≤ n) (i : Fin ⌊ n ∸ 2 /2⌋) →
                toℕ (anc (standardᴹ n p) i) ≡ n + toℕ i
standardᴹ-anc (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) i =
  Fin.toℕ-↑ʳ (suc (suc (suc m))) i

-- Its ⌊(n − 2)/2⌋ ancillas are the paper's ⌈(n − 3)/2⌉.

standardᴹ-ancillas : (n : ℕ) → 3 ≤ n → ⌊ n ∸ 2 /2⌋ ≡ ⌈ n ∸ 3 /2⌉
standardᴹ-ancillas (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) = refl

-- Off the clean inputs the construction is not Toffoli_n: at n = 4,
-- from the input whose only 1 is on the ancilla, the first gate leaves
-- the ancilla at 1, the CNOT copies it onto the target, and the target
-- ends flipped, where Toffoli_4 leaves it alone (all controls are 0).

applyᴹ-unclean :
  ¬ (∀ x w → applyᴹ (standardᴹ 4 (s≤s (s≤s (s≤s z≤n)))) x w ≡
             toffoliᴹ (standardᴹ 4 (s≤s (s≤s (s≤s z≤n)))) x w)
applyᴹ-unclean h = true≢false (h x₁ (tgt L₄))
  where
  L₄ : Layout (4 + ⌈ 4 ∸ 3 /2⌉) (4 ∸ 2)
  L₄ = standardᴹ 4 (s≤s (s≤s (s≤s z≤n)))

  x₁ : Assign (4 + ⌈ 4 ∸ 3 /2⌉)
  x₁ = (λ _ → false) [ anc L₄ zero ≔ true ]

  true≢false : true ≢ false
  true≢false ()
