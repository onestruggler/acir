------------------------------------------------------------------------
-- Presentations of groups
--
-- A complete reduction of any hidden shift path-sum with three
-- Hadamard layers, and its length
--
-- PathSum.HiddenShift.ExistsSymbolic reduces the path-sum of figure
-- 3(b) (Amy, QPL 2018, section 5.2) completely by PathSum.HiddenShift.
-- Exists's three passes of [HH] and [Elim] (PathSum.HiddenShift.
-- MainPasses), run on the labelled machine of PathSum.HiddenShift.
-- Engine.  All that argument reads of the path-sum is that its 3n path
-- variables are three Hadamard layers of n = 2m wires each, numbered as
-- definition 2.9 numbers a circuit's Hadamards -- the third layer's,
-- the second's, the first's, wire w of each at n-1-w (lay₁, lay₂,
-- lay₃) -- that along every path its phase is ½ times the hidden shift
-- parity
--
--    f(y₁ ⊕ s) + y₁·y₂ + f̃(y₂) + y₂·y₃
--
-- (PathSum.HiddenShift.Layout's hs-par) modulo 1, for a shift s that
-- may depend on the input, and that its outputs read the third layer
-- only.  This module proves the reduction for every path-sum with these
-- values (three-layers), so that the circuits of the paper's tool
-- (PathSum.HiddenShift.ToolExists) need only their values.
--
-- It also counts the steps.  Every step of the machine is two rule
-- applications -- [HH] and then [Elim], PathSum.HiddenShift.TrackX's
-- hh-elimˣ, whose chain is literally two steps -- and removes two path
-- variables, so the length of the chain built so far plus the number
-- of path variables left stays the number K the path-sum started with
-- (Inv, step-inv).  The three passes are rerun here carrying that
-- invariant (MainPasses' pass₁, pass₂, pass₃ through Exists's
-- Sweep.all), so the chain ending without path variables has exactly
-- K = 3n steps: lenᶠ, PathSum.Full's length of a chain of figure 2's
-- rules, is K.  (Any chain from K path variables to none has between
-- K/2 and K steps, by PathSum.Full's ⟶ᶠ*-length and
-- ⟶ᶠ*-length-lower; this one has the most, one variable per step.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.ThreeLayers (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using
  (Fin; zero; suc; toℕ; opposite; cast; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (_-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.List.Base using (List)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.CRK.Trace M₀ using (Stream; str; pathOf-str)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Blocks
open import PathSum.HiddenShift.Engine M₀ using (QExp; ⟦_⟧q; QOk)
open import PathSum.HiddenShift.Exists M₀ using (module Sweep)
open import PathSum.HiddenShift.ExistsSymbolic M₀ using
  (labR; posR; labR-posR; posR-labR)
open import PathSum.HiddenShift.Gates M₀ using (Term; sumᵇ; sumᵇ-resp)
open import PathSum.HiddenShift.Layout using (split-inv; hs-par; blocks-par)
open import PathSum.HiddenShift.TrackX M₀ using (Tracksˣ)
open import PathSum.HiddenShift.Walsh using (lhalf; rhalf)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Bind using (odd)

import PathSum.HiddenShift.MainPasses M₀ as MP

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full M using (_⟶ᶠ*_; _◅◅ᶠ_; εᶠ; _◅ᶠ_; lenᶠ)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)


------------------------------------------------------------------------
-- The layers of a path

-- Along the stream of a path, the bit the Hadamard of wire w reads in
-- the first, second and third of three layers of n Hadamards each.

lay₁ lay₂ lay₃ : ∀ n → Stream → Assign n
lay₁ n st w = st (n ℕ+ (n ℕ+ toℕ (opposite w)))
lay₂ n st w = st (n ℕ+ toℕ (opposite w))
lay₃ n st w = st (toℕ (opposite w))


------------------------------------------------------------------------
-- The length of a chain

-- Lengths add along concatenation.

lenᶠ-◅◅ᶠ : ∀ {N k m k′ m′ k″ m″} {ξ : PathSum N k m} {ζ : PathSum N k′ m′}
           {χ : PathSum N k″ m″} (ch : ξ ⟶ᶠ* ζ) (c : ζ ⟶ᶠ* χ) →
           lenᶠ (ch ◅◅ᶠ c) ≡ lenᶠ ch ℕ+ lenᶠ c
lenᶠ-◅◅ᶠ εᶠ        c = refl
lenᶠ-◅◅ᶠ (s ◅ᶠ ss) c = cong suc (lenᶠ-◅◅ᶠ ss c)


------------------------------------------------------------------------
-- The reduction

private
  t≢f : true ≢ false
  t≢f ()

  _≟⊥_ : DecidableEquality ⊥
  () ≟⊥ _

-- The labels: the six blocks, and nothing else.

L : ℕ → Set
L m = Lbl m ⊎ ⊥

module Layered
  {m N : ℕ} (gs : List (Term m)) (sv : Assign N → Assign (m ℕ+ m))
  (qL qR : Fin m → QExp (L m) N)
  (qL-ok : ∀ Ret v u i → QOk Ret v u (qL i))
  (qR-ok : ∀ Ret v u i → QOk Ret v u (qR i))
  (qL-val : ∀ i x Z → ⟦ qL i ⟧q x Z ≡ lhalf {m} (sv x) i)
  (qR-val : ∀ i x Z → ⟦ qR i ⟧q x Z ≡ rhalf {m} (sv x) i)
  (Gw : Fin N → Assign N → Assign (m ℕ+ m) → Bool)
  (Gw-resp : ∀ w x {u u′ : Assign (m ℕ+ m)} → (∀ i → u i ≡ u′ i) →
             Gw w x u ≡ Gw w x u′)
  where

  private
    n : ℕ
    n = m ℕ+ m

  -- The shift halves, the values (phase ½ Fblk of the blocks, outputs
  -- Gw of the third layer) and the fixed values of removed labels.

  sL sR : Assign N → Fin m → Bool
  sL x = lhalf {m} (sv x)
  sR x = rhalf {m} (sv x)

  F : Assign N → (L m → Bool) → Bool
  F x Z = Phase.Fblk (sumᵇ gs) (sumᵇ-resp gs) (sL x) (sR x)
                     (λ ℓ → Z (inj₁ ℓ))

  G : Fin N → Assign N → (L m → Bool) → Bool
  G w x Z = Gw w x (λ i → Gblk i (λ ℓ → Z (inj₁ ℓ)))

  dflt : Assign N → L m → (L m → Bool) → Bool
  dflt x (inj₁ ℓ) Z = Phase.dflt (sumᵇ gs) (sumᵇ-resp gs) (sL x) (sR x) ℓ
                                 (λ ℓ′ → Z (inj₁ ℓ′))
  dflt x (inj₂ ())  Z

  private
    G-main : ∀ x (Z Z′ : L m → Bool) →
             (∀ i → Z (inj₁ (E₃ , i)) ≡ Z′ (inj₁ (E₃ , i))) →
             (∀ i → Z (inj₁ (H₃ , i)) ≡ Z′ (inj₁ (H₃ , i))) →
             ∀ w → G w x Z ≡ G w x Z′
    G-main x Z Z′ hE hH w = Gw-resp w x
      (Gblk-cong {Z = λ ℓ → Z (inj₁ ℓ)} {Z′ = λ ℓ → Z′ (inj₁ ℓ)} hE hH)

  -- The three passes, on any path-sum over K variables.

  module P {K : ℕ} (ξ₀ : PathSum N K K) =
    MP.Passes _≟⊥_ (sumᵇ gs) (sumᵇ-resp gs) sL sR qL qR qL-ok qR-ok
      qL-val qR-val F G dflt (λ _ _ _ → refl) (λ _ _ _ → refl) G-main ξ₀

  ----------------------------------------------------------------------
  -- Counting the steps

  module Count {K : ℕ} (ξ₀ : PathSum N K K) where

    open P ξ₀

    -- The chain so far and the path variables left account for all K.

    Inv : ∀ {Ret} → State Ret → Set
    Inv st = lenᶠ (State.chain st) ℕ+ State.size st ≡ K

    private
      fin0 : Fin zero → ⊥
      fin0 ()

      one : (p q : Fin (suc zero)) → p ≡ q
      one zero zero = refl

      two : ∀ a k → (a ℕ+ 2) ℕ+ k ≡ a ℕ+ suc (suc k)
      two a k = trans (ℕ.+-assoc a 2 k) refl

    -- A step appends [HH] and [Elim] and removes two variables.

    step-inv : ∀ {Ret v u} (st : State Ret) (S : Step Ret v u)
               (Ret′ : L m → Bool) (Rv : Ret′ v ≡ false) (Ru : Ret′ u ≡ false)
               (R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u → Ret′ ℓ ≡ Ret ℓ) →
               Inv st → Inv (step st S Ret′ Rv Ru R′)
    step-inv {v = v} (stage zero ξ lab ρ ch tr rd df fd on ij) S
             Ret′ Rv Ru R′ iv = ⊥-elim (fin0 (proj₁ (fd v (Step.v-on S))))
    step-inv {v = v} {u} (stage (suc zero) ξ lab ρ ch tr rd df fd on ij) S
             Ret′ Rv Ru R′ iv = ⊥-elim (Step.v≢u S
      (trans (sym (proj₂ (fd v (Step.v-on S))))
        (trans (cong lab (one (proj₁ (fd v (Step.v-on S)))
                              (proj₁ (fd u (Step.u-on S)))))
               (proj₂ (fd u (Step.u-on S))))))
    step-inv (stage (suc (suc k)) ξ lab ρ ch tr rd df fd on ij) S
             Ret′ Rv Ru R′ iv =
      trans (cong (_ℕ+ k) (lenᶠ-◅◅ᶠ ch _)) (trans (two (lenᶠ ch) k) iv)

    -- Each pass keeps the count.

    Counted : ((Fin m → Bool) → L m → Bool) → (Fin m → Bool) → Set
    Counted Ret d = Σ (State (Ret d)) Inv

    private
      resp-M₁ : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
                ∀ ℓ → RetM₁ d ℓ ≡ RetM₁ d′ ℓ
      resp-M₁ h (inj₁ ℓ) = Ret₁-resp h ℓ
      resp-M₁ h (inj₂ ())

      resp-M₂ : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
                ∀ ℓ → RetM₂ d ℓ ≡ RetM₂ d′ ℓ
      resp-M₂ h (inj₁ ℓ) = Ret₂-resp h ℓ
      resp-M₂ h (inj₂ ())

      resp-M₃ : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
                ∀ ℓ → RetM₃ d ℓ ≡ RetM₃ d′ ℓ
      resp-M₃ h (inj₁ ℓ) = Ret₃-resp h ℓ
      resp-M₃ h (inj₂ ())

      M₁₂ : ∀ ℓ → RetM₁ (λ _ → true) ℓ ≡ RetM₂ (λ _ → false) ℓ
      M₁₂ (inj₁ ℓ) = Ret₁₂ ℓ
      M₁₂ (inj₂ ())

      M₂₃ : ∀ ℓ → RetM₂ (λ _ → true) ℓ ≡ RetM₃ (λ _ → false) ℓ
      M₂₃ (inj₁ ℓ) = Ret₂₃ ℓ
      M₂₃ (inj₂ ())

      M₃-none : ∀ ℓ → RetM₃ (λ _ → true) ℓ ≡ false
      M₃-none (inj₁ ℓ) = Ret₃-none ℓ
      M₃-none (inj₂ ())

    pass₁-inv : ∀ d i (di : d i ≡ false) (st : State (RetM₁ d)) → Inv st →
                Inv (pass₁ d i di st)
    pass₁-inv d i di st = step-inv st _ _ _ _ _

    pass₂-inv : ∀ d i (di : d i ≡ false) (st : State (RetM₂ d)) → Inv st →
                Inv (pass₂ d i di st)
    pass₂-inv d i di st = step-inv st _ _ _ _ _

    pass₃-inv : ∀ d i (di : d i ≡ false) (st : State (RetM₃ d)) → Inv st →
                Inv (pass₃ d i di st)
    pass₃-inv d i di st = step-inv st _ _ _ _ _

    -- The three passes, counted.

    passesᴸ : Counted RetM₁ (λ _ → false) → Counted RetM₃ (λ _ → true)
    passesᴸ c = third (State-resp M₂₃ (proj₁ c₂) , proj₂ c₂)
      where
      first : Counted RetM₁ (λ _ → false) → Counted RetM₁ (λ _ → true)
      first = Sweep.all (Counted RetM₁)
        (λ h c′ → State-resp (resp-M₁ h) (proj₁ c′) , proj₂ c′)
        (λ d i di c′ → pass₁ d i di (proj₁ c′) ,
                       pass₁-inv d i di (proj₁ c′) (proj₂ c′))

      second : Counted RetM₂ (λ _ → false) → Counted RetM₂ (λ _ → true)
      second = Sweep.all (Counted RetM₂)
        (λ h c′ → State-resp (resp-M₂ h) (proj₁ c′) , proj₂ c′)
        (λ d i di c′ → pass₂ d i di (proj₁ c′) ,
                       pass₂-inv d i di (proj₁ c′) (proj₂ c′))

      third : Counted RetM₃ (λ _ → false) → Counted RetM₃ (λ _ → true)
      third = Sweep.all (Counted RetM₃)
        (λ h c′ → State-resp (resp-M₃ h) (proj₁ c′) , proj₂ c′)
        (λ d i di c′ → pass₃ d i di (proj₁ c′) ,
                       pass₃-inv d i di (proj₁ c′) (proj₂ c′))

      c₁ : Counted RetM₁ (λ _ → true)
      c₁ = first c

      c₂ : Counted RetM₂ (λ _ → true)
      c₂ = second (State-resp M₁₂ (proj₁ c₁) , proj₂ c₁)

    -- No label left: the chain has K steps.

    finishᴸ : ∀ {Ret} (st : State Ret) → (∀ ℓ → Ret ℓ ≡ false) → Inv st →
              Σ (PathSum N 0 0) (λ ζ → Σ (ξ₀ ⟶ᶠ* ζ) (λ ch → lenᶠ ch ≡ K))
    finishᴸ (stage zero ξ lab ρ ch tr rd df fd on ij) none iv =
      ξ , ch , trans (sym (ℕ.+-identityʳ (lenᶠ ch))) iv
    finishᴸ (stage (suc _) ξ lab ρ ch tr rd df fd on ij) none iv =
      ⊥-elim (t≢f (trans (sym (on zero)) (none (lab zero))))

    completeᴸ : (st : State (RetM₁ (λ _ → false))) → Inv st →
                Σ (PathSum N 0 0) (λ ζ → Σ (ξ₀ ⟶ᶠ* ζ) (λ ch → lenᶠ ch ≡ K))
    completeᴸ st iv =
      finishᴸ (proj₁ (passesᴸ (st , iv))) M₃-none (proj₂ (passesᴸ (st , iv)))

  ----------------------------------------------------------------------
  -- The labelled path-sum

  private
    toℕ-↑ʳ↑ʳ : (q : Fin n) → toℕ (n ↑ʳ (n ↑ʳ q)) ≡ n ℕ+ (n ℕ+ toℕ q)
    toℕ-↑ʳ↑ʳ q =
      trans (Fin.toℕ-↑ʳ n (n ↑ʳ q)) (cong (n ℕ+_) (Fin.toℕ-↑ʳ n q))

    toℕ-↑ʳ↑ˡ : (q : Fin n) → toℕ (n ↑ʳ (q ↑ˡ n)) ≡ n ℕ+ toℕ q
    toℕ-↑ʳ↑ˡ q =
      trans (Fin.toℕ-↑ʳ n (q ↑ˡ n)) (cong (n ℕ+_) (Fin.toℕ-↑ˡ q n))

    -- A label is read at its position in definition 2.9's numbering.

    ρ₀ : ∀ {K} → Assign N → Assign K → L m → Bool
    ρ₀ x y (inj₁ ℓ) = str y (toℕ (posR gs ℓ))
    ρ₀ x y (inj₂ ())

    -- The layers' bits are the labelled path's.

    hA : ∀ {K} x (y : Assign K) i →
         lay₁ n (str y) (i ↑ˡ m) ≡ ρ₀ x y (inj₁ (A₁ , i))
    hA x y i = cong (str y) (sym (toℕ-↑ʳ↑ʳ (opposite (i ↑ˡ m))))

    hB : ∀ {K} x (y : Assign K) i →
         lay₁ n (str y) (m ↑ʳ i) ≡ ρ₀ x y (inj₁ (B₁ , i))
    hB x y i = cong (str y) (sym (toℕ-↑ʳ↑ʳ (opposite (m ↑ʳ i))))

    hC : ∀ {K} x (y : Assign K) i →
         lay₂ n (str y) (i ↑ˡ m) ≡ ρ₀ x y (inj₁ (C₂ , i))
    hC x y i = cong (str y) (sym (toℕ-↑ʳ↑ˡ (opposite (i ↑ˡ m))))

    hD : ∀ {K} x (y : Assign K) i →
         lay₂ n (str y) (m ↑ʳ i) ≡ ρ₀ x y (inj₁ (D₂ , i))
    hD x y i = cong (str y) (sym (toℕ-↑ʳ↑ˡ (opposite (m ↑ʳ i))))

    hE : ∀ {K} x (y : Assign K) i →
         lay₃ n (str y) (i ↑ˡ m) ≡ ρ₀ x y (inj₁ (E₃ , i))
    hE x y i =
      cong (str y) (sym (Fin.toℕ-↑ˡ (opposite (i ↑ˡ m)) (n ℕ+ n)))

    hH : ∀ {K} x (y : Assign K) i →
         lay₃ n (str y) (m ↑ʳ i) ≡ ρ₀ x y (inj₁ (H₃ , i))
    hH x y i =
      cong (str y) (sym (Fin.toℕ-↑ˡ (opposite (m ↑ʳ i)) (n ℕ+ n)))

    -- The third layer is what Gblk reads.

    lay₃-Gblk : ∀ {K} x (y : Assign K) i →
                lay₃ n (str y) i ≡ Gblk i (λ ℓ → ρ₀ x y (inj₁ ℓ))
    lay₃-Gblk x y i = sym (split-inv m m
      (λ j → ρ₀ x y (inj₁ (E₃ , j))) (λ j → ρ₀ x y (inj₁ (H₃ , j)))
      (λ b → b) (lay₃ n (str y)) (λ j → sym (hE x y j))
      (λ j → sym (hH x y j)) i)

  -- Any path-sum over 3n path variables in that numbering, whose
  -- normalisation is its number of path variables, whose phase along a
  -- path is ½ hs-par modulo 1 and whose outputs are Gw of the third
  -- layer, reduces completely by figure 2's rules, in exactly 3n steps.

  three-layers :
    ∀ {k K} (ξ : PathSum N k K) → k ≡ K → (eK : K ≡ n ℕ+ (n ℕ+ n)) →
    (∀ x y → pow M ∣ (eval (phase ξ) x y -
                      ½ * [ hs-par (sumᵇ gs) (sv x) (lay₁ n (str y))
                                   (lay₂ n (str y)) (lay₃ n (str y)) ]ᶻ)) →
    (∀ w x y → odd (eval (out ξ w) x y) ≡ Gw w x (lay₃ n (str y))) →
    Σ (PathSum N 0 0) (λ ζ → Σ (ξ ⟶ᶠ* ζ) (λ ch → lenᶠ ch ≡ K))
  three-layers {K = K} ξ refl eK ph ob =
    Count.completeᴸ ξ
      (P.stage K ξ lab₀ ρ₀ εᶠ tracks₀ reads₀ dflts₀ find₀ only₀ inj₀) refl
    where
    lab₀ : Fin K → L m
    lab₀ p = inj₁ (labR gs (cast eK p))

    reads₀ : ∀ x y p → ρ₀ x y (lab₀ p) ≡ y p
    reads₀ x y p = trans
      (cong (λ t → str y (toℕ t)) (posR-labR gs (cast eK p)))
      (trans (cong (str y) (Fin.toℕ-cast eK p)) (pathOf-str y p))

    dflts₀ : ∀ x y ℓ → P.RetM₁ ξ (λ _ → false) ℓ ≡ false →
             ρ₀ x y ℓ ≡ dflt x ℓ (ρ₀ x y)
    dflts₀ x y (inj₁ ℓ) R = ⊥-elim (t≢f (trans (sym (Ret₁-all ℓ)) R))
    dflts₀ x y (inj₂ ()) R

    find₀ : ∀ ℓ → P.RetM₁ ξ (λ _ → false) ℓ ≡ true →
            Σ (Fin K) (λ p → lab₀ p ≡ ℓ)
    find₀ (inj₁ ℓ) _ = cast (sym eK) (posR gs ℓ) ,
      cong inj₁ (trans (cong (labR gs)
                             (Fin.cast-involutive eK (sym eK) (posR gs ℓ)))
                       (labR-posR gs ℓ))
    find₀ (inj₂ ()) _

    only₀ : ∀ p → P.RetM₁ ξ (λ _ → false) (lab₀ p) ≡ true
    only₀ p = Ret₁-all (labR gs (cast eK p))

    inj₀ : ∀ p q → lab₀ p ≡ lab₀ q → p ≡ q
    inj₀ p q e = trans (sym (Fin.cast-involutive (sym eK) eK p))
      (trans (cong (cast (sym eK)) casts)
             (Fin.cast-involutive (sym eK) eK q))
      where
      casts : cast eK p ≡ cast eK q
      casts = trans (sym (posR-labR gs (cast eK p)))
        (trans (cong (posR gs) (inj₁-injective e))
               (posR-labR gs (cast eK q)))

    tracks₀ : Tracksˣ ξ (λ x y → F x (ρ₀ x y)) (λ w x y → G w x (ρ₀ x y))
    tracks₀ = record { phase-atˣ = phs ; out-atˣ = outs }
      where
      phs : ∀ x y → pow M ∣ (eval (phase ξ) x y - ½ * [ F x (ρ₀ x y) ]ᶻ)
      phs x y = subst (λ b → pow M ∣ (eval (phase ξ) x y - ½ * [ b ]ᶻ))
        (blocks-par (sumᵇ gs) (sumᵇ-resp gs) (sv x) (lay₁ n (str y))
                    (lay₂ n (str y)) (lay₃ n (str y))
                    (λ ℓ → ρ₀ x y (inj₁ ℓ))
                    (hA x y) (hB x y) (hC x y) (hD x y) (hE x y) (hH x y))
        (ph x y)

      outs : ∀ w x y → odd (eval (out ξ w) x y) ≡ G w x (ρ₀ x y)
      outs w x y = trans (ob w x y) (Gw-resp w x (lay₃-Gblk x y))
