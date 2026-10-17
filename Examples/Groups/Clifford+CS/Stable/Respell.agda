------------------------------------------------------------------------
-- Presentations of groups
--
-- The hybrid's block in the other order, at every width
--
-- The hybrid's two-level block on (p , q) is iZ on (q , p) times the
-- hybrid's block on (q , p) (Five.K4's respelling, which needs it only
-- on five wires).  On four wires at (0 , e₀) it is decided on tries
-- (`respell₄`); the white control carries it a wire up at a time, a
-- two-level block under ctrl⁰ being the same block with a 0 on top
-- (`respell-oe`, GadgetSem.ctrl⁰-tl); and conjugating by the bit map of
-- the affine circuit α p q, which sends 0 to p and e₀ to q, moves it to
-- any two distinct states (`respell`, Five.Sem.TL.Bij).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.Respell
  (c4 : Complete 4) (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; _∷ʳ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Notations using (₃₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; up ; _≟_)
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Clifford+CS.Semantics.Control using (ctrl⁰ ; ctrl⁰-~ ; ctrl⁰-∙)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl ; tlOp ; module Bij)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (blkOf ; kpp ; kki ; o₄ ; e₄)
open import Examples.Groups.Clifford+CS.Stable.GadgetSem f4 f5 tr F using (o ; e ; o≡ ; e≡ ; ctrl⁰-tl)
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Stable.AlphaEnds as AlphaEnds
import Examples.Groups.Clifford+CS.Stable.DecSem as DecSem

-- The two blocks.
Ki Pp : ∀ {n} → Bits n → Bits n → Scaled n
Ki p q = tl (blkOf kki) p q
Pp p q = tl (blkOf kpp) p q

private
  -- An identity of four-wire scaled operators, decided on tries.
  by-tries : (k l : ℕ) (M N : Op 4) →
             eqM (scaleM (γ^ l) (matOf M)) (scaleM (γ^ k) (matOf N)) ≡ true → (k , M) ~ (l , N)
  by-tries k l M N eq =
    ≐-trans (·-cong Eq.refl (≐-sym (ix-matOf M)))
      (≐-trans (≐-sym (ix-scaleM (γ^ l) (matOf M)))
        (≐-trans (ix-≡ (eqM-sound _ _ eq))
          (≐-trans (ix-scaleM (γ^ k) (matOf N)) (·-cong Eq.refl (ix-matOf N)))))

respell₄ : Ki o₄ e₄ ~ (Pp e₄ o₄ ∙ Ki e₄ o₄)
respell₄ = by-tries 1 1 (tlOp (blkOf kki) o₄ e₄) (tlOp (blkOf kpp) e₄ o₄ ⊙ tlOp (blkOf kki) e₄ o₄) Eq.refl

-- At 0 and e₀, at every width.
respell-oe : ∀ m → Ki (o m) (e m) ~ (Pp (e m) (o m) ∙ Ki (e m) (o m))
respell-oe zero    = respell₄
respell-oe (suc m) =
  ~-trans {s = Ki o′ e′} {ctrl⁰ (Ki (o m) (e m))} {Pp e′ o′ ∙ Ki e′ o′}
    (~-sym {s = ctrl⁰ (Ki (o m) (e m))} {Ki o′ e′} (ctrl⁰-tl (blkOf kki) (o m) (e m)))
    (~-trans {s = ctrl⁰ (Ki (o m) (e m))} {ctrl⁰ (Pp (e m) (o m) ∙ Ki (e m) (o m))} {Pp e′ o′ ∙ Ki e′ o′}
      (ctrl⁰-~ {s = Ki (o m) (e m)} {Pp (e m) (o m) ∙ Ki (e m) (o m)} (respell-oe m))
      (~-trans {s = ctrl⁰ (Pp (e m) (o m) ∙ Ki (e m) (o m))}
               {ctrl⁰ (Pp (e m) (o m)) ∙ ctrl⁰ (Ki (e m) (o m))} {Pp e′ o′ ∙ Ki e′ o′}
        (ctrl⁰-∙ (Pp (e m) (o m)) (Ki (e m) (o m)))
        (∙-cong {s = ctrl⁰ (Pp (e m) (o m))} {s' = Pp e′ o′} {t = ctrl⁰ (Ki (e m) (o m))} {t' = Ki e′ o′}
          (ctrl⁰-tl (blkOf kpp) (e m) (o m)) (ctrl⁰-tl (blkOf kki) (e m) (o m)))))
  where
  o′ e′ : Bits (₄₊ (suc m))
  o′ = o m ∷ʳ false
  e′ = e m ∷ʳ false

-- At any two distinct states.
respell : ∀ m (p q : Bits (₄₊ m)) → p ≢ q → Ki p q ~ (Pp q p ∙ Ki q p)
respell m p q ne =
  Eq.subst₂ (λ x y → Ki x y ~ (Pp y x ∙ Ki y x)) fo fe
    (~-trans {s = Ki (f (o m)) (f (e m))} {X.conjS (Ki (o m) (e m))} {Pp (f (e m)) (f (o m)) ∙ Ki (f (e m)) (f (o m))}
      (~-sym {s = X.conjS (Ki (o m) (e m))} {Ki (f (o m)) (f (e m))} (X.conj-tl (blkOf kki) (o m) (e m)))
      (~-trans {s = X.conjS (Ki (o m) (e m))} {X.conjS (Pp (e m) (o m) ∙ Ki (e m) (o m))}
               {Pp (f (e m)) (f (o m)) ∙ Ki (f (e m)) (f (o m))}
        (X.conj-cong {s = Ki (o m) (e m)} {Pp (e m) (o m) ∙ Ki (e m) (o m)} (respell-oe m))
        (~-trans {s = X.conjS (Pp (e m) (o m) ∙ Ki (e m) (o m))}
                 {X.conjS (Pp (e m) (o m)) ∙ X.conjS (Ki (e m) (o m))}
                 {Pp (f (e m)) (f (o m)) ∙ Ki (f (e m)) (f (o m))}
          (X.conj-∙ (Pp (e m) (o m)) (Ki (e m) (o m)))
          (∙-cong {s = X.conjS (Pp (e m) (o m))} {s' = Pp (f (e m)) (f (o m))}
                  {t = X.conjS (Ki (e m) (o m))} {t' = Ki (f (e m)) (f (o m))}
            (X.conj-tl (blkOf kpp) (e m) (o m)) (X.conj-tl (blkOf kki) (e m) (o m))))))
  where
  module A  = Theory (₃₊ m)
  module Al = Alpha (₃₊ m)
  module AE = AlphaEnds (₃₊ m)
  module DS = DecSem m c4

  w = Al.α p q

  f g : Bits (₄₊ m) → Bits (₄₊ m)
  f = Al.amapʷ w
  g = Al.amapʷ (A.rev w)

  module X = Bij f g (DS.amapʷ-rev′ w) (DS.amapʷ-rev w)

  fo : f (o m) ≡ p
  fo = Eq.trans (Eq.cong f (o≡ m)) (AE.α-0 p q)

  fe : f (e m) ≡ q
  fe = Eq.trans (Eq.cong f (e≡ m)) (AE.α-e p q ne)
