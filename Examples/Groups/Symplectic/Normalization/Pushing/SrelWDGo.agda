------------------------------------------------------------------------
-- Presentations of groups
--
-- Assembled inj₂ clause bodies of srel-wd, one lemma per dispatcher
-- clause, so the dispatcher itself stays a table of one-liners and the
-- proof bodies are checked once and cached.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDGo
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; _≢_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Empty using (⊥-elim)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿+-comm)

open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (dir-of-DS ; d-of-DS)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDCZ p-2 p-prime

------------------------------------------------------------------------
-- order-S on inj₂ cosets.

orderS-go-0 : ∀ {m} (b : ℤ ₚ) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , b) , lm)) (S ^ p)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , b) , lm)) ε)
orderS-go-0 {m} b lm =
  let open PB ((₁₊ m) QRel,_===_) in
  trans (refl' (ract-S^-resid-a0 b lm p)) (axiom order-S) ,
  Eq.trans (ract-S^-coset (₀ , b) lm p)
           (Eq.cong (λ z → inj₂ (z , lm)) (dDS^p≡id (₀ , b)))

orderS-go-+ : ∀ {m} (a : Fin (₁₊ p-2)) (b : ℤ ₚ) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a , b) , lm)) (S ^ p)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a , b) , lm)) ε)
orderS-go-+ {m} a b lm =
  ract-S^-resid-a+ (₁₊ a , b) lm p (λ ()) ,
  Eq.trans (ract-S^-coset (₁₊ a , b) lm p)
           (Eq.cong (λ z → inj₂ (z , lm)) (dDS^p≡id (₁₊ a , b)))

------------------------------------------------------------------------
-- order-H on inj₂ cosets.

orderH-go-00 : ∀ {m} (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₀) , lm)) (H ^ 4)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₀) , lm)) ε)
orderH-go-00 lm =
  orderH-resid-00 ,
  Eq.cong (λ v → inj₂ (v , lm))
    (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ -0#≈0#) -0#≈0#)
                  (Eq.trans (Eq.cong -_ -0#≈0#) -0#≈0#))

orderH-go-0b : ∀ {m} (b' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₁₊ b') , lm)) (H ^ 4)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₁₊ b') , lm)) ε)
orderH-go-0b b' lm =
  elim-suc (- ₁₊ b') (neg≢0 (₁₊ b') λ ()) λ z eq-z →
  orderH-resid-0b b' z eq-z ,
  Eq.cong (λ v → inj₂ (v , lm))
    (Eq.cong₂ _,_ (Eq.trans (Eq.cong -_ -0#≈0#) -0#≈0#)
                  (-‿involutive (₁₊ b')))

orderH-go-a0 : ∀ {m} (a' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₀) , lm)) (H ^ 4)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₀) , lm)) ε)
orderH-go-a0 a' lm =
  elim-suc (- ₁₊ a') (neg≢0 (₁₊ a') λ ()) λ y eq-y →
  orderH-resid-a0 a' y eq-y ,
  Eq.cong (λ v → inj₂ (v , lm))
    (Eq.cong₂ _,_ (-‿involutive (₁₊ a'))
                  (Eq.trans (Eq.cong -_ -0#≈0#) -0#≈0#))

orderH-go-nn : ∀ {m} (a' b' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) (H ^ 4)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) ε)
orderH-go-nn a' b' lm =
  elim-suc (- ₁₊ a') (neg≢0 (₁₊ a') λ ()) λ y eq-y →
  elim-suc (- ₁₊ b') (neg≢0 (₁₊ b') λ ()) λ z eq-z →
  orderH-resid-nn a' b' y z eq-y eq-z ,
  Eq.cong (λ v → inj₂ (v , lm))
    (Eq.cong₂ _,_ (-‿involutive (₁₊ a')) (-‿involutive (₁₊ b')))

------------------------------------------------------------------------
-- order-SH on inj₂ cosets.

orderSH-go-00 : ∀ {m} (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₀) , lm)) ((S • H) ^ 3)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₀) , lm)) ε)
orderSH-go-00 {m} lm =
  PB.trans (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong₂ _•_ Eq.refl
        (Eq.cong (λ v → Hdir v ↓ᵏ m) (Eq.cong (₀ ,_) -0#≈0#)))
      (Eq.cong₂ _•_
        (Eq.cong (λ v → dir-of-DS v) (Eq.cong₂ _,_ -0#≈0# -0#≈0#))
        (Eq.cong (λ v → Hdir v ↓ᵏ m)
          (Eq.cong (λ v → d-of-DS v) (Eq.cong₂ _,_ -0#≈0# -0#≈0#)))))))
    (PB.axiom order-SH) ,
  Eq.trans (Eq.cong (λ v → inj₂ (Hd' (d-of-DS v) , lm))
             (Eq.cong₂ _,_ -0#≈0# -0#≈0#))
           (Eq.cong (λ v → inj₂ ((₀ , v) , lm)) -0#≈0#)

orderSH-go-0b : ∀ {m} (b' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₁₊ b') , lm)) ((S • H) ^ 3)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₁₊ b') , lm)) ε)
orderSH-go-0b b' lm =
  elim-suc (- ₁₊ b') (neg≢0 (₁₊ b') λ ()) λ z eq-z →
  orderSH-resid-0b b' z eq-z ,
  Eq.trans (Eq.cong (λ v → inj₂ (Hd' (d-of-DS v) , lm))
             (Eq.cong₂ _,_
               (Eq.trans (Eq.cong₂ _+_ -0#≈0# eq-z) (+-0ˡ (₁₊ z))) eq-z))
    (Eq.cong₂ (λ v w → inj₂ ((v , w) , lm)) (+-inverseʳ (₁₊ z))
      (Eq.trans (Eq.cong -_ (Eq.sym eq-z)) (-‿involutive (₁₊ b'))))

orderSH-go-a0 : ∀ {m} (a' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₀) , lm)) ((S • H) ^ 3)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₀) , lm)) ε)
orderSH-go-a0 a' lm =
  elim-suc (- ₁₊ a') (neg≢0 (₁₊ a') λ ()) λ y eq-y →
  orderSH-resid-a0 a' y eq-y ,
  Eq.trans (Eq.cong (λ v → inj₂ (Hd' (d-of-DS (Hd' (d-of-DS (v , - ₁₊ a')))) , lm))
             (Eq.trans (+-0ˡ (- ₁₊ a')) eq-y))
  (Eq.trans (Eq.cong (λ v → inj₂ (Hd' (d-of-DS v) , lm))
             (Eq.cong (_, - ₁₊ y)
               (Eq.trans (Eq.cong (_+ - ₁₊ y) eq-y) (+-inverseʳ (₁₊ y)))))
    (Eq.cong₂ (λ v w → inj₂ ((v , w) , lm))
      (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a'))) -0#≈0#))

orderSH-go-nn : ∀ {m} (a' b' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) ((S • H) ^ 3)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) ε)
orderSH-go-nn a' b' lm =
  elim-suc (- ₁₊ a') (neg≢0 (₁₊ a') λ ()) λ y eq-y →
  elim-suc (- ₁₊ b') (neg≢0 (₁₊ b') λ ()) λ z eq-z →
  elim-fin (₁₊ b' + - ₁₊ a')
    (λ Xeq →
      orderSH-resid-nn0 a' b' y eq-y Xeq ,
      Eq.trans
        (Eq.trans (Eq.cong (λ v → inj₂ (Hd' (d-of-DS (Hd' (d-of-DS v))) , lm))
                    (Eq.cong₂ _,_ Xeq eq-y))
          (Eq.cong₂ (λ v w → inj₂ ((v , w) , lm))
            (Eq.trans (Eq.cong₂ _+_ -0#≈0#
                (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a'))))
              (+-0ˡ (₁₊ a')))
            (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a')))))
        (Eq.sym (Eq.cong (λ v → inj₂ ((₁₊ a' , v) , lm))
          (+-‿cancel (₁₊ b') (₁₊ a') Xeq))))
    (λ w Xeq →
      orderSH-resid-nnw a' b' y z w eq-y eq-z Xeq ,
      Eq.trans (Eq.cong
          (λ v → inj₂ (Hd' (d-of-DS (Hd' (d-of-DS (v , - ₁₊ a')))) , lm)) Xeq)
      (Eq.trans (Eq.cong (λ v → inj₂ (Hd' (d-of-DS v) , lm))
                  (Eq.cong (_, - ₁₊ w) (sndZ-lem a' b' w z Xeq eq-z)))
        (Eq.cong₂ (λ v w' → inj₂ ((v , w') , lm))
          (sndA-lem a' b' w z Xeq eq-z)
          (Eq.trans (Eq.cong -_ (Eq.sym eq-z)) (-‿involutive (₁₊ b'))))))

------------------------------------------------------------------------
-- comm-HHS on inj₂ cosets.

commHHS-go-00 : ∀ {m} (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₀) , lm)) (H • H • S)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₀) , lm)) (S • H • H))
commHHS-go-00 {m} lm =
  PB.trans (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → Hdir v ↓ᵏ m) (Eq.cong (₀ ,_) -0#≈0#))
      (Eq.cong (λ v → dir-of-DS v) (Eq.cong₂ _,_ -0#≈0# -0#≈0#)))))
  (PB.trans (PB.axiom comm-HHS)
    (PB.sym (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_ Eq.refl
      (Eq.cong (λ v → Hdir v ↓ᵏ m) (Eq.cong (₀ ,_) -0#≈0#))))))) ,
  Eq.trans (Eq.cong (λ v → inj₂ (d-of-DS v , lm)) (Eq.cong₂ _,_ -0#≈0# -0#≈0#))
           (Eq.sym (Eq.cong (λ v → inj₂ (v , lm)) (Eq.cong₂ _,_ -0#≈0# -0#≈0#)))

commHHS-go-0b : ∀ {m} (b' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₁₊ b') , lm)) (H • H • S)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₀ , ₁₊ b') , lm)) (S • H • H))
commHHS-go-0b {m} b' lm =
  elim-suc (- ₁₊ b') (neg≢0 (₁₊ b') λ ()) λ z eq-z →
  PB.trans
    (PB.trans (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
        (Eq.cong (λ v → Hdir v ↓ᵏ m) (Eq.cong (₁₊ b' ,_) -0#≈0#))
        (Eq.cong (λ v → dir-of-DS v) (Eq.cong₂ _,_ -0#≈0# eq-z)))))
      (PB.trans PB.left-unit (PB.trans PB.assoc (PB.axiom comm-HHS))))
    (PB.sym (PB.trans (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_ Eq.refl
        (Eq.cong (λ v → Hdir v ↓ᵏ m) (Eq.cong (₁₊ b' ,_) -0#≈0#)))))
      (PB.cong PB.refl PB.left-unit))) ,
  Eq.trans (Eq.cong (λ v → inj₂ (d-of-DS v , lm)) (Eq.cong₂ _,_ -0#≈0# eq-z))
           (Eq.sym (Eq.cong₂ (λ v w → inj₂ ((v , w) , lm)) -0#≈0# eq-z))

commHHS-go-a0 : ∀ {m} (a' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₀) , lm)) (H • H • S)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₀) , lm)) (S • H • H))
commHHS-go-a0 a' lm =
  elim-suc (- ₁₊ a') (neg≢0 (₁₊ a') λ ()) λ y eq-y →
  commHHS-a0-resid a' y eq-y ,
  Eq.trans
    (Eq.trans (Eq.cong (λ v → inj₂ (d-of-DS v , lm))
                (Eq.cong₂ _,_ eq-y -0#≈0#))
      (Eq.cong (λ v → inj₂ ((₁₊ y , v) , lm))
        (Eq.trans (+-0ˡ (- ₁₊ y))
          (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a'))))))
    (Eq.sym (Eq.cong₂ (λ v w → inj₂ ((v , w) , lm)) eq-y
      (Eq.trans (Eq.cong -_ (+-0ˡ (- ₁₊ a'))) (-‿involutive (₁₊ a')))))

commHHS-go-nn : ∀ {m} (a' b' : Fin (₁₊ p-2)) (lm : C (₁₊ m)) →
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) (H • H • S)) ≋
  ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a' , ₁₊ b') , lm)) (S • H • H))
commHHS-go-nn a' b' lm =
  elim-suc (- ₁₊ a') (neg≢0 (₁₊ a') λ ()) λ y eq-y →
  elim-suc (- ₁₊ b') (neg≢0 (₁₊ b') λ ()) λ z eq-z →
  elim-fin (₁₊ b' + - ₁₊ a')
    (λ Xeq →
      commHHS-nn0-resid a' b' y eq-y Xeq ,
      Eq.trans
        (Eq.trans (Eq.cong (λ v → inj₂ (d-of-DS v , lm))
                    (Eq.cong₂ _,_ eq-y eq-z))
          (Eq.cong (λ v → inj₂ ((₁₊ y , v) , lm))
            (Eq.trans (Eq.cong₂ _+_ (Eq.sym eq-z)
                (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a'))))
            (Eq.trans (Eq.cong (λ v → - v + ₁₊ a')
                (+-‿cancel (₁₊ b') (₁₊ a') Xeq))
              (+-inverseˡ (₁₊ a'))))))
        (Eq.sym (Eq.cong₂ (λ v w → inj₂ ((v , w) , lm)) eq-y
          (Eq.trans (Eq.cong -_ Xeq) -0#≈0#))))
    (λ w Xeq →
      commHHS-nnw-resid a' b' y w eq-y Xeq ,
      Eq.trans
        (Eq.trans (Eq.cong (λ v → inj₂ (d-of-DS v , lm))
                    (Eq.cong₂ _,_ eq-y eq-z))
          (Eq.cong (λ v → inj₂ ((₁₊ y , v) , lm))
            (Eq.trans (Eq.cong₂ _+_ (Eq.sym eq-z)
                (Eq.trans (Eq.cong -_ (Eq.sym eq-y)) (-‿involutive (₁₊ a'))))
            (Eq.sym
              (Eq.trans (Eq.cong -_ (Eq.sym Xeq))
              (Eq.trans (Eq.sym (-‿+-comm (₁₊ b') (- ₁₊ a')))
                (Eq.cong (- ₁₊ b' +_) (-‿involutive (₁₊ a')))))))))
        (Eq.sym (Eq.cong₂ (λ v w' → inj₂ ((v , w') , lm)) eq-y
          (Eq.cong -_ Xeq))))

------------------------------------------------------------------------
-- order-CZ and comm-CZ-S↓/↑ on doubly-inj₂ cosets.

orderCZ-go : ∀ {m} (d1 d2 : D) (lm2 : C (₁₊ m)) →
  ((ract {₂₊ m} ᵗ) (inj₂ (d1 , inj₂ (d2 , lm2))) (CZ ^ p)) ≋
  ((ract {₂₊ m} ᵗ) (inj₂ (d1 , inj₂ (d2 , lm2))) ε)
orderCZ-go (₀ , b1) (₀ , g2) lm2 =
  PB.trans (ract-CZ^-resid (₀ , b1) (₀ , g2) lm2 p) (ddp-00 b1 g2) ,
  Eq.trans (ract-CZ^-coset (₀ , b1) (₀ , g2) lm2 p)
    (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
      (Eq.trans (Eq.cong (b1 +_) (nsum-p≡0 (- ₀))) (+-identityʳ b1))
      (Eq.trans (Eq.cong (g2 +_) (nsum-p≡0 (- ₀))) (+-identityʳ g2)))
orderCZ-go (₀ , b1) (₁₊ c2 , g2) lm2 =
  PB.trans (ract-CZ^-resid (₀ , b1) (₁₊ c2 , g2) lm2 p) (ddp-0c b1 g2 c2) ,
  Eq.trans (ract-CZ^-coset (₀ , b1) (₁₊ c2 , g2) lm2 p)
    (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₁₊ c2 , w) , lm2)))
      (Eq.trans (Eq.cong (b1 +_) (nsum-p≡0 (- ₁₊ c2))) (+-identityʳ b1))
      (Eq.trans (Eq.cong (g2 +_) (nsum-p≡0 (- ₀))) (+-identityʳ g2)))
orderCZ-go (₁₊ a1 , b1) (₀ , g2) lm2 =
  PB.trans (ract-CZ^-resid (₁₊ a1 , b1) (₀ , g2) lm2 p) (ddp-a0 a1 b1 g2) ,
  Eq.trans (ract-CZ^-coset (₁₊ a1 , b1) (₀ , g2) lm2 p)
    (Eq.cong₂ (λ v w → inj₂ ((₁₊ a1 , v) , inj₂ ((₀ , w) , lm2)))
      (Eq.trans (Eq.cong (b1 +_) (nsum-p≡0 (- ₀))) (+-identityʳ b1))
      (Eq.trans (Eq.cong (g2 +_) (nsum-p≡0 (- ₁₊ a1))) (+-identityʳ g2)))
orderCZ-go (₁₊ a1 , b1) (₁₊ c2 , g2) lm2 =
  PB.trans (ract-CZ^-resid (₁₊ a1 , b1) (₁₊ c2 , g2) lm2 p) (ddp-cc a1 c2 b1 g2) ,
  Eq.trans (ract-CZ^-coset (₁₊ a1 , b1) (₁₊ c2 , g2) lm2 p)
    (Eq.cong₂ (λ v w → inj₂ ((₁₊ a1 , v) , inj₂ ((₁₊ c2 , w) , lm2)))
      (Eq.trans (Eq.cong (b1 +_) (nsum-p≡0 (- ₁₊ c2))) (+-identityʳ b1))
      (Eq.trans (Eq.cong (g2 +_) (nsum-p≡0 (- ₁₊ a1))) (+-identityʳ g2)))

commCZS↓-go-+ : ∀ {m} (a1 : Fin (₁₊ p-2)) (b1 : ℤ ₚ) (d2 : D) (lm2 : C (₁₊ m)) →
  ((ract {₂₊ m} ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ (d2 , lm2))) (CZ • S ↓)) ≋
  ((ract {₂₊ m} ᵗ) (inj₂ ((₁₊ a1 , b1) , inj₂ (d2 , lm2))) (S ↓ • CZ))
commCZS↓-go-+ {m} a1 b1 d2 lm2 =
  PB.trans PB.right-unit
    (PB.trans
      (refl'ᵣ (Eq.cong (_↓ᵏ m)
        (DDdir-birrelˡ (₁₊ a1) b1 (b1 + - ₁₊ a1) d2)))
      (PB.sym PB.left-unit)) ,
  Eq.cong (λ v → inj₂ ((₁₊ a1 , v) ,
                       inj₂ ((proj₁ d2 , proj₂ d2 + - ₁₊ a1) , lm2)))
          (sub-swap b1 (proj₁ d2) (₁₊ a1))

commCZS↑-go-+ : ∀ {m} (d : D) (a2 : Fin (₁₊ p-2)) (b2 : ℤ ₚ) (lm2 : C (₁₊ m)) →
  ((ract {₂₊ m} ᵗ) (inj₂ (d , inj₂ ((₁₊ a2 , b2) , lm2))) (CZ • S ↑)) ≋
  ((ract {₂₊ m} ᵗ) (inj₂ (d , inj₂ ((₁₊ a2 , b2) , lm2))) (S ↑ • CZ))
commCZS↑-go-+ {m} d a2 b2 lm2 =
  PB.trans PB.right-unit
    (PB.trans
      (refl'ᵣ (Eq.cong (_↓ᵏ m)
        (DDdir-birrelʳ d (₁₊ a2) b2 (b2 + - ₁₊ a2))))
      (PB.sym PB.left-unit)) ,
  Eq.cong (λ v → inj₂ ((proj₁ d , proj₂ d + - ₁₊ a2) ,
                       inj₂ ((₁₊ a2 , v) , lm2)))
          (sub-swap b2 (proj₁ d) (₁₊ a2))
