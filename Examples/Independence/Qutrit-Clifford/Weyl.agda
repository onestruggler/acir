------------------------------------------------------------------------
-- Presentations of groups
--
-- Qutrit Weyl operators, and how Clifford matrices conjugate them
--
-- The Weyl operator of a Pauli label (a , b) on one qutrit is
-- D(a , b) = ω^(½ab) X^a Z^b, |c⟩ ↦ ω^(½ab + bc) |c + a⟩ (ω = ω₃,
-- ½ = 2 mod 3), and on n qutrits the Kronecker product over the
-- wires, wire 0 first — the order of the labels of
-- Examples.Groups.ProjectivePauli.Semantics.  A matrix U obeys the law
-- of a Pauli P and a symplectic map S when
--
--     U D(v) = ω^(sform P (S v)) D(S v) U        for every label v,
--
-- that is, U conjugates the Weyl operators by the affine map (P , S).
-- For odd p this is the whole Clifford action, with no correction to
-- the phase: the law of a gate on the bottom wires (law-emb₁,
-- law-emb₂) or shifted (law-up) is that of its matrix on its own
-- wires, and a product obeys the law of the semidirect product
-- (law-⊙: (P , S) (P' , S') = (P + S P' , S S')).  The local laws
-- of H, S and CZ are decided on their matrices (local-H, local-S,
-- local-CZ); Examples.Groups.ProjectiveClifford.Qupit's own semantics
-- gives H the map (a , b) ↦ (- b , a), S the map (a , b) ↦ (a , b + a)
-- with the Pauli part (0 , - ½), and CZ the symmetric shear, and those
-- are the maps that appear.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.Weyl where

open import Data.Bool.Base using (Bool ; T)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Nat.Base using (ℕ) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import ForStdlib.Data.Fin.Mod.Solver using (solve ; _⊕_ ; _⊗_ ; ⊝_)

open import Examples.Independence.Semantics.Qutrit
open import ForStdlib.Data.Fin.Mod using (ℤ)
import ForStdlib.Data.Fin.Mod as F3
import Examples.Independence.Qutrit-Clifford.P3 as P3
open P3 using (ₚ)
import Examples.Groups.ProjectivePauli.Semantics 1 P3.p-prime as PS
open PS using (Pauli1 ; Pauli ; sform1 ; sform ; _+ₚ_ ; pIₙ)
open import Examples.Groups.Symplectic.Semantics 1 P3.p-prime using (Symplectic ; _∘ˢ_)
open Symplectic using (ap ; preserves)

open import Algebra.Bundles using (CommutativeRing)
open CommutativeRing R using (*-assoc ; *-comm ; *-identityˡ ; *-identityʳ ; +-identityʳ)

private
  variable
    n : ℕ

  open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Powers of ω₃

-- ω₃ = ζ⁴, as the table of its three values (ζ⁴ = ζ² − 1, ζ⁸ = −ζ²):
-- read as x ^ (4 * a), every use multiplied out up to eight products.
ω^ : ℤ ₚ → Q
ω^ zero             = Zζ.⟨ + 1 , + 0 , + 0 , + 0 ⟩
ω^ (suc zero)       = Zζ.⟨ -[1+ 0 ] , + 0 , + 1 , + 0 ⟩
ω^ (suc (suc zero)) = Zζ.⟨ + 0 , + 0 , -[1+ 0 ] , + 0 ⟩

ω^-x : (a : ℤ ₚ) → x ^ (4 *ℕ toℕ a) ≡ ω^ a
ω^-x zero             = refl
ω^-x (suc zero)       = refl
ω^-x (suc (suc zero)) = refl

ω^-+ : (a b : ℤ ₚ) → ω^ (a F3.+ b) ≡ ω^ a * ω^ b
ω^-+ zero                 zero                 = refl
ω^-+ zero                 (suc zero)           = refl
ω^-+ zero                 (suc (suc zero))     = refl
ω^-+ (suc zero)           zero                 = refl
ω^-+ (suc zero)           (suc zero)           = refl
ω^-+ (suc zero)           (suc (suc zero))     = refl
ω^-+ (suc (suc zero))     zero                 = refl
ω^-+ (suc (suc zero))     (suc zero)           = refl
ω^-+ (suc (suc zero))     (suc (suc zero))     = refl

ω^-0 : ω^ (zero {2}) ≡ 1#
ω^-0 = refl

------------------------------------------------------------------------
-- Weyl operators

-- ½ mod 3.
½ : ℤ ₚ
½ = suc (suc zero)

D₁ : Pauli1 → Op 1
D₁ (a , b) (r ∷ []) (c ∷ []) = δ₁ r (c F3.+ a) * ω^ ((½ F3.* a F3.* b) F3.+ (b F3.* c))

D : Pauli n → Op n
D []      = Idₒ
D (p ∷ v) = tensor (D₁ p) (D v)

-- Two wires.
D₂ : Pauli1 → Pauli1 → Op 2
D₂ p q = tensor (D₁ p) (D₁ q)

------------------------------------------------------------------------
-- The law

LawF : Op n → Symplectic n → Pauli n → Set
LawF U S P = ∀ v → (U ⊙ D v) ≐ scale (ω^ (sform P (ap S v))) (D (ap S v) ⊙ U)

-- On one and two wires, with the map and the Pauli given locally.
Law₁F : Op 1 → (Pauli1 → Pauli1) → Pauli1 → Set
Law₁F U s P = ∀ p → (U ⊙ D₁ p) ≐ scale (ω^ (sform1 P (s p))) (D₁ (s p) ⊙ U)

Law₂F : Op 2 → (Pauli1 → Pauli1 → Pauli1) → (Pauli1 → Pauli1 → Pauli1) →
       Pauli1 → Pauli1 → Set
Law₂F U s t P Q = ∀ p q →
  (U ⊙ D₂ p q) ≐ scale (ω^ (sform1 P (s p q) F3.+ sform1 Q (t p q))) (D₂ (s p q) (t p q) ⊙ U)

------------------------------------------------------------------------
-- Deciding a local law on stored matrices

allP1 : (Pauli1 → Bool) → Bool
allP1 f = allFin λ a → allFin λ b → f (a , b)

allP1-sound : (f : Pauli1 → Bool) → T (allP1 f) → ∀ p → T (f p)
allP1-sound f t (a , b) = allFin-sound (λ b → f (a , b)) (allFin-sound (λ a → allFin λ b → f (a , b)) t a) b

module Decide₁ (U : Mat 1) (s : Pauli1 → Pauli1) (P : Pauli1) where

  φ : Pauli1 → ℤ ₚ
  φ p = sform1 P (s p)

  ok : Pauli1 → Bool
  ok p = eqₖ (4 *ℕ toℕ (φ p)) (0 , mulM U (matOf (D₁ p))) (0 , mulM (matOf (D₁ (s p))) U)

  sound : T (allP1 ok) → Law₁F (ix U) s P
  sound t p i j = begin
    (ix U ⊙ D₁ p) i j                    ≡⟨ Eq.sym (ix-⊙ U (D₁ p) i j) ⟩
    ix (mulM U (matOf (D₁ p))) i j       ≡⟨ Eq.sym (*-identityˡ _) ⟩
    1# * ix (mulM U (matOf (D₁ p))) i j  ≡⟨ e i j ⟩
    (x ^ (4 *ℕ toℕ (φ p)) * 1#) * ix (mulM (matOf (D₁ (s p))) U) i j
      ≡⟨ Eq.cong (λ c → (c * 1#) * ix (mulM (matOf (D₁ (s p))) U) i j) (ω^-x (φ p)) ⟩
    (ω^ (φ p) * 1#) * ix (mulM (matOf (D₁ (s p))) U) i j
      ≡⟨ Eq.cong₂ _*_ (*-identityʳ (ω^ (φ p))) (ix-⊙′ (D₁ (s p)) U i j) ⟩
    ω^ (φ p) * (D₁ (s p) ⊙ ix U) i j     ∎
    where
    e = eqₖ-sound (4 *ℕ toℕ (φ p)) (0 , mulM U (matOf (D₁ p)))
                  (0 , mulM (matOf (D₁ (s p))) U) (allP1-sound ok t p)
    ix-⊙ : (M : Mat 1) (N : Op 1) → ix (mulM M (matOf N)) ≐ (ix M ⊙ N)
    ix-⊙ M N = ≐-trans (ix-mul M (matOf N)) (⊙-cong (≐-refl (ix M)) (ix-matOf N))
    ix-⊙′ : (N : Op 1) (M : Mat 1) → ix (mulM (matOf N) M) ≐ (N ⊙ ix M)
    ix-⊙′ N M = ≐-trans (ix-mul (matOf N) M) (⊙-cong (ix-matOf N) (≐-refl (ix M)))

module Decide₂ (U : Mat 2) (s t : Pauli1 → Pauli1 → Pauli1) (P Q : Pauli1) where

  φ : Pauli1 → Pauli1 → ℤ ₚ
  φ p q = sform1 P (s p q) F3.+ sform1 Q (t p q)

  ok : Pauli1 → Pauli1 → Bool
  ok p q = eqₖ (4 *ℕ toℕ (φ p q)) (0 , mulM U (matOf (D₂ p q)))
             (0 , mulM (matOf (D₂ (s p q) (t p q))) U)

  sound : T (allP1 λ p → allP1 λ q → ok p q) → Law₂F (ix U) s t P Q
  sound h p q i j = begin
    (ix U ⊙ D₂ p q) i j                    ≡⟨ Eq.sym (ix-⊙ U (D₂ p q) i j) ⟩
    ix (mulM U (matOf (D₂ p q))) i j       ≡⟨ Eq.sym (*-identityˡ _) ⟩
    1# * ix (mulM U (matOf (D₂ p q))) i j  ≡⟨ e i j ⟩
    (x ^ (4 *ℕ toℕ (φ p q)) * 1#) * ix (mulM (matOf (D₂ (s p q) (t p q))) U) i j
      ≡⟨ Eq.cong (λ c → (c * 1#) * ix (mulM (matOf (D₂ (s p q) (t p q))) U) i j) (ω^-x (φ p q)) ⟩
    (ω^ (φ p q) * 1#) * ix (mulM (matOf (D₂ (s p q) (t p q))) U) i j
      ≡⟨ Eq.cong₂ _*_ (*-identityʳ (ω^ (φ p q))) (ix-⊙′ (D₂ (s p q) (t p q)) U i j) ⟩
    ω^ (φ p q) * (D₂ (s p q) (t p q) ⊙ ix U) i j ∎
    where
    e = eqₖ-sound (4 *ℕ toℕ (φ p q)) (0 , mulM U (matOf (D₂ p q)))
                  (0 , mulM (matOf (D₂ (s p q) (t p q))) U)
                  (allP1-sound (ok p) (allP1-sound (λ p → allP1 (ok p)) h p) q)
    ix-⊙ : (M : Mat 2) (N : Op 2) → ix (mulM M (matOf N)) ≐ (ix M ⊙ N)
    ix-⊙ M N = ≐-trans (ix-mul M (matOf N)) (⊙-cong (≐-refl (ix M)) (ix-matOf N))
    ix-⊙′ : (N : Op 2) (M : Mat 2) → ix (mulM (matOf N) M) ≐ (N ⊙ ix M)
    ix-⊙′ N M = ≐-trans (ix-mul (matOf N) M) (⊙-cong (ix-matOf N) (≐-refl (ix M)))

------------------------------------------------------------------------
-- The symplectic form

private
  add4 : (w x y z : ℤ ₚ) → (w F3.+ x) F3.+ (y F3.+ z) ≡ (w F3.+ y) F3.+ (x F3.+ z)
  add4 = solve 1 4 (λ w x y z → ((w ⊕ x) ⊕ (y ⊕ z)) , ((w ⊕ y) ⊕ (x ⊕ z)))
                   (λ {_} {_} {_} {_} → refl)

  s1+ : (a b c d e f : ℤ ₚ) →
        (F3.- (a F3.+ c)) F3.* f F3.+ e F3.* (b F3.+ d) ≡
        ((F3.- a) F3.* f F3.+ e F3.* b) F3.+ ((F3.- c) F3.* f F3.+ e F3.* d)
  s1+ = solve 1 6 (λ a b c d e f → ((⊝ (a ⊕ c)) ⊗ f ⊕ e ⊗ (b ⊕ d)) ,
                                   (((⊝ a) ⊗ f ⊕ e ⊗ b) ⊕ ((⊝ c) ⊗ f ⊕ e ⊗ d)))
                  (λ {_} {_} {_} {_} {_} {_} → refl)

  +0 : (a : ℤ ₚ) → a F3.+ zero ≡ a
  +0 zero             = refl
  +0 (suc zero)       = refl
  +0 (suc (suc zero)) = refl

  0+ : (a : ℤ ₚ) → zero F3.+ a ≡ a
  0+ zero             = refl
  0+ (suc zero)       = refl
  0+ (suc (suc zero)) = refl

sform1-I : (p : Pauli1) → sform1 PS.pI p ≡ zero
sform1-I (zero , zero)                     = refl
sform1-I (zero , suc zero)                 = refl
sform1-I (zero , suc (suc zero))           = refl
sform1-I (suc zero , zero)                 = refl
sform1-I (suc zero , suc zero)             = refl
sform1-I (suc zero , suc (suc zero))       = refl
sform1-I (suc (suc zero) , zero)           = refl
sform1-I (suc (suc zero) , suc zero)       = refl
sform1-I (suc (suc zero) , suc (suc zero)) = refl

sform-I : (v : Pauli n) → sform pIₙ v ≡ zero
sform-I []      = refl
sform-I (p ∷ v) = Eq.trans (Eq.cong₂ F3._+_ (sform1-I p) (sform-I v)) refl

sform1-+ˡ : (p q r : Pauli1) → sform1 (p PS.+₁ q) r ≡ sform1 p r F3.+ sform1 q r
sform1-+ˡ (a , b) (c , d) (e , f) = s1+ a b c d e f

sform-+ˡ : (P Q v : Pauli n) → sform (P +ₚ Q) v ≡ sform P v F3.+ sform Q v
sform-+ˡ []      []      []      = refl
sform-+ˡ (p ∷ P) (q ∷ Q) (r ∷ v) = begin
  sform1 (p PS.+₁ q) r F3.+ sform (P +ₚ Q) v
    ≡⟨ Eq.cong₂ F3._+_ (sform1-+ˡ p q r) (sform-+ˡ P Q v) ⟩
  (sform1 p r F3.+ sform1 q r) F3.+ (sform P v F3.+ sform Q v)
    ≡⟨ add4 (sform1 p r) (sform1 q r) (sform P v) (sform Q v) ⟩
  (sform1 p r F3.+ sform P v) F3.+ (sform1 q r F3.+ sform Q v) ∎

------------------------------------------------------------------------
-- Moving a law along equalities

private
  scale-≡ : {a b : Q} (M : Op n) → a ≡ b → scale a M ≐ scale b M
  scale-≡ M refl = ≐-refl _

law-congF : {U U' : Op n} {S : Symplectic n} {P : Pauli n} → U ≐ U' → LawF U S P → LawF U' S P
law-congF {U = U} {U'} {S} {P} e l v =
  ≐-trans (⊙-cong (≐-sym e) (≐-refl (D v)))
    (≐-trans (l v) (scale-cong {c = ω^ (sform P (ap S v))} (⊙-cong (≐-refl (D (ap S v))) e)))

law-SF : {U : Op n} {S S' : Symplectic n} {P : Pauli n} → (∀ v → ap S v ≡ ap S' v) →
        LawF U S P → LawF U S' P
law-SF {U = U} {S} {S'} {P} e l v rewrite Eq.sym (e v) = l v

law-PF : {U : Op n} {S : Symplectic n} {P P' : Pauli n} → P ≡ P' → LawF U S P → LawF U S P'
law-PF refl l = l

-- A scalar passes every Weyl operator.
law-scaleF : {U : Op n} {S : Symplectic n} {P : Pauli n} (c : Q) → LawF U S P → LawF (scale c U) S P
law-scaleF {U = U} {S} {P} c l v =
  ≐-trans (scale-⊙ˡ c U (D v))
    (≐-trans (scale-cong {c = c} (l v))
      (≐-trans (scale-scale c φ (D (ap S v) ⊙ U))
        (≐-trans (scale-≡ (D (ap S v) ⊙ U) (*-comm c φ))
          (≐-trans (≐-sym (scale-scale φ c (D (ap S v) ⊙ U)))
            (scale-cong {c = φ} (≐-sym (scale-⊙ʳ c (D (ap S v)) U)))))))
  where φ = ω^ (sform P (ap S v))

------------------------------------------------------------------------
-- Gates on the bottom wires, shifted gates, products

law-emb₁F : {U : Op 1} {s : Pauli1 → Pauli1} {P : Pauli1} → Law₁F U s P →
           (S : Symplectic (Data.Nat.Base.suc n)) → (∀ p v → ap S (p ∷ v) ≡ s p ∷ v) →
           LawF (emb {1} {n} U) S (P ∷ pIₙ)
law-emb₁F {n = n} {U} {s} {P} l S hS (p ∷ v) rewrite hS p v =
  ≐-trans (tensor-⊙ U (D₁ p) Idₒ (D v))
    (≐-trans (tensor-cong (l p) (≐-trans (⊙-identityˡ (D v)) (≐-sym (⊙-identityʳ (D v)))))
      (≐-trans (tensor-scaleˡ c (D₁ (s p) ⊙ U) (D v ⊙ Idₒ))
        (≐-trans (scale-cong {c = c} (≐-sym (tensor-⊙ (D₁ (s p)) U (D v) Idₒ)))
          (scale-≡ (D (s p ∷ v) ⊙ emb {1} {n} U) ph))))
  where
  c = ω^ (sform1 P (s p))
  ph : c ≡ ω^ (sform (P ∷ pIₙ) (s p ∷ v))
  ph = Eq.cong ω^ (Eq.sym (Eq.trans (Eq.cong (sform1 P (s p) F3.+_) (sform-I v)) (+0 (sform1 P (s p)))))

law-emb₂F : {U : Op 2} {s t : Pauli1 → Pauli1 → Pauli1} {P Q : Pauli1} → Law₂F U s t P Q →
           (S : Symplectic (Data.Nat.Base.suc (Data.Nat.Base.suc n))) →
           (∀ p q v → ap S (p ∷ q ∷ v) ≡ s p q ∷ t p q ∷ v) →
           LawF (emb {2} {n} U) S (P ∷ Q ∷ pIₙ)
law-emb₂F {n = n} {U} {s} {t} {P} {Q} l S hS (p ∷ q ∷ v) rewrite hS p q v =
  ≐-trans (⊙-cong (≐-refl (emb {2} {n} U)) (≐-sym (tensor-assoc₁ (D₁ p) (D₁ q) (D v))))
    (≐-trans (tensor-⊙ U (D₂ p q) Idₒ (D v))
      (≐-trans (tensor-cong (l p q) (≐-trans (⊙-identityˡ (D v)) (≐-sym (⊙-identityʳ (D v)))))
        (≐-trans (tensor-scaleˡ c (D₂ (s p q) (t p q) ⊙ U) (D v ⊙ Idₒ))
          (≐-trans (scale-cong {c = c} (≐-sym (tensor-⊙ (D₂ (s p q) (t p q)) U (D v) Idₒ)))
            (≐-trans (scale-cong {c = c}
                       (⊙-cong (tensor-assoc₁ (D₁ (s p q)) (D₁ (t p q)) (D v)) (≐-refl (emb {2} {n} U))))
              (scale-≡ (D (s p q ∷ t p q ∷ v) ⊙ emb {2} {n} U) ph))))))
  where
  c = ω^ (sform1 P (s p q) F3.+ sform1 Q (t p q))
  ph : c ≡ ω^ (sform (P ∷ Q ∷ pIₙ) (s p q ∷ t p q ∷ v))
  ph = Eq.cong ω^ (Eq.sym (begin
    sform1 P (s p q) F3.+ (sform1 Q (t p q) F3.+ sform pIₙ v)
      ≡⟨ Eq.cong (λ z → sform1 P (s p q) F3.+ (sform1 Q (t p q) F3.+ z)) (sform-I v) ⟩
    sform1 P (s p q) F3.+ (sform1 Q (t p q) F3.+ zero)
      ≡⟨ Eq.cong (sform1 P (s p q) F3.+_) (+0 (sform1 Q (t p q))) ⟩
    sform1 P (s p q) F3.+ sform1 Q (t p q) ∎))

law-upF : {U : Op n} {S : Symplectic n} {P : Pauli n} → LawF U S P →
         (S' : Symplectic (Data.Nat.Base.suc n)) → (∀ p v → ap S' (p ∷ v) ≡ p ∷ ap S v) →
         LawF (up U) S' (PS.pI ∷ P)
law-upF {n = n} {U} {S} {P} l S' hS (p ∷ v) rewrite hS p v =
  ≐-trans (tensor-⊙ Idₒ (D₁ p) U (D v))
    (≐-trans (tensor-cong (≐-trans (⊙-identityˡ (D₁ p)) (≐-sym (⊙-identityʳ (D₁ p)))) (l v))
      (≐-trans (tensor-scaleʳ c (D₁ p ⊙ Idₒ) (D (ap S v) ⊙ U))
        (≐-trans (scale-cong {c = c} (≐-sym (tensor-⊙ (D₁ p) Idₒ (D (ap S v)) U)))
          (scale-≡ (D (p ∷ ap S v) ⊙ up U) ph))))
  where
  c = ω^ (sform P (ap S v))
  ph : c ≡ ω^ (sform (PS.pI ∷ P) (p ∷ ap S v))
  ph = Eq.cong ω^ (Eq.sym (Eq.trans (Eq.cong (F3._+ sform P (ap S v)) (sform1-I p)) (0+ (sform P (ap S v)))))

-- (P , S) (P' , S') = (P + S P' , S S'), the product of the
-- semidirect product, with the right factor acting first.
law-⊙F : {U U' : Op n} {S S' : Symplectic n} {P P' : Pauli n} → LawF U S P → LawF U' S' P' →
        LawF (U ⊙ U') (S ∘ˢ S') (P +ₚ ap S P')
law-⊙F {U = U} {U'} {S} {S'} {P} {P'} l l' v =
  ≐-trans (⊙-assoc U U' (D v))
  (≐-trans (⊙-cong (≐-refl U) (l' v))
  (≐-trans (scale-⊙ʳ c' U (D y ⊙ U'))
  (≐-trans (scale-cong {c = c'} (≐-sym (⊙-assoc U (D y) U')))
  (≐-trans (scale-cong {c = c'} (⊙-cong (l y) (≐-refl U')))
  (≐-trans (scale-cong {c = c'} (scale-⊙ˡ c (D z ⊙ U) U'))
  (≐-trans (scale-cong {c = c'} (scale-cong {c = c} (⊙-assoc (D z) U U')))
  (≐-trans (scale-scale c' c (D z ⊙ (U ⊙ U')))
           (scale-≡ (D z ⊙ (U ⊙ U')) ph))))))))
  where
  y = ap S' v
  z = ap S y
  c' = ω^ (sform P' y)
  c  = ω^ (sform P z)
  ph : c' * c ≡ ω^ (sform (P +ₚ ap S P') z)
  ph = begin
    c' * c                                    ≡⟨ *-comm c' c ⟩
    c * c'                                    ≡⟨ Eq.sym (ω^-+ (sform P z) (sform P' y)) ⟩
    ω^ (sform P z F3.+ sform P' y)            ≡⟨ Eq.cong (λ t → ω^ (sform P z F3.+ t)) (Eq.sym (preserves S P' y)) ⟩
    ω^ (sform P z F3.+ sform (ap S P') z)     ≡⟨ Eq.cong ω^ (Eq.sym (sform-+ˡ P (ap S P') z)) ⟩
    ω^ (sform (P +ₚ ap S P') z)               ∎

------------------------------------------------------------------------
-- The local laws of H, S and CZ
--
-- The maps are those of Examples.Groups.Symplectic.Semantics' actg,
-- and the Pauli part of S that of Simplified-V1.Forward (S ↦ Z^(-½) S,
-- and -½ = 1 mod 3).

sH sS : Pauli1 → Pauli1
sH (a , b) = (F3.- b , a)
sS (a , b) = (a , b F3.+ a)

sCZ tCZ : Pauli1 → Pauli1 → Pauli1
sCZ (a , b) (a' , b') = (a , b F3.+ a')
tCZ (a , b) (a' , b') = (a' , b' F3.+ a)

-- CZ |b₀ , b₁⟩ = ω^(b₀ b₁) |b₀ , b₁⟩.
CZᵍ : Sc 2
CZᵍ = 0 , matOf λ x y → δv x y * cz y
  where
  cz : Digits 2 → Q
  cz (b₀ ∷ b₁ ∷ []) = ω^ (b₀ F3.* b₁)

local-HF : Law₁F (ix (proj₂ Hᵍ)) sH PS.pI
local-HF = Decide₁.sound (proj₂ Hᵍ) sH PS.pI _

local-SF : Law₁F (ix (proj₂ Sᵍ)) sS (zero , suc zero)
local-SF = Decide₁.sound (proj₂ Sᵍ) sS (zero , suc zero) _

local-CZF : Law₂F (ix (proj₂ CZᵍ)) sCZ tCZ PS.pI PS.pI
local-CZF = Decide₂.sound (proj₂ CZᵍ) sCZ tCZ PS.pI PS.pI _

------------------------------------------------------------------------
-- The same, as records, so that the map and the Pauli are inferred

record Law (U : Op n) (S : Symplectic n) (P : Pauli n) : Set where
  constructor mkLaw
  field at : LawF U S P
open Law public

record Law₁ (U : Op 1) (s : Pauli1 → Pauli1) (P : Pauli1) : Set where
  constructor mkLaw₁
  field at₁ : Law₁F U s P
open Law₁ public

record Law₂ (U : Op 2) (s t : Pauli1 → Pauli1 → Pauli1) (P Q : Pauli1) : Set where
  constructor mkLaw₂
  field at₂ : Law₂F U s t P Q
open Law₂ public

law-cong : {U U' : Op n} {S : Symplectic n} {P : Pauli n} → U ≐ U' → Law U S P → Law U' S P
law-cong {U = U} {U'} {S} {P} e l = mkLaw (law-congF {U = U} {U'} {S} {P} e (at l))

law-S : {U : Op n} {S S' : Symplectic n} {P : Pauli n} → (∀ v → ap S v ≡ ap S' v) →
        Law U S P → Law U S' P
law-S {U = U} {S} {S'} {P} e l = mkLaw (law-SF {U = U} {S} {S'} {P} e (at l))

law-P : {U : Op n} {S : Symplectic n} {P P' : Pauli n} → P ≡ P' → Law U S P → Law U S P'
law-P refl l = l

law-scale : {U : Op n} {S : Symplectic n} {P : Pauli n} (c : Q) → Law U S P → Law (scale c U) S P
law-scale {U = U} {S} {P} c l = mkLaw (law-scaleF {U = U} {S} {P} c (at l))

law-emb₁ : {U : Op 1} {s : Pauli1 → Pauli1} {P : Pauli1} → Law₁ U s P →
           (S : Symplectic (Data.Nat.Base.suc n)) → (∀ p v → ap S (p ∷ v) ≡ s p ∷ v) →
           Law (emb {1} {n} U) S (P ∷ pIₙ)
law-emb₁ {U = U} {s} {P} l S hS = mkLaw (law-emb₁F {U = U} {s} {P} (at₁ l) S hS)

law-emb₂ : {U : Op 2} {s t : Pauli1 → Pauli1 → Pauli1} {P Q : Pauli1} → Law₂ U s t P Q →
           (S : Symplectic (Data.Nat.Base.suc (Data.Nat.Base.suc n))) →
           (∀ p q v → ap S (p ∷ q ∷ v) ≡ s p q ∷ t p q ∷ v) →
           Law (emb {2} {n} U) S (P ∷ Q ∷ pIₙ)
law-emb₂ {U = U} {s} {t} {P} {Q} l S hS = mkLaw (law-emb₂F {U = U} {s} {t} {P} {Q} (at₂ l) S hS)

law-up : {U : Op n} {S : Symplectic n} {P : Pauli n} → Law U S P →
         (S' : Symplectic (Data.Nat.Base.suc n)) → (∀ p v → ap S' (p ∷ v) ≡ p ∷ ap S v) →
         Law (up U) S' (PS.pI ∷ P)
law-up {U = U} {S} {P} l S' hS = mkLaw (law-upF {U = U} {S} {P} (at l) S' hS)

law-⊙ : {U U' : Op n} {S S' : Symplectic n} {P P' : Pauli n} → Law U S P → Law U' S' P' →
        Law (U ⊙ U') (S ∘ˢ S') (P +ₚ ap S P')
law-⊙ {U = U} {U'} {S} {S'} {P} {P'} l l' =
  mkLaw (law-⊙F {U = U} {U'} {S} {S'} {P} {P'} (at l) (at l'))

local-H : Law₁ (ix (proj₂ Hᵍ)) sH PS.pI
local-H = mkLaw₁ local-HF

local-S : Law₁ (ix (proj₂ Sᵍ)) sS (zero , suc zero)
local-S = mkLaw₁ local-SF

local-CZ : Law₂ (ix (proj₂ CZᵍ)) sCZ tCZ PS.pI PS.pI
local-CZ = mkLaw₂ local-CZF
