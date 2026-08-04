------------------------------------------------------------------------
-- Presentations of groups
--
-- Well-definedness of the coset action on the group-specific axioms
-- (the srel case of ⁻¹[⇑]-wd'' in Normalization.agda), one axiom at a
-- time.  For an axiom u === t we must show the threaded action agrees:
-- (ract ᵗ) c u ≋ (ract ᵗ) c t.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDCZ
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise)
open import Data.Sum using (inj₁ ; inj₂)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

import Examples.Groups.Symplectic.Normalization.Pushing.PushML p-2 p-prime as PushML
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (dir-of-DS ; d-of-DS)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir)
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (S^-↓ᵏ ; ↑↓ᵏ-comm)
import Relation.Binary.Reasoning.Setoid as SR
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)

open import Data.Nat using (zero ; suc) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Nat.DivMod using (_%_ ; m%n<n ; %-distribˡ-+ ; m*n%n≡0 ; m<n⇒m%n≡m ; m%n%n≡m%n)
open import Data.Product using (∃)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ<)
import Data.Nat.Properties as NP
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_)
open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-* ; -‿+-comm)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushLM1 p-2 p-prime
  using (A-dir-S-power)
import Examples.Groups.Symplectic.BR.One.A p-2 p-prime as OA
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥-elim)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime

------------------------------------------------------------------------
-- Machinery for the comm-CZ-S axioms on doubly-inj₂ cosets.  The DD-CZ
-- escape word depends only on the a components of the two D boxes
-- (which every coset map in sight preserves), and for the reachable
-- zero patterns its letters commute with the S escape by axioms.

-- The DD-CZ escape ignores the b components.
DDdir-birrelˡ : ∀ (a1 b b' : ℤ ₚ) (d2 : D) →
  DDCZ.dir-of ((a1 , b) ∷ d2 ∷ []) ≡ DDCZ.dir-of ((a1 , b') ∷ d2 ∷ [])
DDdir-birrelˡ ₀      b b' (₀ , g)    = Eq.refl
DDdir-birrelˡ ₀      b b' (₁₊ _ , g) = Eq.refl
DDdir-birrelˡ (₁₊ _) b b' (₀ , g)    = Eq.refl
DDdir-birrelˡ (₁₊ _) b b' (₁₊ _ , g) = Eq.refl

DDdir-birrelʳ : ∀ (d1 : D) (a2 b b' : ℤ ₚ) →
  DDCZ.dir-of (d1 ∷ (a2 , b) ∷ []) ≡ DDCZ.dir-of (d1 ∷ (a2 , b') ∷ [])
DDdir-birrelʳ (₀ , _)    ₀      b b' = Eq.refl
DDdir-birrelʳ (₀ , _)    (₁₊ _) b b' = Eq.refl
DDdir-birrelʳ (₁₊ _ , _) ₀      b b' = Eq.refl
DDdir-birrelʳ (₁₊ _ , _) (₁₊ _) b b' = Eq.refl

DDdir-birrel₂ : ∀ (a1 b b' a2 g g' : ℤ ₚ) →
  DDCZ.dir-of ((a1 , b) ∷ (a2 , g) ∷ []) ≡
  DDCZ.dir-of ((a1 , b') ∷ (a2 , g') ∷ [])
DDdir-birrel₂ ₀      b b' ₀      g g' = Eq.refl
DDdir-birrel₂ ₀      b b' (₁₊ _) g g' = Eq.refl
DDdir-birrel₂ (₁₊ _) b b' ₀      g g' = Eq.refl
DDdir-birrel₂ (₁₊ _) b b' (₁₊ _) g g' = Eq.refl

-- Threading CZ ^ k through a doubly-inj₂ coset: the two bottom D boxes
-- accumulate b-shifts, and the residual is the k-th power of the (fixed)
-- DD-CZ escape.
ract-CZ^-coset : ∀ {m} (d d2 : D) (lm2 : C (₁₊ m)) (k : ℕ) →
  ((ract {₂₊ m} ᵗ) (inj₂ (d , inj₂ (d2 , lm2))) (CZ ^ k)) .proj₂
  ≡ inj₂ ((proj₁ d , proj₂ d + nsum k (- proj₁ d2)) ,
          inj₂ ((proj₁ d2 , proj₂ d2 + nsum k (- proj₁ d)) , lm2))
ract-CZ^-coset d d2 lm2 zero =
  Eq.cong₂ (λ v w → inj₂ ((proj₁ d , v) , inj₂ ((proj₁ d2 , w) , lm2)))
    (Eq.sym (+-identityʳ (proj₂ d))) (Eq.sym (+-identityʳ (proj₂ d2)))
ract-CZ^-coset d d2 lm2 (suc zero) =
  Eq.cong₂ (λ v w → inj₂ ((proj₁ d , v) , inj₂ ((proj₁ d2 , w) , lm2)))
    (Eq.cong (proj₂ d +_) (Eq.sym (+-identityʳ (- proj₁ d2))))
    (Eq.cong (proj₂ d2 +_) (Eq.sym (+-identityʳ (- proj₁ d))))
ract-CZ^-coset d d2 lm2 (suc (suc k)) =
  Eq.trans
    (ract-CZ^-coset (proj₁ d , proj₂ d + - proj₁ d2)
                    (proj₁ d2 , proj₂ d2 + - proj₁ d) lm2 (suc k))
    (Eq.cong₂ (λ v w → inj₂ ((proj₁ d , v) , inj₂ ((proj₁ d2 , w) , lm2)))
      (+-assoc (proj₂ d) (- proj₁ d2) (nsum (suc k) (- proj₁ d2)))
      (+-assoc (proj₂ d2) (- proj₁ d) (nsum (suc k) (- proj₁ d))))

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  ract-CZ^-resid : ∀ (d d2 : D) (lm2 : C (₁₊ m)) (k : ℕ) →
    ((ract {₂₊ m} ᵗ) (inj₂ (d , inj₂ (d2 , lm2))) (CZ ^ k)) .proj₁
    ≈ (DDCZ.dir-of (d ∷ d2 ∷ []) ↓ᵏ m) ^ k
  ract-CZ^-resid d d2 lm2 zero = refl
  ract-CZ^-resid d d2 lm2 (suc zero) = refl
  ract-CZ^-resid d d2 lm2 (suc (suc k)) =
    cong refl
      (trans
        (ract-CZ^-resid (proj₁ d , proj₂ d + - proj₁ d2)
                        (proj₁ d2 , proj₂ d2 + - proj₁ d) lm2 (suc k))
        (refl'ᵣ (Eq.cong (λ w → (w ↓ᵏ m) ^ ₁₊ k)
          (DDdir-birrel₂ (proj₁ d) (proj₂ d + - proj₁ d2) (proj₂ d)
                         (proj₁ d2) (proj₂ d2 + - proj₁ d) (proj₂ d2)))))

-- Powers of a lift are lifts of powers.
pow-↑ : ∀ {j} (w : Circuit j) (t : ℕ) → (w ↑) ^ t ≡ (w ^ t) ↑
pow-↑ w zero          = Eq.refl
pow-↑ w (suc zero)    = Eq.refl
pow-↑ w (suc (suc t)) = Eq.cong ((w ↑) •_) (pow-↑ w (suc t))

-- H ^ 3 • H ≈ ε and S-power collapses, width-generically.
module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)

  H3H≈ε : H ^ 3 • H ≈ ε
  H3H≈ε = trans (sym (^-+ H 3 1)) (axiom order-H)

  ε-pow : ∀ (t : ℕ) → _^_ {X = Gen (₁₊ j)} ε t ≈ ε
  ε-pow zero          = refl
  ε-pow (suc zero)    = refl
  ε-pow (suc (suc t)) = trans left-unit (ε-pow (suc t))

  S-pow-p : ∀ (t : ℕ) → (S ^ t) ^ p ≈ ε
  S-pow-p t = trans (^^ S t p)
    (trans (refl'ᵣ (Eq.cong (S ^_) (NP.*-comm t p)))
    (trans (sym (^^ S p t))
    (trans (^-cong (S ^ p) ε t (axiom order-S)) (ε-pow t))))

module _ {k : ℕ} where
  open PB ((₂₊ k) QRel,_===_)
  open PP ((₂₊ k) QRel,_===_)
  open SR word-setoid

  -- The escape of a (₀,·)-headed pair commutes with the bottom S.
  comm-W-S : ∀ (b1 : ℤ ₚ) (d2 : D) →
    (DDCZ.dir-of ((₀ , b1) ∷ d2 ∷ []) ↓ᵏ k) • S ≈
    S • (DDCZ.dir-of ((₀ , b1) ∷ d2 ∷ []) ↓ᵏ k)
  comm-W-S b1 (₀ , g) = axiom comm-CZ-S↓
  comm-W-S b1 (₁₊ _ , g) = begin
    (H ↑ • (CZ • H ↑ ^ 3)) • S    ≈⟨ assoc ⟩
    H ↑ • ((CZ • H ↑ ^ 3) • S)    ≈⟨ cright assoc ⟩
    H ↑ • (CZ • (H ↑ ^ 3 • S))    ≈⟨ cright (cright (sym (lemma-comm-S-w↑ (H ^ 3)))) ⟩
    H ↑ • (CZ • (S • H ↑ ^ 3))    ≈⟨ cright (sym assoc) ⟩
    H ↑ • ((CZ • S) • H ↑ ^ 3)    ≈⟨ cright (cleft (axiom comm-CZ-S↓)) ⟩
    H ↑ • ((S • CZ) • H ↑ ^ 3)    ≈⟨ cright assoc ⟩
    H ↑ • (S • (CZ • H ↑ ^ 3))    ≈⟨ sym assoc ⟩
    (H ↑ • S) • (CZ • H ↑ ^ 3)    ≈⟨ cleft (sym (lemma-comm-S-w↑ H)) ⟩
    (S • H ↑) • (CZ • H ↑ ^ 3)    ≈⟨ assoc ⟩
    S • (H ↑ • (CZ • H ↑ ^ 3))    ∎

  -- Powers of a conjugate P • (C • Q) with Q • P ≈ ε.
  conj-pow : ∀ (P C Q : Word (Gen (₂₊ k))) (j : ℕ) → Q • P ≈ ε →
    (P • (C • Q)) ^ (₁₊ j) ≈ P • (C ^ (₁₊ j) • Q)
  conj-pow P C Q zero qp = refl
  conj-pow P C Q (suc j) qp = begin
    (P • (C • Q)) • (P • (C • Q)) ^ (₁₊ j)  ≈⟨ cright (conj-pow P C Q j qp) ⟩
    (P • (C • Q)) • (P • (C ^ ₁₊ j • Q))    ≈⟨ assoc ⟩
    P • ((C • Q) • (P • (C ^ ₁₊ j • Q)))    ≈⟨ cright assoc ⟩
    P • (C • (Q • (P • (C ^ ₁₊ j • Q))))    ≈⟨ cright (cright (sym assoc)) ⟩
    P • (C • ((Q • P) • (C ^ ₁₊ j • Q)))    ≈⟨ cright (cright (cleft qp)) ⟩
    P • (C • (ε • (C ^ ₁₊ j • Q)))          ≈⟨ cright (cright left-unit) ⟩
    P • (C • (C ^ ₁₊ j • Q))                ≈⟨ cright (sym assoc) ⟩
    P • ((C • C ^ ₁₊ j) • Q)                ∎

  -- The p-th power of the DD-CZ escape vanishes: (₀,·),(₀,·) pattern.
  ddp-00 : ∀ (b g : ℤ ₚ) →
    ((DDCZ.dir-of ((₀ , b) ∷ (₀ , g) ∷ []) ↓ᵏ k)) ^ p ≈ ε
  ddp-00 b g = axiom order-CZ

  -- (₀,·),(a≠0,·) pattern: H↑-conjugate of CZ.
  ddp-0c : ∀ (b g : ℤ ₚ) (c' : Fin (₁₊ p-2)) →
    ((DDCZ.dir-of ((₀ , b) ∷ (₁₊ c' , g) ∷ []) ↓ᵏ k)) ^ p ≈ ε
  ddp-0c b g c' = begin
    (H ↑ • (CZ • H ↑ ^ 3)) ^ p       ≈⟨ conj-pow (H ↑) CZ (H ↑ ^ 3) (₁₊ p-2)
                                          (lemma-cong↑ (H ^ 3 • H) ε (H3H≈ε {k})) ⟩
    H ↑ • (CZ ^ p • H ↑ ^ 3)         ≈⟨ cright (cleft (axiom order-CZ)) ⟩
    H ↑ • (ε • H ↑ ^ 3)              ≈⟨ cright left-unit ⟩
    H ↑ • H ↑ ^ 3                    ≈⟨ lemma-cong↑ (H ^ 4) ε (PB.axiom order-H) ⟩
    ε ∎

  -- (a≠0,·),(₀,·) pattern: H-conjugate of CZ.
  ddp-a0 : ∀ (a' : Fin (₁₊ p-2)) (b g : ℤ ₚ) →
    ((DDCZ.dir-of ((₁₊ a' , b) ∷ (₀ , g) ∷ []) ↓ᵏ k)) ^ p ≈ ε
  ddp-a0 a' b g = begin
    (H • (CZ • H ^ 3)) ^ p           ≈⟨ conj-pow H CZ (H ^ 3) (₁₊ p-2) H3H≈ε ⟩
    H • (CZ ^ p • H ^ 3)             ≈⟨ cright (cleft (axiom order-CZ)) ⟩
    H • (ε • H ^ 3)                  ≈⟨ cright left-unit ⟩
    H • H ^ 3                        ≈⟨ axiom order-H ⟩
    ε ∎

  -- Powers of a product of commuting words.
  pow-•-comm : ∀ (X Y : Word (Gen (₂₊ k))) (j : ℕ) → X • Y ≈ Y • X →
    (X • Y) ^ j ≈ X ^ j • Y ^ j
  pow-•-comm X Y zero c = sym left-unit
  pow-•-comm X Y (suc zero) c = refl
  pow-•-comm X Y (suc (suc j)) c = begin
    (X • Y) • (X • Y) ^ ₁₊ j        ≈⟨ cright (pow-•-comm X Y (suc j) c) ⟩
    (X • Y) • (X ^ ₁₊ j • Y ^ ₁₊ j) ≈⟨ assoc ⟩
    X • (Y • (X ^ ₁₊ j • Y ^ ₁₊ j)) ≈⟨ cright (sym assoc) ⟩
    X • ((Y • X ^ ₁₊ j) • Y ^ ₁₊ j) ≈⟨ cright (cleft (comm⇒pow-comm 1 (₁₊ j) (sym c))) ⟩
    X • ((X ^ ₁₊ j • Y) • Y ^ ₁₊ j) ≈⟨ cright assoc ⟩
    X • (X ^ ₁₊ j • (Y • Y ^ ₁₊ j)) ≈⟨ sym assoc ⟩
    (X • X ^ ₁₊ j) • (Y • Y ^ ₁₊ j) ∎

  -- (a≠0,·),(c≠0,·) pattern: an H•H↑-conjugate of CZ times commuting
  -- S-powers, all of which vanish at the p-th power.
  ddp-cc : ∀ (a' c' : Fin (₁₊ p-2)) (b g : ℤ ₚ) →
    ((DDCZ.dir-of ((₁₊ a' , b) ∷ (₁₊ c' , g) ∷ []) ↓ᵏ k)) ^ p ≈ ε
  ddp-cc a' c' b g = trans (refl'ᵣ (Eq.cong (_^ p) pad-fix)) (begin
    W ^ p               ≈⟨ ^-cong W (P • (Cx • Q)) p W≈PCQ ⟩
    (P • (Cx • Q)) ^ p  ≈⟨ conj-pow P Cx Q (₁₊ p-2) QP ⟩
    P • (Cx ^ p • Q)    ≈⟨ cright (cleft Cxp) ⟩
    P • (ε • Q)         ≈⟨ cright left-unit ⟩
    P • Q               ≈⟨ PQ ⟩
    ε ∎)
    where
    u = - (₁₊ c') * ((₁₊ a' , λ ()) ⁻¹) .proj₁
    v = - (₁₊ a') * ((₁₊ c' , λ ()) ⁻¹) .proj₁

    W P Cx Q : Word (Gen (₂₊ k))
    W  = H • (H ↑ • (CZ • (S^ u • (H ^ 3 • (S^ v ↑ • H ↑ ^ 3)))))
    P  = H • H ↑
    Cx = CZ • (S^ u • S^ v ↑)
    Q  = H ^ 3 • H ↑ ^ 3

    pad-fix : (DDCZ.dir-of ((₁₊ a' , b) ∷ (₁₊ c' , g) ∷ []) ↓ᵏ k) ≡ W
    pad-fix = Eq.cong₂
      (λ x y → H • (H ↑ • (CZ • (x • (H ^ 3 • (y • H ↑ ^ 3))))))
      (S^-↓ᵏ u k)
      (Eq.trans (↑↓ᵏ-comm (S^ v) k) (Eq.cong _↑ (S^-↓ᵏ v k)))

    W≈PCQ : W ≈ P • (Cx • Q)
    W≈PCQ = begin
      W ≈⟨ cright (cright (cright (cright (sym assoc)))) ⟩
      H • (H ↑ • (CZ • (S^ u • ((H ^ 3 • S^ v ↑) • H ↑ ^ 3))))
        ≈⟨ cright (cright (cright (cright (cleft
             (comm⇒pow-comm 3 1 (lemma-comm-H-w↑ (S^ v))))))) ⟩
      H • (H ↑ • (CZ • (S^ u • ((S^ v ↑ • H ^ 3) • H ↑ ^ 3))))
        ≈⟨ cright (cright (cright (cright assoc))) ⟩
      H • (H ↑ • (CZ • (S^ u • (S^ v ↑ • (H ^ 3 • H ↑ ^ 3)))))
        ≈⟨ cright (cright (cright (sym assoc))) ⟩
      H • (H ↑ • (CZ • ((S^ u • S^ v ↑) • Q)))
        ≈⟨ cright (cright (sym assoc)) ⟩
      H • (H ↑ • ((CZ • (S^ u • S^ v ↑)) • Q))
        ≈⟨ cright (sym assoc) ⟩
      H • ((H ↑ • Cx) • Q)
        ≈⟨ sym assoc ⟩
      (H • (H ↑ • Cx)) • Q
        ≈⟨ cleft (sym assoc) ⟩
      ((H • H ↑) • Cx) • Q
        ≈⟨ assoc ⟩
      P • (Cx • Q) ∎

    QP : Q • P ≈ ε
    QP = begin
      (H ^ 3 • H ↑ ^ 3) • (H • H ↑)   ≈⟨ assoc ⟩
      H ^ 3 • (H ↑ ^ 3 • (H • H ↑))   ≈⟨ cright (sym assoc) ⟩
      H ^ 3 • ((H ↑ ^ 3 • H) • H ↑)   ≈⟨ cright (cleft (sym (lemma-comm-H-w↑ (H ^ 3)))) ⟩
      H ^ 3 • ((H • H ↑ ^ 3) • H ↑)   ≈⟨ cright assoc ⟩
      H ^ 3 • (H • (H ↑ ^ 3 • H ↑))   ≈⟨ cright (cright (lemma-cong↑ (H ^ 3 • H) ε (H3H≈ε {k}))) ⟩
      H ^ 3 • (H • ε)                 ≈⟨ cright right-unit ⟩
      H ^ 3 • H                       ≈⟨ H3H≈ε {₁₊ k} ⟩
      ε ∎

    comm-CZ-T : CZ • (S^ u • S^ v ↑) ≈ (S^ u • S^ v ↑) • CZ
    comm-CZ-T = begin
      CZ • (S^ u • S^ v ↑)   ≈⟨ sym assoc ⟩
      (CZ • S^ u) • S^ v ↑   ≈⟨ cleft (comm⇒pow-comm 1 (toℕ u) (axiom comm-CZ-S↓)) ⟩
      (S^ u • CZ) • S^ v ↑   ≈⟨ assoc ⟩
      S^ u • (CZ • S^ v ↑)   ≈⟨ cright (cright (refl'ᵣ (Eq.sym (pow-↑ S (toℕ v))))) ⟩
      S^ u • (CZ • (S ↑) ^ toℕ v)
        ≈⟨ cright (comm⇒pow-comm 1 (toℕ v) (axiom comm-CZ-S↑)) ⟩
      S^ u • ((S ↑) ^ toℕ v • CZ)
        ≈⟨ cright (cleft (refl'ᵣ (pow-↑ S (toℕ v)))) ⟩
      S^ u • (S^ v ↑ • CZ)   ≈⟨ sym assoc ⟩
      (S^ u • S^ v ↑) • CZ   ∎

    comm-uv : S^ u • S^ v ↑ ≈ S^ v ↑ • S^ u
    comm-uv = begin
      S^ u • S^ v ↑          ≈⟨ cright (refl'ᵣ (Eq.sym (pow-↑ S (toℕ v)))) ⟩
      S^ u • (S ↑) ^ toℕ v   ≈⟨ comm⇒pow-comm (toℕ u) (toℕ v) (sym (axiom comm-S)) ⟩
      (S ↑) ^ toℕ v • S^ u   ≈⟨ cleft (refl'ᵣ (pow-↑ S (toℕ v))) ⟩
      S^ v ↑ • S^ u          ∎

    Cxp : Cx ^ p ≈ ε
    Cxp = begin
      (CZ • (S^ u • S^ v ↑)) ^ p
        ≈⟨ pow-•-comm CZ (S^ u • S^ v ↑) p comm-CZ-T ⟩
      CZ ^ p • (S^ u • S^ v ↑) ^ p
        ≈⟨ cong (axiom order-CZ) (pow-•-comm (S^ u) (S^ v ↑) p comm-uv) ⟩
      ε • ((S^ u) ^ p • (S^ v ↑) ^ p)
        ≈⟨ left-unit ⟩
      (S^ u) ^ p • (S^ v ↑) ^ p
        ≈⟨ cong (S-pow-p {₁₊ k} (toℕ u))
                (trans (refl'ᵣ (pow-↑ (S ^ toℕ v) p))
                       (lemma-cong↑ ((S ^ toℕ v) ^ p) ε (S-pow-p {k} (toℕ v)))) ⟩
      ε • ε   ≈⟨ left-unit ⟩
      ε ∎

    PQ : P • Q ≈ ε
    PQ = begin
      (H • H ↑) • (H ^ 3 • H ↑ ^ 3)   ≈⟨ assoc ⟩
      H • (H ↑ • (H ^ 3 • H ↑ ^ 3))   ≈⟨ cright (sym assoc) ⟩
      H • ((H ↑ • H ^ 3) • H ↑ ^ 3)   ≈⟨ cright (cleft (comm⇒pow-comm 1 3 (sym (lemma-comm-H-w↑ H)))) ⟩
      H • ((H ^ 3 • H ↑) • H ↑ ^ 3)   ≈⟨ cright assoc ⟩
      H • (H ^ 3 • (H ↑ • H ↑ ^ 3))   ≈⟨ cright (cright (lemma-cong↑ (H ^ 4) ε (PB.axiom order-H))) ⟩
      H • (H ^ 3 • ε)                 ≈⟨ cright right-unit ⟩
      H • H ^ 3                       ≈⟨ axiom order-H ⟩
      ε ∎

  -- The escape of a pair with (₀,·) second box commutes with S ↑.
  comm-W-S↑ : ∀ (d1 : D) (g2 : ℤ ₚ) →
    (DDCZ.dir-of (d1 ∷ (₀ , g2) ∷ []) ↓ᵏ k) • S ↑ ≈
    S ↑ • (DDCZ.dir-of (d1 ∷ (₀ , g2) ∷ []) ↓ᵏ k)
  comm-W-S↑ (₀ , b1) g2 = axiom comm-CZ-S↑
  comm-W-S↑ (₁₊ _ , b1) g2 = begin
    (H • (CZ • H ^ 3)) • S ↑      ≈⟨ assoc ⟩
    H • ((CZ • H ^ 3) • S ↑)      ≈⟨ cright assoc ⟩
    H • (CZ • (H ^ 3 • S ↑))      ≈⟨ cright (cright commH3-S↑) ⟩
    H • (CZ • (S ↑ • H ^ 3))      ≈⟨ cright (sym assoc) ⟩
    H • ((CZ • S ↑) • H ^ 3)      ≈⟨ cright (cleft (axiom comm-CZ-S↑)) ⟩
    H • ((S ↑ • CZ) • H ^ 3)      ≈⟨ cright assoc ⟩
    H • (S ↑ • (CZ • H ^ 3))      ≈⟨ sym assoc ⟩
    (H • S ↑) • (CZ • H ^ 3)      ≈⟨ cleft (sym (axiom comm-H)) ⟩
    (S ↑ • H) • (CZ • H ^ 3)      ≈⟨ assoc ⟩
    S ↑ • (H • (CZ • H ^ 3))      ∎
    where
    commH3-S↑ : H ^ 3 • S ↑ ≈ S ↑ • H ^ 3
    commH3-S↑ = begin
      (H • (H • H)) • S ↑    ≈⟨ assoc ⟩
      H • ((H • H) • S ↑)    ≈⟨ cright assoc ⟩
      H • (H • (H • S ↑))    ≈⟨ cright (cright (sym (axiom comm-H))) ⟩
      H • (H • (S ↑ • H))    ≈⟨ cright (sym assoc) ⟩
      H • ((H • S ↑) • H)    ≈⟨ cright (cleft (sym (axiom comm-H))) ⟩
      H • ((S ↑ • H) • H)    ≈⟨ cright assoc ⟩
      H • (S ↑ • (H • H))    ≈⟨ sym assoc ⟩
      (H • S ↑) • (H • H)    ≈⟨ cleft (sym (axiom comm-H)) ⟩
      (S ↑ • H) • (H • H)    ≈⟨ assoc ⟩
      S ↑ • (H • (H • H))    ∎

------------------------------------------------------------------------
-- order-H residuals on inj₂ cosets: the D box 4-cycles under
-- Hd' (a,b) = (b, -a) (a total map, so the whole orbit computes), and
-- the four Hdir escapes collapse to H ^ 4 ≈ ε after normalising the
-- negated-zero components.  The fully nonzero pattern (ZM-word escapes)
-- is not covered here.

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)
  open PP ((₁₊ m) QRel,_===_)

  private
    dcong : {d d' : D} → d ≡ d' → (Hdir d ↓ᵏ m) ≡ (Hdir d' ↓ᵏ m)
    dcong = Eq.cong (λ v → Hdir v ↓ᵏ m)

    z-z : - - ₀ ≡ ₀
    z-z = Eq.trans (Eq.cong -_ -0#≈0#) -0#≈0#

  orderH-resid-00 :
    (Hdir (₀ , ₀) ↓ᵏ m) •
    ((Hdir (₀ , - ₀) ↓ᵏ m) •
     ((Hdir (- ₀ , - ₀) ↓ᵏ m) • (Hdir (- ₀ , - - ₀) ↓ᵏ m))) ≈ ε
  orderH-resid-00 = trans
    (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (dcong (Eq.cong (₀ ,_) -0#≈0#))
      (Eq.cong₂ _•_
        (dcong (Eq.cong₂ _,_ -0#≈0# -0#≈0#))
        (dcong (Eq.cong₂ _,_ -0#≈0# z-z))))))
    (axiom order-H)

  orderH-resid-0b : ∀ (b' z : Fin (₁₊ p-2)) → - ₁₊ b' ≡ ₁₊ z →
    (Hdir (₀ , ₁₊ b') ↓ᵏ m) •
    ((Hdir (₁₊ b' , - ₀) ↓ᵏ m) •
     ((Hdir (- ₀ , - ₁₊ b') ↓ᵏ m) • (Hdir (- ₁₊ b' , - - ₀) ↓ᵏ m))) ≈ ε
  orderH-resid-0b b' z eq-z = trans
    (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (dcong (Eq.cong (₁₊ b' ,_) -0#≈0#))
      (Eq.cong₂ _•_
        (dcong (Eq.cong₂ _,_ -0#≈0# eq-z))
        (dcong (Eq.cong₂ _,_ eq-z z-z))))))
    (trans left-unit
    (trans (cright left-unit)
    (trans assoc (axiom order-H))))

  orderH-resid-a0 : ∀ (a' y : Fin (₁₊ p-2)) → - ₁₊ a' ≡ ₁₊ y →
    (Hdir (₁₊ a' , ₀) ↓ᵏ m) •
    ((Hdir (₀ , - ₁₊ a') ↓ᵏ m) •
     ((Hdir (- ₁₊ a' , - ₀) ↓ᵏ m) • (Hdir (- ₀ , - - ₁₊ a') ↓ᵏ m))) ≈ ε
  orderH-resid-a0 a' y eq-y = trans
    (refl'ᵣ (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (dcong (Eq.cong (₀ ,_) eq-y))
      (Eq.cong₂ _•_
        (dcong (Eq.cong₂ _,_ eq-y -0#≈0#))
        (dcong (Eq.cong₂ _,_ -0#≈0# (-‿involutive (₁₊ a'))))))))
    (trans (cright left-unit)
    (trans (cright right-unit)
    (trans assoc (axiom order-H))))
