------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c10 on doubly-inj₂ boxes (₀,b1)/(₀,₁₊b2').  The middle H↑
-- escapes ε and rotates b₂ into the a-slot, so the final CZ escapes in
-- H↑-conjugated form W = H↑•CZ•H↑³; on the RHS the S⁻¹↑ chunks shift
-- b₂ back (nsum-p-1) and the Hdir unit collapses to a single S↑.  The
-- residual identity CZ•W ≈ S⁻¹↑•W•S↑•S⁻¹ reduces via the axiom to the
-- one-wire fact TW : S⁻¹•H•S⁻¹•H³ ≈ H³•S, proved with the ZM-calculus
-- (the word completes to ZM(-1) ≈ HH, and S commutes with HH).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Vec using ([] ; _∷_)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-cong↑)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿distribˡ-* ; -‿distribʳ-*)

import Data.Nat.Properties as NP

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM p-2 p-prime
  using (hpad ; ineg)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDCZ p-2 p-prime
  using (pow-↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ p-2 p-prime
  using (↓-pow-S)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2 p-2 p-prime
  using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10 p-2 p-prime
  using (nsum-p-1)

------------------------------------------------------------------------
-- The one-wire identity TW : S⁻¹ • H • S⁻¹ • H³ ≈ H³ • S.  The word
-- S⁻¹•H•S⁻¹ completes on the right to the ZM(-1) word (≈ HH by
-- lemma-HH-M-1), and S slides through HH by lemma-S^kM at x = -1.

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)
  open PP ((₁₊ j) QRel,_===_)
  open Lemmas0 j

  private
    SI : Word (Gen (₁₊ j))
    SI = S ^ p-1

  -- S^(p-1) • S ≈ S^p ≈ ε (self-commutation reshuffles the powers).
  Sp-1-S : SI • S ≈ ε
  Sp-1-S = trans (comm⇒pow-comm {w = S} {v = S} p-1 1 refl)
                 (axiom order-S)

  -- H³ • H³ ≈ H² (an inner H⁴ cancels).
  H33 : H ^ 3 • H ^ 3 ≈ H • H
  H33 = trans assoc (cright (trans assoc
    (trans (cright (cright (sym assoc)))
    (trans (cright (sym assoc))
    (trans (sym assoc)
    (trans (cleft (axiom order-H)) left-unit))))))

  -- S^(-1) is S^(p-1) on the nose.
  SIfix : S^ (- ₁) ≡ SI
  SIfix = Eq.cong (S ^_) lemma-toℕ-1ₚ

  -- The inserted bracket collapses: H•S⁻¹•H • H³•S•H³ ≈ ε.
  bracketε : (H • (SI • H)) • (H ^ 3 • (S • H ^ 3)) ≈ ε
  bracketε =
    trans assoc
    (trans (cright assoc)
    (trans (cright (cright (sym assoc)))
    (trans (cright (cright (cleft (axiom order-H))))
    (trans (cright (cright left-unit))
    (trans (cright (sym assoc))
    (trans (cright (cleft Sp-1-S))
    (trans (cright left-unit)
           (axiom order-H))))))))

  -- The regrouped six-letter word is literally the ZM(-1) word.
  ZMword : SI • (H • (SI • (H • (SI • H)))) ≡ ZM -'₁
  ZMword = Eq.cong₂ (λ u v → u • (H • (v • (H • (u • H)))))
    (Eq.sym SIfix)
    (Eq.trans (Eq.sym SIfix) (Eq.cong S^ (Eq.sym aux-₁⁻¹)))

  -- S⁻¹ • H • S⁻¹ ≈ H • S • H³ by completing to ZM(-1) ≈ HH.
  core : SI • (H • SI) ≈ H • (S • H ^ 3)
  core =
    trans (sym right-unit)
    (trans (cright (sym bracketε))
    (trans (sym assoc)
    (trans (cleft (trans assoc (trans (cright assoc) (refl' ZMword))))
    (trans (cleft (sym lemma-HH-M-1))
    (trans assoc
    (trans (cright (sym assoc))
    (trans (cright (cleft (axiom order-H)))
           (cright left-unit))))))))

  -- S commutes with HH (= ZM(-1); the semi-relation exponent is 1).
  SHH : S • (H • H) ≈ (H • H) • S
  SHH =
    trans (cright lemma-HH-M-1)
    (trans (lemma-S^kM (- ₁) ₁ (-'₁ .proj₂))
    (trans (cright (refl' (Eq.cong S^ val1)))
           (cleft (sym lemma-HH-M-1))))
    where
    i₁ = ((-'₁) ⁻¹) .proj₁
    val1 : ₁ * (i₁ * i₁) ≡ ₁
    val1 = Eq.trans (*-identityˡ (i₁ * i₁))
      (Eq.trans (Eq.cong₂ _*_ aux-₁⁻¹ aux-₁⁻¹) aux-₁²)

  TW : SI • (H • (SI • H ^ 3)) ≈ H ^ 3 • S
  TW =
    trans (cright (sym assoc))
    (trans (sym assoc)
    (trans (cleft core)
    (trans assoc
    (trans (cright assoc)
    (trans (cright (cright H33))
    (trans (cright SHH)
           (sym assoc)))))))

------------------------------------------------------------------------
-- The diagonal Hdir unit is a single S: ZM(b/b) • S^(b/b) ≈ S.

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)
  open Lemmas0 m

  unitS : ∀ (u : Fin (₁₊ p-2)) → (Hdir (₁₊ u , ₁₊ u) ↓ᵏ m) ≈ S
  unitS u =
    trans (refl' (hpad u u))
    (trans (cong (aux-MM (Q .proj₂) (λ ()) Qv) (refl' (Eq.cong S^ Rv)))
    (trans (cleft (sym lemma-M1)) left-unit))
    where
    Q = (₁₊ u , λ ()) *' ((₁₊ u , λ ()) ⁻¹)
    inst-u = nztoℕ {y = ₁₊ u} {neq0 = λ ()}
    Qv : Q .proj₁ ≡ ₁
    Qv = lemma-⁻¹ʳ (₁₊ u) {{inst-u}}
    Rv : ₁₊ u * ((₁₊ u , λ ()) ⁻¹) .proj₁ ≡ ₁
    Rv = lemma-⁻¹ʳ (₁₊ u) {{inst-u}}

------------------------------------------------------------------------
-- The residual identity and the pattern itself, at width ₂₊ m.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

    W : Word (Gen (₂₊ m))
    W = H ↑ • (CZ • (H ↑) ^ 3)

  -- S⁻¹↑ commutes with CZ (comm-CZ-S↑ powered).
  SupCZ : S⁻¹ ↑ • CZ ≈ CZ • S⁻¹ ↑
  SupCZ =
    trans (cleft (refl' (Eq.sym (pow-↑ S p-1))))
    (trans (comm⇒pow-comm {w = S ↑} {v = CZ} p-1 1 (sym (axiom comm-CZ-S↑)))
           (cright (refl' (pow-↑ S p-1))))

  -- Bottom S⁻¹ commutes with H↑³.
  Scomm3 : S⁻¹ • (H ↑) ^ 3 ≈ (H ↑) ^ 3 • S⁻¹
  Scomm3 = comm⇒pow-comm {w = S} {v = H ↑} p-1 3 (lemma-comm-S-w↑ H)

  -- TW lifted to the top wire.
  TWlift : S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (H ↑) ^ 3)) ≈ (H ↑) ^ 3 • S ↑
  TWlift = lemma-cong↑ (S⁻¹ • (H • (S⁻¹ • H ^ 3))) (H ^ 3 • S) TW

  -- The key residual identity: CZ • W ≈ S⁻¹↑ • (W • (S↑ • S⁻¹)).
  residkey : CZ • W ≈ S⁻¹ ↑ • (W • (S ↑ • S⁻¹))
  residkey =
    trans (cright (sym assoc))
    (trans (sym assoc)
    (trans (cleft (axiom selinger-c10))
    (trans (cleft (refl' fixdown))
    (trans assoc (cright inner)))))
    where
    fixdown : S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
              S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))
    fixdown = Eq.cong
      (λ u → S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • u))))))
      (↓-pow-S p-1)

    inner : (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹))))) • (H ↑) ^ 3 ≈
            W • (S ↑ • S⁻¹)
    inner =
      trans assoc
      (trans (cright assoc)
      (trans (cright (cright assoc))
      (trans (cright (cright (cright assoc)))
      (trans (cright (cright (cright (cright assoc))))
      (trans (cright (cright (cright (cright (cright Scomm3)))))
      (trans (cright (cright (cright (cright (sym assoc)))))
      (trans (cright (cright (cright (sym assoc))))
      (trans (cright (sym assoc))
      (trans (cright (cleft SupCZ))
      (trans (cright assoc)
      (trans (cright (cright (sym assoc)))
      (trans (cright (cright (cleft TWlift)))
      (trans (cright (cright assoc))
      (trans (cright (sym assoc)) (sym assoc)))))))))))))))

  c10-go-0b2 : ∀ (b1 : ℤ ₚ) (b2' : Fin (₁₊ p-2)) (lm2 : C (₁₊ m)) →
    ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , ₁₊ b2') , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₀ , ₁₊ b2') , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-0b2 b1 b2' lm2 = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    z00 : - ₀ + - ₀ ≡ ₀
    z00 = Eq.trans (Eq.cong₂ _+_ -0#≈0# -0#≈0#) (+-identityʳ ₀)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , ₁₊ b2') , lm2)

    -- The S-orbit value fixes: p-1 steps shift b by +(₁₊ b2').
    nfix : nsum p-1 (- ₁₊ b2') ≡ ₁₊ b2'
    nfix = Eq.trans (nsum-p-1 (- ₁₊ b2')) (-‿involutive (₁₊ b2'))

    bfix3 : - ₀ + nsum p-1 (- ₁₊ b2') ≡ ₁₊ b2'
    bfix3 = Eq.trans (Eq.cong₂ _+_ -0#≈0# nfix) (+-0ˡ (₁₊ b2'))

    bfix6 : - ₁₊ b2' + nsum p-1 (- ₁₊ b2') ≡ ₀
    bfix6 = Eq.trans (Eq.cong (- ₁₊ b2' +_) nfix) (+-inverseˡ (₁₊ b2'))

    -- LHS: fix the stuck slots; the escapes are CZ, ε, and W.
    L-fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₁ ≡
            CZ • ((Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ • W)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → (Hdir (₀ , v) ↓ᵏ m) ↑) (e0 (₁₊ b2')))
      (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ ((₀ , b1 + - ₀) , inj₂ (Hd' (₀ , v) , lm2)))
          (e0 (₁₊ b2')))))

    L-c : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₂ ≡
          inj₂ ((₀ , b1 + - ₁₊ b2') , inj₂ ((₁₊ b2' , ₀) , lm2))
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ ((₀ , b1 + - ₀) , inj₂ (Hd' (₀ , v) , lm2)))
          (e0 (₁₊ b2'))))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₁₊ b2' , w) , lm2)))
        (Eq.cong (_+ - ₁₊ b2') (e0 b1))
        z00)

    -- RHS letters: the two a≠0 S⁻¹↑ chunks and the Hdir unit are the
    -- only ≈-level escapes; everything else is ≡.
    E₃raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ b2' , - ₀) , lm2)) S⁻¹) .proj₁
    E₆raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ b2' , - ₁₊ b2') , lm2)) S⁻¹) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1 : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (S⁻¹ ↑)) ≡
         ((S ^ p-1) ↑ , inj₂ ((₀ , b1) , lm))
    r1 = Eq.trans (ract-↑-≡ (₀ , b1) lm S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (₁₊ b2') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
          (Eq.trans (ract-S^-coset (₀ , ₁₊ b2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2)) (it-dDS-a0 p-1 (₁₊ b2'))))))

    r3fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ b2' , - ₀) , lm2)))
              (S⁻¹ ↑)) ≡
            (E₃raw ↑ , inj₂ ((₀ , b1) , inj₂ ((₁₊ b2' , ₁₊ b2') , lm2)))
    r3fix = Eq.trans (ract-↑-≡ (₀ , b1) (inj₂ ((₁₊ b2' , - ₀) , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ b2' , - ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ b2') (- ₀) (λ ()))
                (Eq.cong (₁₊ b2' ,_) bfix3))))))

    r5fix : ((ract2 ᵗ) (inj₂ ((₀ , b1 + - ₁₊ b2') ,
              inj₂ ((₁₊ b2' , ₁₊ b2' + - ₀) , lm2))) (H ↑)) ≡
            ((Hdir (₁₊ b2' , ₁₊ b2') ↓ᵏ m) ↑ ,
             inj₂ ((₀ , b1 + - ₁₊ b2') ,
               inj₂ ((₁₊ b2' , - ₁₊ b2') , lm2)))
    r5fix = Eq.cong (λ v → ((Hdir (₁₊ b2' , v) ↓ᵏ m) ↑ ,
        inj₂ ((₀ , b1 + - ₁₊ b2') , inj₂ (Hd' (₁₊ b2' , v) , lm2))))
      (e0 (₁₊ b2'))

    r6fix : ((ract2 ᵗ) (inj₂ ((₀ , b1 + - ₁₊ b2') ,
              inj₂ ((₁₊ b2' , - ₁₊ b2') , lm2))) (S⁻¹ ↑)) ≡
            (E₆raw ↑ , inj₂ ((₀ , b1 + - ₁₊ b2') ,
              inj₂ ((₁₊ b2' , ₀) , lm2)))
    r6fix = Eq.trans
      (ract-↑-≡ (₀ , b1 + - ₁₊ b2') (inj₂ ((₁₊ b2' , - ₁₊ b2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₀ , b1 + - ₁₊ b2') , c))
          (Eq.trans (ract-S^-coset (₁₊ b2' , - ₁₊ b2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ b2') (- ₁₊ b2') (λ ()))
                (Eq.cong (₁₊ b2' ,_) bfix6))))))

    c₆ : C (₃₊ m)
    c₆ = inj₂ ((₀ , b1 + - ₁₊ b2') , inj₂ ((₁₊ b2' , ₀) , lm2))

    R-fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            (S ^ p-1) ↑ • ((Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ •
              (E₃raw ↑ • (W • ((Hdir (₁₊ b2' , ₁₊ b2') ↓ᵏ m) ↑ •
                (E₆raw ↑ • S ^ p-1)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1)
      (Eq.cong ((S ^ p-1) ↑ •_)
      (Eq.cong (λ t → (Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3fix)
      (Eq.cong (λ t → E₃raw ↑ • t)
      (Eq.cong (λ t → W • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5fix)
      (Eq.cong (λ t → (Hdir (₁₊ b2' , ₁₊ b2') ↓ᵏ m) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6fix)
      (Eq.cong (λ t → E₆raw ↑ • t)
        (Eq.trans (Eq.cong (λ w → ((ract2 ᵗ) c₆ w) .proj₁) (↓-pow-S p-1))
          (ract-S^-resid-a0 (b1 + - ₁₊ b2')
            (inj₂ ((₁₊ b2' , ₀) , lm2)) p-1)))))))))))

    -- Collapse the ≈-level escapes: ε-units, the diagonal Hdir ≈ S↑.
    Rclean : (S ^ p-1) ↑ • ((Hdir (₀ , ₁₊ b2') ↓ᵏ m) ↑ •
               (E₃raw ↑ • (W • ((Hdir (₁₊ b2' , ₁₊ b2') ↓ᵏ m) ↑ •
                 (E₆raw ↑ • S ^ p-1))))) ≈
             S⁻¹ ↑ • (W • (S ↑ • S⁻¹))
    Rclean =
      trans (cright left-unit)
      (trans (cright (trans (cleft (lemma-cong↑ E₃raw ε
          (ract-S^-resid-a+ (₁₊ b2' , - ₀) lm2 p-1 (λ ())))) left-unit))
      (trans (cright (cright (cleft
          (lemma-cong↑ (Hdir (₁₊ b2' , ₁₊ b2') ↓ᵏ m) S (unitS b2')))))
             (cright (cright (cright (trans (cleft (lemma-cong↑ E₆raw ε
          (ract-S^-resid-a+ (₁₊ b2' , - ₁₊ b2') lm2 p-1 (λ ()))))
          left-unit))))))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (cright left-unit)
      (trans residkey
      (sym (trans (refl' R-fix) Rclean))))

    R-c : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡
          inj₂ ((₀ , b1 + - ₁₊ b2') , inj₂ ((₁₊ b2' , ₀) , lm2))
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3fix)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5fix)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6fix)
      (Eq.trans (Eq.cong (λ w → ((ract2 ᵗ) c₆ w) .proj₂) (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₀ , b1 + - ₁₊ b2')
          (inj₂ ((₁₊ b2' , ₀) , lm2)) p-1)
        (Eq.cong (λ d → inj₂ (d , inj₂ ((₁₊ b2' , ₀) , lm2)))
          (it-dDS-a0 p-1 (b1 + - ₁₊ b2'))))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)

------------------------------------------------------------------------
-- The second one-wire identity TW2 : H • S⁻¹ • H • S⁻¹ ≈ S • H,
-- immediate from core and SHH.

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)

  -- HH • H³ ≈ H (an inner H⁴ cancels).
  HHH3 : (H • H) • H ^ 3 ≈ H
  HHH3 = trans assoc
    (trans (cright (cright (sym assoc)))
    (trans (cright (sym assoc))
    (trans (sym assoc)
    (trans (cleft (axiom order-H)) left-unit))))

  -- H³ • HH ≈ H likewise.
  H5 : H ^ 3 • (H • H) ≈ H
  H5 = trans assoc (trans (cright (trans assoc (axiom order-H))) right-unit)

  TW2 : H • (S⁻¹ • (H • S⁻¹)) ≈ S • H
  TW2 =
    trans (cright core)
    (trans (sym assoc)
    (trans (sym assoc)
    (trans (cleft (sym SHH))
    (trans assoc (cright HHH3)))))

------------------------------------------------------------------------
-- The residual identity for the (₀,·)/(₁₊,₀) pattern:
-- W • HH↑ • CZ ≈ S↑ • W • HH↑ • S⁻¹↑ • S⁻¹.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)

  private
    W2 : Word (Gen (₂₊ m))
    W2 = H ↑ • (CZ • (H ↑) ^ 3)

  H5lift : (H {m} ↑) ^ 3 • (H ↑ • H ↑) ≈ H ↑
  H5lift = lemma-cong↑ (H ^ 3 • (H • H)) H H5

  TW2lift : H {m} ↑ • (S⁻¹ ↑ • (H ↑ • S⁻¹ ↑)) ≈ S ↑ • H ↑
  TW2lift = lemma-cong↑ (H • (S⁻¹ • (H • S⁻¹))) (S • H) TW2

  fixdown2 : S⁻¹ {m} ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹ ↓))))) ≡
             S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • S⁻¹)))))
  fixdown2 = Eq.cong
    (λ u → S⁻¹ ↑ • (H ↑ • (S⁻¹ ↑ • (CZ • (H ↑ • (S⁻¹ ↑ • u))))))
    (↓-pow-S p-1)

  -- W • (HH↑ • Z) collapses to H↑ • (CZ • (H↑ • Z)) by H↑⁵ ≈ H↑.
  collapseWHH : ∀ (Z : Word (Gen (₂₊ m))) →
    W2 • (HH ↑ • Z) ≈ H ↑ • (CZ • (H ↑ • Z))
  collapseWHH Z =
    trans assoc
    (trans (cright assoc)
    (trans (cright (cright (sym assoc)))
           (cright (cright (cleft H5lift)))))

  resid2key : W2 • (HH ↑ • CZ) ≈ S ↑ • (W2 • (HH ↑ • (S⁻¹ ↑ • S⁻¹)))
  resid2key =
    trans (collapseWHH CZ)
    (trans (cright (axiom selinger-c10))
    (trans (cright (refl' fixdown2))
    (trans (cright (cright (sym assoc)))
    (trans (cright (sym assoc))
    (trans (sym assoc)
    (trans (cleft TW2lift)
    (trans assoc
           (cright (sym (collapseWHH (S⁻¹ ↑ • S⁻¹)))))))))))

------------------------------------------------------------------------
-- The pattern (₀,b1)/(₁₊ a2',₀): the middle H↑ escapes HH, the CZs
-- escape in conjugated form, and the S⁻¹↑ chunks cycle the box through
-- (₁₊ a2', ₀) → (₁₊ a2', ₁₊ a2') → (₁₊ a2', -₁₊ a2') → (₁₊ a2', ₀).

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract2 = ract {₂₊ m}

    W2' : Word (Gen (₂₊ m))
    W2' = H ↑ • (CZ • (H ↑) ^ 3)

  c10-go-0a0 : ∀ (b1 : ℤ ₚ) (a2' : Fin (₁₊ p-2)) (lm2 : C (₁₊ m)) →
    ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₀) , lm2)))
      (CZ • H ↑ • CZ)) ≋
    ((ract2 ᵗ) (inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₀) , lm2)))
      (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓))
  c10-go-0a0 b1 a2' lm2 = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₁₊ a2' , ₀) , lm2)

    nfixa : nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    nfixa = Eq.trans (nsum-p-1 (- ₁₊ a2')) (-‿involutive (₁₊ a2'))

    bfix1 : ₀ + nsum p-1 (- ₁₊ a2') ≡ ₁₊ a2'
    bfix1 = Eq.trans (Eq.cong (₀ +_) nfixa) (+-0ˡ (₁₊ a2'))

    bfix3 : - ₁₊ a2' + nsum p-1 (- ₁₊ a2') ≡ ₀
    bfix3 = Eq.trans (Eq.cong (- ₁₊ a2' +_) nfixa) (+-inverseˡ (₁₊ a2'))

    -- LHS: the first CZ escapes W, the H↑ escapes HH, the last CZ
    -- escapes CZ.
    L-fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₁ ≡
            W2' • (HH ↑ • CZ)
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.cong (λ v → (Hdir (₁₊ a2' , v) ↓ᵏ m) ↑) (e0 ₀))
      (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ ((₀ , b1 + - ₁₊ a2') ,
            inj₂ (Hd' (₁₊ a2' , v) , lm2)))
          (e0 ₀))))

    L-c : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₂ ≡
          inj₂ ((₀ , b1 + - ₁₊ a2') , inj₂ ((₀ , - ₁₊ a2') , lm2))
    L-c = Eq.trans (Eq.cong (λ pr → ((ract2 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ ((₀ , b1 + - ₁₊ a2') ,
            inj₂ (Hd' (₁₊ a2' , v) , lm2)))
          (e0 ₀)))
      (Eq.cong₂ (λ v w → inj₂ ((₀ , v) , inj₂ ((₀ , w) , lm2)))
        (e0 (b1 + - ₁₊ a2'))
        (e0 (- ₁₊ a2')))

    -- RHS letters.
    E₁raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a2' , ₀) , lm2)) S⁻¹) .proj₁
    E₃raw = ((ract {₁₊ m} ᵗ) (inj₂ ((₁₊ a2' , - ₁₊ a2') , lm2)) S⁻¹) .proj₁

    REST5 = H ↑ • S⁻¹ ↑ • S⁻¹ ↓

    r1fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (S⁻¹ ↑)) ≡
            (E₁raw ↑ , inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₁₊ a2') , lm2)))
    r1fix = Eq.trans (ract-↑-≡ (₀ , b1) lm S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , ₀) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') ₀ (λ ()))
                (Eq.cong (₁₊ a2' ,_) bfix1))))))

    r3fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) ,
              inj₂ ((₁₊ a2' , - ₁₊ a2') , lm2))) (S⁻¹ ↑)) ≡
            (E₃raw ↑ , inj₂ ((₀ , b1) , inj₂ ((₁₊ a2' , ₀) , lm2)))
    r3fix = Eq.trans
      (ract-↑-≡ (₀ , b1) (inj₂ ((₁₊ a2' , - ₁₊ a2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_ Eq.refl
        (Eq.cong (λ c → inj₂ ((₀ , b1) , c))
          (Eq.trans (ract-S^-coset (₁₊ a2' , - ₁₊ a2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (Eq.trans (it-dDS-nz p-1 (₁₊ a2') (- ₁₊ a2') (λ ()))
                (Eq.cong (₁₊ a2' ,_) bfix3))))))

    r5fix : ((ract2 ᵗ) (inj₂ ((₀ , b1 + - ₁₊ a2') ,
              inj₂ ((₁₊ a2' , ₀ + - ₀) , lm2))) (H ↑)) ≡
            ((Hdir (₁₊ a2' , ₀) ↓ᵏ m) ↑ ,
             inj₂ ((₀ , b1 + - ₁₊ a2') , inj₂ ((₀ , - ₁₊ a2') , lm2)))
    r5fix = Eq.cong (λ v → ((Hdir (₁₊ a2' , v) ↓ᵏ m) ↑ ,
        inj₂ ((₀ , b1 + - ₁₊ a2') , inj₂ (Hd' (₁₊ a2' , v) , lm2))))
      (e0 ₀)

    r6fix : ((ract2 ᵗ) (inj₂ ((₀ , b1 + - ₁₊ a2') ,
              inj₂ ((₀ , - ₁₊ a2') , lm2))) (S⁻¹ ↑)) ≡
            ((S ^ p-1) ↑ , inj₂ ((₀ , b1 + - ₁₊ a2') ,
              inj₂ ((₀ , - ₁₊ a2') , lm2)))
    r6fix = Eq.trans
      (ract-↑-≡ (₀ , b1 + - ₁₊ a2') (inj₂ ((₀ , - ₁₊ a2') , lm2)) S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (- ₁₊ a2') lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₀ , b1 + - ₁₊ a2') , c))
          (Eq.trans (ract-S^-coset (₀ , - ₁₊ a2') lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (- ₁₊ a2'))))))

    c₆ : C (₃₊ m)
    c₆ = inj₂ ((₀ , b1 + - ₁₊ a2') , inj₂ ((₀ , - ₁₊ a2') , lm2))

    R-fix : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
              (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁ ≡
            E₁raw ↑ • ((Hdir (₁₊ a2' , ₁₊ a2') ↓ᵏ m) ↑ •
              (E₃raw ↑ • (W2' • ((Hdir (₁₊ a2' , ₀) ↓ᵏ m) ↑ •
                ((S ^ p-1) ↑ • S ^ p-1)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₁)
          r1fix)
      (Eq.cong (λ t → E₁raw ↑ • t)
      (Eq.cong (λ t → (Hdir (₁₊ a2' , ₁₊ a2') ↓ᵏ m) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₁)
          r3fix)
      (Eq.cong (λ t → E₃raw ↑ • t)
      (Eq.cong (λ t → W2' • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₁)
          r5fix)
      (Eq.cong (λ t → (Hdir (₁₊ a2' , ₀) ↓ᵏ m) ↑ • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ • ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₁)
          r6fix)
      (Eq.cong (λ t → (S ^ p-1) ↑ • t)
        (Eq.trans (Eq.cong (λ w → ((ract2 ᵗ) c₆ w) .proj₁) (↓-pow-S p-1))
          (ract-S^-resid-a0 (b1 + - ₁₊ a2')
            (inj₂ ((₀ , - ₁₊ a2') , lm2)) p-1)))))))))))

    Rclean : E₁raw ↑ • ((Hdir (₁₊ a2' , ₁₊ a2') ↓ᵏ m) ↑ •
               (E₃raw ↑ • (W2' • ((Hdir (₁₊ a2' , ₀) ↓ᵏ m) ↑ •
                 ((S ^ p-1) ↑ • S ^ p-1))))) ≈
             S ↑ • (W2' • (HH ↑ • (S⁻¹ ↑ • S⁻¹)))
    Rclean =
      trans (trans (cleft (lemma-cong↑ E₁raw ε
          (ract-S^-resid-a+ (₁₊ a2' , ₀) lm2 p-1 (λ ())))) left-unit)
      (trans (cleft (lemma-cong↑ (Hdir (₁₊ a2' , ₁₊ a2') ↓ᵏ m) S
          (unitS a2')))
             (cright (trans (cleft (lemma-cong↑ E₃raw ε
          (ract-S^-resid-a+ (₁₊ a2' , - ₁₊ a2') lm2 p-1 (λ ()))))
          left-unit)))

    resid≈ : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₁ ≈
             ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans resid2key
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
            (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂ ≡
          inj₂ ((₀ , b1 + - ₁₊ a2') , inj₂ ((₀ , - ₁₊ a2') , lm2))
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (H ↑ • S⁻¹ ↑ • CZ • REST5)) .proj₂)
          r1fix)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (CZ • REST5)) .proj₂)
          r3fix)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↑ • S⁻¹ ↓)) .proj₂)
          r5fix)
      (Eq.trans (Eq.cong
          (λ pr → ((ract2 ᵗ) (pr .proj₂) (S⁻¹ ↓)) .proj₂)
          r6fix)
      (Eq.trans (Eq.cong (λ w → ((ract2 ᵗ) c₆ w) .proj₂) (↓-pow-S p-1))
      (Eq.trans (ract-S^-coset (₀ , b1 + - ₁₊ a2')
          (inj₂ ((₀ , - ₁₊ a2') , lm2)) p-1)
        (Eq.cong (λ d → inj₂ (d , inj₂ ((₀ , - ₁₊ a2') , lm2)))
          (it-dDS-a0 p-1 (b1 + - ₁₊ a2'))))))))

    coset≡ : ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm)) (CZ • H ↑ • CZ)) .proj₂ ≡
             ((ract2 ᵗ) (inj₂ ((₀ , b1) , lm))
               (S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)


------------------------------------------------------------------------
-- TW3 : H • S⁻¹ • H ≈ S • H • S (append S to TW2 and cancel).

module _ {j : ℕ} where
  open PB ((₁₊ j) QRel,_===_)

  SSinv : S • S⁻¹ ≈ ε
  SSinv = axiom order-S

  H4ε : H ^ 4 ≈ ε
  H4ε = axiom order-H

  TW3 : H • (S⁻¹ • H) ≈ S • (H • S)
  TW3 =
    trans (sym right-unit)
    (trans (cright (sym Sp-1-S))
    (trans assoc
    (trans (cright assoc)
    (trans (cright (cright (sym assoc)))
    (trans (cright (sym assoc))
    (trans (sym assoc)
    (trans (cleft TW2) assoc)))))))

------------------------------------------------------------------------
-- The anti-diagonal Hdir unit is HH • S⁻¹: when v ≡ -u the quotient
-- and the phase both take the value -1.

module _ {m : ℕ} where
  open PB ((₁₊ m) QRel,_===_)
  open Lemmas0 m

  unitHS : ∀ (u v : Fin (₁₊ p-2)) → ₁₊ v ≡ - ₁₊ u →
    (Hdir (₁₊ u , ₁₊ v) ↓ᵏ m) ≈ HH • S⁻¹
  unitHS u v veq =
    trans (refl' (hpad u v))
    (trans (cong (aux-MM (Q .proj₂) ((-' (₁ , λ ())) .proj₂) Qv)
                 (refl' (Eq.trans (Eq.cong S^ Rv) SIfix)))
           (cleft (sym lemma-HH-M-1)))
    where
    U* V* : ℤ* ₚ
    U* = (₁₊ u , λ ())
    V* = (₁₊ v , λ ())
    Q = U* *' (V* ⁻¹)
    iU = (U* ⁻¹) .proj₁
    inst-u = nztoℕ {y = ₁₊ u} {neq0 = λ ()}
    Qv : Q .proj₁ ≡ - ₁
    Qv = Eq.trans (Eq.cong (₁₊ u *_) (ineg U* V* veq))
         (Eq.trans (Eq.sym (-‿distribʳ-* (₁₊ u) iU))
                   (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ u) {{inst-u}})))
    Rv : ₁₊ v * iU ≡ - ₁
    Rv = Eq.trans (Eq.cong (_* iU) veq)
         (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ u) iU))
                   (Eq.cong -_ (lemma-⁻¹ʳ (₁₊ u) {{inst-u}})))

------------------------------------------------------------------------
-- The branch-A residual identity:
-- W • (HH↑ • S⁻¹↑) • W ≈ HH↑ • S⁻¹↑ • CZ • S⁻¹.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)

  private
    W3 : Word (Gen (₂₊ m))
    W3 = H ↑ • (CZ • (H ↑) ^ 3)

  SupSinv : S {m} ↑ • S⁻¹ ↑ ≈ ε
  SupSinv = lemma-cong↑ (S • S⁻¹) ε SSinv

  SinvupS : S⁻¹ {m} ↑ • S ↑ ≈ ε
  SinvupS = lemma-cong↑ (S⁻¹ • S) ε Sp-1-S

  H4up : H {m} ↑ • (H ↑) ^ 3 ≈ ε
  H4up = lemma-cong↑ (H ^ 4) ε H4ε

  SdownSup : S⁻¹ • S {m} ↑ ≈ S ↑ • S⁻¹
  SdownSup = comm⇒pow-comm {w = S} {v = S ↑} p-1 1 (lemma-comm-S-w↑ S)

  TW3lift : H {m} ↑ • (S⁻¹ ↑ • H ↑) ≈ S ↑ • (H ↑ • S ↑)
  TW3lift = lemma-cong↑ (H • (S⁻¹ • H)) (S • (H • S)) TW3

  residAkey : W3 • ((HH ↑ • S⁻¹ ↑) • W3) ≈
              HH ↑ • (S⁻¹ ↑ • (CZ • S⁻¹))
  residAkey =
    trans assoc
    (trans (cright assoc)
    (trans (cright (cright (sym assoc)))
    (trans (cright (cright (cleft (sym assoc))))
    (trans (cright (cright (cleft (cleft H5lift))))
    (trans (cright (cright assoc))
    (trans (cright (cright
        (trans (cright (sym assoc))
        (trans (sym assoc) (cleft TW3lift)))))
    (trans (cright (cright assoc))
    (trans (cright (sym assoc))
    (trans (cright (cleft (axiom comm-CZ-S↑)))
    (trans (cright assoc)
    (trans (cright (cright (cright
        (trans assoc (cright
          (trans (sym assoc)
          (trans (cleft (sym (axiom comm-CZ-S↑))) assoc)))))))
    (trans (cright (cright
        (trans (cright (sym assoc))
        (trans (sym assoc)
        (trans (cleft (axiom selinger-c10))
               (cleft (refl' fixdown2)))))))
    (trans (cright (sym assoc))
    (trans (cright (cleft
        (trans (sym assoc) (trans (cleft SupSinv) left-unit))))
    (trans (cright assoc)
    (trans (cright (cright assoc))
    (trans (cright (cright (cright assoc)))
    (trans (cright (cright (cright (cright assoc))))
    (trans (cright (cright (cright (cright (cright assoc)))))
    (trans (cright (cright (cright (cright (cright (cright
        (trans (sym assoc) (trans (cleft SdownSup) assoc))))))))
    (trans (cright (cright (cright (cright (cright
        (trans (sym assoc) (trans (cleft SinvupS) left-unit)))))))
    (trans (cright (cright (cright (cright (cright Scomm3)))))
    (trans (cright (cright (cright (cright
        (trans (sym assoc) (trans (cleft H4up) left-unit))))))
           (sym assoc))))))))))))))))))))))))

