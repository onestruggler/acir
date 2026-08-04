------------------------------------------------------------------------
-- Presentations of groups
--
-- selinger-c11 on doubly-inj₂ boxes (₁₊a1',₁₊b1'')/(₀,b2), branch β:
-- all three H-escapes are full Borel pads, but each one sits in the
-- midgen pattern H³ • ZM Q • S^(Q⁻¹) • H, so every ZM collapses and no
-- CZ-power ever appears.  Both sides then meet at a common normal form.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel11g
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
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Algebra.Properties.Ring (+-*-ring p-2)
  using (-0#≈0# ; -‿involutive ; -‿+-comm ; -‿distribˡ-*)

open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase
  p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ
  p-2 p-prime using (↓-pow-S ; comm-Spow-↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10b
  p-2 p-prime using (SIfix)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush
  p-2 p-prime using (Hdir ; Hd')
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDMCZ2
  p-2 p-prime using (ract-↑-≡)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDZM
  p-2 p-prime using (hpad)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10
  p-2 p-prime using (nsum-p-1)
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDSel10n
  p-2 p-prime using (midgen)

------------------------------------------------------------------------
-- The branch-β residual identity.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)
  open PP ((₂₊ m) QRel,_===_)
  open SR word-setoid
  open Lemmas-Sym using (lemma-comm-H-w↑)
  open Lemmas0 (₁₊ m) using (lemma-S^k+l)

  private
    WDg : Word (Gen (₂₊ m))
    WDg = H • (CZ • H ^ 3)

    -- The common normal form both sides reduce to.
    NFg : ℤ ₚ → ℤ ₚ → Word (Gen (₂₊ m))
    NFg s t =
      H • (S^ s • (H • (S⁻¹ • (CZ • (H • (S^ t • (H ^ 3 • S⁻¹ ↑)))))))

    czS : ∀ (t : ℤ ₚ) → S^ t • CZ ≈ CZ • S^ t
    czS t = comm⇒pow-comm {w = S} {v = CZ} (toℕ t) 1
      (sym (axiom comm-CZ-S↓))

    SupH3g : S⁻¹ {m} ↑ • H ^ 3 ≈ H ^ 3 • S⁻¹ ↑
    SupH3g = sym (comm⇒pow-comm {w = H} {v = S⁻¹ ↑} 3 1
      (lemma-comm-H-w↑ S⁻¹))

    mgR : ∀ (t : ℤ ₚ) → S^ t • S⁻¹ ≈ S^ (t + - ₁)
    mgR t =
      trans (refl' (Eq.cong (S^ t •_) (Eq.sym SIfix)))
        (lemma-S^k+l t (- ₁))

    mgL : ∀ (t : ℤ ₚ) → S⁻¹ • S^ t ≈ S^ (- ₁ + t)
    mgL t =
      trans (refl' (Eq.cong (_• S^ t) (Eq.sym SIfix)))
        (lemma-S^k+l (- ₁) t)

    fixdowng : S⁻¹ ↓ • (H ↓ • (S⁻¹ ↓ • (CZ • (H ↓ •
        (S⁻¹ {₁₊ m} ↓ • S⁻¹ ↑))))) ≡
      S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑)))))
    fixdowng = Eq.cong₂
      (λ u v → u • (H • (v • (CZ • (H • (v • S⁻¹ ↑))))))
      (↓-pow-S p-1) (↓-pow-S p-1)

    -- midgen with no leading S-power.
    mid0 : ∀ (Q : ℤ* ₚ) →
      H ^ 3 • (ZM Q • (S^ ((Q ⁻¹) .proj₁) • H)) ≈
      S^ (- ((Q ⁻¹) .proj₁)) • (H • S^ (- (Q .proj₁)))
    mid0 Q =
      trans (sym left-unit)
      (trans (midgen ₀ Q)
        (cleft (refl' (Eq.cong S^
          (+-identityˡ (- ((Q ⁻¹) .proj₁)))))))

    -- The same collapse with the trailing H moved to an H³ on the
    -- right, which is the shape the R-side pad arrives in.
    tailfix : ∀ (Q : ℤ* ₚ) →
      H ^ 3 • (ZM Q • S^ ((Q ⁻¹) .proj₁)) ≈
      S^ (- ((Q ⁻¹) .proj₁)) • (H • (S^ (- (Q .proj₁)) • H ^ 3))
    tailfix Q =
      trans (sym right-unit)
      (trans (cright (sym (axiom order-H)))
      (trans (trans assoc (trans (cright assoc)
        (trans (cright (cright (sym assoc)))
        (trans (cright (sym assoc)) (sym assoc)))))
      (trans (cleft (mid0 Q))
        (trans assoc (cright assoc)))))

  -- The left side.
  leftg : ∀ (QL : ℤ* ₚ) →
    WDg • ((ZM QL • S^ ((QL ⁻¹) .proj₁)) • WDg) ≈
    NFg (- ((QL ⁻¹) .proj₁) + - ₁) (- ₁ + - (QL .proj₁))
  leftg QL = begin
    WDg • ((ZM QL • S^ iQL) • WDg)
      ≈⟨ trans assoc (trans (cright assoc)
           (cright (cright (cright assoc)))) ⟩
    H • (CZ • (H ^ 3 • (ZM QL • (S^ iQL • (H • (CZ • H ^ 3))))))
      ≈⟨ cright (cright (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc)) (sym assoc)))) ⟩
    H • (CZ • ((H ^ 3 • (ZM QL • (S^ iQL • H))) • (CZ • H ^ 3)))
      ≈⟨ cright (cright (cleft (mid0 QL))) ⟩
    H • (CZ • ((S^ (- iQL) • (H • S^ (- qL))) • (CZ • H ^ 3)))
      ≈⟨ cright (cright (trans assoc (trans (cright assoc)
           (cright (cright (trans (sym assoc)
             (trans (cleft (czS (- qL))) assoc))))))) ⟩
    H • (CZ • (S^ (- iQL) • (H • (CZ • (S^ (- qL) • H ^ 3)))))
      ≈⟨ cright (trans (sym assoc)
           (trans (cleft (sym (czS (- iQL)))) assoc)) ⟩
    H • (S^ (- iQL) • (CZ • (H • (CZ • (S^ (- qL) • H ^ 3)))))
      ≈⟨ cright (cright (trans (cright (sym assoc))
           (trans (sym assoc)
             (cleft (trans (axiom selinger-c11) (refl' fixdowng)))))) ⟩
    H • (S^ (- iQL) • ((S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ • S⁻¹ ↑))))))
      • (S^ (- qL) • H ^ 3)))
      ≈⟨ cright (cright (trans assoc (cright (trans assoc (cright
           (trans assoc (cright (trans assoc (cright (trans assoc
             (cright assoc))))))))))) ⟩
    H • (S^ (- iQL) • (S⁻¹ • (H • (S⁻¹ • (CZ • (H • (S⁻¹ •
      (S⁻¹ ↑ • (S^ (- qL) • H ^ 3)))))))))
      ≈⟨ cright (trans (sym assoc) (cleft (mgR (- iQL)))) ⟩
    H • (S^ (- iQL + - ₁) • (H • (S⁻¹ • (CZ • (H • (S⁻¹ •
      (S⁻¹ ↑ • (S^ (- qL) • H ^ 3))))))))
      ≈⟨ cright (cright (cright (cright (cright (cright
           (trans (cright (trans (sym assoc)
             (trans (cleft (sym (comm-Spow-↑ (toℕ (- qL)) S⁻¹)))
               assoc)))
           (trans (trans (sym assoc) (cleft (mgL (- qL))))
             (cright SupH3g)))))))) ⟩
    NFg (- iQL + - ₁) (- ₁ + - qL) ∎
    where
    qL = QL .proj₁
    iQL = (QL ⁻¹) .proj₁

  -- The right side.
  rightg : ∀ (QL Q2 Q5 : ℤ* ₚ) →
    (Q2 ⁻¹) .proj₁ ≡ ₁ + (QL ⁻¹) .proj₁ →
    Q2 .proj₁ ≡ ₁ + - ((Q5 ⁻¹) .proj₁) →
    Q5 .proj₁ ≡ ₁ + QL .proj₁ →
    (ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)) •
      (WDg • ((ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)) • S⁻¹ ↑)) ≈
    NFg (- ((QL ⁻¹) .proj₁) + - ₁) (- ₁ + - (QL .proj₁))
  rightg QL Q2 Q5 h2 h2' h5 = begin
    (ZM Q2 • S^ iQ2) • (WDg • ((ZM Q5 • S^ iQ5) • S⁻¹ ↑))
      ≈⟨ trans assoc (cright (cright (trans assoc (cright assoc)))) ⟩
    ZM Q2 • (S^ iQ2 • (H • (CZ • (H ^ 3 •
      ((ZM Q5 • S^ iQ5) • S⁻¹ ↑)))))
      ≈⟨ cright (cright (cright (cright
           (trans (sym assoc)
           (trans (cleft (tailfix Q5))
             (trans assoc (cright (trans assoc (cright assoc))))))))) ⟩
    ZM Q2 • (S^ iQ2 • (H • (CZ • (S^ (- iQ5) •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑)))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (trans (cleft (sym (czS (- iQ5)))) assoc)))) ⟩
    ZM Q2 • (S^ iQ2 • (H • (S^ (- iQ5) • (CZ •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑)))))))
      ≈⟨ trans (sym left-unit)
           (trans (cleft (sym (axiom order-H))) assoc) ⟩
    H • (H ^ 3 • (ZM Q2 • (S^ iQ2 • (H • (S^ (- iQ5) • (CZ •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑)))))))))
      ≈⟨ cright (trans (cright (cright (sym assoc)))
           (trans (cright (sym assoc))
           (trans (sym assoc)
           (trans (cleft (mid0 Q2))
             (trans assoc (cright assoc)))))) ⟩
    H • (S^ (- iQ2) • (H • (S^ (- q2) • (S^ (- iQ5) • (CZ •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑))))))))
      ≈⟨ cright (cright (cright (trans (sym assoc)
           (cleft (trans (lemma-S^k+l (- q2) (- iQ5))
             (refl' (Eq.trans (Eq.cong S^ vB) SIfix))))))) ⟩
    H • (S^ (- iQ2) • (H • (S⁻¹ • (CZ •
      (H • (S^ (- q5) • (H ^ 3 • S⁻¹ ↑)))))))
      ≈⟨ trans (cright (cleft (refl' (Eq.cong S^ vA))))
           (cright (cright (cright (cright (cright (cright
             (cleft (refl' (Eq.cong S^ vC))))))))) ⟩
    NFg (- iQL + - ₁) (- ₁ + - qL) ∎
    where
    qL = QL .proj₁
    iQL = (QL ⁻¹) .proj₁
    q2 = Q2 .proj₁
    iQ2 = (Q2 ⁻¹) .proj₁
    q5 = Q5 .proj₁
    iQ5 = (Q5 ⁻¹) .proj₁

    vA : - iQ2 ≡ - iQL + - ₁
    vA = Eq.trans (Eq.cong -_ h2)
      (Eq.trans (Eq.sym (-‿+-comm ₁ iQL)) (+-comm (- ₁) (- iQL)))

    vB : - q2 + - iQ5 ≡ - ₁
    vB = Eq.trans (Eq.cong (λ t → - t + - iQ5) h2')
      (Eq.trans (Eq.cong (_+ - iQ5)
          (Eq.trans (Eq.sym (-‿+-comm ₁ (- iQ5)))
            (Eq.cong (- ₁ +_) (-‿involutive iQ5))))
      (Eq.trans (+-assoc (- ₁) iQ5 (- iQ5))
      (Eq.trans (Eq.cong (- ₁ +_) (+-inverseʳ iQ5))
        (+-identityʳ (- ₁)))))

    vC : - q5 ≡ - ₁ + - qL
    vC = Eq.trans (Eq.cong -_ h5) (Eq.sym (-‿+-comm ₁ qL))

  id11g : ∀ (QL Q2 Q5 : ℤ* ₚ) →
    (Q2 ⁻¹) .proj₁ ≡ ₁ + (QL ⁻¹) .proj₁ →
    Q2 .proj₁ ≡ ₁ + - ((Q5 ⁻¹) .proj₁) →
    Q5 .proj₁ ≡ ₁ + QL .proj₁ →
    WDg • ((ZM QL • S^ ((QL ⁻¹) .proj₁)) • WDg) ≈
    (ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)) •
      (WDg • ((ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)) • S⁻¹ ↑))
  id11g QL Q2 Q5 h2 h2' h5 =
    trans (leftg QL) (sym (rightg QL Q2 Q5 h2 h2' h5))

------------------------------------------------------------------------
-- The branch-β orbit.

module _ {m : ℕ} where
  open PB ((₂₊ m) QRel,_===_)

  private
    ract3 = ract {₂₊ m}

    WDg' : Word (Gen (₂₊ m))
    WDg' = H • (CZ • H ^ 3)

  -- Dividing a sum by one of its summands peels off a ₁.
  addone : ∀ (c d i : ℤ ₚ) → d * i ≡ ₁ → (d + c) * i ≡ ₁ + c * i
  addone c d i di1 =
    Eq.trans (*-distribʳ-+ i d c) (Eq.cong (_+ c * i) di1)

  c11-go-ab0β : ∀ (b2 : ℤ ₚ) (a1' b1'' y : Fin (₁₊ p-2))
    (lm2 : C (₁₊ m)) → ₁₊ b1'' + ₁₊ a1' ≡ ₁₊ y →
    ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , inj₂ ((₀ , b2) , lm2)))
      (CZ • H ↓ • CZ)) ≋
    ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , inj₂ ((₀ , b2) , lm2)))
      (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑))
  c11-go-ab0β b2 a1' b1'' y lm2 eqY = resid≈ , coset≡
    where
    e0 : ∀ (t : ℤ ₚ) → t + - ₀ ≡ t
    e0 t = Eq.trans (Eq.cong (t +_) -0#≈0#) (+-identityʳ t)

    lm : C (₂₊ m)
    lm = inj₂ ((₀ , b2) , lm2)

    lm2f : C (₂₊ m)
    lm2f = inj₂ ((₀ , b2 + - ₁₊ y) , lm2)

    instA = nztoℕ {y = ₁₊ a1'} {neq0 = λ ()}
    instB = nztoℕ {y = ₁₊ b1''} {neq0 = λ ()}
    instY = nztoℕ {y = ₁₊ y} {neq0 = λ ()}

    iA = ((₁₊ a1' , λ ()) ⁻¹) .proj₁
    iB = ((₁₊ b1'' , λ ()) ⁻¹) .proj₁
    iY = ((₁₊ y , λ ()) ⁻¹) .proj₁

    AiA : ₁₊ a1' * iA ≡ ₁
    AiA = lemma-⁻¹ʳ (₁₊ a1') {{instA}}

    BiB : ₁₊ b1'' * iB ≡ ₁
    BiB = lemma-⁻¹ʳ (₁₊ b1'') {{instB}}

    YiY : ₁₊ y * iY ≡ ₁
    YiY = lemma-⁻¹ʳ (₁₊ y) {{instY}}

    QL Q2 Q5 : ℤ* ₚ
    QL = (₁₊ a1' , λ ()) *' ((₁₊ b1'' , λ ()) ⁻¹)
    Q2 = (₁₊ a1' , λ ()) *' ((₁₊ y , λ ()) ⁻¹)
    Q5 = (₁₊ y , λ ()) *' ((₁₊ b1'' , λ ()) ⁻¹)

    vL : ₁₊ b1'' * iA ≡ (QL ⁻¹) .proj₁
    vL = Eq.sym
      (Eq.trans (inv-distrib (₁₊ a1' , λ ()) ((₁₊ b1'' , λ ()) ⁻¹))
      (Eq.trans (Eq.cong (iA *_) (inv-involutive (₁₊ b1'' , λ ())))
        (*-comm iA (₁₊ b1''))))

    v2 : ₁₊ y * iA ≡ (Q2 ⁻¹) .proj₁
    v2 = Eq.sym
      (Eq.trans (inv-distrib (₁₊ a1' , λ ()) ((₁₊ y , λ ()) ⁻¹))
      (Eq.trans (Eq.cong (iA *_) (inv-involutive (₁₊ y , λ ())))
        (*-comm iA (₁₊ y))))

    v5 : ₁₊ b1'' * iY ≡ (Q5 ⁻¹) .proj₁
    v5 = Eq.sym
      (Eq.trans (inv-distrib (₁₊ y , λ ()) ((₁₊ b1'' , λ ()) ⁻¹))
      (Eq.trans (Eq.cong (iY *_) (inv-involutive (₁₊ b1'' , λ ())))
        (*-comm iY (₁₊ b1''))))

    Yeq : ₁₊ a1' + ₁₊ b1'' ≡ ₁₊ y
    Yeq = Eq.trans (+-comm (₁₊ a1') (₁₊ b1'')) eqY

    AeqYB : ₁₊ a1' ≡ ₁₊ y + - ₁₊ b1''
    AeqYB = Eq.trans (Eq.sym (+-identityʳ (₁₊ a1')))
      (Eq.trans (Eq.cong (₁₊ a1' +_) (Eq.sym (+-inverseʳ (₁₊ b1''))))
      (Eq.trans (Eq.sym (+-assoc (₁₊ a1') (₁₊ b1'') (- ₁₊ b1'')))
        (Eq.cong (_+ - ₁₊ b1'') Yeq)))

    -- The three side conditions id11g needs.
    h2 : (Q2 ⁻¹) .proj₁ ≡ ₁ + (QL ⁻¹) .proj₁
    h2 = Eq.trans (Eq.sym v2)
      (Eq.trans (Eq.cong (_* iA) (Eq.sym Yeq))
      (Eq.trans (addone (₁₊ b1'') (₁₊ a1') iA AiA)
        (Eq.cong (₁ +_) vL)))

    h2' : Q2 .proj₁ ≡ ₁ + - ((Q5 ⁻¹) .proj₁)
    h2' = Eq.trans (Eq.cong (_* iY) AeqYB)
      (Eq.trans (addone (- ₁₊ b1'') (₁₊ y) iY YiY)
        (Eq.cong (₁ +_)
          (Eq.trans (Eq.sym (-‿distribˡ-* (₁₊ b1'') iY))
            (Eq.cong -_ v5))))

    h5 : Q5 .proj₁ ≡ ₁ + QL .proj₁
    h5 = Eq.trans (Eq.cong (_* iB) (Eq.sym eqY))
      (addone (₁₊ a1') (₁₊ b1'') iB BiB)

    -- Escape pads.
    padL : (Hdir (₁₊ a1' , ₁₊ b1'') ↓ᵏ (₁₊ m)) ≡
           ZM QL • S^ ((QL ⁻¹) .proj₁)
    padL = Eq.trans (hpad a1' b1'')
      (Eq.cong (λ z → ZM QL • S^ z) vL)

    pad2 : (Hdir (₁₊ a1' , ₁₊ y) ↓ᵏ (₁₊ m)) ≡
           ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)
    pad2 = Eq.trans (hpad a1' y) (Eq.cong (λ z → ZM Q2 • S^ z) v2)

    pad5 : (Hdir (₁₊ y , ₁₊ b1'') ↓ᵏ (₁₊ m)) ≡
           ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)
    pad5 = Eq.trans (hpad y b1'') (Eq.cong (λ z → ZM Q5 • S^ z) v5)

    -- Coset arithmetic.
    nfixa1 : nsum p-1 (- ₁₊ a1') ≡ ₁₊ a1'
    nfixa1 = Eq.trans (nsum-p-1 (- ₁₊ a1')) (-‿involutive (₁₊ a1'))

    nfixy : nsum p-1 (- ₁₊ y) ≡ ₁₊ y
    nfixy = Eq.trans (nsum-p-1 (- ₁₊ y)) (-‿involutive (₁₊ y))

    nfixb1 : nsum p-1 (- ₁₊ b1'') ≡ ₁₊ b1''
    nfixb1 = Eq.trans (nsum-p-1 (- ₁₊ b1'')) (-‿involutive (₁₊ b1''))

    cR1 : ₁₊ b1'' + nsum p-1 (- ₁₊ a1') ≡ ₁₊ y
    cR1 = Eq.trans (Eq.cong (₁₊ b1'' +_) nfixa1) eqY

    nAY : - ₁₊ a1' + ₁₊ y ≡ ₁₊ b1''
    nAY = Eq.trans (Eq.cong (- ₁₊ a1' +_) (Eq.sym Yeq))
      (Eq.trans (Eq.sym (+-assoc (- ₁₊ a1') (₁₊ a1') (₁₊ b1'')))
      (Eq.trans (Eq.cong (_+ ₁₊ b1'') (+-inverseˡ (₁₊ a1')))
        (+-identityˡ (₁₊ b1''))))

    cR3 : - ₁₊ a1' + nsum p-1 (- ₁₊ y) ≡ ₁₊ b1''
    cR3 = Eq.trans (Eq.cong (- ₁₊ a1' +_) nfixy) nAY

    nYB : - ₁₊ y + ₁₊ b1'' ≡ - ₁₊ a1'
    nYB = Eq.trans (Eq.cong (λ t → - t + ₁₊ b1'') (Eq.sym Yeq))
      (Eq.trans (Eq.cong (_+ ₁₊ b1'')
          (Eq.sym (-‿+-comm (₁₊ a1') (₁₊ b1''))))
      (Eq.trans (+-assoc (- ₁₊ a1') (- ₁₊ b1'') (₁₊ b1''))
      (Eq.trans (Eq.cong (- ₁₊ a1' +_) (+-inverseˡ (₁₊ b1'')))
        (+-identityʳ (- ₁₊ a1')))))

    cR6 : - ₁₊ y + nsum p-1 (- ₁₊ b1'') ≡ - ₁₊ a1'
    cR6 = Eq.trans (Eq.cong (- ₁₊ y +_) nfixb1) nYB

    cL2 : (b2 + - ₁₊ a1') + - ₁₊ b1'' ≡ b2 + - ₁₊ y
    cL2 = Eq.trans (+-assoc b2 (- ₁₊ a1') (- ₁₊ b1''))
      (Eq.cong (b2 +_)
        (Eq.trans (-‿+-comm (₁₊ a1') (₁₊ b1'')) (Eq.cong -_ Yeq)))

    cF : C (₃₊ m)
    cF = inj₂ ((₁₊ b1'' , - ₁₊ a1') , lm2f)

    -- LHS.
    L-fix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) (CZ • H ↓ • CZ))
              .proj₁ ≡
            WDg' • ((ZM QL • S^ ((QL ⁻¹) .proj₁)) • WDg')
    L-fix = Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_
      (Eq.trans
        (Eq.cong (λ v → Hdir (₁₊ a1' , v) ↓ᵏ (₁₊ m)) (e0 (₁₊ b1'')))
        padL)
      (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₁)
        (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
          (e0 (₁₊ b1'')))))

    L-c : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) (CZ • H ↓ • CZ))
            .proj₂ ≡ cF
    L-c = Eq.trans (Eq.cong (λ pr → ((ract3 ᵗ) pr CZ) .proj₂)
        (Eq.cong (λ v → inj₂ (Hd' (₁₊ a1' , v) ,
            inj₂ ((₀ , b2 + - ₁₊ a1') , lm2)))
          (e0 (₁₊ b1''))))
      (Eq.cong₂ (λ v w → inj₂ ((₁₊ b1'' , v) , inj₂ ((₀ , w) , lm2)))
        (e0 (- ₁₊ a1')) cL2)

    -- RHS.
    E₁raw = ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) (S ^ p-1)) .proj₁
    E₃raw = ((ract3 ᵗ) (inj₂ ((₁₊ y , - ₁₊ a1') , lm)) (S ^ p-1)) .proj₁
    E₆raw = ((ract3 ᵗ) (inj₂ ((₁₊ b1'' , - ₁₊ y) , lm2f)) (S ^ p-1))
              .proj₁

    REST5g = H ↓ • S⁻¹ ↓ • S⁻¹ ↑

    r1 : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) (S⁻¹ ↓)) ≡
         (E₁raw , inj₂ ((₁₊ a1' , ₁₊ y) , lm))
    r1 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ a1' , ₁₊ b1'') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ a1') (₁₊ b1'') (λ ()))
              (Eq.cong (₁₊ a1' ,_) cR1)))))

    r3 : ((ract3 ᵗ) (inj₂ ((₁₊ y , - ₁₊ a1') , lm)) (S⁻¹ ↓)) ≡
         (E₃raw , inj₂ ((₁₊ y , ₁₊ b1'') , lm))
    r3 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ y , - ₁₊ a1') , lm)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ y , - ₁₊ a1') lm p-1)
          (Eq.cong (λ d → inj₂ (d , lm))
            (Eq.trans (it-dDS-nz p-1 (₁₊ y) (- ₁₊ a1') (λ ()))
              (Eq.cong (₁₊ y ,_) cR3)))))

    r6 : ((ract3 ᵗ) (inj₂ ((₁₊ b1'' , - ₁₊ y) , lm2f)) (S⁻¹ ↓)) ≡
         (E₆raw , inj₂ ((₁₊ b1'' , - ₁₊ a1') , lm2f))
    r6 = Eq.trans
      (Eq.cong (λ w → (ract3 ᵗ) (inj₂ ((₁₊ b1'' , - ₁₊ y) , lm2f)) w)
        (↓-pow-S p-1))
      (Eq.cong₂ _,_ Eq.refl
        (Eq.trans (ract-S^-coset (₁₊ b1'' , - ₁₊ y) lm2f p-1)
          (Eq.cong (λ d → inj₂ (d , lm2f))
            (Eq.trans (it-dDS-nz p-1 (₁₊ b1'') (- ₁₊ y) (λ ()))
              (Eq.cong (₁₊ b1'' ,_) cR6)))))

    r7 : ((ract3 ᵗ) (inj₂ ((₁₊ b1'' , - ₁₊ a1') , lm2f)) (S⁻¹ ↑)) ≡
         ((S ^ p-1) ↑ , cF)
    r7 = Eq.trans
      (ract-↑-≡ (₁₊ b1'' , - ₁₊ a1') lm2f S⁻¹)
      (Eq.cong₂ _,_
        (Eq.cong _↑ (ract-S^-resid-a0 (b2 + - ₁₊ y) lm2 p-1))
        (Eq.cong (λ c → inj₂ ((₁₊ b1'' , - ₁₊ a1') , c))
          (Eq.trans (ract-S^-coset (₀ , b2 + - ₁₊ y) lm2 p-1)
            (Eq.cong (λ d → inj₂ (d , lm2))
              (it-dDS-a0 p-1 (b2 + - ₁₊ y))))))

    R-fix : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
              (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁ ≡
            E₁raw • ((ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)) •
              (E₃raw • (WDg' • ((ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)) •
                (E₆raw • (S ^ p-1) ↑)))))
    R-fix =
      Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (H ↓ • S⁻¹ ↓ • CZ • REST5g)) .proj₁)
          r1)
      (Eq.cong (λ t → E₁raw • t)
      (Eq.trans (Eq.cong₂ _•_ pad2 Eq.refl)
      (Eq.cong (λ t → (ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (CZ • REST5g)) .proj₁)
          r3)
      (Eq.cong (λ t → E₃raw • t)
      (Eq.cong (λ t → WDg' • t)
      (Eq.trans (Eq.cong₂ _•_
          (Eq.trans
            (Eq.cong (λ v → Hdir (₁₊ y , v) ↓ᵏ (₁₊ m)) (e0 (₁₊ b1'')))
            pad5)
          (Eq.cong (λ pr → ((ract3 ᵗ) pr (S⁻¹ ↓ • S⁻¹ ↑)) .proj₁)
            (Eq.cong (λ v → inj₂ (Hd' (₁₊ y , v) , lm2f)) (e0 (₁₊ b1'')))))
      (Eq.cong (λ t → (ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)) • t)
      (Eq.trans (Eq.cong
          (λ pr → pr .proj₁ •
            ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₁)
          r6)
        (Eq.cong (λ t → E₆raw • t) (Eq.cong proj₁ r7)))))))))))

    Rclean : E₁raw • ((ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)) •
               (E₃raw • (WDg' • ((ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)) •
                 (E₆raw • (S ^ p-1) ↑))))) ≈
             (ZM Q2 • S^ ((Q2 ⁻¹) .proj₁)) •
               (WDg' • ((ZM Q5 • S^ ((Q5 ⁻¹) .proj₁)) • S⁻¹ ↑))
    Rclean =
      trans (trans (cleft
          (ract-S^-resid-a+ (₁₊ a1' , ₁₊ b1'') lm p-1 (λ ()))) left-unit)
      (trans (cright (trans (cleft
          (ract-S^-resid-a+ (₁₊ y , - ₁₊ a1') lm p-1 (λ ()))) left-unit))
        (cright (cright (cright (trans (cleft
          (ract-S^-resid-a+ (₁₊ b1'' , - ₁₊ y) lm2f p-1 (λ ())))
          left-unit)))))

    resid≈ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
                (CZ • H ↓ • CZ)) .proj₁ ≈
             ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₁
    resid≈ =
      trans (refl' L-fix)
      (trans (id11g QL Q2 Q5 h2 h2' h5)
      (sym (trans (refl' R-fix) Rclean)))

    R-c : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
            (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂ ≡ cF
    R-c =
      Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂)
            (H ↓ • S⁻¹ ↓ • CZ • REST5g)) .proj₂)
          r1)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (CZ • REST5g)) .proj₂)
          r3)
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) pr (S⁻¹ ↓ • S⁻¹ ↑)) .proj₂)
          (Eq.cong (λ v → inj₂ (Hd' (₁₊ y , v) , lm2f)) (e0 (₁₊ b1''))))
      (Eq.trans (Eq.cong
          (λ pr → ((ract3 ᵗ) (pr .proj₂) (S⁻¹ ↑)) .proj₂)
          r6)
        (Eq.cong proj₂ r7))))

    coset≡ : ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
                (CZ • H ↓ • CZ)) .proj₂ ≡
             ((ract3 ᵗ) (inj₂ ((₁₊ a1' , ₁₊ b1'') , lm))
               (S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑)) .proj₂
    coset≡ = Eq.trans L-c (Eq.sym R-c)

