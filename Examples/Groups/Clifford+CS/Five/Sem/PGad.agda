------------------------------------------------------------------------
-- Presentations of groups
--
-- The gadgets as letters of P′, read on bit vectors
--
-- From four wires on the letters of P′ are read at the Gray numbering
-- (BridgeGray).  Each gadget of the affine decoding is one letter: the
-- phase pair iZ on (p , q) is pp p q, the signed exchange XZ is
-- (−1)_[p] X_[p,q] (px with its sign on p, the exchange in whichever
-- order the indices come), and the hybrid's block on (p , q) is
-- K_[q,p] i_[q]⁻¹, the letter ki q p q when q comes before p.  Read on
-- bit vectors each is the two-level operator of its block (`pp-tl`,
-- `rot<-tl`, `rot>-tl`, `ki-tl`), row by row.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Five.Sem.PGad (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Fin using (Fin) renaming (_<_ to _<ᶠ_)
import Data.Fin.Properties as FinP
open import Data.Nat using () renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Properties using (≡-dec)
import Data.Bool.Properties as BoolP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import Algebra.Bundles using (CommutativeRing)
open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Ring using (+-*-commutativeRing)
open import Algebra.Properties.Ring (CommutativeRing.ring +-*-commutativeRing) using (-1*x≈-x)
open import Examples.Groups.Clifford+CS.Encoding m using (n ; idx ; idx-inj)
open import Examples.Groups.Clifford+CS.BridgeGray n
  using (⟦_⟧Y ; ⟦_⟧ᴾ ; coefℤ ; cX-a ; cX-b ; cX-≢ ; cK-a ; cK-b ; cK-≢)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Diag using (diag ; diag-⊙ ; δb-≢)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Letters m
  using (δᶠ-idx ; phs ; phs-hit ; phs-miss ; i-M)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas using (eqB-complete ; eqB-false)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; ki)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (Blk ; tl ; tlOp)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (kpp ; krot ; kki ; blkOf)

private
  _≟ᵇ_ : (x y : Bits n) → Dec (x ≡ y)
  _≟ᵇ_ = ≡-dec BoolP._≟_

  if-t : ∀ {b : Bool} {u v : 𝔽} → b ≡ true → (if b then u else v) ≡ u
  if-t refl = refl

  if-f : ∀ {b : Bool} {u v : 𝔽} → b ≡ false → (if b then u else v) ≡ v
  if-f refl = refl

  ite≡ : ∀ {b b′ : Bool} {u v : 𝔽} → b ≡ b′ → (if b then u else v) ≡ (if b′ then u else v)
  ite≡ refl = refl

  -- Substitute three values and compute.
  pt : ∀ {u v w u′ v′ w′ : 𝔽} (E F : 𝔽 → 𝔽 → 𝔽 → 𝔽) →
       u ≡ u′ → v ≡ v′ → w ≡ w′ → E u′ v′ w′ ≡ F u′ v′ w′ → E u v w ≡ F u v w
  pt E F refl refl refl e = e

  δ1 : ∀ (x : Bits n) → δb x x ≡ 1#
  δ1 = δb-refl

  δ0 : ∀ (x y : Bits n) → x ≢ y → δb x y ≡ 0#
  δ0 = δb-≢

  sym≢ : ∀ {x y : Bits n} → x ≢ y → y ≢ x
  sym≢ ne e = ne (Eq.sym e)

------------------------------------------------------------------------
-- The rows of a two-level operator

module Rows (B : Blk) (p q : Bits n) (p≢q : p ≢ q) where
  open Blk B

  at-p : ∀ y → tlOp B p q p y ≡ a * δb p y + b * δb q y
  at-p y = if-t (eqB-complete p p refl)

  at-q : ∀ y → tlOp B p q q y ≡ c * δb p y + d * δb q y
  at-q y = Eq.trans (if-f (eqB-false q p (sym≢ p≢q)))
             (if-t (eqB-complete q q refl))

  at-o : ∀ x y → x ≢ p → x ≢ q → tlOp B p q x y ≡ γ^ k * δb x y
  at-o x y nep neq =
    Eq.trans (if-f (eqB-false x p nep))
             (if-f (eqB-false x q neq))

------------------------------------------------------------------------
-- Multiplying by a diagonal

private
  diag-ˡ : (h : Bits n → 𝔽) (M : Op n) → (diag h ⊙ M) ≐ (λ x y → h x * M x y)
  diag-ˡ h M x y =
    Eq.trans (Σ-cong {f = λ z → (h x * δb x z) * M z y} {g = λ z → δb x z * (h x * M z y)}
               (λ z → Eq.trans (Eq.cong (_* M z y) (*-comm (h x) (δb x z))) (*-assoc (δb x z) (h x) (M z y))))
      (Σ-δˡ x (λ z → h x * M z y))

  diag-ʳ : (h : Bits n → 𝔽) (M : Op n) → (M ⊙ diag h) ≐ (λ x y → M x y * h y)
  diag-ʳ h M x y =
    Eq.trans (Σ-cong {f = λ z → M x z * (h z * δb z y)} {g = λ z → (M x z * h z) * δb z y}
               (λ z → Eq.sym (*-assoc (M x z) (h z) (δb z y))))
      (Σ-δʳ y (λ z → M x z * h z))

------------------------------------------------------------------------
-- X and K read on bit vectors

xOp : Bits n → Bits n → Op n
xOp s s′ x y = if eqB x s then δb s′ y else if eqB x s′ then δb s y else δb x y

kOp : Bits n → Bits n → Op n
kOp s s′ x y = if eqB x s then δb s y + δb s′ y
               else if eqB x s′ then δb s y + -1# * δb s′ y
               else γ * δb x y

private
  -1*x : ∀ v → - v ≡ -1# * v
  -1*x v = Eq.sym (-1*x≈-x v)

X-M : ∀ (s s′ : Bits n) .(lt : idx s <ᶠ idx s′) → proj₂ ⟦ TL.X (idx s) (idx s′) lt ⟧Y ≐ xOp s s′
X-M s s′ lt x y = go (idx x FinP.≟ idx s) (idx x FinP.≟ idx s′)
  where
  go : Dec (idx x ≡ idx s) → Dec (idx x ≡ idx s′) →
       coefℤ (TL.X-gen (idx s) (idx s′) lt) (idx x) (idx y) ≡ xOp s s′ x y
  go (yes e) _ = Eq.subst (λ v → coefℤ (TL.X-gen (idx s) (idx s′) lt) (idx v) (idx y) ≡ xOp s s′ v y)
                   (Eq.sym (idx-inj {x} {s} e))
                   (Eq.trans (cX-a {a = idx s} {idx s′} lt (idx y))
                     (Eq.trans (δᶠ-idx s′ y)
                       (Eq.sym (if-t (eqB-complete s s refl)))))
  go (no ne) (yes e) =
    Eq.subst (λ v → idx v ≢ idx s → coefℤ (TL.X-gen (idx s) (idx s′) lt) (idx v) (idx y) ≡ xOp s s′ v y)
      (Eq.sym (idx-inj {x} {s′} e))
      (λ ne′ → Eq.trans (cX-b {a = idx s} {idx s′} lt (idx y))
        (Eq.trans (δᶠ-idx s y)
          (Eq.sym (Eq.trans (if-f (eqB-false s′ s (λ e′ → ne′ (Eq.cong idx e′))))
                            (if-t (eqB-complete s′ s′ refl))))))
      ne
  go (no ne) (no ne′) =
    Eq.trans (cX-≢ {a = idx s} {idx s′} lt ne ne′ (idx y))
      (Eq.trans (δᶠ-idx x y)
        (Eq.sym (Eq.trans (if-f (eqB-false x s (λ e → ne (Eq.cong idx e))))
                          (if-f (eqB-false x s′ (λ e → ne′ (Eq.cong idx e)))))))

K-M : ∀ (s s′ : Bits n) .(lt : idx s <ᶠ idx s′) → proj₂ ⟦ TL.K (idx s) (idx s′) lt ⟧Y ≐ kOp s s′
K-M s s′ lt x y = go (idx x FinP.≟ idx s) (idx x FinP.≟ idx s′)
  where
  go : Dec (idx x ≡ idx s) → Dec (idx x ≡ idx s′) →
       coefℤ (TL.K-gen (idx s) (idx s′) lt) (idx x) (idx y) ≡ kOp s s′ x y
  go (yes e) _ = Eq.subst (λ v → coefℤ (TL.K-gen (idx s) (idx s′) lt) (idx v) (idx y) ≡ kOp s s′ v y)
                   (Eq.sym (idx-inj {x} {s} e))
                   (Eq.trans (cK-a {a = idx s} {idx s′} lt (idx y))
                     (Eq.trans (Eq.cong₂ _+_ (δᶠ-idx s y) (δᶠ-idx s′ y))
                       (Eq.sym (if-t (eqB-complete s s refl)))))
  go (no ne) (yes e) =
    Eq.subst (λ v → idx v ≢ idx s → coefℤ (TL.K-gen (idx s) (idx s′) lt) (idx v) (idx y) ≡ kOp s s′ v y)
      (Eq.sym (idx-inj {x} {s′} e))
      (λ ne′ → Eq.trans (cK-b {a = idx s} {idx s′} lt (idx y))
        (Eq.trans (Eq.cong₂ (λ u w → u + - w) (δᶠ-idx s y) (δᶠ-idx s′ y))
          (Eq.trans (Eq.cong (δb s y +_) (-1*x (δb s′ y)))
            (Eq.sym (Eq.trans (if-f (eqB-false s′ s (λ e′ → ne′ (Eq.cong idx e′))))
                              (if-t (eqB-complete s′ s′ refl)))))))
      ne
  go (no ne) (no ne′) =
    Eq.trans (cK-≢ {a = idx s} {idx s′} lt ne ne′ (idx y))
      (Eq.trans (Eq.cong (γ *_) (δᶠ-idx x y))
        (Eq.sym (Eq.trans (if-f (eqB-false x s (λ e → ne (Eq.cong idx e))))
                          (if-f (eqB-false x s′ (λ e → ne′ (Eq.cong idx e)))))))

------------------------------------------------------------------------
-- The phase pair

module PP (p q : Bits n) (p≢q : p ≢ q) where
  open Rows (blkOf kpp) p q p≢q

  private
    H : Bits n → 𝔽
    H x = phs p x * (phs q x * (phs q x * phs q x))

    op : ∀ x y → proj₂ ⟦ pp (idx p) (idx q) ⟧ᴾ x y ≡ H x * δb x y
    op x y =
      Eq.trans (⊙-cong (i-M p) (⊙-cong (i-M q) (⊙-cong (i-M q) (i-M q))) x y)
        (Eq.trans (⊙-cong (≐-refl (diag (phs p))) (⊙-cong (≐-refl (diag (phs q))) (diag-⊙ (phs q) (phs q))) x y)
          (Eq.trans (⊙-cong (≐-refl (diag (phs p))) (diag-⊙ (phs q) (λ z → phs q z * phs q z)) x y)
            (diag-⊙ (phs p) (λ z → phs q z * (phs q z * phs q z)) x y)))

    H4 : ∀ {u v} x → phs p x ≡ u → phs q x ≡ v → H x ≡ u * (v * (v * v))
    H4 x refl refl = refl

    row : ∀ x y → Dec (x ≡ p) → Dec (x ≡ q) → H x * δb x y ≡ tlOp (blkOf kpp) p q x y
    row .p y (yes refl) _ =
      Eq.trans (Eq.cong (_* δb p y) (H4 p (phs-hit p p refl) (phs-miss q p p≢q)))
        (Eq.sym (Eq.trans (at-p y) (lemma (δb p y) (δb q y))))
      where
      lemma : ∀ u v → ⅈ * u + 0# * v ≡ (ⅈ * (1# * (1# * 1#))) * u
      lemma u v = Eq.trans (Eq.cong (ⅈ * u +_) (*-zeroˡ v)) (+-identityʳ (ⅈ * u))
    row .q y (no ne) (yes refl) =
      Eq.trans (Eq.cong (_* δb q y) (H4 q (phs-miss p q ne) (phs-hit q q refl)))
        (Eq.sym (Eq.trans (at-q y) (Eq.trans (Eq.cong (_+ -ⅈ * δb q y) (*-zeroˡ (δb p y))) (+-identityˡ _))))
    row x y (no ne) (no ne′) =
      Eq.trans (Eq.cong (_* δb x y) (H4 x (phs-miss p x ne) (phs-miss q x ne′)))
        (Eq.sym (at-o x y ne ne′))

  pp-tl : ⟦ pp (idx p) (idx q) ⟧ᴾ ~ tl (blkOf kpp) p q
  pp-tl = ~-reflexive {l = 0 +ℕ (0 +ℕ (0 +ℕ 0))} {0} {M = proj₂ ⟦ pp (idx p) (idx q) ⟧ᴾ} {tlOp (blkOf kpp) p q}
            refl (λ x y → Eq.trans (op x y) (row x y (x ≟ᵇ p) (x ≟ᵇ q)))

------------------------------------------------------------------------
-- The rows of X and K

module XRows (s s′ : Bits n) (s≢s′ : s ≢ s′) where

  at-s : ∀ y → xOp s s′ s y ≡ δb s′ y
  at-s y = if-t (eqB-complete s s refl)

  at-s′ : ∀ y → xOp s s′ s′ y ≡ δb s y
  at-s′ y = Eq.trans (if-f (eqB-false s′ s (sym≢ s≢s′)))
              (if-t (eqB-complete s′ s′ refl))

  at-o : ∀ x y → x ≢ s → x ≢ s′ → xOp s s′ x y ≡ δb x y
  at-o x y ne ne′ = Eq.trans (if-f (eqB-false x s ne))
                      (if-f (eqB-false x s′ ne′))

module KRows (s s′ : Bits n) (s≢s′ : s ≢ s′) where

  at-s : ∀ y → kOp s s′ s y ≡ δb s y + δb s′ y
  at-s y = if-t (eqB-complete s s refl)

  at-s′ : ∀ y → kOp s s′ s′ y ≡ δb s y + -1# * δb s′ y
  at-s′ y = Eq.trans (if-f (eqB-false s′ s (sym≢ s≢s′)))
              (if-t (eqB-complete s′ s′ refl))

  at-o : ∀ x y → x ≢ s → x ≢ s′ → kOp s s′ x y ≡ γ * δb x y
  at-o x y ne ne′ = Eq.trans (if-f (eqB-false x s ne))
                      (if-f (eqB-false x s′ ne′))

------------------------------------------------------------------------
-- The signed exchange

module Rot (p q : Bits n) (p≢q : p ≢ q) where
  open Rows (blkOf krot) p q p≢q

  private
    -- The rows, once the exchange is read on bit vectors.
    row : (X : Op n) → (∀ y → X p y ≡ δb q y) → (∀ y → X q y ≡ δb p y) →
          (∀ x y → x ≢ p → x ≢ q → X x y ≡ δb x y) →
          ∀ x y → Dec (x ≡ p) → Dec (x ≡ q) → phs p x * (phs p x * X x y) ≡ tlOp (blkOf krot) p q x y
    row X Xp Xq Xo .p y (yes refl) _ =
      Eq.trans (Eq.cong₂ (λ u w → u * (u * w)) (phs-hit p p refl) (Xp y))
        (Eq.trans (Eq.sym (*-assoc ⅈ ⅈ (δb q y)))
          (Eq.sym (Eq.trans (at-p y) (Eq.trans (Eq.cong (_+ -1# * δb q y) (*-zeroˡ (δb p y))) (+-identityˡ _)))))
    row X Xp Xq Xo .q y (no ne) (yes refl) =
      Eq.trans (Eq.cong₂ (λ u w → u * (u * w)) (phs-miss p q ne) (Xq y))
        (Eq.trans (Eq.cong (1# *_) (*-identityˡ (δb p y)))
          (Eq.sym (Eq.trans (at-q y) (Eq.trans (Eq.cong (1# * δb p y +_) (*-zeroˡ (δb q y))) (+-identityʳ _)))))
    row X Xp Xq Xo x y (no ne) (no ne′) =
      Eq.trans (Eq.cong₂ (λ u w → u * (u * w)) (phs-miss p x ne) (Xo x y ne ne′))
        (Eq.trans (Eq.cong (1# *_) (*-identityˡ (δb x y))) (Eq.sym (at-o x y ne ne′)))

    op : ∀ {a b} .(lt : a <ᶠ b) → ∀ (X : Op n) → proj₂ ⟦ TL.X a b lt ⟧Y ≐ X →
         ∀ x y → proj₂ ⟦ px (idx p) a b lt ⟧ᴾ x y ≡ phs p x * (phs p x * X x y)
    op lt X e x y =
      Eq.trans (⊙-cong (i-M p) (⊙-cong (i-M p) e) x y)
        (Eq.trans (⊙-cong (≐-refl (diag (phs p))) (diag-ˡ (phs p) X) x y)
          (diag-ˡ (phs p) (λ x y → phs p x * X x y) x y))

  rot<-tl : .(lt : idx p <ᶠ idx q) → ⟦ px (idx p) (idx p) (idx q) lt ⟧ᴾ ~ tl (blkOf krot) p q
  rot<-tl lt =
    ~-reflexive {l = 0 +ℕ (0 +ℕ 0)} {0} {M = proj₂ ⟦ px (idx p) (idx p) (idx q) lt ⟧ᴾ} {tlOp (blkOf krot) p q} refl
      (λ x y → Eq.trans (op lt (xOp p q) (X-M p q lt) x y)
        (row (xOp p q) XR.at-s XR.at-s′ XR.at-o x y (x ≟ᵇ p) (x ≟ᵇ q)))
    where module XR = XRows p q p≢q

  rot>-tl : .(gt : idx q <ᶠ idx p) → ⟦ px (idx p) (idx q) (idx p) gt ⟧ᴾ ~ tl (blkOf krot) p q
  rot>-tl gt =
    ~-reflexive {l = 0 +ℕ (0 +ℕ 0)} {0} {M = proj₂ ⟦ px (idx p) (idx q) (idx p) gt ⟧ᴾ} {tlOp (blkOf krot) p q} refl
      (λ x y → Eq.trans (op gt (xOp q p) (X-M q p gt) x y)
        (row (xOp q p) XR.at-s′ XR.at-s (λ x y ne ne′ → XR.at-o x y ne′ ne) x y (x ≟ᵇ p) (x ≟ᵇ q)))
    where module XR = XRows q p (sym≢ p≢q)

------------------------------------------------------------------------
-- The hybrid

module Ki (p q : Bits n) (p≢q : p ≢ q) where
  open Rows (blkOf kki) p q p≢q
  open KRows q p (sym≢ p≢q) renaming (at-s to k-q ; at-s′ to k-p ; at-o to k-o)

  private
    h3 : Bits n → 𝔽
    h3 z = phs q z * (phs q z * phs q z)

    h3≡ : ∀ {v} z → phs q z ≡ v → h3 z ≡ v * (v * v)
    h3≡ z refl = refl

    op : .(lt : idx q <ᶠ idx p) → ∀ x y → proj₂ ⟦ ki (idx q) (idx p) (idx q) lt ⟧ᴾ x y ≡ kOp q p x y * h3 y
    op lt x y =
      Eq.trans (⊙-cong (K-M q p lt) (⊙-cong (i-M q) (⊙-cong (i-M q) (i-M q))) x y)
        (Eq.trans (⊙-cong (≐-refl (kOp q p)) (⊙-cong (≐-refl (diag (phs q))) (diag-⊙ (phs q) (phs q))) x y)
          (Eq.trans (⊙-cong (≐-refl (kOp q p)) (diag-⊙ (phs q) (λ z → phs q z * phs q z)) x y)
            (diag-ʳ h3 (kOp q p) x y)))

    -- Column by column, each a closed computation.
    col-p : ∀ y → Dec (y ≡ p) → Dec (y ≡ q) →
            (δb q y + -1# * δb p y) * h3 y ≡ -1# * δb p y + -ⅈ * δb q y
    col-p .p (yes refl) _ =
      pt (λ u v w → (u + -1# * v) * w) (λ u v _ → -1# * v + -ⅈ * u)
         (δ0 q p (sym≢ p≢q)) (δ1 p) (h3≡ p (phs-miss q p p≢q)) refl
    col-p .q (no _) (yes refl) =
      pt (λ u v w → (u + -1# * v) * w) (λ u v _ → -1# * v + -ⅈ * u)
         (δ1 q) (δ0 p q p≢q) (h3≡ q (phs-hit q q refl)) refl
    col-p y (no ne) (no ne′) =
      pt (λ u v w → (u + -1# * v) * w) (λ u v _ → -1# * v + -ⅈ * u)
         (δ0 q y (sym≢ ne′)) (δ0 p y (sym≢ ne)) (h3≡ y (phs-miss q y ne′)) refl

    col-q : ∀ y → Dec (y ≡ p) → Dec (y ≡ q) →
            (δb q y + δb p y) * h3 y ≡ 1# * δb p y + -ⅈ * δb q y
    col-q .p (yes refl) _ =
      pt (λ u v w → (u + v) * w) (λ u v _ → 1# * v + -ⅈ * u)
         (δ0 q p (sym≢ p≢q)) (δ1 p) (h3≡ p (phs-miss q p p≢q)) refl
    col-q .q (no _) (yes refl) =
      pt (λ u v w → (u + v) * w) (λ u v _ → 1# * v + -ⅈ * u)
         (δ1 q) (δ0 p q p≢q) (h3≡ q (phs-hit q q refl)) refl
    col-q y (no ne) (no ne′) =
      pt (λ u v w → (u + v) * w) (λ u v _ → 1# * v + -ⅈ * u)
         (δ0 q y (sym≢ ne′)) (δ0 p y (sym≢ ne)) (h3≡ y (phs-miss q y ne′)) refl

    col-o : ∀ x y → x ≢ q → Dec (x ≡ y) → (γ * δb x y) * h3 y ≡ γ^ 1 * δb x y
    col-o x .x ne (yes refl) =
      pt {v = 0#} {v′ = 0#} (λ u _ w → (γ * u) * w) (λ u _ _ → γ^ 1 * u)
         (δ1 x) refl (h3≡ x (phs-miss q x ne)) refl
    col-o x y ne (no ne′) =
      Eq.trans (Eq.cong (λ u → (γ * u) * h3 y) (δ0 x y ne′))
        (Eq.trans (*-zeroˡ (h3 y)) (Eq.sym (Eq.cong (γ^ 1 *_) (δ0 x y ne′))))

    row : ∀ x y → Dec (x ≡ p) → Dec (x ≡ q) → kOp q p x y * h3 y ≡ tlOp (blkOf kki) p q x y
    row .p y (yes refl) _ =
      Eq.trans (Eq.cong (_* h3 y) (k-p y)) (Eq.trans (col-p y (y ≟ᵇ p) (y ≟ᵇ q)) (Eq.sym (at-p y)))
    row .q y (no _) (yes refl) =
      Eq.trans (Eq.cong (_* h3 y) (k-q y)) (Eq.trans (col-q y (y ≟ᵇ p) (y ≟ᵇ q)) (Eq.sym (at-q y)))
    row x y (no ne) (no ne′) =
      Eq.trans (Eq.cong (_* h3 y) (k-o x y ne′ ne))
        (Eq.trans (col-o x y ne′ (x ≟ᵇ y)) (Eq.sym (at-o x y ne ne′)))

  ki-tl : .(lt : idx q <ᶠ idx p) → ⟦ ki (idx q) (idx p) (idx q) lt ⟧ᴾ ~ tl (blkOf kki) p q
  ki-tl lt =
    ~-reflexive {l = 1 +ℕ (0 +ℕ (0 +ℕ 0))} {1} {M = proj₂ ⟦ ki (idx q) (idx p) (idx q) lt ⟧ᴾ} {tlOp (blkOf kki) p q}
      refl (λ x y → Eq.trans (op lt x y) (row x y (x ≟ᵇ p) (x ≟ᵇ q)))
