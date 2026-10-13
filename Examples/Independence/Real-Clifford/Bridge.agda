------------------------------------------------------------------------
-- Presentations of groups
--
-- RCliff₂'s matrices against Makary, Ross and Selinger's semantics:
-- the encoding
--
-- Makary, Ross and Selinger's presentation (Examples.Groups.Real-
-- Clifford) reads its words over −1, H, Z and CZ in operator order, as
-- matrices over any ring with 1/√2; at 𝔻[ω] it is complete.  The
-- encoding ℰ sends RCliff₂'s gates to its words — CNOT to H CZ H on the
-- target, the swap to three CNOTs so spelled — and a circuit to the
-- encodings of its gates in the reverse order (ℰʷ), so that their
-- reading of ℰʷ w, right to left, is RCliff₂'s matrix of w, left to
-- right.  RCliff₂'s matrix (h , M), M over ℤ[ω], is read in 𝔻[ω] as
-- (1/√2)^h φ(M) (⟪_⟫, with φ of Clifford.Ring), and bridge says that
-- their matrix of ℰʷ w is that reading of w's.  The gates are compared
-- entry by entry, theirs through its integer matrices
-- (Interpretation.bridge); everything else is the tensor calculus, as
-- in Clifford.Bridge.  Equal matrices of RCliff₂ give equal readings
-- (exact).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Real-Clifford.Bridge where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₂₊)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; module DR ; RingD ; isCommutativeRing-D ; √½ ; ωᴰ ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.Real-Clifford.Presentation.DOmega using (√½-sq)
import Examples.Groups.Real-Clifford.Syntactics as Q
import Examples.Groups.Real-Clifford.Semantics.Interpretation as QInterp
import Examples.Groups.Real-Clifford.Semantics.Laws as QLaws
import Examples.Groups.Real-Clifford.Semantics.Soundness as QSound

open import Examples.Independence.Real-Clifford.Syntactics
import Examples.Independence.Real-Clifford.Semantics as Sem
import Examples.Independence.Semantics.Qubit as O
open O using (module ZΩ ; √2)
open import Examples.Independence.Clifford.Ring using (φ ; φ-+ ; φ-* ; φ-0 ; φ-1 ; √½-√2)

module QI where
  open QLaws {A = D} {{RingD}} isCommutativeRing-D public
  open QInterp {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq public
module QS = QSound {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq

open QI.AR using (_+_ ; _*_ ; 1# ; 0# ; +-identityʳ ; *-identityˡ ; *-identityʳ ;
                  zeroˡ ; zeroʳ ; *-assoc ; *-comm)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Digits and bits

dig : Bool → Fin 2
dig false = zero
dig true  = suc zero

digs : QI.Bits n → O.Digits n
digs []      = []
digs (b ∷ x) = dig b ∷ digs x

------------------------------------------------------------------------
-- Cliff₂'s operators read in 𝔻[ω]

Φ : O.Op n → QI.Op n
Φ M x y = φ (M (digs x) (digs y))

Φ-cong : {M N : O.Op n} → M O.≐ N → Φ M QI.≐ Φ N
Φ-cong e x y = Eq.cong φ (e (digs x) (digs y))

φΣ : (f : O.Digits n → ZΩ.Q) → φ (O.Σv f) ≡ QI.Σb (λ z → φ (f (digs z)))
φΣ {zero}  f = refl
φΣ {suc n} f =
  Eq.trans (φ-+ F₀ (F₁ ZΩ.+ ZΩ.0q))
    (Eq.trans (Eq.cong (φ F₀ +_) (Eq.trans (φ-+ F₁ ZΩ.0q) (+-identityʳ (φ F₁))))
              (Eq.cong₂ _+_ (φΣ (λ xs → f (zero ∷ xs))) (φΣ (λ xs → f (suc zero ∷ xs)))))
  where
  F₀ = O.Σv (λ xs → f (zero ∷ xs))
  F₁ = O.Σv (λ xs → f (suc zero ∷ xs))

Φ-⊙ : (M N : O.Op n) → Φ (M O.⊙ N) QI.≐ (Φ M QI.⊙ Φ N)
Φ-⊙ M N x y =
  Eq.trans (φΣ (λ z → M (digs x) z ZΩ.* N z (digs y)))
           (QI.Σ-cong (λ z → φ-* (M (digs x) (digs z)) (N (digs z) (digs y))))

Φ-δ : Φ (O.Idₒ {n}) QI.≐ QI.Idₒ
Φ-δ []           []           = refl
Φ-δ (true ∷ x)  (true ∷ y)  =
  Eq.trans (φ-* ZΩ.1q (O.δv (digs x) (digs y))) (Eq.trans (*-identityˡ _) (Φ-δ x y))
Φ-δ (false ∷ x) (false ∷ y) =
  Eq.trans (φ-* ZΩ.1q (O.δv (digs x) (digs y))) (Eq.trans (*-identityˡ _) (Φ-δ x y))
Φ-δ (true ∷ x)  (false ∷ y) = Eq.trans (φ-* ZΩ.0q (O.δv (digs x) (digs y))) (zeroˡ _)
Φ-δ (false ∷ x) (true ∷ y)  = Eq.trans (φ-* ZΩ.0q (O.δv (digs x) (digs y))) (zeroˡ _)

Φ-tensor : {m : ℕ} (M : O.Op m) (N : O.Op n) → Φ (O.tensor M N) QI.≐ QI.tensor (Φ M) (Φ N)
Φ-tensor {m = zero}  M N x       y       = φ-* (M [] []) (N (digs x) (digs y))
Φ-tensor {m = suc m} M N (a ∷ x) (b ∷ y) =
  Φ-tensor {m = m} (λ u v → M (dig a ∷ u) (dig b ∷ v)) N x y

Φ-emb : (M : O.Op k) → Φ (O.emb {k} {n} M) QI.≐ QI.emb {k} {n} (Φ M)
Φ-emb {k} {n} M = QI.≐-trans (Φ-tensor M (O.Idₒ {n})) (QI.tensor-cong {m = k} {n = n} (QI.≐-refl _) Φ-δ)

Φ-up : (M : O.Op n) → Φ (O.up M) QI.≐ QI.up (Φ M)
Φ-up {n} M = QI.≐-trans (Φ-tensor (O.Idₒ {1}) M) (QI.tensor-cong {m = 1} {n = n} Φ-δ (QI.≐-refl _))

Φ-scal : (c : ZΩ.Q) → Φ (O.scal {n} c) QI.≐ QI.scal (φ c)
Φ-scal c x y = Eq.trans (φ-* c (O.δv (digs x) (digs y))) (Eq.cong (φ c *_) (Φ-δ x y))

-- A value of RCliff₂, read in 𝔻[ω].
⟪_⟫ : O.Sc n → QI.Op n
⟪ s ⟫ = QI.scale (√½ QI.^ proj₁ s) (Φ (O.ix (proj₂ s)))

private
  scale-1 : (M : QI.Op n) → QI.scale 1# M QI.≐ M
  scale-1 M x y = *-identityˡ (M x y)

  scale-emb : (c : D) (M : QI.Op k) →
              QI.scale c (QI.emb {k} {n} M) QI.≐ QI.emb {k} {n} (QI.scale c M)
  scale-emb c M x y = Eq.sym (QI.tensor-scaleˡ c M QI.Idₒ x y)

  scale-up : (c : D) (M : QI.Op n) → QI.scale c (QI.up M) QI.≐ QI.up (QI.scale c M)
  scale-up c M x y = Eq.sym (QI.tensor-scaleʳ c (QI.Idₒ {1}) M x y)

------------------------------------------------------------------------
-- The encoding

-- CNOT and the swap, as their words on two wires.
uCX uσ : Q.Circuit (₂₊ n)
uCX = Q.H • Q.CZ • Q.H
uσ  = Q.H • Q.CZ • Q.H • Q.H Q.↑ • Q.CZ • Q.H Q.↑ • Q.H • Q.CZ • Q.H

ℰ : Gen n → Q.Circuit n
ℰ (gate₀ ⌈ m-gate ⌉)  = Q.neg
ℰ (gate₁ ⌈ H-gate ⌉)  = Q.H
ℰ (gate₁ ⌈ Z-gate ⌉)  = Q.Z
ℰ (gate₂ ⌈ CX-gate ⌉) = uCX
ℰ (gate₂ swap)        = uσ
ℰ (g ↥)               = ℰ g Q.↑

-- A circuit: its gates encoded, in the reverse order.
ℰʷ : Circuit n → Q.Circuit n
ℰʷ [ g ]ʷ  = ℰ g
ℰʷ ε       = ε
ℰʷ (w • v) = ℰʷ v • ℰʷ w

------------------------------------------------------------------------
-- The gates, entry by entry

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  neg≡ : φ (ZΩ.- ZΩ.1q) ≡ QI.AR.-_ 1#
  neg≡ = refl

  closedH : QI.scale (√½ QI.^ 1) (Φ (O.ix (proj₂ O.Hᵍ))) QI.≐ QI.scale √½ (QI.ιO (QI.ZI.ix QI.hZ))
  closedH (false ∷ []) (false ∷ []) = refl
  closedH (false ∷ []) (true ∷ []) = refl
  closedH (true ∷ []) (false ∷ []) = refl
  closedH (true ∷ []) (true ∷ []) = refl

  closedZ : QI.scale (√½ QI.^ 0) (Φ (O.ix (proj₂ O.Zᵍ))) QI.≐ QI.ιO (QI.ZI.ix QI.zZ)
  closedZ (false ∷ []) (false ∷ []) = refl
  closedZ (false ∷ []) (true ∷ []) = refl
  closedZ (true ∷ []) (false ∷ []) = refl
  closedZ (true ∷ []) (true ∷ []) = refl

  closedCX : QI.scale (√½ QI.^ 0) (Φ (O.ix (proj₂ O.CXᵍ))) QI.≐
             QI.scale (√½ QI.^ 2) (QI.ιO (QI.ZI.ix QI.⟦ uCX ⟧ᶻ))
  closedCX (false ∷ false ∷ []) (false ∷ false ∷ []) = refl
  closedCX (false ∷ false ∷ []) (false ∷ true ∷ []) = refl
  closedCX (false ∷ false ∷ []) (true ∷ false ∷ []) = refl
  closedCX (false ∷ false ∷ []) (true ∷ true ∷ []) = refl
  closedCX (false ∷ true ∷ []) (false ∷ false ∷ []) = refl
  closedCX (false ∷ true ∷ []) (false ∷ true ∷ []) = refl
  closedCX (false ∷ true ∷ []) (true ∷ false ∷ []) = refl
  closedCX (false ∷ true ∷ []) (true ∷ true ∷ []) = refl
  closedCX (true ∷ false ∷ []) (false ∷ false ∷ []) = refl
  closedCX (true ∷ false ∷ []) (false ∷ true ∷ []) = refl
  closedCX (true ∷ false ∷ []) (true ∷ false ∷ []) = refl
  closedCX (true ∷ false ∷ []) (true ∷ true ∷ []) = refl
  closedCX (true ∷ true ∷ []) (false ∷ false ∷ []) = refl
  closedCX (true ∷ true ∷ []) (false ∷ true ∷ []) = refl
  closedCX (true ∷ true ∷ []) (true ∷ false ∷ []) = refl
  closedCX (true ∷ true ∷ []) (true ∷ true ∷ []) = refl

  closedσ : QI.scale (√½ QI.^ 0) (Φ (O.ix (proj₂ O.SWᵍ))) QI.≐
            QI.scale (√½ QI.^ 6) (QI.ιO (QI.ZI.ix QI.⟦ uσ ⟧ᶻ))
  closedσ (false ∷ false ∷ []) (false ∷ false ∷ []) = refl
  closedσ (false ∷ false ∷ []) (false ∷ true ∷ []) = refl
  closedσ (false ∷ false ∷ []) (true ∷ false ∷ []) = refl
  closedσ (false ∷ false ∷ []) (true ∷ true ∷ []) = refl
  closedσ (false ∷ true ∷ []) (false ∷ false ∷ []) = refl
  closedσ (false ∷ true ∷ []) (false ∷ true ∷ []) = refl
  closedσ (false ∷ true ∷ []) (true ∷ false ∷ []) = refl
  closedσ (false ∷ true ∷ []) (true ∷ true ∷ []) = refl
  closedσ (true ∷ false ∷ []) (false ∷ false ∷ []) = refl
  closedσ (true ∷ false ∷ []) (false ∷ true ∷ []) = refl
  closedσ (true ∷ false ∷ []) (true ∷ false ∷ []) = refl
  closedσ (true ∷ false ∷ []) (true ∷ true ∷ []) = refl
  closedσ (true ∷ true ∷ []) (false ∷ false ∷ []) = refl
  closedσ (true ∷ true ∷ []) (false ∷ true ∷ []) = refl
  closedσ (true ∷ true ∷ []) (true ∷ false ∷ []) = refl
  closedσ (true ∷ true ∷ []) (true ∷ true ∷ []) = refl

------------------------------------------------------------------------
-- Every circuit

private
  -- A gate on the bottom wires of a wider circuit.
  placed : (s : O.Sc k) (L : QI.Op k) → ⟪ s ⟫ QI.≐ L →
           ⟪ O.embs {k} {n} s ⟫ QI.≐ QI.emb {k} {n} L
  placed {k} {n} (h , M) L e =
    QI.≐-trans (QI.scale-cong (Φ-cong (O.ix-emb {k} {n} M)))
    (QI.≐-trans (QI.scale-cong (Φ-emb {k} {n} (O.ix M)))
    (QI.≐-trans (scale-emb (√½ QI.^ h) (Φ (O.ix M))) (QI.emb-cong e)))

  -- One wire up.
  lifted : (s : O.Sc n) → ⟪ O.↑s s ⟫ QI.≐ QI.up ⟪ s ⟫
  lifted (h , M) =
    QI.≐-trans (QI.scale-cong (Φ-cong (O.ix-up M)))
    (QI.≐-trans (QI.scale-cong (Φ-up (O.ix M))) (scale-up (√½ QI.^ h) (Φ (O.ix M))))

gen : (g : Gen n) → QI.⟦ ℰ g ⟧ᴬ QI.≐ ⟪ Sem.⟦ g ⟧₀ ⟫
gen {n} (gate₀ ⌈ m-gate ⌉) x y = Eq.sym (
  Eq.trans (*-identityˡ _)
    (Eq.trans (Φ-cong (O.ix-scalM {n} (ZΩ.- ZΩ.1q)) x y)
      (Eq.trans (Φ-scal (ZΩ.- ZΩ.1q) x y) (Eq.cong (λ c → c * QI.δb x y) neg≡))))
gen {suc n} (gate₁ ⌈ H-gate ⌉) =
  QI.≐-sym (placed {1} {n} O.Hᵍ _ (QI.≐-trans closedH (QI.≐-refl _)))
gen {suc n} (gate₁ ⌈ Z-gate ⌉) =
  QI.≐-sym (placed {1} {n} O.Zᵍ _ closedZ)
gen {suc (suc n)} (gate₂ ⌈ CX-gate ⌉) =
  QI.≐-trans (QI.localise {2} {n} uCX)
    (QI.≐-trans (QI.emb-cong (QI.bridge uCX))
      (QI.≐-sym (placed {2} {n} O.CXᵍ _ closedCX)))
gen {suc (suc n)} (gate₂ swap) =
  QI.≐-trans (QI.localise {2} {n} uσ)
    (QI.≐-trans (QI.emb-cong (QI.bridge uσ))
      (QI.≐-sym (placed {2} {n} O.SWᵍ _ closedσ)))
gen (g ↥) =
  QI.≐-trans (QS.⟦↑⟧ (ℰ g))
    (QI.≐-trans (QI.up-cong (gen g)) (QI.≐-sym (lifted Sem.⟦ g ⟧₀)))

private
  ^-swap : (a b : ℕ) → (√½ QI.^ a) * (√½ QI.^ b) ≡ √½ QI.^ (b +ℕ a)
  ^-swap a b = Eq.trans (*-comm _ _) (Eq.sym (QI.^-+ √½ b a))

-- Their matrix of the encoding is RCliff₂'s matrix, read in 𝔻[ω].
bridge : (w : Circuit n) → QI.⟦ ℰʷ w ⟧ᴬ QI.≐ ⟪ Sem.⟦ w ⟧ ⟫
bridge [ g ]ʷ  = gen g
bridge ε       =
  QI.≐-sym (QI.≐-trans (scale-1 _) (QI.≐-trans (Φ-cong O.ix-id) Φ-δ))
bridge (w • v) =
  QI.≐-trans (QI.⊙-cong (bridge v) (bridge w))
  (QI.≐-trans (QI.scale-⊙ (√½ QI.^ hv) (√½ QI.^ hw) (Φ (O.ix Mv)) (Φ (O.ix Mw)))
  (QI.≐-trans (λ x y → Eq.cong (λ c → c * (Φ (O.ix Mv) QI.⊙ Φ (O.ix Mw)) x y) (^-swap hv hw))
  (QI.scale-cong (QI.≐-sym (QI.≐-trans (Φ-cong (O.ix-mul Mv Mw)) (Φ-⊙ (O.ix Mv) (O.ix Mw)))))))
  where
  hw = proj₁ Sem.⟦ w ⟧
  hv = proj₁ Sem.⟦ v ⟧
  Mw = proj₂ Sem.⟦ w ⟧
  Mv = proj₂ Sem.⟦ v ⟧

------------------------------------------------------------------------
-- Equal matrices, equal readings

private
  φ-^ : (a : ZΩ.Q) (k : ℕ) → φ (a O.^ k) ≡ φ a QI.^ k
  φ-^ a zero    = φ-1
  φ-^ a (suc k) = Eq.trans (φ-* a (a O.^ k)) (Eq.cong (φ a *_) (φ-^ a k))

  r = φ √2

  -- (1/√2)^k √2^k = 1.
  cancel : (k : ℕ) → (√½ QI.^ k) * (r QI.^ k) ≡ 1#
  cancel zero    = *-identityˡ 1#
  cancel (suc k) = Eq.trans (swap4 √½ (√½ QI.^ k) r (r QI.^ k))
                     (Eq.trans (Eq.cong₂ _*_ √½-√2 (cancel k)) (*-identityˡ 1#))
    where
    swap4 : (a b c d : D) → (a * b) * (c * d) ≡ (a * c) * (b * d)
    swap4 a b c d =
      Eq.trans (*-assoc a b (c * d))
      (Eq.trans (Eq.cong (a *_) (Eq.trans (Eq.sym (*-assoc b c d))
                (Eq.trans (Eq.cong (_* d) (*-comm b c)) (*-assoc c b d))))
                (Eq.sym (*-assoc a c (b * d))))

  -- From r^a F = r^b G, (1/√2)^b F = (1/√2)^a G.
  unscale : (a b : ℕ) {F G : D} → (r QI.^ a) * F ≡ (r QI.^ b) * G →
            (√½ QI.^ b) * F ≡ (√½ QI.^ a) * G
  unscale a b {F} {G} e = begin
    (√½ QI.^ b) * F
      ≡⟨ Eq.sym (*-identityˡ _) ⟩
    1# * ((√½ QI.^ b) * F)
      ≡⟨ Eq.cong (_* ((√½ QI.^ b) * F)) (Eq.sym (cancel a)) ⟩
    ((√½ QI.^ a) * (r QI.^ a)) * ((√½ QI.^ b) * F)
      ≡⟨ shuffle (√½ QI.^ a) (r QI.^ a) (√½ QI.^ b) F ⟩
    ((√½ QI.^ a) * (√½ QI.^ b)) * ((r QI.^ a) * F)
      ≡⟨ Eq.cong (((√½ QI.^ a) * (√½ QI.^ b)) *_) e ⟩
    ((√½ QI.^ a) * (√½ QI.^ b)) * ((r QI.^ b) * G)
      ≡⟨ shuffle′ (√½ QI.^ a) (√½ QI.^ b) (r QI.^ b) G ⟩
    ((√½ QI.^ b) * (r QI.^ b)) * ((√½ QI.^ a) * G)
      ≡⟨ Eq.cong (_* ((√½ QI.^ a) * G)) (cancel b) ⟩
    1# * ((√½ QI.^ a) * G)
      ≡⟨ *-identityˡ _ ⟩
    (√½ QI.^ a) * G ∎
    where
    open Eq.≡-Reasoning
    shuffle : (a b c d : D) → (a * b) * (c * d) ≡ (a * c) * (b * d)
    shuffle a b c d =
      Eq.trans (*-assoc a b (c * d))
      (Eq.trans (Eq.cong (a *_) (Eq.trans (Eq.sym (*-assoc b c d))
                (Eq.trans (Eq.cong (_* d) (*-comm b c)) (*-assoc c b d))))
                (Eq.sym (*-assoc a c (b * d))))
    shuffle′ : (a b c d : D) → (a * b) * (c * d) ≡ (b * c) * (a * d)
    shuffle′ a b c d =
      Eq.trans (Eq.cong (_* (c * d)) (*-comm a b)) (shuffle b a c d)

open O.Circuits Sem.val using (module Exact)

exact : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → ⟪ Sem.⟦ w ⟧ ⟫ QI.≐ ⟪ Sem.⟦ v ⟧ ⟫
exact {w = w} {v} (Exact.phased _ refl agree) x y =
  unscale hv hw (Eq.trans (Eq.sym L) (Eq.trans (Eq.cong φ (agree (digs x) (digs y))) R))
  where
  hw = proj₁ Sem.⟦ w ⟧
  hv = proj₁ Sem.⟦ v ⟧
  Fw = O.ix (proj₂ Sem.⟦ w ⟧) (digs x) (digs y)
  Fv = O.ix (proj₂ Sem.⟦ v ⟧) (digs x) (digs y)

  L : φ ((√2 O.^ hv) ZΩ.* Fw) ≡ (r QI.^ hv) * φ Fw
  L = Eq.trans (φ-* (√2 O.^ hv) Fw) (Eq.cong (_* φ Fw) (φ-^ √2 hv))

  R : φ (((O.x O.^ 0) ZΩ.* (√2 O.^ hw)) ZΩ.* Fv) ≡ (r QI.^ hw) * φ Fv
  R = Eq.trans (φ-* ((O.x O.^ 0) ZΩ.* (√2 O.^ hw)) Fv)
        (Eq.cong (_* φ Fv) (Eq.trans (φ-* (O.x O.^ 0) (√2 O.^ hw))
          (Eq.trans (Eq.cong₂ _*_ φ-1 (φ-^ √2 hw)) (*-identityˡ _))))
