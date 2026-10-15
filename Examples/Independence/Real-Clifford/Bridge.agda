------------------------------------------------------------------------
-- Presentations of groups
--
-- RCliff₂'s matrices against Makary, Ross and Selinger's semantics:
-- the encoding
--
-- Their presentation (Examples.Groups.Real-Clifford) reads its words
-- over −1, H, Z and CZ in operator order, as matrices over any ring
-- with 1/√2; at 𝔻[ω] it is complete.  The encoding ℰ sends RCliff₂'s
-- gates to its words — CNOT to H CZ H on the target, the swap to three
-- CNOTs so spelled — and a circuit to the encodings of its gates in
-- the reverse order (ℰʷ), so that their reading of ℰʷ w, right to left,
-- is RCliff₂'s matrix of w, left to right: no transpose is involved.
-- RCliff₂'s matrix (h , M), M over ℤ[ω], is read in 𝔻[ω] as
-- (1/√2)^h φ(M) (⟪_⟫, with φ of Clifford.Ring), and bridge says that
-- their matrix of ℰʷ w is that reading of w's.  The gates are compared
-- entry by entry, theirs through its integer matrices
-- (Interpretation.bridge); everything else is the tensor calculus, as
-- for Cliff₂ (Clifford.Bridge).  Equal matrices of RCliff₂ give equal
-- readings (exact).
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
  using (D ; module DR ; RingD ; isCommutativeRing-D ; √½ ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.Real-Clifford.Presentation.DOmega using (√½-sq)
import Examples.Groups.Real-Clifford.Syntactics as Q
import Examples.Groups.Real-Clifford.Semantics.Laws as RLaws
import Examples.Groups.Real-Clifford.Semantics.Interpretation as RInterp
import Examples.Groups.Real-Clifford.Semantics.Soundness as RSound

open import Examples.Independence.Real-Clifford.Syntactics
import Examples.Independence.Real-Clifford.Semantics as Sem
import Examples.Independence.Semantics.Qubit as O
open O using (module ZΩ ; √2)
open import Examples.Independence.Clifford.Ring using (φ ; φ-+ ; φ-* ; φ-0 ; φ-1 ; √½-√2)

module RL = RLaws {A = D} {{RingD}} isCommutativeRing-D
module RI = RInterp {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq
module RS = RSound {A = D} {{RingD}} isCommutativeRing-D √½ √½-sq

open RL.AR using (_+_ ; _*_ ; -_ ; 1# ; 0# ; +-identityʳ ; *-identityˡ ; *-identityʳ ;
                  zeroˡ ; zeroʳ ; *-assoc ; *-comm)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Digits and bits

dig : Bool → Fin 2
dig false = zero
dig true  = suc zero

digs : RL.Bits n → O.Digits n
digs []      = []
digs (b ∷ x) = dig b ∷ digs x

------------------------------------------------------------------------
-- RCliff₂'s operators read in 𝔻[ω]

Φ : O.Op n → RL.Op n
Φ M x y = φ (M (digs x) (digs y))

Φ-cong : {M N : O.Op n} → M O.≐ N → Φ M RL.≐ Φ N
Φ-cong e x y = Eq.cong φ (e (digs x) (digs y))

φΣ : (f : O.Digits n → ZΩ.Q) → φ (O.Σv f) ≡ RL.Σb (λ z → φ (f (digs z)))
φΣ {zero}  f = refl
φΣ {suc n} f =
  Eq.trans (φ-+ F₀ (F₁ ZΩ.+ ZΩ.0q))
    (Eq.trans (Eq.cong (φ F₀ +_) (Eq.trans (φ-+ F₁ ZΩ.0q) (+-identityʳ (φ F₁))))
              (Eq.cong₂ _+_ (φΣ (λ xs → f (zero ∷ xs))) (φΣ (λ xs → f (suc zero ∷ xs)))))
  where
  F₀ = O.Σv (λ xs → f (zero ∷ xs))
  F₁ = O.Σv (λ xs → f (suc zero ∷ xs))

Φ-⊙ : (M N : O.Op n) → Φ (M O.⊙ N) RL.≐ (Φ M RL.⊙ Φ N)
Φ-⊙ M N x y =
  Eq.trans (φΣ (λ z → M (digs x) z ZΩ.* N z (digs y)))
           (RL.Σ-cong (λ z → φ-* (M (digs x) (digs z)) (N (digs z) (digs y))))

Φ-δ : Φ (O.Idₒ {n}) RL.≐ RL.Idₒ
Φ-δ []           []           = refl
Φ-δ (true ∷ x)  (true ∷ y)  =
  Eq.trans (φ-* ZΩ.1q (O.δv (digs x) (digs y))) (Eq.trans (*-identityˡ _) (Φ-δ x y))
Φ-δ (false ∷ x) (false ∷ y) =
  Eq.trans (φ-* ZΩ.1q (O.δv (digs x) (digs y))) (Eq.trans (*-identityˡ _) (Φ-δ x y))
Φ-δ (true ∷ x)  (false ∷ y) = Eq.trans (φ-* ZΩ.0q (O.δv (digs x) (digs y))) (zeroˡ _)
Φ-δ (false ∷ x) (true ∷ y)  = Eq.trans (φ-* ZΩ.0q (O.δv (digs x) (digs y))) (zeroˡ _)

Φ-tensor : {m : ℕ} (M : O.Op m) (N : O.Op n) → Φ (O.tensor M N) RL.≐ RL.tensor (Φ M) (Φ N)
Φ-tensor {m = zero}  M N x       y       = φ-* (M [] []) (N (digs x) (digs y))
Φ-tensor {m = suc m} M N (a ∷ x) (b ∷ y) =
  Φ-tensor {m = m} (λ u v → M (dig a ∷ u) (dig b ∷ v)) N x y

Φ-emb : (M : O.Op k) → Φ (O.emb {k} {n} M) RL.≐ RL.emb {k} {n} (Φ M)
Φ-emb {k} {n} M = RL.≐-trans (Φ-tensor M (O.Idₒ {n})) (RL.tensor-cong {m = k} {n = n} (RL.≐-refl _) Φ-δ)

Φ-up : (M : O.Op n) → Φ (O.up M) RL.≐ RL.up (Φ M)
Φ-up {n} M = RL.≐-trans (Φ-tensor (O.Idₒ {1}) M) (RL.tensor-cong {m = 1} {n = n} Φ-δ (RL.≐-refl _))

Φ-scal : (c : ZΩ.Q) → Φ (O.scal {n} c) RL.≐ RL.scal (φ c)
Φ-scal c x y = Eq.trans (φ-* c (O.δv (digs x) (digs y))) (Eq.cong (φ c *_) (Φ-δ x y))

-- A value of RCliff₂, read in 𝔻[ω].
⟪_⟫ : O.Sc n → RL.Op n
⟪ s ⟫ = RI.scale (√½ RI.^ proj₁ s) (Φ (O.ix (proj₂ s)))

private
  scale-1 : (M : RL.Op n) → RI.scale 1# M RL.≐ M
  scale-1 M x y = *-identityˡ (M x y)

  scale-emb : (c : D) (M : RL.Op k) →
              RI.scale c (RL.emb {k} {n} M) RL.≐ RL.emb {k} {n} (RI.scale c M)
  scale-emb c M x y = Eq.sym (RL.tensor-scaleˡ c M RL.Idₒ x y)

  scale-up : (c : D) (M : RL.Op n) → RI.scale c (RL.up M) RL.≐ RL.up (RI.scale c M)
  scale-up c M x y = Eq.sym (RL.tensor-scaleʳ c (RL.Idₒ {1}) M x y)

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
ℰ (gate₃ ⌈ () ⌉)
ℰ (g ↥)               = ℰ g Q.↑

-- A circuit: its gates encoded, in the reverse order.
ℰʷ : Circuit n → Q.Circuit n
ℰʷ [ g ]ʷ  = ℰ g
ℰʷ ε       = ε
ℰʷ (w • v) = ℰʷ v • ℰʷ w

------------------------------------------------------------------------
-- The gates, entry by entry

-- The scalar −1 of RCliff₂.
c−1 : ZΩ.Q
c−1 = O.entries (proj₂ O.−1ᵍ)

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  φ−1 : φ c−1 ≡ - 1#
  φ−1 = refl

  closedH : RI.scale (√½ RI.^ 1) (Φ (O.ix (proj₂ O.Hᵍ))) RL.≐ RI.scale √½ (RI.ιO (RI.ZI.ix RI.hZ))
  closedH (false ∷ []) (false ∷ []) = refl
  closedH (false ∷ []) (true ∷ []) = refl
  closedH (true ∷ []) (false ∷ []) = refl
  closedH (true ∷ []) (true ∷ []) = refl

  closedZ : RI.scale (√½ RI.^ 0) (Φ (O.ix (proj₂ O.Zᵍ))) RL.≐ RI.ιO (RI.ZI.ix RI.zZ)
  closedZ (false ∷ []) (false ∷ []) = refl
  closedZ (false ∷ []) (true ∷ []) = refl
  closedZ (true ∷ []) (false ∷ []) = refl
  closedZ (true ∷ []) (true ∷ []) = refl

  closedCX : RI.scale (√½ RI.^ 0) (Φ (O.ix (proj₂ O.CXᵍ))) RL.≐
             RI.scale (√½ RI.^ 2) (RI.ιO (RI.ZI.ix RI.⟦ uCX ⟧ᶻ))
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

  closedσ : RI.scale (√½ RI.^ 0) (Φ (O.ix (proj₂ O.SWᵍ))) RL.≐
            RI.scale (√½ RI.^ 6) (RI.ιO (RI.ZI.ix RI.⟦ uσ ⟧ᶻ))
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
  placed : (s : O.Sc k) (L : RL.Op k) → ⟪ s ⟫ RL.≐ L →
           ⟪ O.embs {k} {n} s ⟫ RL.≐ RL.emb {k} {n} L
  placed {k} {n} (h , M) L e =
    RL.≐-trans (RI.scale-cong (Φ-cong (O.ix-emb {k} {n} M)))
    (RL.≐-trans (RI.scale-cong (Φ-emb {k} {n} (O.ix M)))
    (RL.≐-trans (scale-emb (√½ RI.^ h) (Φ (O.ix M))) (RL.emb-cong e)))

  -- One wire up.
  lifted : (s : O.Sc n) → ⟪ O.↑s s ⟫ RL.≐ RL.up ⟪ s ⟫
  lifted (h , M) =
    RL.≐-trans (RI.scale-cong (Φ-cong (O.ix-up M)))
    (RL.≐-trans (RI.scale-cong (Φ-up (O.ix M))) (scale-up (√½ RI.^ h) (Φ (O.ix M))))

gen : (g : Gen n) → RI.⟦ ℰ g ⟧ᴬ RL.≐ ⟪ Sem.⟦ g ⟧₀ ⟫
gen {n} (gate₀ ⌈ m-gate ⌉) x y = Eq.sym (
  Eq.trans (*-identityˡ _)
    (Eq.trans (Φ-cong (O.ix-scalM {n} c−1) x y)
      (Eq.trans (Φ-scal c−1 x y) (Eq.cong (λ c → c * RL.δb x y) φ−1))))
gen {suc n} (gate₁ ⌈ H-gate ⌉) =
  RL.≐-sym (placed {1} {n} O.Hᵍ _ closedH)
gen {suc n} (gate₁ ⌈ Z-gate ⌉) =
  RL.≐-sym (placed {1} {n} O.Zᵍ _ closedZ)
gen {suc (suc n)} (gate₂ ⌈ CX-gate ⌉) =
  RL.≐-trans (RI.localise {2} {n} uCX)
    (RL.≐-trans (RL.emb-cong (RI.bridge uCX))
      (RL.≐-sym (placed {2} {n} O.CXᵍ _ closedCX)))
gen {suc (suc n)} (gate₂ swap) =
  RL.≐-trans (RI.localise {2} {n} uσ)
    (RL.≐-trans (RL.emb-cong (RI.bridge uσ))
      (RL.≐-sym (placed {2} {n} O.SWᵍ _ closedσ)))
gen (gate₃ ⌈ () ⌉)
gen (g ↥) =
  RL.≐-trans (RS.⟦↑⟧ (ℰ g))
    (RL.≐-trans (RL.up-cong (gen g)) (RL.≐-sym (lifted Sem.⟦ g ⟧₀)))

private
  ^-swap : (a b : ℕ) → (√½ RI.^ a) * (√½ RI.^ b) ≡ √½ RI.^ (b +ℕ a)
  ^-swap a b = Eq.trans (*-comm _ _) (Eq.sym (RI.^-+ √½ b a))

-- Their matrix of the encoding is RCliff₂'s matrix, read in 𝔻[ω].
bridge : (w : Circuit n) → RI.⟦ ℰʷ w ⟧ᴬ RL.≐ ⟪ Sem.⟦ w ⟧ ⟫
bridge [ g ]ʷ  = gen g
bridge ε       =
  RL.≐-sym (RL.≐-trans (scale-1 _) (RL.≐-trans (Φ-cong O.ix-id) Φ-δ))
bridge (w • v) =
  RL.≐-trans (RL.⊙-cong (bridge v) (bridge w))
  (RL.≐-trans (RI.scale-⊙ (√½ RI.^ hv) (√½ RI.^ hw) (Φ (O.ix Mv)) (Φ (O.ix Mw)))
  (RL.≐-trans (λ x y → Eq.cong (λ c → c * (Φ (O.ix Mv) RL.⊙ Φ (O.ix Mw)) x y) (^-swap hv hw))
  (RI.scale-cong (RL.≐-sym (RL.≐-trans (Φ-cong (O.ix-mul Mv Mw)) (Φ-⊙ (O.ix Mv) (O.ix Mw)))))))
  where
  hw = proj₁ Sem.⟦ w ⟧
  hv = proj₁ Sem.⟦ v ⟧
  Mw = proj₂ Sem.⟦ w ⟧
  Mv = proj₂ Sem.⟦ v ⟧

------------------------------------------------------------------------
-- Equal matrices, equal readings

private
  φ-^ : (a : ZΩ.Q) (k : ℕ) → φ (a O.^ k) ≡ φ a RI.^ k
  φ-^ a zero    = φ-1
  φ-^ a (suc k) = Eq.trans (φ-* a (a O.^ k)) (Eq.cong (φ a *_) (φ-^ a k))

  r = φ √2

  swap4 : (a b c d : D) → (a * b) * (c * d) ≡ (a * c) * (b * d)
  swap4 a b c d =
    Eq.trans (*-assoc a b (c * d))
    (Eq.trans (Eq.cong (a *_) (Eq.trans (Eq.sym (*-assoc b c d))
              (Eq.trans (Eq.cong (_* d) (*-comm b c)) (*-assoc c b d))))
              (Eq.sym (*-assoc a c (b * d))))

  -- (1/√2)^k √2^k = 1.
  cancel : (k : ℕ) → (√½ RI.^ k) * (r RI.^ k) ≡ 1#
  cancel zero    = *-identityˡ 1#
  cancel (suc k) = Eq.trans (swap4 √½ (√½ RI.^ k) r (r RI.^ k))
                     (Eq.trans (Eq.cong₂ _*_ √½-√2 (cancel k)) (*-identityˡ 1#))

  -- From r^a p = r^b q, (1/√2)^b p = (1/√2)^a q.
  unscale : (a b : ℕ) {p q : D} → (r RI.^ a) * p ≡ (r RI.^ b) * q →
            (√½ RI.^ b) * p ≡ (√½ RI.^ a) * q
  unscale a b {p} {q} e = begin
    (√½ RI.^ b) * p
      ≡⟨ Eq.sym (*-identityˡ _) ⟩
    1# * ((√½ RI.^ b) * p)
      ≡⟨ Eq.cong (_* ((√½ RI.^ b) * p)) (Eq.sym (cancel a)) ⟩
    ((√½ RI.^ a) * (r RI.^ a)) * ((√½ RI.^ b) * p)
      ≡⟨ swap4 (√½ RI.^ a) (r RI.^ a) (√½ RI.^ b) p ⟩
    ((√½ RI.^ a) * (√½ RI.^ b)) * ((r RI.^ a) * p)
      ≡⟨ Eq.cong (((√½ RI.^ a) * (√½ RI.^ b)) *_) e ⟩
    ((√½ RI.^ a) * (√½ RI.^ b)) * ((r RI.^ b) * q)
      ≡⟨ shuffle′ (√½ RI.^ a) (√½ RI.^ b) (r RI.^ b) q ⟩
    ((√½ RI.^ b) * (r RI.^ b)) * ((√½ RI.^ a) * q)
      ≡⟨ Eq.cong (_* ((√½ RI.^ a) * q)) (cancel b) ⟩
    1# * ((√½ RI.^ a) * q)
      ≡⟨ *-identityˡ _ ⟩
    (√½ RI.^ a) * q ∎
    where
    open Eq.≡-Reasoning
    shuffle′ : (a b c d : D) → (a * b) * (c * d) ≡ (b * c) * (a * d)
    shuffle′ a b c d =
      Eq.trans (Eq.cong (_* (c * d)) (*-comm a b)) (swap4 b a c d)

open O.Circuits Sem.val using (module Exact)

exact : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → ⟪ Sem.⟦ w ⟧ ⟫ RL.≐ ⟪ Sem.⟦ v ⟧ ⟫
exact {w = w} {v} (Exact.phased _ refl agree) x y =
  unscale hv hw (Eq.trans (Eq.sym L) (Eq.trans (Eq.cong φ (agree (digs x) (digs y))) R))
  where
  hw = proj₁ Sem.⟦ w ⟧
  hv = proj₁ Sem.⟦ v ⟧
  Fw = O.ix (proj₂ Sem.⟦ w ⟧) (digs x) (digs y)
  Fv = O.ix (proj₂ Sem.⟦ v ⟧) (digs x) (digs y)

  L : φ ((√2 O.^ hv) ZΩ.* Fw) ≡ (r RI.^ hv) * φ Fw
  L = Eq.trans (φ-* (√2 O.^ hv) Fw) (Eq.cong (_* φ Fw) (φ-^ √2 hv))

  R : φ (((O.x O.^ 0) ZΩ.* (√2 O.^ hw)) ZΩ.* Fv) ≡ (r RI.^ hw) * φ Fv
  R = Eq.trans (φ-* ((O.x O.^ 0) ZΩ.* (√2 O.^ hw)) Fv)
        (Eq.cong (_* φ Fv) (Eq.trans (φ-* (O.x O.^ 0) (√2 O.^ hw))
          (Eq.trans (Eq.cong₂ _*_ φ-1 (φ-^ √2 hw)) (*-identityˡ _))))
