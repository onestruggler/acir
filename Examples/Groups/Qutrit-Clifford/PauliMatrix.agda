------------------------------------------------------------------------
-- Presentations of groups
--
-- Qutrit Pauli operators as matrices, and the action of circuits on
-- them
--
-- PauliLocal has the matrices and the gates on their own wires; here
-- the tensor calculus carries those to every wire (pv-gen), the phase
-- goes along (pmat-gen), and a circuit conjugates a Pauli matrix as
-- Pauli.act says (pmat-act).  Then the converse: the matrix determines
-- the Pauli operator (pmat-injective).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.PauliMatrix where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail ; replicate)
open import Data.Vec.Properties using (≡-dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (yes ; no)

open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics hiding (_⊞_ ; _⊠_)
open import Examples.Groups.Qutrit-Clifford.Pauli
open import Examples.Groups.Qutrit-Clifford.PauliLocal public

open CommutativeRing R using (*-assoc ; *-comm ; *-identityˡ ; *-identityʳ ; zeroˡ ; zeroʳ)

private
  variable
    k m n : ℕ

  open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Gates on every wire

-- A gate on the bottom wires, and an operator moved up.
liftT : (G Lp Lq : Op m) (c : Q) (R : Op n) → (G ⊙ Lp) ≐ (scale c Lq ⊙ G) →
        (tensor G (Idₒ {n}) ⊙ tensor Lp R) ≐ (scale c (tensor Lq R) ⊙ tensor G (Idₒ {n}))
liftT G Lp Lq c R e =
  ≐-trans (tensor-⊙ G Lp Idₒ R)
  (≐-trans (tensor-cong e (≐-trans (⊙-identityˡ R) (≐-sym (⊙-identityʳ R))))
  (≐-trans (≐-sym (tensor-⊙ (scale c Lq) G R Idₒ))
           (⊙-cong (tensor-scaleˡ c Lq R) (≐-refl (tensor G Idₒ)))))

upT : (Lp : Op m) (G R R' : Op n) (c : Q) → (G ⊙ R) ≐ (scale c R' ⊙ G) →
      (tensor (Idₒ {m}) G ⊙ tensor Lp R) ≐ (scale c (tensor Lp R') ⊙ tensor (Idₒ {m}) G)
upT Lp G R R' c e =
  ≐-trans (tensor-⊙ Idₒ Lp G R)
  (≐-trans (tensor-cong (≐-trans (⊙-identityˡ Lp) (≐-sym (⊙-identityʳ Lp))) e)
  (≐-trans (≐-sym (tensor-⊙ Lp Idₒ (scale c R') G))
           (⊙-cong (tensor-scaleʳ c Lp R') (≐-refl (tensor Idₒ G)))))

-- The operator of a generator.
gop : Gen n → Op n
gop g = ix (proj₂ ⟦ g ⟧₀)

private
  -- A gate on the bottom wires, its matrix replaced by an equal one.
  emb≐ : {M : Mat k} {G : Op k} → ix M ≐ G → ix (tenM M (idM {n})) ≐ tensor G (Idₒ {n})
  emb≐ {M = M} e = ≐-trans (ix-tenM M idM) (tensor-cong e ix-id)

  -- Conjugation, transported along equal matrices of the gate.
  conj≐ : {G G' : Op k} (P P' : Op k) → G ≐ G' → (G' ⊙ P) ≐ (P' ⊙ G') → (G ⊙ P) ≐ (P' ⊙ G)
  conj≐ P P' e c =
    ≐-trans (⊙-cong e (≐-refl P)) (≐-trans c (⊙-cong (≐-refl P') (≐-sym e)))

  one-gate : (g : Gate 1) → Op 1
  one-gate H-gate = Hₒ
  one-gate S-gate = Sₒ

  one-ix : (g : Gate 1) → ix (proj₂ (val g)) ≐ one-gate g
  one-ix H-gate = ix-matOf Hₒ
  one-ix S-gate = ix-matOf Sₒ

-- A letter, on a Pauli operator with phase 1.
pv-gen : (g : Gen n) (ps : Vec Letter n) → (gop g ⊙ pv ps) ≐ (pmat (actL g (𝟎 , ps)) ⊙ gop g)
pv-gen (gate₀ ν-gate) ps =
  conj≐ (pv ps) (scale (ωL 𝟎) (pv ps)) (ix-scalM (x ^q 10))
    (≐-trans (scal-central (x ^q 10) (pv ps)) (⊙-cong (≐-sym (scale-1 (pv ps))) (≐-refl (scal (x ^q 10)))))
pv-gen {suc n} (gate₁ H-gate) (p ∷ ps) =
  conj≐ (pv (p ∷ ps)) (pmat (actL (gate₁ H-gate) (𝟎 , p ∷ ps))) (emb≐ {n = n} (one-ix H-gate))
    (liftT Hₒ (lM p) (lM (ℓ₁ H-gate p)) (ωL (φ₁ H-gate p)) (pv ps) (H-loc p))
pv-gen {suc n} (gate₁ S-gate) (p ∷ ps) =
  conj≐ (pv (p ∷ ps)) (pmat (actL (gate₁ S-gate) (𝟎 , p ∷ ps))) (emb≐ {n = n} (one-ix S-gate))
    (liftT Sₒ (lM p) (lM (ℓ₁ S-gate p)) (ωL (φ₁ S-gate p)) (pv ps) (S-loc p))
pv-gen {suc (suc n)} (gate₂ CZ-gate) (p ∷ q ∷ ps) =
  conj≐ (pv (p ∷ q ∷ ps)) (pmat (actL (gate₂ CZ-gate) (𝟎 , p ∷ q ∷ ps))) (emb≐ {n = n} (ix-matOf CZₒ))
    (≐-trans (⊙-cong (≐-refl (tensor CZₒ Idₒ)) (≐-sym (tensor-assoc₁ l₁ l₂ (pv ps))))
    (≐-trans (liftT CZₒ (tensor {1} l₁ l₂) (tensor {1} l₁' l₂') (ωL (φ₂ p q)) (pv ps) (CZ-loc p q))
             (⊙-cong (scale-cong {c = ωL (φ₂ p q)} (tensor-assoc₁ l₁' l₂' (pv ps)))
                     (≐-refl (tensor CZₒ Idₒ)))))
  where
  l₁ = lM p
  l₂ = lM q
  l₁' = lM (ℓ₂ p q)
  l₂' = lM (ℓ₂′ p q)
pv-gen {suc n} (g ↥) (p ∷ ps) =
  conj≐ (pv (p ∷ ps)) (pmat (actL (g ↥) (𝟎 , p ∷ ps))) (ix-up (proj₂ ⟦ g ⟧₀))
    (upT (lM p) (gop g) (pv ps) (pv (proj₂ (actL g (𝟎 , ps)))) (ωL (proj₁ (actL g (𝟎 , ps))))
         (pv-gen g ps))

-- The phase goes along: σ is added to what a letter does to P.
actL-phase : (g : Gen n) (σ : Z3) (ps : Vec Letter n) →
             actL g (σ , ps) ≡ (σ ⊞ proj₁ (actL g (𝟎 , ps)) , proj₂ (actL g (𝟎 , ps)))
actL-phase (gate₀ ν-gate) σ ps = Eq.cong (_, ps) (Eq.sym (⊞-identityʳ σ))
actL-phase (gate₁ H-gate) σ ((a , b) ∷ ps) =
  Eq.cong (λ u → σ ⊞ u , (𝟐 ⊠ b , a) ∷ ps) (Eq.sym (⊞-identityˡ (𝟐 ⊠ (a ⊠ b))))
actL-phase (gate₁ S-gate) σ ((a , b) ∷ ps) =
  Eq.cong (λ u → σ ⊞ u , (a , b ⊞ 𝟐 ⊠ a) ∷ ps) (Eq.sym (⊞-identityˡ (sφ a)))
actL-phase (gate₂ CZ-gate) σ ((a , b) ∷ (c , d) ∷ ps) =
  Eq.cong (λ u → σ ⊞ u , (a , b ⊞ c) ∷ (c , d ⊞ a) ∷ ps) (Eq.sym (⊞-identityˡ (a ⊠ c)))
actL-phase (g ↥) σ (p ∷ ps) =
  Eq.cong₂ (λ x y → x , p ∷ y) (Eq.cong proj₁ (actL-phase g σ ps)) (Eq.cong proj₂ (actL-phase g σ ps))

-- A letter, on any Pauli operator.
pmat-gen : (g : Gen n) (P : Pauli n) → (gop g ⊙ pmat P) ≐ (pmat (actL g P) ⊙ gop g)
pmat-gen g (σ , ps) x y = begin
  (G ⊙ scale (ωL σ) (pv ps)) x y               ≡⟨ scale-⊙ʳ′ (ωL σ) G (pv ps) x y ⟩
  ωL σ * (G ⊙ pv ps) x y                       ≡⟨ Eq.cong (ωL σ *_) (pv-gen g ps x y) ⟩
  ωL σ * (scale (ωL σ') (pv ps') ⊙ G) x y      ≡⟨ Eq.cong (ωL σ *_) (scale-⊙ˡ′ (ωL σ') (pv ps') G x y) ⟩
  ωL σ * (ωL σ' * (pv ps' ⊙ G) x y)            ≡⟨ Eq.sym (*-assoc (ωL σ) (ωL σ') _) ⟩
  (ωL σ * ωL σ') * (pv ps' ⊙ G) x y            ≡⟨ Eq.cong (_* (pv ps' ⊙ G) x y) (Eq.sym (ωL-⊞ σ σ')) ⟩
  ωL (σ ⊞ σ') * (pv ps' ⊙ G) x y               ≡⟨ Eq.sym (scale-⊙ˡ′ (ωL (σ ⊞ σ')) (pv ps') G x y) ⟩
  (pmat (σ ⊞ σ' , ps') ⊙ G) x y                ≡⟨ Eq.cong (λ P → (pmat P ⊙ G) x y) (Eq.sym (actL-phase g σ ps)) ⟩
  (pmat (actL g (σ , ps)) ⊙ G) x y             ∎
  where
  G   = gop g
  σ'  = proj₁ (actL g (𝟎 , ps))
  ps' = proj₂ (actL g (𝟎 , ps))

-- The operator of a circuit.
wop : Circuit n → Op n
wop w = ix (proj₂ ⟦ w ⟧)

-- A circuit conjugates Pauli matrices as act says.
pmat-act : (w : Circuit n) (P : Pauli n) → (wop w ⊙ pmat P) ≐ (pmat (act w P) ⊙ wop w)
pmat-act [ g ]ʷ  P = pmat-gen g P
pmat-act ε       P =
  ≐-trans (⊙-cong ix-id (≐-refl (pmat P)))
  (≐-trans (⊙-identityˡ (pmat P))
  (≐-trans (≐-sym (⊙-identityʳ (pmat P))) (⊙-cong (≐-refl (pmat P)) (≐-sym ix-id))))
pmat-act (w • v) P =
  ≐-trans (⊙-cong (ix-mul W V) (≐-refl (pmat P)))
  (≐-trans (⊙-assoc (ix W) (ix V) (pmat P))
  (≐-trans (⊙-cong (≐-refl (ix W)) (pmat-act v P))
  (≐-trans (≐-sym (⊙-assoc (ix W) (pmat (act v P)) (ix V)))
  (≐-trans (⊙-cong (pmat-act w (act v P)) (≐-refl (ix V)))
  (≐-trans (⊙-assoc (pmat (act w (act v P))) (ix W) (ix V))
           (⊙-cong (≐-refl (pmat (act w (act v P)))) (≐-sym (ix-mul W V))))))))
  where
  W = proj₂ ⟦ w ⟧
  V = proj₂ ⟦ v ⟧

------------------------------------------------------------------------
-- The entries of a Pauli matrix

-- Column y has its non-zero entry in row y + a, where it is ω^(b · y).
row : Vec Letter n → Digits n → Digits n
row []             []       = []
row ((a , _) ∷ ps) (y ∷ ys) = (y ⊞ a) ∷ row ps ys

ph : Vec Letter n → Digits n → Z3
ph []             []       = 𝟎
ph ((_ , b) ∷ ps) (y ∷ ys) = b ⊠ y ⊞ ph ps ys

private
  δ₁-refl : (x : Z3) → δ₁ x x ≡ 1#
  δ₁-refl 𝟎 = refl
  δ₁-refl 𝟏 = refl
  δ₁-refl 𝟐 = refl

  δ₁-≢ : (x y : Z3) → x ≢ y → δ₁ x y ≡ 0#
  δ₁-≢ 𝟎 𝟎 ne = ⊥-elim (ne refl)
  δ₁-≢ 𝟎 𝟏 ne = refl
  δ₁-≢ 𝟎 𝟐 ne = refl
  δ₁-≢ 𝟏 𝟎 ne = refl
  δ₁-≢ 𝟏 𝟏 ne = ⊥-elim (ne refl)
  δ₁-≢ 𝟏 𝟐 ne = refl
  δ₁-≢ 𝟐 𝟎 ne = refl
  δ₁-≢ 𝟐 𝟏 ne = refl
  δ₁-≢ 𝟐 𝟐 ne = ⊥-elim (ne refl)

pv-diag : (ps : Vec Letter n) (y : Digits n) → pv ps (row ps y) y ≡ ωL (ph ps y)
pv-diag []             []       = refl
pv-diag ((a , b) ∷ ps) (y ∷ ys) = begin
  (δ₁ (y ⊞ a) (y ⊞ a) * ωL (b ⊠ y)) * pv ps (row ps ys) ys
    ≡⟨ Eq.cong₂ _*_ (Eq.trans (Eq.cong (_* ωL (b ⊠ y)) (δ₁-refl (y ⊞ a))) (*-identityˡ (ωL (b ⊠ y))))
                    (pv-diag ps ys) ⟩
  ωL (b ⊠ y) * ωL (ph ps ys)
    ≡⟨ Eq.sym (ωL-⊞ (b ⊠ y) (ph ps ys)) ⟩
  ωL (b ⊠ y ⊞ ph ps ys) ∎

pv-off : (ps : Vec Letter n) (x y : Digits n) → x ≢ row ps y → pv ps x y ≡ 0#
pv-off []             []       []       ne = ⊥-elim (ne refl)
pv-off ((a , b) ∷ ps) (x ∷ xs) (y ∷ ys) ne with x FinP.≟ (y ⊞ a)
... | no x≢    = Eq.trans (Eq.cong (λ c → (c * ωL (b ⊠ y)) * pv ps xs ys) (δ₁-≢ x (y ⊞ a) x≢))
                   (Eq.trans (Eq.cong (_* pv ps xs ys) (zeroˡ (ωL (b ⊠ y)))) (zeroˡ (pv ps xs ys)))
... | yes refl = Eq.trans (Eq.cong ((δ₁ (y ⊞ a) (y ⊞ a) * ωL (b ⊠ y)) *_)
                   (pv-off ps xs ys (λ e → ne (Eq.cong ((y ⊞ a) ∷_) e))))
                   (zeroʳ (δ₁ (y ⊞ a) (y ⊞ a) * ωL (b ⊠ y)))

-- The rows and the phases determine the Pauli operator.
private
  zeros : (n : ℕ) → Digits n
  zeros n = replicate n 𝟎

  ⊠-zeroʳ : (b : Z3) → b ⊠ 𝟎 ≡ 𝟎
  ⊠-zeroʳ 𝟎 = refl
  ⊠-zeroʳ 𝟏 = refl
  ⊠-zeroʳ 𝟐 = refl

  ⊠-oneʳ : (b : Z3) → b ⊠ 𝟏 ≡ b
  ⊠-oneʳ 𝟎 = refl
  ⊠-oneʳ 𝟏 = refl
  ⊠-oneʳ 𝟐 = refl

  z0 : (b x : Z3) → b ⊠ 𝟎 ⊞ x ≡ x
  z0 b x = Eq.trans (Eq.cong (_⊞ x) (⊠-zeroʳ b)) (⊞-identityˡ x)

  ⊞-cancelˡ : (σ τ τ' : Z3) → σ ⊞ τ ≡ σ ⊞ τ' → τ ≡ τ'
  ⊞-cancelˡ σ τ τ' e = ⊞-cancel τ τ' σ (Eq.trans (⊞-comm τ σ) (Eq.trans e (⊞-comm σ τ')))

  ph-0 : (ps : Vec Letter n) → ph ps (zeros n) ≡ 𝟎
  ph-0 []             = refl
  ph-0 ((a , b) ∷ ps) = Eq.trans (z0 b (ph ps (zeros _))) (ph-0 ps)

decode : (σ τ : Z3) (ps qs : Vec Letter n) →
         (∀ y → row ps y ≡ row qs y) → (∀ y → σ ⊞ ph ps y ≡ τ ⊞ ph qs y) → (σ , ps) ≡ (τ , qs)
decode σ τ [] [] _ h =
  Eq.cong (_, []) (Eq.trans (Eq.sym (⊞-identityʳ σ)) (Eq.trans (h []) (⊞-identityʳ τ)))
decode σ τ ((a , b) ∷ ps) ((c , d) ∷ qs) hr hp
  with refl ← decode σ τ ps qs (λ y → Eq.cong tail (hr (𝟎 ∷ y)))
                (λ y → Eq.trans (Eq.cong (σ ⊞_) (Eq.sym (z0 b (ph ps y))))
                         (Eq.trans (hp (𝟎 ∷ y)) (Eq.cong (τ ⊞_) (z0 d (ph qs y)))))
  with refl ← Eq.trans (Eq.sym (⊞-identityˡ a))
                (Eq.trans (Eq.cong head (hr (𝟎 ∷ zeros _))) (⊞-identityˡ c))
  with refl ← Eq.trans (Eq.sym (⊠-oneʳ b))
                (Eq.trans (⊞-cancel (b ⊠ 𝟏) (d ⊠ 𝟏) (ph ps (zeros _))
                            (⊞-cancelˡ σ _ _ (hp (𝟏 ∷ zeros _))))
                          (⊠-oneʳ d))
  = refl

------------------------------------------------------------------------
-- The matrix determines the Pauli operator

pmat-injective : (P P' : Pauli n) → pmat P ≐ pmat P' → P ≡ P'
pmat-injective (σ , ps) (τ , qs) e = decode σ τ ps qs rows phases
  where
  entry : (σ : Z3) (ps : Vec Letter _) (y : Digits _) →
          ωL σ * pv ps (row ps y) y ≡ ωL (σ ⊞ ph ps y)
  entry σ ps y = Eq.trans (Eq.cong (ωL σ *_) (pv-diag ps y)) (Eq.sym (ωL-⊞ σ (ph ps y)))
  rows : ∀ y → row ps y ≡ row qs y
  rows y with ≡-dec FinP._≟_ (row ps y) (row qs y)
  ... | yes r = r
  ... | no r  = ⊥-elim (ωL≢0 (σ ⊞ ph ps y) (begin
    ωL (σ ⊞ ph ps y)              ≡⟨ entry σ ps y ⟨
    ωL σ * pv ps (row ps y) y     ≡⟨ e (row ps y) y ⟩
    ωL τ * pv qs (row ps y) y     ≡⟨ Eq.cong (ωL τ *_) (pv-off qs (row ps y) y r) ⟩
    ωL τ * 0#                     ≡⟨ zeroʳ (ωL τ) ⟩
    0#                            ∎))
  phases : ∀ y → σ ⊞ ph ps y ≡ τ ⊞ ph qs y
  phases y = ωL-inj _ _ (begin
    ωL (σ ⊞ ph ps y)              ≡⟨ entry σ ps y ⟨
    ωL σ * pv ps (row ps y) y     ≡⟨ e (row ps y) y ⟩
    ωL τ * pv qs (row ps y) y     ≡⟨ Eq.cong (λ x → ωL τ * pv qs x y) (rows y) ⟩
    ωL τ * pv qs (row qs y) y     ≡⟨ entry τ qs y ⟩
    ωL (τ ⊞ ph qs y)              ∎)
