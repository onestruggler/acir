------------------------------------------------------------------------
-- Presentations of groups
--
-- Qutrit Pauli operators as matrices, and the gates conjugating them
-- on their own wires (the part of PauliMatrix decided by evaluation)
--
-- The matrix of ω^σ X^a Z^b ⊗ … is ω^σ times the Kronecker product of
-- the 3 × 3 matrices X^a Z^b, whose entry in row x of column y is
-- ω^{b y} if x = y + a and 0 otherwise (pmat).  A circuit w conjugates
-- them as Pauli.act says: M P = (act w P) M for the matrix M of w
-- (pmat-act).  For a gate this is an identity of 3 × 3 or 9 × 9
-- matrices, decided by evaluation for every letter (H-loc, S-loc,
-- CZ-loc), which the tensor calculus carries to every wire; the
-- factor √3 of H plays no part, being on both sides.  S and CZ are
-- diagonal, so for them the identity is checked entry by entry without
-- a sum, and the powers of ω are literals (ωL), not powers of ζ.
--
-- The matrix determines the Pauli operator (pmat-injective): column y
-- has a single non-zero entry, in row y + a, and it is ω^(σ + b · y), so
-- it tells a, then σ and b; the three powers of ω are distinct.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.PauliLocal where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using (Bool ; T)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)

open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics hiding (_⊞_ ; _⊠_)
open import Examples.Groups.Qutrit-Clifford.Evaluation using (eqQ ; eqQ-sound)
open import Examples.Groups.Qutrit-Clifford.Pauli

open CommutativeRing R using (*-assoc ; *-comm ; *-identityˡ ; *-identityʳ ; zeroˡ ; zeroʳ)

private
  variable
    k m n : ℕ

  open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Phases

-- ω^j as a literal: ω = ζ⁴ = ζ² − 1, ω² = ζ⁸ = −ζ².
ωL : Z3 → Q
ωL 𝟎 = ⟨ + 1 , + 0 , + 0 , + 0 ⟩
ωL 𝟏 = ⟨ -[1+ 0 ] , + 0 , + 1 , + 0 ⟩
ωL 𝟐 = ⟨ + 0 , + 0 , -[1+ 0 ] , + 0 ⟩

ωL≡ω^ : (j : Z3) → ωL j ≡ ω^ j
ωL≡ω^ 𝟎 = refl
ωL≡ω^ 𝟏 = refl
ωL≡ω^ 𝟐 = refl

ωL-⊞ : (σ τ : Z3) → ωL (σ ⊞ τ) ≡ ωL σ * ωL τ
ωL-⊞ 𝟎 𝟎 = refl
ωL-⊞ 𝟎 𝟏 = refl
ωL-⊞ 𝟎 𝟐 = refl
ωL-⊞ 𝟏 𝟎 = refl
ωL-⊞ 𝟏 𝟏 = refl
ωL-⊞ 𝟏 𝟐 = refl
ωL-⊞ 𝟐 𝟎 = refl
ωL-⊞ 𝟐 𝟏 = refl
ωL-⊞ 𝟐 𝟐 = refl

ωL-inj : (σ τ : Z3) → ωL σ ≡ ωL τ → σ ≡ τ
ωL-inj 𝟎 𝟎 _ = refl
ωL-inj 𝟏 𝟏 _ = refl
ωL-inj 𝟐 𝟐 _ = refl
ωL-inj 𝟎 𝟏 ()
ωL-inj 𝟎 𝟐 ()
ωL-inj 𝟏 𝟎 ()
ωL-inj 𝟏 𝟐 ()
ωL-inj 𝟐 𝟎 ()
ωL-inj 𝟐 𝟏 ()

ωL≢0 : (σ : Z3) → ωL σ ≢ 0#
ωL≢0 𝟎 ()
ωL≢0 𝟏 ()
ωL≢0 𝟐 ()

------------------------------------------------------------------------
-- Pauli matrices

-- X^a Z^b.
lM : Letter → Op 1
lM (a , b) (x ∷ []) (y ∷ []) = δ₁ x (y ⊞ a) * ωL (b ⊠ y)

pv : Vec Letter n → Op n
pv []       = Idₒ
pv (p ∷ ps) = tensor {1} (lM p) (pv ps)

pmat : Pauli n → Op n
pmat P = scale (ωL (proj₁ P)) (pv (proj₂ P))

------------------------------------------------------------------------
-- Scalars

scale-⊙ˡ′ : (a : Q) (M N : Op n) → (scale a M ⊙ N) ≐ scale a (M ⊙ N)
scale-⊙ˡ′ a M N x y =
  Eq.trans (Σ-cong (λ z → *-assoc a (M x z) (N z y))) (Σ-scaleˡ a (λ z → M x z * N z y))

scale-⊙ʳ′ : (a : Q) (M N : Op n) → (M ⊙ scale a N) ≐ scale a (M ⊙ N)
scale-⊙ʳ′ a M N x y =
  Eq.trans (Σ-cong (λ z → swap (M x z) (N z y))) (Σ-scaleˡ a (λ z → M x z * N z y))
  where
  swap : (b c : Q) → b * (a * c) ≡ a * (b * c)
  swap b c = Eq.trans (Eq.sym (*-assoc b a c))
    (Eq.trans (Eq.cong (_* c) (*-comm b a)) (*-assoc a b c))

scaled : (a : Q) {G P P' : Op k} → (G ⊙ P) ≐ (P' ⊙ G) → (scale a G ⊙ P) ≐ (P' ⊙ scale a G)
scaled a {G} {P} {P'} e =
  ≐-trans (scale-⊙ˡ′ a G P) (≐-trans (scale-cong {c = a} e) (≐-sym (scale-⊙ʳ′ a P' G)))

-- A scalar matrix commutes with everything.
scal-central : (c : Q) (M : Op n) → (scal c ⊙ M) ≐ (M ⊙ scal c)
scal-central c M x y = begin
  Σv (λ z → (c * δv x z) * M z y)   ≡⟨ Σ-cong (λ z → *-assoc c (δv x z) (M z y)) ⟩
  Σv (λ z → c * (δv x z * M z y))   ≡⟨ Σ-scaleˡ c (λ z → δv x z * M z y) ⟩
  c * Σv (λ z → δv x z * M z y)     ≡⟨ Eq.cong (c *_) (Σ-δˡ x (λ z → M z y)) ⟩
  c * M x y                         ≡⟨ *-comm c (M x y) ⟩
  M x y * c                         ≡⟨ Eq.sym (Σ-δʳ y (λ z → M x z * c)) ⟩
  Σv (λ z → (M x z * c) * δv z y)   ≡⟨ Σ-cong (λ z → *-assoc (M x z) c (δv z y)) ⟩
  Σv (λ z → M x z * (c * δv z y))   ∎

------------------------------------------------------------------------
-- The gates, on one or two wires, decided by evaluation

-- G P = ω^c P' G.
Conj : Op k → Op k → Z3 → Op k → Set
Conj G P c P' = (G ⊙ P) ≐ (scale (ωL c) P' ⊙ G)

conj? : Op k → Op k → Z3 → Op k → Bool
conj? {k} G P c P' = allD k λ x → allD k λ y → eqQ ((G ⊙ P) x y) ((scale (ωL c) P' ⊙ G) x y)

conj-sound : (G P : Op k) (c : Z3) (P' : Op k) → T (conj? G P c P') → Conj G P c P'
conj-sound {k} G P c P' t x y =
  eqQ-sound _ _ (allD-sound k _ (allD-sound k (λ x → allD k λ y →
    eqQ ((G ⊙ P) x y) ((scale (ωL c) P' ⊙ G) x y)) t x) y)

-- A diagonal gate, d on the diagonal: G P = ω^c P' G entry by entry,
-- d x P x y = ω^c P' x y d y, with no sum to evaluate.
module Diagonal (G : Op k) (d : Digits k → Q) (G-diag : ∀ x z → G x z ≡ δv x z * d z) where

  ⊙G : (P : Op k) → ∀ x y → (P ⊙ G) x y ≡ P x y * d y
  ⊙G P x y = begin
    Σv (λ z → P x z * G z y)           ≡⟨ Σ-cong (λ z → Eq.cong (P x z *_) (G-diag z y)) ⟩
    Σv (λ z → P x z * (δv z y * d y))  ≡⟨ Σ-cong (λ z → Eq.sym (*-assoc (P x z) (δv z y) (d y))) ⟩
    Σv (λ z → (P x z * δv z y) * d y)  ≡⟨ Σ-scaleʳ (d y) (λ z → P x z * δv z y) ⟩
    Σv (λ z → P x z * δv z y) * d y    ≡⟨ Eq.cong (_* d y) (Σ-δʳ y (P x)) ⟩
    P x y * d y                        ∎

  G⊙ : (P : Op k) → ∀ x y → (G ⊙ P) x y ≡ d x * P x y
  G⊙ P x y = begin
    Σv (λ z → G x z * P z y)           ≡⟨ Σ-cong (λ z → Eq.cong (_* P z y) (G-diag x z)) ⟩
    Σv (λ z → (δv x z * d z) * P z y)  ≡⟨ Σ-cong (λ z → *-assoc (δv x z) (d z) (P z y)) ⟩
    Σv (λ z → δv x z * (d z * P z y))  ≡⟨ Σ-δˡ x (λ z → d z * P z y) ⟩
    d x * P x y                        ∎

  dconj? : Op k → Z3 → Op k → Bool
  dconj? P c P' = allD k λ x → allD k λ y → eqQ (d x * P x y) ((ωL c * P' x y) * d y)

  dconj-sound : (P : Op k) (c : Z3) (P' : Op k) → T (dconj? P c P') → Conj G P c P'
  dconj-sound P c P' t x y = Eq.trans (G⊙ P x y)
    (Eq.trans (eqQ-sound _ _ (allD-sound k _ (allD-sound k (λ x → allD k λ y →
                 eqQ (d x * P x y) ((ωL c * P' x y) * d y)) t x) y))
              (Eq.sym (⊙G (scale (ωL c) P') x y)))

-- What a one-wire gate does to a letter, and a two-wire gate to two.
φ₁ : Gate 1 → Letter → Z3
φ₁ g p = proj₁ (actL (gate₁ {0} g) (𝟎 , p ∷ []))

ℓ₁ : Gate 1 → Letter → Letter
ℓ₁ g p = head (proj₂ (actL (gate₁ {0} g) (𝟎 , p ∷ [])))

φ₂ : Letter → Letter → Z3
φ₂ p q = proj₁ (actL (gate₂ {0} CZ-gate) (𝟎 , p ∷ q ∷ []))

ℓ₂ ℓ₂′ : Letter → Letter → Letter
ℓ₂  p q = head (proj₂ (actL (gate₂ {0} CZ-gate) (𝟎 , p ∷ q ∷ [])))
ℓ₂′ p q = head (tail (proj₂ (actL (gate₂ {0} CZ-gate) (𝟎 , p ∷ q ∷ []))))

act₁ : (g : Gate 1) (p : Letter) (ps : Vec Letter n) →
       actL (gate₁ g) (𝟎 , p ∷ ps) ≡ (φ₁ g p , ℓ₁ g p ∷ ps)
act₁ H-gate (a , b) ps = refl
act₁ S-gate (a , b) ps = refl

act₂ : (p q : Letter) (ps : Vec Letter n) →
       actL (gate₂ CZ-gate) (𝟎 , p ∷ q ∷ ps) ≡ (φ₂ p q , ℓ₂ p q ∷ ℓ₂′ p q ∷ ps)
act₂ (a , b) (c , d) ps = refl

private
  allL : (Letter → Bool) → Bool
  allL f = allD 2 λ { (a ∷ b ∷ []) → f (a , b) }

  allL-sound : (f : Letter → Bool) → T (allL f) → ∀ p → T (f p)
  allL-sound f t (a , b) = allD-sound 2 (λ { (a ∷ b ∷ []) → f (a , b) }) t (a ∷ b ∷ [])

  allL₂ : (Letter → Letter → Bool) → Bool
  allL₂ f = allD 4 λ { (a ∷ b ∷ c ∷ d ∷ []) → f (a , b) (c , d) }

  allL₂-sound : (f : Letter → Letter → Bool) → T (allL₂ f) → ∀ p q → T (f p q)
  allL₂-sound f t (a , b) (c , d) =
    allD-sound 4 (λ { (a ∷ b ∷ c ∷ d ∷ []) → f (a , b) (c , d) }) t (a ∷ b ∷ c ∷ d ∷ [])

  -- S and CZ on the diagonal.
  dS : Digits 1 → Q
  dS (b ∷ []) = sph b

  S-diag : ∀ x z → Sₒ x z ≡ δv x z * dS z
  S-diag (a ∷ []) (b ∷ []) = Eq.cong (_* sph b) (Eq.sym (*-identityʳ (δ₁ a b)))

  dCZ : Digits 2 → Q
  dCZ (b₀ ∷ b₁ ∷ []) = ωL (b₀ ⊠ b₁)

  CZ-diag : ∀ x z → CZₒ x z ≡ δv x z * dCZ z
  CZ-diag (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []) = begin
    δ₁ a₀ b₀ * (δ₁ a₁ b₁ * ω^ (b₀ ⊠′ b₁))          ≡⟨ Eq.cong (λ w → δ₁ a₀ b₀ * (δ₁ a₁ b₁ * w)) (ω-same b₀ b₁) ⟩
    δ₁ a₀ b₀ * (δ₁ a₁ b₁ * ωL (b₀ ⊠ b₁))          ≡⟨ Eq.cong (δ₁ a₀ b₀ *_) (Eq.cong (_* ωL (b₀ ⊠ b₁))
                                                      (Eq.sym (*-identityʳ (δ₁ a₁ b₁)))) ⟩
    δ₁ a₀ b₀ * ((δ₁ a₁ b₁ * 1#) * ωL (b₀ ⊠ b₁))   ≡⟨ Eq.sym (*-assoc (δ₁ a₀ b₀) (δ₁ a₁ b₁ * 1#) _) ⟩
    (δ₁ a₀ b₀ * (δ₁ a₁ b₁ * 1#)) * ωL (b₀ ⊠ b₁)   ∎
    where
    open import Examples.Groups.Qutrit-Clifford.Semantics using () renaming (_⊠_ to _⊠′_)
    ω-same : ∀ b₀ b₁ → ω^ (b₀ ⊠′ b₁) ≡ ωL (b₀ ⊠ b₁)
    ω-same 𝟎 𝟎 = refl
    ω-same 𝟎 𝟏 = refl
    ω-same 𝟎 𝟐 = refl
    ω-same 𝟏 𝟎 = refl
    ω-same 𝟏 𝟏 = refl
    ω-same 𝟏 𝟐 = refl
    ω-same 𝟐 𝟎 = refl
    ω-same 𝟐 𝟏 = refl
    ω-same 𝟐 𝟐 = refl

  module DS = Diagonal Sₒ dS S-diag
  module DCZ = Diagonal CZₒ dCZ CZ-diag

H-loc : (p : Letter) → Conj Hₒ (lM p) (φ₁ H-gate p) (lM (ℓ₁ H-gate p))
H-loc p = conj-sound Hₒ (lM p) (φ₁ H-gate p) (lM (ℓ₁ H-gate p))
  (allL-sound (λ p → conj? Hₒ (lM p) (φ₁ H-gate p) (lM (ℓ₁ H-gate p))) tt p)

S-loc : (p : Letter) → Conj Sₒ (lM p) (φ₁ S-gate p) (lM (ℓ₁ S-gate p))
S-loc p = DS.dconj-sound (lM p) (φ₁ S-gate p) (lM (ℓ₁ S-gate p))
  (allL-sound (λ p → DS.dconj? (lM p) (φ₁ S-gate p) (lM (ℓ₁ S-gate p))) tt p)

CZ-loc : (p q : Letter) →
         Conj CZₒ (tensor {1} (lM p) (lM q)) (φ₂ p q) (tensor {1} (lM (ℓ₂ p q)) (lM (ℓ₂′ p q)))
CZ-loc p q = DCZ.dconj-sound (tensor {1} (lM p) (lM q)) (φ₂ p q)
  (tensor {1} (lM (ℓ₂ p q)) (lM (ℓ₂′ p q)))
  (allL₂-sound (λ p q → DCZ.dconj? (tensor {1} (lM p) (lM q)) (φ₂ p q)
                                   (tensor {1} (lM (ℓ₂ p q)) (lM (ℓ₂′ p q)))) tt p q)
