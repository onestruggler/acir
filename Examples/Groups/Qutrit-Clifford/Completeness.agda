------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness: circuits with the same matrix are equal, given the box
-- relations
--
-- Two circuits whose values agree exactly (Semantics._≈_: equal
-- matrices once the powers of √3 are cleared) act alike on Pauli
-- operators (act-of-mat: the matrix of a circuit conjugates Pauli
-- matrices as Pauli.act says, it is invertible up to a power of √3 —
-- its inverse circuit (Inverse) — and Pauli matrices are determined by
-- their entries).  So their normal forms differ at most in the scalar
-- (−ω)^t (Uniqueness, the paper's Proposition 3.9), and not even
-- there, since the six powers of −ω are distinct.  Each circuit equals
-- its normal form (Normalise), given the box relations on its width,
-- hence the two are equal.  This is the paper's Theorem 4.4, with the
-- box relations as a hypothesis: completeness on two and three qutrits
-- is what derives them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Completeness where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₁₊)
import Presentation.Base as PB

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Reasoning using (module Width ; lift ; ν↑)
open import Examples.Groups.Qutrit-Clifford.Semantics hiding (_⊞_ ; _⊠_ ; lift)
open import Examples.Groups.Qutrit-Clifford.Soundness using (sound)
open import Examples.Groups.Qutrit-Clifford.Inverse using (inv ; inv-r)
open import Examples.Groups.Qutrit-Clifford.Pauli using (Pauli ; act)
open import Examples.Groups.Qutrit-Clifford.PauliMatrix
  using (pmat ; pmat-act ; pmat-injective ; wop ; scale-⊙ˡ′ ; scale-⊙ʳ′)
open import Examples.Groups.Qutrit-Clifford.NormalForm using (NF ; nf₀ ; nfₛ ; ⟦_⟧ⁿ ; ⟦_⟧ˣ ; ⟦_⟧ᶻ)
open import Examples.Groups.Qutrit-Clifford.Uniqueness
  using (_≗ᵃ_ ; phase ; unphase ; unphase-phase ; act-unique)
open import Examples.Groups.Qutrit-Clifford.Rels using (Rels)
open import Examples.Groups.Qutrit-Clifford.Normalise using (normalise ; normalise-ok)
open import Examples.Groups.Qutrit-Clifford.Box1 using (br₁)
open import Data.Unit using (tt)

open CommutativeRing R using (*-assoc ; *-comm ; *-identityˡ ; *-identityʳ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Exact agreement as an equation of matrices

-- The exponent of √3 and the operator of a circuit.
hx : Circuit n → ℕ
hx w = proj₁ ⟦ w ⟧

-- √3^{h'} M = √3^h M'.
agree : (w v : Circuit n) → ⟦ w ⟧ ≈ ⟦ v ⟧ →
        ∀ x y → √3 ^q hx v * wop w x y ≡ √3 ^q hx w * wop v x y
agree w v (phased k refl e) x y = Eq.trans (e x y) (Eq.cong (_* wop v x y) (*-identityˡ (√3 ^q hx w)))

private
  ⊙-scal : (c : Q) (M : Op n) → ∀ x y → (M ⊙ scal c) x y ≡ c * M x y
  ⊙-scal c M x y = begin
    Σv (λ z → M x z * (c * δv z y))   ≡⟨ Σ-cong (λ z → swap (M x z) (δv z y)) ⟩
    Σv (λ z → (M x z * δv z y) * c)   ≡⟨ Σ-scaleʳ c (λ z → M x z * δv z y) ⟩
    Σv (λ z → M x z * δv z y) * c     ≡⟨ Eq.cong (_* c) (Σ-δʳ y (M x)) ⟩
    M x y * c                         ≡⟨ *-comm (M x y) c ⟩
    c * M x y                         ∎
    where
    open Eq.≡-Reasoning
    swap : (a d : Q) → a * (c * d) ≡ (a * d) * c
    swap a d = Eq.trans (Eq.cong (a *_) (*-comm c d)) (Eq.sym (*-assoc a d c))

  scal-⊙ : (c : Q) (M : Op n) → ∀ x y → (scal c ⊙ M) x y ≡ c * M x y
  scal-⊙ c M x y = begin
    Σv (λ z → (c * δv x z) * M z y)   ≡⟨ Σ-cong (λ z → *-assoc c (δv x z) (M z y)) ⟩
    Σv (λ z → c * (δv x z * M z y))   ≡⟨ Σ-scaleˡ c (λ z → δv x z * M z y) ⟩
    c * Σv (λ z → δv x z * M z y)     ≡⟨ Eq.cong (c *_) (Σ-δˡ x (λ z → M z y)) ⟩
    c * M x y                         ∎
    where open Eq.≡-Reasoning

-- A circuit times its inverse is a power of √3.
inv-scal : (w : Circuit n) → ∀ x y → (wop w ⊙ wop (inv w)) x y ≡ √3 ^q hx (w • inv w) * δv x y
inv-scal {n} w x y = begin
  (wop w ⊙ wop (inv w)) x y                        ≡⟨ Eq.sym (ix-mul (proj₂ ⟦ w ⟧) (proj₂ ⟦ inv w ⟧) x y) ⟩
  wop (w • inv w) x y                              ≡⟨ Eq.sym (*-identityˡ (wop (w • inv w) x y)) ⟩
  √3 ^q hx (ε {X = Gen n}) * wop (w • inv w) x y   ≡⟨ agree (w • inv w) ε (sound (inv-r w)) x y ⟩
  √3 ^q hx (w • inv w) * wop ε x y                 ≡⟨ Eq.cong (√3 ^q hx (w • inv w) *_) (ix-id x y) ⟩
  √3 ^q hx (w • inv w) * δv x y                    ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Circuits with the same value act alike on Pauli operators

act-of-mat : (w v : Circuit n) → ⟦ w ⟧ ≈ ⟦ v ⟧ → w ≗ᵃ v
act-of-mat w v e P = pmat-injective (act w P) (act v P) λ x y →
  r^-cancel (hx (v • inv v)) (begin
    c * Pw x y                       ≡⟨ Eq.sym (strip Pw x y) ⟩
    ((Pw ⊙ V) ⊙ Vi) x y              ≡⟨ ⊙-cong (λ x y → mid x y) (≐-refl Vi) x y ⟩
    ((Pv ⊙ V) ⊙ Vi) x y              ≡⟨ strip Pv x y ⟩
    c * Pv x y                       ∎)
  where
  open Eq.≡-Reasoning
  W  = wop w
  V  = wop v
  Vi = wop (inv v)
  a  = √3 ^q hx v
  b  = √3 ^q hx w
  c  = √3 ^q hx (v • inv v)
  Pw = pmat (act w P)
  Pv = pmat (act v P)
  P₀ = pmat P
  E : ∀ x y → a * W x y ≡ b * V x y
  E = agree w v e
  strip : (M : Op _) → ∀ x y → ((M ⊙ V) ⊙ Vi) x y ≡ c * M x y
  strip M x y = begin
    ((M ⊙ V) ⊙ Vi) x y      ≡⟨ ⊙-assoc M V Vi x y ⟩
    (M ⊙ (V ⊙ Vi)) x y      ≡⟨ ⊙-cong (≐-refl M) (inv-scal v) x y ⟩
    (M ⊙ scal c) x y        ≡⟨ ⊙-scal c M x y ⟩
    c * M x y               ∎
  mid : ∀ x y → (Pw ⊙ V) x y ≡ (Pv ⊙ V) x y
  mid x y = r^-cancel (hx w) (begin
    b * (Pw ⊙ V) x y          ≡⟨ Eq.sym (scale-⊙ʳ′ b Pw V x y) ⟩
    (Pw ⊙ scale b V) x y      ≡⟨ ⊙-cong (≐-refl Pw) (λ x y → Eq.sym (E x y)) x y ⟩
    (Pw ⊙ scale a W) x y      ≡⟨ scale-⊙ʳ′ a Pw W x y ⟩
    a * (Pw ⊙ W) x y          ≡⟨ Eq.cong (a *_) (Eq.sym (pmat-act w P x y)) ⟩
    a * (W ⊙ P₀) x y          ≡⟨ Eq.sym (scale-⊙ˡ′ a W P₀ x y) ⟩
    (scale a W ⊙ P₀) x y      ≡⟨ ⊙-cong E (≐-refl P₀) x y ⟩
    (scale b V ⊙ P₀) x y      ≡⟨ scale-⊙ˡ′ b V P₀ x y ⟩
    b * (V ⊙ P₀) x y          ≡⟨ Eq.cong (b *_) (pmat-act v P x y) ⟩
    b * (Pv ⊙ V) x y          ∎)

------------------------------------------------------------------------
-- The powers of −ω are distinct

-- (−ω)^k, as the circuit ν^k reads.
νs : ℕ → Q
νs zero    = 1q
νs (suc k) = x ^q 10 * νs k

νs-inj : (t t' : Fin 6) → νs (toℕ t) ≡ νs (toℕ t') → t ≡ t'
νs-inj ₀ ₀ _ = refl
νs-inj ₁ ₁ _ = refl
νs-inj ₂ ₂ _ = refl
νs-inj ₃ ₃ _ = refl
νs-inj ₄ ₄ _ = refl
νs-inj ₅ ₅ _ = refl
νs-inj ₀ ₁ ()
νs-inj ₀ ₂ ()
νs-inj ₀ ₃ ()
νs-inj ₀ ₄ ()
νs-inj ₀ ₅ ()
νs-inj ₁ ₀ ()
νs-inj ₁ ₂ ()
νs-inj ₁ ₃ ()
νs-inj ₁ ₄ ()
νs-inj ₁ ₅ ()
νs-inj ₂ ₀ ()
νs-inj ₂ ₁ ()
νs-inj ₂ ₃ ()
νs-inj ₂ ₄ ()
νs-inj ₂ ₅ ()
νs-inj ₃ ₀ ()
νs-inj ₃ ₁ ()
νs-inj ₃ ₂ ()
νs-inj ₃ ₄ ()
νs-inj ₃ ₅ ()
νs-inj ₄ ₀ ()
νs-inj ₄ ₁ ()
νs-inj ₄ ₂ ()
νs-inj ₄ ₃ ()
νs-inj ₄ ₅ ()
νs-inj ₅ ₀ ()
νs-inj ₅ ₁ ()
νs-inj ₅ ₂ ()
νs-inj ₅ ₃ ()
νs-inj ₅ ₄ ()

-- The value of ν^k: no power of √3, and the scalar (−ω)^k.
hx-ν^ : (k : ℕ) → hx {n} (ν ^ k) ≡ 0
hx-ν^ zero          = refl
hx-ν^ (suc zero)    = refl
hx-ν^ (suc (suc k)) = Eq.trans (Eq.cong (_+ℕ 0) (hx-ν^ (suc k))) refl

wop-ν^ : (k : ℕ) → ∀ a b → wop {n} (ν ^ k) a b ≡ νs k * δv a b
wop-ν^ zero          a b = Eq.trans (ix-id a b) (Eq.sym (*-identityˡ (δv a b)))
wop-ν^ (suc zero)    a b = Eq.trans (ix-scalM (x ^q 10) a b)
  (Eq.cong (_* δv a b) (Eq.sym (*-identityʳ (x ^q 10))))
wop-ν^ (suc (suc k)) a b = begin
  wop (ν • ν ^ suc k) a b                     ≡⟨ ix-mul (proj₂ ⟦ ν ⟧) (proj₂ ⟦ ν ^ suc k ⟧) a b ⟩
  (wop ν ⊙ wop (ν ^ suc k)) a b               ≡⟨ ⊙-cong (ix-scalM (x ^q 10)) (≐-refl (wop (ν ^ suc k))) a b ⟩
  (scal (x ^q 10) ⊙ wop (ν ^ suc k)) a b      ≡⟨ scal-⊙ (x ^q 10) (wop (ν ^ suc k)) a b ⟩
  x ^q 10 * wop (ν ^ suc k) a b               ≡⟨ Eq.cong (x ^q 10 *_) (wop-ν^ (suc k) a b) ⟩
  x ^q 10 * (νs (suc k) * δv a b)             ≡⟨ Eq.sym (*-assoc (x ^q 10) (νs (suc k)) (δv a b)) ⟩
  νs (suc (suc k)) * δv a b                   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The scalar

private
  ν^↑ : (k : ℕ) → (₁₊ n) ⊢ (ν ^ k) ↑ ≈ ν ^ k
  ν^↑ zero          = Width.refl
  ν^↑ (suc zero)    = ν↑
  ν^↑ (suc (suc k)) = Width.cong ν↑ (ν^↑ (suc k))

-- A normal form is its scalar times the rest.
nf-phase : (nf : NF n) → n ⊢ ⟦ nf ⟧ⁿ ≈ ν ^ toℕ (phase nf) • ⟦ unphase nf ⟧ⁿ
nf-phase {n} (nf₀ t)     = Width.sym Width.right-unit
nf-phase {n} (nfₛ L M N) = begin
  ⟦ N ⟧ⁿ ↑ • M' • L'                                        ≈⟨ front (M' • L') (lift (nf-phase N)) ⟩
  (Ω ↑ • ⟦ unphase N ⟧ⁿ ↑) • M' • L'                        ≈⟨ front (M' • L') (front (⟦ unphase N ⟧ⁿ ↑) (ν^↑ (toℕ (phase N)))) ⟩
  (Ω • ⟦ unphase N ⟧ⁿ ↑) • M' • L'                          ≈⟨ assoc ⟩
  Ω • ⟦ unphase N ⟧ⁿ ↑ • M' • L'                            ∎
  where
  open Width n
  M' = ⟦ M ⟧ˣ
  L' = ⟦ L ⟧ᶻ
  Ω : {k : ℕ} → Circuit k
  Ω = ν ^ toℕ (phase N)

private
  δ₁-refl : (a : Fin 3) → δ₁ a a ≡ 1#
  δ₁-refl ₀ = refl
  δ₁-refl ₁ = refl
  δ₁-refl ₂ = refl

  δv-refl : (x : Digits n) → δv x x ≡ 1#
  δv-refl []      = refl
  δv-refl (a ∷ x) = Eq.trans (Eq.cong (δ₁ a a *_) (δv-refl x))
                      (Eq.trans (*-identityʳ (δ₁ a a)) (δ₁-refl a))

  ≈-trans' : {s₁ s₂ s₃ : Sc n} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
  ≈-trans' {s₁ = s₁} {s₂} {s₃} = ≈-trans {s₁ = s₁} {s₂} {s₃}

  ≈-sym' : {s s' : Sc n} → s ≈ s' → s' ≈ s
  ≈-sym' {s = s} {s'} = ≈-sym {s = s} {s'}

-- The scalar is seen by the matrix: (−ω)^t U ≠ (−ω)^t' U, U being
-- invertible up to a power of √3.
phase-cancel : (t t' : Fin 6) (u : Circuit n) →
               ⟦ ν ^ toℕ t • u ⟧ ≈ ⟦ ν ^ toℕ t' • u ⟧ → t ≡ t'
phase-cancel {n} t t' u e = νs-inj t t' (r^-cancel (hx (u • inv u)) (begin
  c * νs (toℕ t)                                ≡⟨ *-comm c _ ⟩
  νs (toℕ t) * c                                ≡⟨ Eq.sym (corner (toℕ t)) ⟩
  (scale (νs (toℕ t)) U ⊙ Ui) x₀ x₀             ≡⟨ ⊙-cong (λ x y → same x y) (≐-refl Ui) x₀ x₀ ⟩
  (scale (νs (toℕ t')) U ⊙ Ui) x₀ x₀            ≡⟨ corner (toℕ t') ⟩
  νs (toℕ t') * c                               ≡⟨ *-comm _ c ⟩
  c * νs (toℕ t')                               ∎))
  where
  open Eq.≡-Reasoning
  U  = wop u
  Ui = wop (inv u)
  c  = √3 ^q hx (u • inv u)
  x₀ : Digits n
  x₀ = replicate n ₀
  -- The value of ν^k • u: the operator of u times (−ω)^k.
  op : (k : ℕ) → ∀ x y → wop (ν ^ k • u) x y ≡ νs k * U x y
  op k x y = begin
    wop (ν ^ k • u) x y                     ≡⟨ ix-mul (proj₂ ⟦ ν ^ k ⟧) (proj₂ ⟦ u ⟧) x y ⟩
    (wop (ν ^ k) ⊙ U) x y                   ≡⟨ ⊙-cong (wop-ν^ k) (≐-refl U) x y ⟩
    (scal (νs k) ⊙ U) x y                   ≡⟨ scal-⊙ (νs k) U x y ⟩
    νs k * U x y                            ∎
  hx-ν : (k : ℕ) → hx (ν ^ k • u) ≡ hx u +ℕ 0
  hx-ν k = Eq.cong (hx u +ℕ_) (hx-ν^ k)
  same : ∀ x y → νs (toℕ t) * U x y ≡ νs (toℕ t') * U x y
  same x y = r^-cancel (hx u +ℕ 0) (begin
    √3 ^q (hx u +ℕ 0) * (νs (toℕ t) * U x y)
      ≡⟨ Eq.cong₂ (λ h m → √3 ^q h * m) (Eq.sym (hx-ν (toℕ t'))) (Eq.sym (op (toℕ t) x y)) ⟩
    √3 ^q hx (ν ^ toℕ t' • u) * wop (ν ^ toℕ t • u) x y
      ≡⟨ agree (ν ^ toℕ t • u) (ν ^ toℕ t' • u) e x y ⟩
    √3 ^q hx (ν ^ toℕ t • u) * wop (ν ^ toℕ t' • u) x y
      ≡⟨ Eq.cong₂ (λ h m → √3 ^q h * m) (hx-ν (toℕ t)) (op (toℕ t') x y) ⟩
    √3 ^q (hx u +ℕ 0) * (νs (toℕ t') * U x y) ∎)
  corner : (k : ℕ) → (scale (νs k) U ⊙ Ui) x₀ x₀ ≡ νs k * c
  corner k = begin
    (scale (νs k) U ⊙ Ui) x₀ x₀          ≡⟨ scale-⊙ˡ′ (νs k) U Ui x₀ x₀ ⟩
    νs k * (U ⊙ Ui) x₀ x₀                ≡⟨ Eq.cong (νs k *_) (inv-scal u x₀ x₀) ⟩
    νs k * (c * δv x₀ x₀)                ≡⟨ Eq.cong (λ d → νs k * (c * d)) (δv-refl x₀) ⟩
    νs k * (c * 1#)                      ≡⟨ Eq.cong (νs k *_) (*-identityʳ c) ⟩
    νs k * c                             ∎

phase-of-mat : (nf nf' : NF n) → unphase nf ≡ unphase nf' →
               ⟦ ⟦ nf ⟧ⁿ ⟧ ≈ ⟦ ⟦ nf' ⟧ⁿ ⟧ → phase nf ≡ phase nf'
phase-of-mat nf nf' eu e = phase-cancel (phase nf) (phase nf') U
  (≈-trans' {s₁ = ⟦ Ω • U ⟧} {⟦ ⟦ nf ⟧ⁿ ⟧} {⟦ Ω' • U ⟧}
    (≈-sym' {s = ⟦ ⟦ nf ⟧ⁿ ⟧} {⟦ Ω • U ⟧} (sound (nf-phase nf)))
    (≈-trans' {s₁ = ⟦ ⟦ nf ⟧ⁿ ⟧} {⟦ ⟦ nf' ⟧ⁿ ⟧} {⟦ Ω' • U ⟧} e
      (Eq.subst (λ m → ⟦ ⟦ nf' ⟧ⁿ ⟧ ≈ ⟦ Ω' • ⟦ m ⟧ⁿ ⟧) (Eq.sym eu) (sound (nf-phase nf')))))
  where
  U  = ⟦ unphase nf ⟧ⁿ
  Ω  = ν ^ toℕ (phase nf)
  Ω' = ν ^ toℕ (phase nf')

------------------------------------------------------------------------
-- Completeness

-- Normal forms with the same value are equal.
nf-injective : (nf nf' : NF n) → ⟦ ⟦ nf ⟧ⁿ ⟧ ≈ ⟦ ⟦ nf' ⟧ⁿ ⟧ → nf ≡ nf'
nf-injective nf nf' e = unphase-phase nf nf' eu (phase-of-mat nf nf' eu e)
  where
  eu = act-unique nf nf' (act-of-mat ⟦ nf ⟧ⁿ ⟦ nf' ⟧ⁿ e)

-- Circuits with the same value are equal, given the box relations on
-- their width.
completeness : (rs : Rels n) {w v : Circuit n} → ⟦ w ⟧ ≈ ⟦ v ⟧ → n ⊢ w ≈ v
completeness {n} rs {w} {v} e = begin
  w                       ≈⟨ normalise-ok n rs w ⟩
  ⟦ normalise n rs w ⟧ⁿ   ≡⟨ Eq.cong ⟦_⟧ⁿ nf≡ ⟩
  ⟦ normalise n rs v ⟧ⁿ   ≈⟨ normalise-ok n rs v ⟨
  v                       ∎
  where
  open Width n
  W = ⟦ normalise n rs w ⟧ⁿ
  V = ⟦ normalise n rs v ⟧ⁿ
  nf≡ = nf-injective (normalise n rs w) (normalise n rs v)
    (≈-trans' {s₁ = ⟦ W ⟧} {⟦ w ⟧} {⟦ V ⟧} (≈-sym' {s = ⟦ w ⟧} {⟦ W ⟧} (sound (normalise-ok n rs w)))
      (≈-trans' {s₁ = ⟦ w ⟧} {⟦ v ⟧} {⟦ V ⟧} e (sound (normalise-ok n rs v))))

-- On no qutrit and on one, the box relations are proved (Box1, from
-- C₁–C₅), so completeness holds outright there.
completeness₀ : {w v : Circuit 0} → ⟦ w ⟧ ≈ ⟦ v ⟧ → 0 ⊢ w ≈ v
completeness₀ = completeness tt

completeness₁ : {w v : Circuit 1} → ⟦ w ⟧ ≈ ⟦ v ⟧ → 1 ⊢ w ≈ v
completeness₁ = completeness br₁
