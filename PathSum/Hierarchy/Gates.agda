------------------------------------------------------------------------
-- Presentations of groups
--
-- The gates as operators, and how they conjugate the Paulis
--
-- Both gate sets of the development act on columns by the three kinds
-- of unnormalised matrix of PathSum.Unitarity.Gates: a Hadamard hadᴬ w,
-- a diagonal phase phaseᴬ e (S, CZ, R_k, R_k†) and a controlled NOT
-- cnotᴬ c t.  Here each is an operator (PathSum.Hierarchy.Operator):
-- its matrix is read off the basis columns, the entry from x to z
-- being the gate's column at x read at z, and its normalisation is 1
-- for a Hadamard and 0 otherwise.  So hadOp w is H on wire w,
-- diagOp e the diagonal matrix of the phases ζ^(e z), and cnotOp c t
-- the permutation matrix of z ↦ z[t ≔ z_t ⊕ z_c].
--
-- Algebra.  Each gate's column map is linear (lin-had, lin-diag,
-- lin-cnot), so a product with a gate on the left is the gate applied
-- to the other factor's columns (col-·), and the product of two gates
-- is their composite column map.  Each is unitary: H and CNOT are
-- real and symmetric, so their own adjoints, and H H = 2, CNOT CNOT = 1
-- (PathSum.Adjoint.Gates); a diagonal's adjoint is the opposite
-- diagonal, which undoes it.
--
-- Pauli conjugation.  For a diagonal, P(a, x, z) moves past diagOp e
-- leaving the diagonal of the phase differences behind:
--
--    D_e P D_e† = D_f P ,   f(u) = e(u) - e(u ⊕ x)          (diag-conj)
--
-- For the phase s on one wire, D(s) = diag(1, ζ^s), that is P when P
-- does not flip the wire and ζ^(-s) D(2s) P when it does (Rs-conj-0,
-- Rs-conj-1): conjugating halves the order of the rotation, which is
-- what makes R_k climb the hierarchy one level per conjugation
-- (PathSum.Hierarchy.Levels).  When the phase differences are Pauli
-- phases, i^a' (-1)^(z'·u), D_e P D_e† is the Pauli i^a' Z^z' P
-- (diag-conj-pauli): so it is for S, Z and CZ.  CNOT conjugates every
-- Pauli to a Pauli by its permutation, X^x ↦ X^(πx) and Z^z ↦ Z^(πᵀz)
-- (cnot-pauli).  For H the generators suffice (PathSum.Hierarchy's
-- generator form): X_w ↔ Z_w, and the X_j and Z_j on other wires
-- commute with it (had-X, had-Z, had-Xj, had-Zj).  Hence H, CNOT, S, Z
-- and CZ are in 𝒞 2 (had-𝒞₂, cnot-𝒞₂, diag-𝒞₂).
--
-- Every identity is proved entry by entry.  A product with a Pauli
-- collapses to a single rotated entry (PathSum.Hierarchy.Pauli's
-- ·-pauli and pauli-·′); the entries of the gates are written as a
-- guarded power of ζ (had-δ: H's entry from v to u is
-- (-1)^(v_w u_w) when v and u agree off w, and 0 otherwise), so that
-- each identity is an equality of guards and a congruence of phases
-- modulo N under the guard.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Gates (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityʳ; +-identityˡ; *-zeroʳ; *-identityʳ; +-inverseʳ;
   neg-distribˡ-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin

open import PathSum.Adjoint.Gates M₀ using
  (had-had; cnot-cnot; phase-cancel; phase-cancel⁻; conj-had; conj-δ)
open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-cong; _=ᵇ_; =ᵇ-refl; =ᵇ-true; same;
   same-true; same-intro; same-≗)
open import PathSum.CircuitSemantics M₀ using
  (Column; δ; δ-resp; rot-cong; sum-cong)
open import PathSum.Compose.Matrix M₀ using (if-⊛; ⊛-if)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong; bool-iff; rot-if)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _·ᴬ_; _≐_; Σᴮ; Σᴮ-cong; Σᴮ-+; zpow; rot; rot-map;
   rot-exp; rot-0; rot-0ᴬ; rot-comp; rot-Σᴮ; rot-+ᴬ; √2·-twice; Respects)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy M₀
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀
open import PathSum.Maslov.Arith M₀ using (½-xor; ½-self)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; zpow-≡ᴺ; rot-≡ᴺ;
   module ≡ᴺ-Reasoning)
open import PathSum.Ring M₀ using
  (_⊛_; ⊛-cong; ⊛-distribˡ-+ᴬ; ⊛-rotʳ; zpow-⊛; conj; conj-cong;
   conj-rot)
open import PathSum.Ring.Laws M₀ using
  (⊛-identityʳ; +ᴬ-identityʳ; +ᴬ-identityˡ)
open import PathSum.Unitarity.Gates M₀ using
  (hadᴬ; phaseᴬ; cnotᴬ; had-resp; cnot-resp; cnot-involutive)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Guarded powers of ζ

-- The entries of the gates and the Paulis are all of this form.

gz : Bool → ℤ → Amp
gz g e = if g then zpow e else 0ᴬ

-- Under its guard, a phase may be read modulo N.

gz-≡ᴺ : (g : Bool) {e e′ : ℤ} → (g ≡ true → e ≡ᴺ e′) → gz g e ≐ gz g e′
gz-≡ᴺ true  h = zpow-≡ᴺ (h refl)
gz-≡ᴺ false h = λ _ → refl

gz-guard : {g g′ : Bool} (e : ℤ) → g ≡ g′ → gz g e ≐ gz g′ e
gz-guard e refl = λ _ → refl

-- Two guarded powers: equal guards, and congruent phases under them.

gz-cong : {g g′ : Bool} {e e′ : ℤ} → g ≡ g′ → (g′ ≡ true → e ≡ᴺ e′) →
          gz g e ≐ gz g′ e′
gz-cong {g′ = g′} {e = e} refl h = gz-≡ᴺ g′ h

private
  ∧-intro : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
  ∧-intro refl refl = refl

  ∧-elimˡ : ∀ a {b} → (a ∧ b) ≡ true → a ≡ true
  ∧-elimˡ true  _ = refl

  ∧-elimʳ : ∀ a {b} → (a ∧ b) ≡ true → b ≡ true
  ∧-elimʳ true  h = h

  -- The unit vector at w.

  e-here : (w : Fin n) → eᵛ w w ≡ true
  e-here w = ≔-here 0ᵛ w true

  e-there : {w j : Fin n} → j ≢ w → eᵛ w j ≡ false
  e-there j≢w = ≔-there 0ᵛ true j≢w


------------------------------------------------------------------------
-- Operators given by their action on columns

-- A column map that respects equality of entries, and one that maps
-- columns respecting pointwise equality to such columns.

ColCong : (Column n → Column n) → Set
ColCong {n} A = ∀ {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
                ∀ z → A φ z ≐ A φ′ z

ColResp : (Column n → Column n) → Set
ColResp {n} A = ∀ {ψ : Column n} → Respects ψ → Respects (A ψ)

-- The matrix read off the basis columns.

colOp : ℕ → (A : Column n → Column n) → ColCong A → ColResp A → Op n
colOp k A A-cong A-resp = op k (λ x z → A (δ x) z)
  (λ {x} {x′} {z} {z′} xx zz →
     A-cong {δ x} {δ x′} (λ u i → cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
                                     (same-≗ {x = x} {x′ = x′} {z = u} {z′ = u}
                                             xx (λ _ → refl))) z
     ∙ A-resp (δ-resp x′) z z′ zz)

-- A linear column map is its matrix acting on columns.

Linear : (Column n → Column n) → Set
Linear {n} A = (ψ : Column n) → Respects ψ →
               ∀ z → A ψ z ≐ Σᴮ (λ w → ψ w ⊛ A (δ w) z)

-- A product with a linear map on the left: the map applied to the
-- columns of the other factor.

col-· : (k : ℕ) (A : Column n → Column n) (A-cong : ColCong A)
        (A-resp : ColResp A) → Linear A → (B : Op n) → ∀ x z →
        mat (colOp k A A-cong A-resp · B) x z ≐ A (λ w → mat B x w) z
col-· k A A-cong A-resp lin B x z = ≐-sym (lin (λ w → mat B x w) (respᶻ B x) z)

col-·-col : (k j : ℕ) (A : Column n → Column n) (A-cong : ColCong A)
            (A-resp : ColResp A) → Linear A →
            (B : Column n → Column n) (B-cong : ColCong B)
            (B-resp : ColResp B) → ∀ x z → mat (colOp k A A-cong A-resp · colOp j B B-cong B-resp) x z
                    ≐ A (B (δ x)) z
col-·-col k j A A-cong A-resp lin B B-cong B-resp x z =
  col-· k A A-cong A-resp lin (colOp j B B-cong B-resp) x z

-- Summing a column against a basis column picks an entry.

Σ-δ : (ψ : Column n) → Respects ψ → ∀ u → Σᴮ (λ w → ψ w ⊛ δ w u) ≐ ψ u
Σ-δ ψ resp u =
  Σᴮ-cong (λ w →
    ⊛-cong {a = ψ w} ≐-refl
           (if-cong {p = same w u} {q = same u w} (same-sym w u) ≐-refl)
    ∙ ⊛-if (same u w) (ψ w) (zpow 0ℤ))
  ∙ Σᴮ-δ u (λ w → ψ w ⊛ zpow 0ℤ)
         (λ g h g≗h → ⊛-cong (resp g h g≗h) ≐-refl)
  ∙ ⊛-identityʳ (ψ u)


------------------------------------------------------------------------
-- The three kinds of gate

had-cong : (w : Fin n) {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
           ∀ z → hadᴬ w φ z ≐ hadᴬ w φ′ z
had-cong w {φ} {φ′} h z =
  sum-cong (φ (z [ w ≔ false ])) (φ′ (z [ w ≔ false ]))
           (φ (z [ w ≔ true ])) (φ′ (z [ w ≔ true ]))
           (½ * [ z w ]ᶻ) (½ * [ z w ]ᶻ)
           (h (z [ w ≔ false ])) refl (h (z [ w ≔ true ]))

hadOp : Fin n → Op n
hadOp w = colOp 1 (hadᴬ w) (had-cong w) (had-resp w)

cnot-cong : (c t : Fin n) {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
            ∀ z → cnotᴬ c t φ z ≐ cnotᴬ c t φ′ z
cnot-cong c t h z = h (z [ t ≔ z t xor z c ])

cnotOp : Fin n → Fin n → Op n
cnotOp c t = colOp 0 (cnotᴬ c t) (cnot-cong c t) (cnot-resp c t)

-- A phase function that reads an assignment through its values.

PhaseFn : ℕ → Set
PhaseFn n = Σ[ e ∈ (Assign n → ℤ) ]
            (∀ {z z′ : Assign n} → (∀ j → z j ≡ z′ j) → e z ≡ e z′)

diag-cong : (e : Assign n → ℤ) {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
            ∀ z → phaseᴬ e φ z ≐ phaseᴬ e φ′ z
diag-cong e h z = rot-map (e z) (h z)

diag-resp : (E : PhaseFn n) {ψ : Column n} → Respects ψ →
            Respects (phaseᴬ (proj₁ E) ψ)
diag-resp (e , e-resp) {ψ} resp z z′ zz =
  rot-cong (ψ z) (ψ z′) (e z) (e z′) (e-resp zz) (resp z z′ zz)

diagOp : PhaseFn n → Op n
diagOp E = colOp 0 (phaseᴬ (proj₁ E)) (diag-cong (proj₁ E)) (diag-resp E)

-- The phase s on wire w: diag(1, ζ^s) there.

wireFn : ℤ → Fin n → PhaseFn n
wireFn s w = (λ z → s * [ z w ]ᶻ) , (λ zz → cong (λ b → s * [ b ]ᶻ) (zz w))

Rs : ℤ → Fin n → Op n
Rs s w = diagOp (wireFn s w)


------------------------------------------------------------------------
-- Linearity

lin-had : (w : Fin n) → Linear (hadᴬ w)
lin-had w ψ resp z = ≐-sym (
  Σᴮ-cong (λ y →
    ⊛-distribˡ-+ᴬ (ψ y) (δ y z₀) (rot e (δ y z₁))
    ∙ (λ i → cong (λ t → (ψ y ⊛ δ y z₀) i + t) (⊛-rotʳ e (ψ y) (δ y z₁) i)))
  ∙ Σᴮ-+ (λ y → ψ y ⊛ δ y z₀) (λ y → rot e (ψ y ⊛ δ y z₁))
  ∙ (λ i → cong₂ _+_ (Σ-δ ψ resp z₀ i)
             (trans (sym (rot-Σᴮ e (λ y → ψ y ⊛ δ y z₁) i))
                    (rot-map e (Σ-δ ψ resp z₁) i))))
  where
  z₀ = z [ w ≔ false ]
  z₁ = z [ w ≔ true ]
  e  = ½ * [ z w ]ᶻ

lin-cnot : (c t : Fin n) → Linear (cnotᴬ c t)
lin-cnot c t ψ resp z = ≐-sym (Σ-δ ψ resp (z [ t ≔ z t xor z c ]))

lin-diag : (e : Assign n → ℤ) → Linear (phaseᴬ e)
lin-diag e ψ resp z = ≐-sym (
  Σᴮ-cong (λ y → ⊛-rotʳ (e z) (ψ y) (δ y z))
  ∙ ≐-sym (rot-Σᴮ (e z) (λ y → ψ y ⊛ δ y z))
  ∙ rot-map (e z) (Σ-δ ψ resp z))


------------------------------------------------------------------------
-- The entries of a Hadamard

-- v and u agree off w, and the sign is (-1)^(v_w u_w).

private
  same-≔ : (v u : Assign n) (w : Fin n) (b : Bool) →
           same v (u [ w ≔ b ]) ≡ ((v w =ᵇ b) ∧ same (v [ w ≔ u w ]) u)
  same-≔ v u w b = bool-iff to from
    where
    to : same v (u [ w ≔ b ]) ≡ true →
         ((v w =ᵇ b) ∧ same (v [ w ≔ u w ]) u) ≡ true
    to h = ∧-intro
      (trans (cong (_=ᵇ b) (trans (pt w) (≔-here u w b))) (=ᵇ-refl b))
      (same-intro (v [ w ≔ u w ]) u (λ j → off j (j Fin.≟ w)))
      where
      pt = same-true v (u [ w ≔ b ]) h
      off : ∀ j → Dec (j ≡ w) → (v [ w ≔ u w ]) j ≡ u j
      off j (yes refl) = ≔-here v w (u w)
      off j (no j≢w)   = trans (≔-there v (u w) j≢w)
                               (trans (pt j) (≔-there u b j≢w))
    from : ((v w =ᵇ b) ∧ same (v [ w ≔ u w ]) u) ≡ true →
           same v (u [ w ≔ b ]) ≡ true
    from h = same-intro v (u [ w ≔ b ]) (λ j → at j (j Fin.≟ w))
      where
      vw : v w ≡ b
      vw = =ᵇ-true (∧-elimˡ (v w =ᵇ b) h)
      pt = same-true (v [ w ≔ u w ]) u (∧-elimʳ (v w =ᵇ b) h)
      at : ∀ j → Dec (j ≡ w) → v j ≡ (u [ w ≔ b ]) j
      at j (yes refl) = trans vw (sym (≔-here u w b))
      at j (no j≢w)   = trans (sym (≔-there v (u w) j≢w))
                              (trans (pt j) (sym (≔-there u b j≢w)))

had-δ : (w : Fin n) (v u : Assign n) →
        hadᴬ w (δ v) u ≐ gz (same (v [ w ≔ u w ]) u) (½ * [ v w ∧ u w ]ᶻ)
had-δ w v u = at (v w) refl
  where
  G = same (v [ w ≔ u w ]) u
  e = ½ * [ u w ]ᶻ

  guard : (b b′ : Bool) → v w ≡ b →
          same v (u [ w ≔ b′ ]) ≡ ((b =ᵇ b′) ∧ G)
  guard b b′ eq = trans (same-≔ v u w b′) (cong (λ c → (c =ᵇ b′) ∧ G) eq)

  at : (b : Bool) → v w ≡ b →
       hadᴬ w (δ v) u ≐ gz G (½ * [ v w ∧ u w ]ᶻ)
  at false eq =
    (λ i → cong₂ _+_
       (gz-guard 0ℤ (guard false false eq) i)
       (trans (rot-map e (gz-guard 0ℤ (guard false true eq)) i)
              (rot-0ᴬ e i)))
    ∙ +ᴬ-identityʳ (gz G 0ℤ)
    ∙ gz-≡ᴺ G (λ _ → ≡ᴺ-≡ (sym (trans (cong (λ c → ½ * [ c ∧ u w ]ᶻ) eq)
                                      (*-zeroʳ ½))))
  at true eq =
    (λ i → cong₂ _+_
       (gz-guard 0ℤ (guard true false eq) i)
       (rot-map e (gz-guard 0ℤ (guard true true eq)) i))
    ∙ +ᴬ-identityˡ (rot e (gz G 0ℤ))
    ∙ rot-if G e 0ℤ
    ∙ gz-≡ᴺ G (λ _ → ≡ᴺ-≡ (trans (+-identityʳ e)
                                 (cong (λ c → ½ * [ c ∧ u w ]ᶻ) (sym eq))))

-- Hence H is symmetric.

had-sym : (w : Fin n) (v u : Assign n) → hadᴬ w (δ v) u ≐ hadᴬ w (δ u) v
had-sym {n} w v u =
  had-δ w v u
  ∙ gz-cong (bool-iff (agree v u) (agree u v))
            (λ _ → ≡ᴺ-≡ (cong (λ c → ½ * [ c ]ᶻ) (∧-comm (v w) (u w))))
  ∙ ≐-sym (had-δ w u v)
  where
  agree : (a b : Assign n) → same (a [ w ≔ b w ]) b ≡ true →
          same (b [ w ≔ a w ]) a ≡ true
  agree a b h = same-intro (b [ w ≔ a w ]) a (λ j → at j (j Fin.≟ w))
    where
    pt = same-true (a [ w ≔ b w ]) b h
    at : ∀ j → Dec (j ≡ w) → (b [ w ≔ a w ]) j ≡ a j
    at j (yes refl) = ≔-here b w (a w)
    at j (no j≢w)   = trans (≔-there b (a w) j≢w)
                            (trans (sym (pt j)) (≔-there a (b w) j≢w))
  ∧-comm : ∀ a b → (a ∧ b) ≡ (b ∧ a)
  ∧-comm true  true  = refl
  ∧-comm true  false = refl
  ∧-comm false true  = refl
  ∧-comm false false = refl


------------------------------------------------------------------------
-- Adjoints and unitarity

-- H is real and symmetric: its own adjoint.

had-† : (w : Fin n) → hadOp w † ≈ hadOp w
had-† w = ≈-by (hadOp w †) (hadOp w) refl (λ x z →
  conj-had w (δ z) x
  ∙ had-cong w (conj-δ z) x
  ∙ had-sym w z x)

-- So is CNOT: its permutation is an involution.

flip : Fin n → Fin n → Assign n → Assign n
flip c t z = z [ t ≔ z t xor z c ]

flip-≗ : (c t : Fin n) {y y′ : Assign n} → (∀ j → y j ≡ y′ j) →
         ∀ j → flip c t y j ≡ flip c t y′ j
flip-≗ c t {y} {y′} yy j =
  trans (≔-cong t (y t xor y c) yy j)
        (cong (λ b → (y′ [ t ≔ b ]) j) (cong₂ _xor_ (yy t) (yy c)))

flip-flip : (c t : Fin n) → c ≢ t → ∀ y j → flip c t (flip c t y) j ≡ y j
flip-flip c t c≢t y j = cnot-involutive c t c≢t y j

private
  same-flip : (c t : Fin n) → c ≢ t → (x z : Assign n) →
              same z (flip c t x) ≡ same x (flip c t z)
  same-flip {n} c t c≢t x z = bool-iff (to x z) (to z x)
    where
    to : (a b : Assign n) → same b (flip c t a) ≡ true →
         same a (flip c t b) ≡ true
    to a b h = same-intro a (flip c t b) (λ j →
      trans (sym (flip-flip c t c≢t a j))
            (sym (flip-≗ c t (same-true b (flip c t a) h) j)))

cnot-† : (c t : Fin n) → c ≢ t → cnotOp c t † ≈ cnotOp c t
cnot-† c t c≢t = ≈-by (cnotOp c t †) (cnotOp c t) refl (λ x z →
  conj-δ z (flip c t x)
  ∙ gz-guard 0ℤ (same-flip c t c≢t x z))

-- A diagonal's adjoint is the opposite diagonal.

negFn : PhaseFn n → PhaseFn n
negFn (e , e-resp) = (λ z → - e z) , (λ zz → cong -_ (e-resp zz))

diag-† : (E : PhaseFn n) → diagOp E † ≈ diagOp (negFn E)
diag-† (e , e-resp) = ≈-by (diagOp (e , e-resp) †) (diagOp (negFn (e , e-resp)))
  refl (λ x z →
    conj-rot (e x) (δ z x)
    ∙ rot-map (- e x) (conj-δ z x)
    ∙ rot-if (same z x) (- e x) 0ℤ
    ∙ gz-cong (same-sym z x)
        (λ h → ≡ᴺ-≡ (cong (λ t → - t + 0ℤ)
                         (e-resp (same-true x z h))))
    ∙ ≐-sym (rot-if (same x z) (- e z) 0ℤ))

-- H H = 2: had-had, at the basis columns.  With normalisation 2 that
-- is the identity.

had-unitary : (w : Fin n) → Unitary (hadOp w)
had-unitary w = ·-congˡ (hadOp w) (had-† w) ⟨≈⟩ HH ,
                ·-congʳ (hadOp w) (had-† w) ⟨≈⟩ HH
  where
  HH : hadOp w · hadOp w ≈ I
  HH = ≈-intro (λ x z →
    col-·-col 1 1 (hadᴬ w) (had-cong w) (had-resp w) (lin-had w)
              (hadᴬ w) (had-cong w) (had-resp w) x z
    ∙ had-had w (δ x) (δ-resp x) z
    ∙ ≐-sym (√2·-twice (δ x z)))

cnot-unitary : (c t : Fin n) → c ≢ t → Unitary (cnotOp c t)
cnot-unitary c t c≢t =
  ·-congˡ (cnotOp c t) (cnot-† c t c≢t) ⟨≈⟩ CC ,
  ·-congʳ (cnotOp c t) (cnot-† c t c≢t) ⟨≈⟩ CC
  where
  CC : cnotOp c t · cnotOp c t ≈ I
  CC = ≈-by (cnotOp c t · cnotOp c t) I refl (λ x z →
    col-·-col 0 0 (cnotᴬ c t) (cnot-cong c t) (cnot-resp c t) (lin-cnot c t)
              (cnotᴬ c t) (cnot-cong c t) (cnot-resp c t) x z
    ∙ cnot-cnot c t c≢t (δ x) (δ-resp x) z)

diag-unitary : (E : PhaseFn n) → Unitary (diagOp E)
diag-unitary E =
  ·-congˡ (diagOp E) (diag-† E) ⟨≈⟩
    ≈-by (diagOp (negFn E) · diagOp E) I refl (λ x z →
      col-·-col 0 0 (phaseᴬ (λ u → - e u)) (diag-cong (λ u → - e u))
                (diag-resp (negFn E)) (lin-diag (λ u → - e u))
                (phaseᴬ e) (diag-cong e) (diag-resp E) x z
      ∙ phase-cancel e (δ x) z) ,
  ·-congʳ (diagOp E) (diag-† E) ⟨≈⟩
    ≈-by (diagOp E · diagOp (negFn E)) I refl (λ x z →
      col-·-col 0 0 (phaseᴬ e) (diag-cong e) (diag-resp E) (lin-diag e)
                (phaseᴬ (λ u → - e u)) (diag-cong (λ u → - e u))
                (diag-resp (negFn E)) x z
      ∙ phase-cancel⁻ e (δ x) z)
  where
  e = proj₁ E


------------------------------------------------------------------------
-- The phases of the generators

private
  φ-X : (j : Fin n) (v : Assign n) → φᴾ (X^ j) v ≡ 0ℤ
  φ-X j v = trans (cong (λ b → ¼ * 0ℤ + ½ * [ b ]ᶻ) (dot-0ˡ 0ᵛ v (λ _ → refl)))
                  (cong₂ _+_ (*-zeroʳ ¼) (*-zeroʳ ½))

  φ-Z : (j : Fin n) (v : Assign n) → φᴾ (Z^ j) v ≡ ½ * [ v j ]ᶻ
  φ-Z j v = trans (cong (λ b → ¼ * 0ℤ + ½ * [ b ]ᶻ) (e-dot j v))
                  (trans (cong (λ t → t + ½ * [ v j ]ᶻ) (*-zeroʳ ¼))
                         (+-identityˡ (½ * [ v j ]ᶻ)))

  bits-XZ : ∀ a b → (b xor false) xor (a ∧ (b xor false)) ≡ ((a xor true) ∧ b)
  bits-XZ true  true  = refl
  bits-XZ true  false = refl
  bits-XZ false true  = refl
  bits-XZ false false = refl

  bits-ZX : ∀ a b → a xor ((a xor false) ∧ b) ≡ (a ∧ (b xor true))
  bits-ZX true  true  = refl
  bits-ZX true  false = refl
  bits-ZX false true  = refl
  bits-ZX false false = refl

  xor-false-∧ : ∀ a b → ((a xor false) ∧ b) ≡ (a ∧ (b xor false))
  xor-false-∧ true  true  = refl
  xor-false-∧ true  false = refl
  xor-false-∧ false b     = refl


------------------------------------------------------------------------
-- H and the generators

-- The entry of H P from v to u, and of P H.

had-·-pauli : (w : Fin n) (p : PauliData n) (v u : Assign n) →
  mat (hadOp w · pauli p) v u ≐
  gz (same ((v ⊕ᵛ xs p) [ w ≔ u w ]) u)
     (φᴾ p v + ½ * [ (v ⊕ᵛ xs p) w ∧ u w ]ᶻ)
had-·-pauli w p v u =
  ·-pauli (hadOp w) p v u
  ∙ rot-map (φᴾ p v) (had-δ w (v ⊕ᵛ xs p) u)
  ∙ rot-if (same ((v ⊕ᵛ xs p) [ w ≔ u w ]) u) (φᴾ p v)
           (½ * [ (v ⊕ᵛ xs p) w ∧ u w ]ᶻ)

pauli-·-had : (w : Fin n) (q : PauliData n) (v u : Assign n) →
  mat (pauli q · hadOp w) v u ≐
  gz (same (v [ w ≔ (u ⊕ᵛ xs q) w ]) (u ⊕ᵛ xs q))
     (φᴾ q (u ⊕ᵛ xs q) + ½ * [ v w ∧ (u ⊕ᵛ xs q) w ]ᶻ)
pauli-·-had w q v u =
  pauli-·′ q (hadOp w) v u
  ∙ rot-map (φᴾ q (u ⊕ᵛ xs q)) (had-δ w v (u ⊕ᵛ xs q))
  ∙ rot-if (same (v [ w ≔ (u ⊕ᵛ xs q) w ]) (u ⊕ᵛ xs q)) (φᴾ q (u ⊕ᵛ xs q))
           (½ * [ v w ∧ (u ⊕ᵛ xs q) w ]ᶻ)

-- H P = Q H: equal guards, and congruent phases under them.

had-intertwine : (w : Fin n) (p q : PauliData n) →
  (∀ v u → same ((v ⊕ᵛ xs p) [ w ≔ u w ]) u ≡
           same (v [ w ≔ (u ⊕ᵛ xs q) w ]) (u ⊕ᵛ xs q)) →
  (∀ v u → same (v [ w ≔ (u ⊕ᵛ xs q) w ]) (u ⊕ᵛ xs q) ≡ true →
     φᴾ p v + ½ * [ (v ⊕ᵛ xs p) w ∧ u w ]ᶻ ≡ᴺ
     φᴾ q (u ⊕ᵛ xs q) + ½ * [ v w ∧ (u ⊕ᵛ xs q) w ]ᶻ) →
  hadOp w · pauli p ≈ pauli q · hadOp w
had-intertwine w p q G E = ≈-by (hadOp w · pauli p) (pauli q · hadOp w) refl
  (λ v u → had-·-pauli w p v u ∙ gz-cong (G v u) (E v u)
           ∙ ≐-sym (pauli-·-had w q v u))

-- H X_w H† = Z_w.

had-X : (w : Fin n) → hadOp w · pauli (X^ w) ≈ pauli (Z^ w) · hadOp w
had-X {n} w = had-intertwine w (X^ w) (Z^ w)
  (λ v u → same-≗ (λ j → pt v u j (j Fin.≟ w)) (λ j → sym (xor-false (u j))))
  (λ v u _ → expo v u)
  where
  pt : (v u : Assign n) (j : Fin n) → Dec (j ≡ w) →
       ((v ⊕ᵛ eᵛ w) [ w ≔ u w ]) j ≡ (v [ w ≔ (u ⊕ᵛ 0ᵛ) w ]) j
  pt v u j (yes refl) =
    trans (≔-here (v ⊕ᵛ eᵛ w) w (u w))
          (trans (sym (xor-false (u w)))
                 (sym (≔-here v w ((u ⊕ᵛ 0ᵛ) w))))
  pt v u j (no j≢w) =
    trans (≔-there (v ⊕ᵛ eᵛ w) (u w) j≢w)
      (trans (cong (v j xor_) (e-there j≢w))
        (trans (xor-false (v j)) (sym (≔-there v ((u ⊕ᵛ 0ᵛ) w) j≢w))))

  expo : (v u : Assign n) →
         φᴾ (X^ w) v + ½ * [ (v ⊕ᵛ eᵛ w) w ∧ u w ]ᶻ ≡ᴺ
         φᴾ (Z^ w) (u ⊕ᵛ 0ᵛ) + ½ * [ v w ∧ (u ⊕ᵛ 0ᵛ) w ]ᶻ
  expo v u = begin
    φᴾ (X^ w) v + ½ * [ (v ⊕ᵛ eᵛ w) w ∧ u w ]ᶻ
      ≡⟨ cong₂ _+_ (φ-X w v)
               (cong (λ b → ½ * [ (v w xor b) ∧ u w ]ᶻ) (e-here w)) ⟩
    0ℤ + ½ * [ (v w xor true) ∧ u w ]ᶻ
      ≡⟨ +-identityˡ _ ⟩
    ½ * [ (v w xor true) ∧ u w ]ᶻ
      ≡⟨ cong (λ b → ½ * [ b ]ᶻ) (sym (bits-XZ (v w) (u w))) ⟩
    ½ * [ (u w xor false) xor (v w ∧ (u w xor false)) ]ᶻ
      ≡ᴺ⟨ ≡ᴺ-sym (½-xor (u w xor false) (v w ∧ (u w xor false))) ⟩
    ½ * [ u w xor false ]ᶻ + ½ * [ v w ∧ (u w xor false) ]ᶻ
      ≡⟨ cong (λ t → t + ½ * [ v w ∧ (u w xor false) ]ᶻ)
              (sym (φ-Z w (u ⊕ᵛ 0ᵛ))) ⟩
    φᴾ (Z^ w) (u ⊕ᵛ 0ᵛ) + ½ * [ v w ∧ (u ⊕ᵛ 0ᵛ) w ]ᶻ ∎
    where open ≡ᴺ-Reasoning

-- H Z_w H† = X_w.

had-Z : (w : Fin n) → hadOp w · pauli (Z^ w) ≈ pauli (X^ w) · hadOp w
had-Z {n} w = had-intertwine w (Z^ w) (X^ w)
  (λ v u → bool-iff (to v u) (from v u))
  (λ v u _ → expo v u)
  where
  to : (v u : Assign n) → same ((v ⊕ᵛ 0ᵛ) [ w ≔ u w ]) u ≡ true →
       same (v [ w ≔ (u ⊕ᵛ eᵛ w) w ]) (u ⊕ᵛ eᵛ w) ≡ true
  to v u h = same-intro (v [ w ≔ (u ⊕ᵛ eᵛ w) w ]) (u ⊕ᵛ eᵛ w)
                        (λ j → at j (j Fin.≟ w))
    where
    pt = same-true ((v ⊕ᵛ 0ᵛ) [ w ≔ u w ]) u h
    at : ∀ j → Dec (j ≡ w) → (v [ w ≔ (u ⊕ᵛ eᵛ w) w ]) j ≡ (u ⊕ᵛ eᵛ w) j
    at j (yes refl) = ≔-here v w ((u ⊕ᵛ eᵛ w) w)
    at j (no j≢w)   =
      trans (≔-there v ((u ⊕ᵛ eᵛ w) w) j≢w)
        (trans (sym (xor-false (v j)))
          (trans (sym (≔-there (v ⊕ᵛ 0ᵛ) (u w) j≢w))
            (trans (pt j)
              (trans (sym (xor-false (u j)))
                     (cong (u j xor_) (sym (e-there j≢w)))))))
  from : (v u : Assign n) →
         same (v [ w ≔ (u ⊕ᵛ eᵛ w) w ]) (u ⊕ᵛ eᵛ w) ≡ true →
         same ((v ⊕ᵛ 0ᵛ) [ w ≔ u w ]) u ≡ true
  from v u h = same-intro ((v ⊕ᵛ 0ᵛ) [ w ≔ u w ]) u (λ j → at j (j Fin.≟ w))
    where
    pt = same-true (v [ w ≔ (u ⊕ᵛ eᵛ w) w ]) (u ⊕ᵛ eᵛ w) h
    at : ∀ j → Dec (j ≡ w) → ((v ⊕ᵛ 0ᵛ) [ w ≔ u w ]) j ≡ u j
    at j (yes refl) = ≔-here (v ⊕ᵛ 0ᵛ) w (u w)
    at j (no j≢w)   =
      trans (≔-there (v ⊕ᵛ 0ᵛ) (u w) j≢w)
        (trans (xor-false (v j))
          (trans (sym (≔-there v ((u ⊕ᵛ eᵛ w) w) j≢w))
            (trans (pt j)
              (trans (cong (u j xor_) (e-there j≢w)) (xor-false (u j))))))

  expo : (v u : Assign n) →
         φᴾ (Z^ w) v + ½ * [ (v ⊕ᵛ 0ᵛ) w ∧ u w ]ᶻ ≡ᴺ
         φᴾ (X^ w) (u ⊕ᵛ eᵛ w) + ½ * [ v w ∧ (u ⊕ᵛ eᵛ w) w ]ᶻ
  expo v u = begin
    φᴾ (Z^ w) v + ½ * [ (v ⊕ᵛ 0ᵛ) w ∧ u w ]ᶻ
      ≡⟨ cong (λ t → t + ½ * [ (v w xor false) ∧ u w ]ᶻ) (φ-Z w v) ⟩
    ½ * [ v w ]ᶻ + ½ * [ (v w xor false) ∧ u w ]ᶻ
      ≡ᴺ⟨ ½-xor (v w) ((v w xor false) ∧ u w) ⟩
    ½ * [ v w xor ((v w xor false) ∧ u w) ]ᶻ
      ≡⟨ cong (λ b → ½ * [ b ]ᶻ) (bits-ZX (v w) (u w)) ⟩
    ½ * [ v w ∧ (u w xor true) ]ᶻ
      ≡⟨ sym (+-identityˡ _) ⟩
    0ℤ + ½ * [ v w ∧ (u w xor true) ]ᶻ
      ≡⟨ sym (cong₂ _+_ (φ-X w (u ⊕ᵛ eᵛ w))
                        (cong (λ b → ½ * [ v w ∧ (u w xor b) ]ᶻ) (e-here w))) ⟩
    φᴾ (X^ w) (u ⊕ᵛ eᵛ w) + ½ * [ v w ∧ (u ⊕ᵛ eᵛ w) w ]ᶻ ∎
    where open ≡ᴺ-Reasoning

-- X_j and Z_j on another wire commute with H.

had-Xj : (w j : Fin n) → j ≢ w →
         hadOp w · pauli (X^ j) ≈ pauli (X^ j) · hadOp w
had-Xj {n} w j j≢w = had-intertwine w (X^ j) (X^ j)
  (λ v u → bool-iff (to v u) (from v u))
  (λ v u _ → ≡ᴺ-≡ (cong₂ _+_
     (trans (φ-X j v) (sym (φ-X j (u ⊕ᵛ eᵛ j))))
     (trans (cong (λ b → ½ * [ (v w xor b) ∧ u w ]ᶻ) (e-there w≢j))
       (trans (cong (λ b → ½ * [ b ]ᶻ) (xor-false-∧ (v w) (u w)))
              (cong (λ b → ½ * [ v w ∧ (u w xor b) ]ᶻ)
                    (sym (e-there w≢j)))))))
  where
  w≢j : w ≢ j
  w≢j e = j≢w (sym e)

  to : (v u : Assign n) → same ((v ⊕ᵛ eᵛ j) [ w ≔ u w ]) u ≡ true →
       same (v [ w ≔ (u ⊕ᵛ eᵛ j) w ]) (u ⊕ᵛ eᵛ j) ≡ true
  to v u h = same-intro (v [ w ≔ (u ⊕ᵛ eᵛ j) w ]) (u ⊕ᵛ eᵛ j)
                        (λ i → at i (i Fin.≟ w))
    where
    pt = same-true ((v ⊕ᵛ eᵛ j) [ w ≔ u w ]) u h
    at : ∀ i → Dec (i ≡ w) → (v [ w ≔ (u ⊕ᵛ eᵛ j) w ]) i ≡ (u ⊕ᵛ eᵛ j) i
    at i (yes refl) = ≔-here v w ((u ⊕ᵛ eᵛ j) w)
    at i (no i≢w)   =
      trans (≔-there v ((u ⊕ᵛ eᵛ j) w) i≢w)
        (sym (xor-move (v i) (eᵛ j i) (u i)
               (trans (sym (≔-there (v ⊕ᵛ eᵛ j) (u w) i≢w)) (pt i))))
  from : (v u : Assign n) →
         same (v [ w ≔ (u ⊕ᵛ eᵛ j) w ]) (u ⊕ᵛ eᵛ j) ≡ true →
         same ((v ⊕ᵛ eᵛ j) [ w ≔ u w ]) u ≡ true
  from v u h = same-intro ((v ⊕ᵛ eᵛ j) [ w ≔ u w ]) u (λ i → at i (i Fin.≟ w))
    where
    pt = same-true (v [ w ≔ (u ⊕ᵛ eᵛ j) w ]) (u ⊕ᵛ eᵛ j) h
    at : ∀ i → Dec (i ≡ w) → ((v ⊕ᵛ eᵛ j) [ w ≔ u w ]) i ≡ u i
    at i (yes refl) = ≔-here (v ⊕ᵛ eᵛ j) w (u w)
    at i (no i≢w)   =
      trans (≔-there (v ⊕ᵛ eᵛ j) (u w) i≢w)
        (xor-move (u i) (eᵛ j i) (v i)
          (sym (trans (sym (≔-there v ((u ⊕ᵛ eᵛ j) w) i≢w)) (pt i))))

had-Zj : (w j : Fin n) → j ≢ w →
         hadOp w · pauli (Z^ j) ≈ pauli (Z^ j) · hadOp w
had-Zj {n} w j j≢w = had-intertwine w (Z^ j) (Z^ j)
  (λ v u → same-≗ (λ i → pt v u i (i Fin.≟ w)) (λ i → sym (xor-false (u i))))
  (λ v u h → ≡ᴺ-≡ (cong₂ _+_
     (trans (φ-Z j v)
       (trans (cong (λ b → ½ * [ b ]ᶻ)
                (trans (sym (≔-there v ((u ⊕ᵛ 0ᵛ) w) j≢w))
                       (same-true (v [ w ≔ (u ⊕ᵛ 0ᵛ) w ]) (u ⊕ᵛ 0ᵛ) h j)))
              (sym (φ-Z j (u ⊕ᵛ 0ᵛ)))))
     (cong (λ b → ½ * [ b ]ᶻ) (xor-false-∧ (v w) (u w)))))
  where
  pt : (v u : Assign n) (i : Fin n) → Dec (i ≡ w) →
       ((v ⊕ᵛ 0ᵛ) [ w ≔ u w ]) i ≡ (v [ w ≔ (u ⊕ᵛ 0ᵛ) w ]) i
  pt v u i (yes refl) =
    trans (≔-here (v ⊕ᵛ 0ᵛ) w (u w))
          (trans (sym (xor-false (u w))) (sym (≔-here v w ((u ⊕ᵛ 0ᵛ) w))))
  pt v u i (no i≢w) =
    trans (≔-there (v ⊕ᵛ 0ᵛ) (u w) i≢w)
          (trans (xor-false (v i)) (sym (≔-there v ((u ⊕ᵛ 0ᵛ) w) i≢w)))

-- So H is a Clifford.

had-𝒞₂ : (w : Fin n) → 𝒞 2 (hadOp w)
had-𝒞₂ {n} w = 𝒞₂-by-intertwining (hadOp w) (had-unitary w)
  (λ j → pickX j (j Fin.≟ w)) (λ j → pickZ j (j Fin.≟ w))
  where
  pickX : ∀ j → Dec (j ≡ w) →
          Σ[ q ∈ PauliData n ] hadOp w · pauli (X^ j) ≈ pauli q · hadOp w
  pickX j (yes refl) = Z^ w , had-X w
  pickX j (no j≢w)   = X^ j , had-Xj w j j≢w

  pickZ : ∀ j → Dec (j ≡ w) →
          Σ[ q ∈ PauliData n ] hadOp w · pauli (Z^ j) ≈ pauli q · hadOp w
  pickZ j (yes refl) = X^ w , had-Z w
  pickZ j (no j≢w)   = Z^ j , had-Zj w j j≢w


------------------------------------------------------------------------
-- CNOT and the Paulis

-- One bit overwritten: the parity changes by the change of that bit.

private
  sc : Bool → Fin n → Assign n
  sc c i j = c ∧ eᵛ i j

  ∧-true : ∀ a → (a ∧ true) ≡ a
  ∧-true true  = refl
  ∧-true false = refl

  ∧-false : ∀ a → (a ∧ false) ≡ false
  ∧-false true  = refl
  ∧-false false = refl

  dot-sc : (z : Assign n) (c : Bool) (i : Fin n) → dot z (sc c i) ≡ (z i ∧ c)
  dot-sc z true  i = trans (dot-e z i) (sym (∧-true (z i)))
  dot-sc z false i = trans (dot-0ʳ z (sc false i) (λ _ → refl))
                           (sym (∧-false (z i)))

  back : ∀ a b → (a xor ((a xor b) ∧ true)) ≡ b
  back true  true  = refl
  back true  false = refl
  back false true  = refl
  back false false = refl

dot-≔ : (z y : Assign n) (i : Fin n) (b : Bool) →
        dot z (y [ i ≔ b ]) ≡ (dot z y xor (z i ∧ (y i xor b)))
dot-≔ {n} z y i b =
  trans (dot-cong {z = z} {z′ = z} (λ _ → refl) (λ j → pt j (j Fin.≟ i)))
        (trans (dot-⊕ʳ z y (sc (y i xor b) i))
               (cong (dot z y xor_) (dot-sc z (y i xor b) i)))
  where
  pt : ∀ j → Dec (j ≡ i) → (y [ i ≔ b ]) j ≡ (y ⊕ᵛ sc (y i xor b) i) j
  pt j (yes refl) = trans (≔-here y i b)
    (trans (sym (back (y i) b))
           (cong (λ e → y i xor ((y i xor b) ∧ e)) (sym (e-here i))))
  pt j (no j≢i) = trans (≔-there y b j≢i)
    (trans (sym (xor-false (y j)))
      (cong (y j xor_) (trans (sym (∧-false (y i xor b)))
                              (cong ((y i xor b) ∧_) (sym (e-there j≢i))))))

-- CNOT's permutation on the X part, and its transpose on the Z part.

flipᵀ : Fin n → Fin n → Assign n → Assign n
flipᵀ c t z = z [ c ≔ z c xor z t ]

private
  cancel4 : ∀ D a b c → ((D xor (a ∧ b)) xor (b ∧ (c xor (c xor a)))) ≡ D
  cancel4 true  true  true  true  = refl
  cancel4 true  true  true  false = refl
  cancel4 true  true  false c     = refl
  cancel4 true  false true  true  = refl
  cancel4 true  false true  false = refl
  cancel4 true  false false c     = refl
  cancel4 false true  true  true  = refl
  cancel4 false true  true  false = refl
  cancel4 false true  false c     = refl
  cancel4 false false true  true  = refl
  cancel4 false false true  false = refl
  cancel4 false false false c     = refl

  self-xor : ∀ a b → (a xor (a xor b)) ≡ b
  self-xor true  true  = refl
  self-xor true  false = refl
  self-xor false b     = refl

-- (πᵀ z)·(π v) = z·v.

dot-flip : (c t : Fin n) → c ≢ t → (z v : Assign n) →
           dot (flipᵀ c t z) (flip c t v) ≡ dot z v
dot-flip c t c≢t z v =
  trans (dot-≔ (flipᵀ c t z) v t (v t xor v c))
    (trans (cong₂ (λ d e → d xor (e ∧ (v t xor (v t xor v c))))
                  (trans (dot-comm (flipᵀ c t z) v)
                    (trans (dot-≔ v z c (z c xor z t))
                      (cong₂ (λ d e → d xor (v c ∧ e))
                             (dot-comm v z) (self-xor (z c) (z t)))))
                  (≔-there z (z c xor z t) t≢c))
           (cancel4 (dot z v) (v c) (z t) (v t)))
  where
  t≢c : t ≢ c
  t≢c e = c≢t (sym e)

private
  flip-⊕ : (c t : Fin n) (u y : Assign n) →
           ∀ j → flip c t (u ⊕ᵛ y) j ≡ (flip c t u ⊕ᵛ flip c t y) j
  flip-⊕ c t u y j with j Fin.≟ t
  ... | yes _ = shuffle (u t) (y t) (u c) (y c)
    where
    shuffle : ∀ a b c d → ((a xor b) xor (c xor d)) ≡ ((a xor c) xor (b xor d))
    shuffle true  true  true  true  = refl
    shuffle true  true  true  false = refl
    shuffle true  true  false true  = refl
    shuffle true  true  false false = refl
    shuffle true  false true  true  = refl
    shuffle true  false true  false = refl
    shuffle true  false false true  = refl
    shuffle true  false false false = refl
    shuffle false true  true  true  = refl
    shuffle false true  true  false = refl
    shuffle false true  false true  = refl
    shuffle false true  false false = refl
    shuffle false false c     d     = refl
  ... | no  _ = refl

-- CNOT P = P′ CNOT with P′ = P(a, πx, πᵀz).

cnot-act : Fin n → Fin n → PauliData n → PauliData n
cnot-act c t p = pd (ph p) (flip c t (xs p)) (flipᵀ c t (zs p))

cnot-pauli : (c t : Fin n) → c ≢ t → (p : PauliData n) →
             cnotOp c t · pauli p ≈ pauli (cnot-act c t p) · cnotOp c t
cnot-pauli {n} c t c≢t p = ≈-by (cnotOp c t · pauli p)
  (pauli (cnot-act c t p) · cnotOp c t) refl (λ v u →
    ·-pauli (cnotOp c t) p v u
    ∙ rot-if (same (v ⊕ᵛ xs p) (flip c t u)) (φᴾ p v) 0ℤ
    ∙ gz-cong (guard v u) (expo v u)
    ∙ ≐-sym (rot-if (same v (flip c t (u ⊕ᵛ x′))) (φᴾ q (u ⊕ᵛ x′)) 0ℤ)
    ∙ ≐-sym (pauli-·′ q (cnotOp c t) v u))
  where
  q  = cnot-act c t p
  x′ = flip c t (xs p)

  guard : (v u : Assign n) →
          same (v ⊕ᵛ xs p) (flip c t u) ≡ same v (flip c t (u ⊕ᵛ x′))
  guard v u = sym (trans
    (same-≗ {x = v} {x′ = v} (λ _ → refl)
            (λ j → trans (flip-⊕ c t u x′ j)
                         (cong (flip c t u j xor_) (flip-flip c t c≢t (xs p) j))))
    (trans (same-sym v (flip c t u ⊕ᵛ xs p))
           (same-⊕-swap (flip c t u) (xs p) v)))

  expo : (v u : Assign n) → same v (flip c t (u ⊕ᵛ x′)) ≡ true →
         φᴾ p v + 0ℤ ≡ᴺ φᴾ q (u ⊕ᵛ x′) + 0ℤ
  expo v u h = ≡ᴺ-≡ (cong (λ b → ¼ * ph p + ½ * [ b ]ᶻ + 0ℤ)
    (sym (trans (dot-cong {z = flipᵀ c t (zs p)} {z′ = flipᵀ c t (zs p)}
                          (λ _ → refl) back′)
                (dot-flip c t c≢t (zs p) v))))
    where
    -- u ⊕ πx is π v.
    back′ : ∀ j → (u ⊕ᵛ x′) j ≡ flip c t v j
    back′ j = trans (sym (flip-flip c t c≢t (u ⊕ᵛ x′) j))
                    (flip-≗ c t (λ i → sym (same-true v (flip c t (u ⊕ᵛ x′)) h i)) j)

cnot-𝒞₂ : (c t : Fin n) → c ≢ t → 𝒞 2 (cnotOp c t)
cnot-𝒞₂ c t c≢t = cnot-unitary c t c≢t , λ p →
  cnot-act c t p ,
  intertwine⇒conj (cnotOp c t) (pauli p) (pauli (cnot-act c t p))
                  (cnot-unitary c t c≢t) (cnot-pauli c t c≢t p)


------------------------------------------------------------------------
-- Diagonals and the Paulis

-- A diagonal applied first multiplies the entries by its phase at the
-- input.

·-diag : (V : Op n) (E : PhaseFn n) (v u : Assign n) →
         mat (V · diagOp E) v u ≐ rot (proj₁ E v + 0ℤ) (mat V v u)
·-diag V (e , e-resp) v u =
  Σᴮ-cong (λ y →
    ⊛-cong {a = rot (e y) (δ v y)} {a′ = gz (same v y) (e y + 0ℤ)}
           {b = mat V y u} {b′ = mat V y u}
           (rot-if (same v y) (e y) 0ℤ) ≐-refl
    ∙ if-⊛ (same v y) (zpow (e y + 0ℤ)) (mat V y u))
  ∙ Σᴮ-δ v (λ y → zpow (e y + 0ℤ) ⊛ mat V y u)
         (λ g h g≗h → ⊛-cong (λ i → cong (λ t → zpow (t + 0ℤ) i) (e-resp g≗h))
                             (respˣ V u g h g≗h))
  ∙ zpow-⊛ (e v + 0ℤ) (mat V v u)

-- The diagonal of the phase differences along P's flip.

ΔFn : PhaseFn n → PauliData n → PhaseFn n
ΔFn (e , e-resp) p =
  (λ u → e u - e (u ⊕ᵛ xs p)) ,
  (λ uu → cong₂ _-_ (e-resp uu) (e-resp (λ j → cong (_xor xs p j) (uu j))))

diag-pauli : (E : PhaseFn n) (p : PauliData n) →
             diagOp E · pauli p ≈ diagOp (ΔFn E p) · pauli p · diagOp E
diag-pauli {n} E p = ≈-by (D · pauli p) (diagOp F · pauli p · D)
  refl (λ v u →
    ·-pauli D p v u
    ∙ rot-map (φᴾ p v) (rot-if (G v u) (e u) 0ℤ)
    ∙ rot-if (G v u) (φᴾ p v) (e u + 0ℤ)
    ∙ gz-≡ᴺ (G v u) (λ h → ≡ᴺ-≡ (expo v u h))
    ∙ ≐-sym (
        ·-diag (diagOp F · pauli p) E v u
        ∙ rot-map (e v + 0ℤ)
            (·-pauli (diagOp F) p v u
             ∙ rot-map (φᴾ p v) (rot-if (G v u) (proj₁ F u) 0ℤ)
             ∙ rot-if (G v u) (φᴾ p v) (proj₁ F u + 0ℤ))
        ∙ rot-if (G v u) (e v + 0ℤ) (φᴾ p v + (proj₁ F u + 0ℤ))))
  where
  e = proj₁ E
  D = diagOp E
  F = ΔFn E p

  G : Assign n → Assign n → Bool
  G v u = same (v ⊕ᵛ xs p) u

  shape : ∀ f eu ev → f + (eu + 0ℤ) ≡ (ev + 0ℤ) + (f + ((eu - ev) + 0ℤ))
  shape = solve 3 (λ f eu ev → f :+ (eu :+ con 0ℤ) :=
                               (ev :+ con 0ℤ) :+ (f :+ ((eu :- ev) :+ con 0ℤ)))
                  refl

  expo : (v u : Assign n) → G v u ≡ true →
         φᴾ p v + (e u + 0ℤ) ≡
         (e v + 0ℤ) + (φᴾ p v + ((e u - e (u ⊕ᵛ xs p)) + 0ℤ))
  expo v u h = trans (shape (φᴾ p v) (e u) (e v))
    (cong (λ s → (e v + 0ℤ) + (φᴾ p v + ((e u - s) + 0ℤ)))
          (proj₂ E (λ j → sym (xor-move (v j) (xs p j) (u j)
                                 (same-true (v ⊕ᵛ xs p) u h j)))))

-- So D P D† = D_Δ P.

diag-conj : (E : PhaseFn n) (p : PauliData n) →
            diagOp E · pauli p · diagOp E † ≈ diagOp (ΔFn E p) · pauli p
diag-conj E p = intertwine⇒conj (diagOp E) (pauli p)
  (diagOp (ΔFn E p) · pauli p) (diag-unitary E) (diag-pauli E p)

-- Diagonals of constant, and of Pauli, phases.

diag-I : (F : PhaseFn n) → (∀ u → proj₁ F u ≡ᴺ 0ℤ) → diagOp F ≈ I
diag-I (f , f-resp) h = ≈-by (diagOp (f , f-resp)) I refl (λ v u →
  rot-≡ᴺ (h u) (δ v u) ∙ rot-0 (δ v u))

diag-◃ : (F G : PhaseFn n) (t : ℤ) → (∀ u → proj₁ F u ≡ᴺ t + proj₁ G u) →
         diagOp F ≈ t ◃ diagOp G
diag-◃ (f , f-resp) (g , g-resp) t h =
  ≈-by (diagOp (f , f-resp)) (t ◃ diagOp (g , g-resp)) refl (λ v u →
    rot-≡ᴺ (h u) (δ v u) ∙ ≐-sym (rot-comp t (g u) (δ v u)))

diag-is-pauli : (F : PhaseFn n) (a : ℤ) (z : Assign n) →
                (∀ u → proj₁ F u ≡ᴺ ¼ * a + ½ * [ dot z u ]ᶻ) →
                diagOp F ≈ pauli (pd a 0ᵛ z)
diag-is-pauli (f , f-resp) a z h = ≈-by (diagOp (f , f-resp)) (pauli (pd a 0ᵛ z))
  refl (λ v u →
    rot-if (same v u) (f u) 0ℤ
    ∙ gz-cong (same-≗ (λ j → sym (xor-false (v j))) (λ _ → refl))
        (λ g → ≡ᴺ-trans (≡ᴺ-≡ (+-identityʳ (f u)))
                 (≡ᴺ-trans (h u)
                   (≡ᴺ-≡ (cong (λ b → ¼ * a + ½ * [ b ]ᶻ)
                     (dot-cong {z = z} {z′ = z} (λ _ → refl)
                       (λ j → sym (trans (sym (xor-false (v j)))
                                         (same-true (v ⊕ᵛ 0ᵛ) u g j)))))))))

-- A diagonal whose phase differences are Pauli phases is a Clifford.

diag-conj-pauli : (E : PhaseFn n) (p : PauliData n) (a : ℤ) (z : Assign n) →
  (∀ u → proj₁ (ΔFn E p) u ≡ᴺ ¼ * a + ½ * [ dot z u ]ᶻ) →
  diagOp E · pauli p · diagOp E † ≈ pauli (pd a 0ᵛ z ∙ᴾ p)
diag-conj-pauli E p a z h =
  diag-conj E p
  ⟨≈⟩ ·-congˡ (pauli p) (diag-is-pauli (ΔFn E p) a z h)
  ⟨≈⟩ pauli-· (pd a 0ᵛ z) p

diag-𝒞₂ : (E : PhaseFn n) →
  (∀ p → Σ[ a ∈ ℤ ] Σ[ z ∈ Assign n ]
           (∀ u → proj₁ (ΔFn E p) u ≡ᴺ ¼ * a + ½ * [ dot z u ]ᶻ)) →
  𝒞 2 (diagOp E)
diag-𝒞₂ E H = diag-unitary E , λ p →
  let (a , z , h) = H p in
  pd a 0ᵛ z ∙ᴾ p , diag-conj-pauli E p a z h


------------------------------------------------------------------------
-- A phase on one wire

-- D(s) P D(s)† is P when P leaves the wire alone, and ζ^(-s) D(2s) P
-- when it flips it.

Rs-conj-0 : (s : ℤ) (w : Fin n) (p : PauliData n) → xs p w ≡ false →
            Rs s w · pauli p · Rs s w † ≈ pauli p
Rs-conj-0 s w p xw =
  diag-conj (wireFn s w) p
  ⟨≈⟩ ·-congˡ (pauli p) (diag-I (ΔFn (wireFn s w) p) (λ u → ≡ᴺ-≡ (zero u)))
  ⟨≈⟩ ·-identityˡ (pauli p)
  where
  zero : ∀ u → s * [ u w ]ᶻ - s * [ u w xor xs p w ]ᶻ ≡ 0ℤ
  zero u = trans (cong (λ b → s * [ u w ]ᶻ - s * [ b ]ᶻ)
                       (trans (cong (u w xor_) xw) (xor-false (u w))))
                 (+-inverseʳ (s * [ u w ]ᶻ))

Rs-conj-1 : (s : ℤ) (w : Fin n) (p : PauliData n) → xs p w ≡ true →
            Rs s w · pauli p · Rs s w † ≈ (- s) ◃ (Rs ((+ 2) * s) w · pauli p)
Rs-conj-1 s w p xw =
  diag-conj (wireFn s w) p
  ⟨≈⟩ ·-congˡ (pauli p) (diag-◃ (ΔFn (wireFn s w) p) (wireFn ((+ 2) * s) w)
                                (- s) (λ u → ≡ᴺ-≡ (twice u)))
  ⟨≈⟩ ◃-·ˡ (- s) (Rs ((+ 2) * s) w) (pauli p)
  where
  tw : ∀ b → s * [ b ]ᶻ - s * [ b xor true ]ᶻ ≡ - s + (+ 2) * s * [ b ]ᶻ
  tw false = solve 1 (λ s → s :* con 0ℤ :- s :* con 1ℤ :=
                            :- s :+ con (+ 2) :* s :* con 0ℤ) refl s
  tw true  = solve 1 (λ s → s :* con 1ℤ :- s :* con 0ℤ :=
                            :- s :+ con (+ 2) :* s :* con 1ℤ) refl s

  twice : ∀ u → s * [ u w ]ᶻ - s * [ u w xor xs p w ]ᶻ ≡
                - s + (+ 2) * s * [ u w ]ᶻ
  twice u = trans (cong (λ b → s * [ u w ]ᶻ - s * [ u w xor b ]ᶻ) xw)
                  (tw (u w))

-- D(±½) is Z on the wire.

Rs-½ : (w : Fin n) → Rs ½ w ≈ pauli (Z^ w)
Rs-½ w = diag-is-pauli (wireFn ½ w) 0ℤ (eᵛ w) (λ u →
  ≡ᴺ-≡ (sym (trans (cong₂ _+_ (*-zeroʳ ¼) (cong (λ b → ½ * [ b ]ᶻ) (e-dot w u)))
                   (+-identityˡ (½ * [ u w ]ᶻ)))))

Rs-−½ : (w : Fin n) → Rs (- ½) w ≈ pauli (Z^ w)
Rs-−½ w = diag-is-pauli (wireFn (- ½) w) 0ℤ (eᵛ w) (λ u →
  ≡ᴺ-trans (≡ᴺ-≡ (sym (neg-distribˡ-* ½ [ u w ]ᶻ)))
    (≡ᴺ-trans (neg-½ (u w))
      (≡ᴺ-≡ (sym (trans (cong₂ _+_ (*-zeroʳ ¼) (cong (λ b → ½ * [ b ]ᶻ) (e-dot w u)))
                        (+-identityˡ (½ * [ u w ]ᶻ)))))))


------------------------------------------------------------------------
-- CZ

czFn : Fin n → Fin n → PhaseFn n
czFn a b = (λ z → ½ * [ z a ∧ z b ]ᶻ) ,
           (λ zz → cong₂ (λ x y → ½ * [ x ∧ y ]ᶻ) (zz a) (zz b))

private
  cz-bits : ∀ ua ub xa xb →
            ((ua ∧ ub) xor ((ua xor xa) ∧ (ub xor xb))) ≡
            ((xa ∧ xb) xor ((xb ∧ ua) xor (xa ∧ ub)))
  cz-bits true  true  true  true  = refl
  cz-bits true  true  true  false = refl
  cz-bits true  true  false true  = refl
  cz-bits true  true  false false = refl
  cz-bits true  false true  true  = refl
  cz-bits true  false true  false = refl
  cz-bits true  false false true  = refl
  cz-bits true  false false false = refl
  cz-bits false true  true  true  = refl
  cz-bits false true  true  false = refl
  cz-bits false true  false true  = refl
  cz-bits false true  false false = refl
  cz-bits false false true  true  = refl
  cz-bits false false true  false = refl
  cz-bits false false false true  = refl
  cz-bits false false false false = refl

  dot-scˡ : (c : Bool) (i : Fin n) (u : Assign n) → dot (sc c i) u ≡ (c ∧ u i)
  dot-scˡ c i u = trans (dot-comm (sc c i) u)
                        (trans (dot-sc u c i) (∧-comm (u i) c))
    where
    ∧-comm : ∀ a b → (a ∧ b) ≡ (b ∧ a)
    ∧-comm true  true  = refl
    ∧-comm true  false = refl
    ∧-comm false true  = refl
    ∧-comm false false = refl

cz-𝒞₂ : (a b : Fin n) → 𝒞 2 (diagOp (czFn a b))
cz-𝒞₂ {n} a b = diag-𝒞₂ (czFn a b) λ p →
  (+ 2) * [ xs p a ∧ xs p b ]ᶻ ,
  sc (xs p b) a ⊕ᵛ sc (xs p a) b ,
  λ u → phase p u
  where
  phase : (p : PauliData n) (u : Assign n) →
          ½ * [ u a ∧ u b ]ᶻ - ½ * [ (u ⊕ᵛ xs p) a ∧ (u ⊕ᵛ xs p) b ]ᶻ ≡ᴺ
          ¼ * ((+ 2) * [ xs p a ∧ xs p b ]ᶻ) +
          ½ * [ dot (sc (xs p b) a ⊕ᵛ sc (xs p a) b) u ]ᶻ
  phase p u = begin
    ½ * [ A ]ᶻ - ½ * [ B ]ᶻ
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ½ * [ A ]ᶻ}) (neg-½ B) ⟩
    ½ * [ A ]ᶻ + ½ * [ B ]ᶻ
      ≡ᴺ⟨ ½-xor A B ⟩
    ½ * [ A xor B ]ᶻ
      ≡⟨ cong (λ c → ½ * [ c ]ᶻ) (cz-bits (u a) (u b) (xs p a) (xs p b)) ⟩
    ½ * [ (xs p a ∧ xs p b) xor C ]ᶻ
      ≡ᴺ⟨ ≡ᴺ-sym (½-xor (xs p a ∧ xs p b) C) ⟩
    ½ * [ xs p a ∧ xs p b ]ᶻ + ½ * [ C ]ᶻ
      ≡⟨ cong₂ _+_ (sym (¼·2 [ xs p a ∧ xs p b ]ᶻ))
           (cong (λ c → ½ * [ c ]ᶻ)
             (sym (trans (dot-⊕ˡ (sc (xs p b) a) (sc (xs p a) b) u)
                         (cong₂ _xor_ (dot-scˡ (xs p b) a u)
                                      (dot-scˡ (xs p a) b u))))) ⟩
    ¼ * ((+ 2) * [ xs p a ∧ xs p b ]ᶻ) +
    ½ * [ dot (sc (xs p b) a ⊕ᵛ sc (xs p a) b) u ]ᶻ ∎
    where
    open ≡ᴺ-Reasoning
    A = u a ∧ u b
    B = (u a xor xs p a) ∧ (u b xor xs p b)
    C = (xs p b ∧ u a) xor (xs p a ∧ u b)
