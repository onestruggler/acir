------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix of a circuit over {H, CNOT, R_k, R_k†}, and the norms of
-- its columns (Amy, QPL 2018, proposition 2.10)
--
-- Proposition 2.10 says that the path-sum of a circuit computes the
-- circuit's matrix.  As in PathSum.CircuitSemantics, the matrix is
-- built a column at a time: a column is a vector of amplitudes indexed
-- by the output assignments, and each gate acts on it by its own
-- unnormalised matrix.  R_k multiplies the entry at z by
-- ζ^(2^(M-k) z_w) -- e^(2πi z_w / 2^k) when k ≤ M (Rk-order and
-- Rk-primitive in PathSum.CRK.Circuit; for k > M the gate is read as
-- R_M, on both sides alike) -- and R_k† by the inverse power.  CNOT
-- with control c and target t permutes the entries, the new entry at z
-- being the old one at z[t ≔ z_t ⊕ z_c].  A Hadamard on w sends the
-- entry at z to the sum of the old entries at z[w≔0] and z[w≔1], the
-- second signed by (-1)^(z_w).  PathSum.CRK.Amp shows that each gate
-- changes the amplitudes of an interpretation state by exactly that
-- matrix, so the amplitudes of ⟦ C ⟧ at the input x are the gates of C
-- applied in turn to the basis column δ x (prop-2-10).  The paper's
-- U_C is that product of gate matrices; here it and the operator of
-- ⟦ C ⟧ are both read unnormalised, by the same factor √2^(norm C).
--
-- Every column of ⟦ C ⟧ is a unit vector once normalised, the norm
-- being PathSum.Norm's trace form.  A rotation preserves the squared
-- norm of each entry.  CNOT permutes the entries of a column: it pairs
-- the assignments z[t≔0] and z[t≔1], and swaps the two when z_c = 1,
-- so it permutes the terms of the sum.  A Hadamard turns the entries a
-- and b at z[w≔0] and z[w≔1] into a + b and a - b, and the
-- parallelogram law adds those norms up to twice those of a and b.  The
-- basis column has norm 1, so a column of ⟦ C ⟧ has norm 2^k, k the
-- number of Hadamards, which is what the normalisation 1/√2^k divides
-- out -- and what lemma 4.1 asks of a path-sum (PathSum.Isometry's
-- WellFormed).  That ⟦ C ⟧ is unitary is true but not stated.
--
-- The column action and its congruences are public, for developments
-- that compare circuits through their matrices.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _∸_; _^_)

module PathSum.CRK.Semantics (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; *-zeroʳ;
   *-assoc; *-comm; pos-*)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Product.Base using (proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-cong; same; same-refl; same-≗)
open import PathSum.AssignSum using
  (Σᶻ; RespectsZ; Σᶻ-cong; Σᶻ-*; Σᶻ-0; Σᶻ-point; Σᶻ-at)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.CRK.Amp M₀ using
  (ampᴸ; ampᴸ-init; ampᴸ-R; ampᴸ-R†; ampᴸ-CNOT; ampᴸ-H)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm; State; init; stepR; stepR†;
   stepCNOT; stepH; run; ⟦_⟧)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _-ᴬ_; _≐_; zpow; rot; rot-map; rot-exp; rot-0;
   rot-anti; Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using (Assign; amp)
open import PathSum.Norm M₀ using
  (‖_‖²; ‖‖²-cong; ‖‖²-rot; parallelogram; ‖zpow0‖²; ‖0ᴬ‖²)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The matrices of the gates

-- Each gate's matrix, unnormalised, acting on a column: the entry at z
-- of the new column.  A Hadamard's normalisation 1/√2 is left to the
-- path-sum's.

gateᴬ : Gate n → Column n → Column n
gateᴬ (H w)        ψ z =
  ψ (z [ w ≔ false ]) +ᴬ rot (½ * [ z w ]ᶻ) (ψ (z [ w ≔ true ]))
gateᴬ (CNOT c t _) ψ z = ψ (z [ t ≔ z t xor z c ])
gateᴬ (R k w)      ψ z = rot (pow (M ∸ k) * [ z w ]ᶻ) (ψ z)
gateᴬ (R† k w)     ψ z = rot (- (pow (M ∸ k) * [ z w ]ᶻ)) (ψ z)

-- The gates of a circuit act first to last.

applyᴬ : Circuit n → Column n → Column n
applyᴬ []      ψ = ψ
applyᴬ (g ∷ C) ψ = applyᴬ C (gateᴬ g ψ)

-- U_(C₁;C₂) = U_C₂ U_C₁.

applyᴬ-++ : (C D : Circuit n) (ψ : Column n) →
            applyᴬ (C ++ D) ψ ≡ applyᴬ D (applyᴬ C ψ)
applyᴬ-++ []      D ψ = refl
applyᴬ-++ (g ∷ C) D ψ = applyᴬ-++ C D (gateᴬ g ψ)


------------------------------------------------------------------------
-- Amplitude algebra

-- Every lemma here is stated over variables, and used by instantiating
-- it.  A rotation is compared only with a rotation by the same
-- exponent, and an exponent is changed only by rot-exp: Agda would
-- otherwise compare the two exponents by unfolding the proofs that
-- Cyclotomic's classify carries.

private
  rot-cong : (a a′ : Amp) (e e′ : ℤ) → e ≡ e′ → a ≐ a′ →
             rot e a ≐ rot e′ a′
  rot-cong a a′ e e′ ee aa i =
    trans (rot-map e aa i) (rot-exp {e} {e′} a′ ee i)

  -- The two terms of a Hadamard.

  sum-cong : (a a′ b b′ : Amp) (e e′ : ℤ) → a ≐ a′ → e ≡ e′ → b ≐ b′ →
             (a +ᴬ rot e b) ≐ (a′ +ᴬ rot e′ b′)
  sum-cong a a′ b b′ e e′ aa ee bb i =
    cong₂ _+_ (aa i) (rot-cong b b′ e e′ ee bb i)

  -- The sign of a Hadamard is 1 when its wire is 0, and -1 when it is
  -- 1: ½ is the exponent H of ζ^H = -1 (Cyclotomic's H, imported as
  -- rank since the gate is H too), and rotating by H negates.

  sign-0 : (a a′ b b′ : Amp) (e : ℤ) → a ≐ a′ → e ≡ 0ℤ → b ≐ b′ →
           (a +ᴬ rot e b) ≐ (a′ +ᴬ b′)
  sign-0 a a′ b b′ e aa ee bb i = cong₂ _+_ (aa i)
    (trans (rot-exp {e} {0ℤ} b ee i) (trans (rot-0 b i) (bb i)))

  sign-1 : (a a′ b b′ : Amp) (e : ℤ) → a ≐ a′ → e ≡ 0ℤ + (+ rank) →
           b ≐ b′ → (a +ᴬ rot e b) ≐ (a′ -ᴬ b′)
  sign-1 a a′ b b′ e aa ee bb i = cong₂ _+_ (aa i)
    (trans (rot-exp {e} {0ℤ + (+ rank)} b ee i)
      (trans (rot-anti 0ℤ b i) (cong -_ (trans (rot-0 b i) (bb i)))))


------------------------------------------------------------------------
-- Columns up to pointwise equality

-- Assignments are functions, so a column is only ever met at an
-- assignment pointwise equal to the one it was built at; the columns
-- that matter see assignments only through their values.  And the
-- gates act on columns entry by entry, so they respect equality of
-- entries.

private
  δ-resp : (x : Assign n) → Respects (δ x)
  δ-resp x z z′ zz i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
    (same-≗ {x = x} {x′ = x} {z = z} {z′ = z′} (λ _ → refl) zz)

gateᴬ-resp : (g : Gate n) {ψ : Column n} → Respects ψ →
             Respects (gateᴬ g ψ)
gateᴬ-resp (H w) {ψ} resp z z′ zz =
  sum-cong (ψ (z [ w ≔ false ])) (ψ (z′ [ w ≔ false ]))
           (ψ (z [ w ≔ true ])) (ψ (z′ [ w ≔ true ]))
           (½ * [ z w ]ᶻ) (½ * [ z′ w ]ᶻ)
           (resp (z [ w ≔ false ]) (z′ [ w ≔ false ]) (≔-cong w false zz))
           (cong (λ b → ½ * [ b ]ᶻ) (zz w))
           (resp (z [ w ≔ true ]) (z′ [ w ≔ true ]) (≔-cong w true zz))
gateᴬ-resp (CNOT c t _) {ψ} resp z z′ zz =
  resp (z [ t ≔ z t xor z c ]) (z′ [ t ≔ z′ t xor z′ c ]) (λ j →
    trans (≔-cong t (z t xor z c) zz j)
          (cong (λ b → (z′ [ t ≔ b ]) j) (cong₂ _xor_ (zz t) (zz c))))
gateᴬ-resp (R k w) {ψ} resp z z′ zz =
  rot-cong (ψ z) (ψ z′) (pow (M ∸ k) * [ z w ]ᶻ) (pow (M ∸ k) * [ z′ w ]ᶻ)
           (cong (λ b → pow (M ∸ k) * [ b ]ᶻ) (zz w)) (resp z z′ zz)
gateᴬ-resp (R† k w) {ψ} resp z z′ zz =
  rot-cong (ψ z) (ψ z′)
           (- (pow (M ∸ k) * [ z w ]ᶻ)) (- (pow (M ∸ k) * [ z′ w ]ᶻ))
           (cong (λ b → - (pow (M ∸ k) * [ b ]ᶻ)) (zz w)) (resp z z′ zz)

applyᴬ-resp : (C : Circuit n) {ψ : Column n} → Respects ψ →
              Respects (applyᴬ C ψ)
applyᴬ-resp []      resp = resp
applyᴬ-resp (g ∷ C) resp = applyᴬ-resp C (gateᴬ-resp g resp)

gateᴬ-cong : (g : Gate n) {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
             ∀ z → gateᴬ g φ z ≐ gateᴬ g φ′ z
gateᴬ-cong (H w) {φ} {φ′} h z =
  sum-cong (φ (z [ w ≔ false ])) (φ′ (z [ w ≔ false ]))
           (φ (z [ w ≔ true ])) (φ′ (z [ w ≔ true ]))
           (½ * [ z w ]ᶻ) (½ * [ z w ]ᶻ)
           (h (z [ w ≔ false ])) refl (h (z [ w ≔ true ]))
gateᴬ-cong (CNOT c t _) h z = h (z [ t ≔ z t xor z c ])
gateᴬ-cong (R k w)      h z = rot-map (pow (M ∸ k) * [ z w ]ᶻ) (h z)
gateᴬ-cong (R† k w)     h z = rot-map (- (pow (M ∸ k) * [ z w ]ᶻ)) (h z)

applyᴬ-cong : (C : Circuit n) {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
              ∀ z → applyᴬ C φ z ≐ applyᴬ C φ′ z
applyᴬ-cong []      h = h
applyᴬ-cong (g ∷ C) {φ} {φ′} h =
  applyᴬ-cong C {gateᴬ g φ} {gateᴬ g φ′} (gateᴬ-cong g h)


------------------------------------------------------------------------
-- Proposition 2.10

-- The amplitudes of an interpretation state at the input x, as a
-- column, after each gate: the gate's matrix applied to the column
-- before it.  These are PathSum.CRK.Amp's step lemmas, read through a
-- column the old amplitudes are equal to.

private
  R-step : (k : ℕ) (w : Fin n) (st : State n m) (x : Assign n)
           (ψ : Column n) → (∀ z → ampᴸ st x z ≐ ψ z) →
           ∀ z → ampᴸ (stepR k w st) x z ≐ gateᴬ (R k w) ψ z
  R-step k w st x ψ h z i = trans (ampᴸ-R k w st x z i)
    (rot-map (pow (M ∸ k) * [ z w ]ᶻ) (h z) i)

  R†-step : (k : ℕ) (w : Fin n) (st : State n m) (x : Assign n)
            (ψ : Column n) → (∀ z → ampᴸ st x z ≐ ψ z) →
            ∀ z → ampᴸ (stepR† k w st) x z ≐ gateᴬ (R† k w) ψ z
  R†-step k w st x ψ h z i = trans (ampᴸ-R† k w st x z i)
    (rot-map (- (pow (M ∸ k) * [ z w ]ᶻ)) (h z) i)

  CNOT-step : (c t : Fin n) (p : c ≢ t) (st : State n m) (x : Assign n)
              (ψ : Column n) → (∀ z → ampᴸ st x z ≐ ψ z) →
              ∀ z → ampᴸ (stepCNOT c t st) x z ≐ gateᴬ (CNOT c t p) ψ z
  CNOT-step c t p st x ψ h z i = trans (ampᴸ-CNOT c t p st x z i)
    (h (z [ t ≔ z t xor z c ]) i)

  H-step : (w : Fin n) (st : State n m) (x : Assign n)
           (ψ : Column n) → (∀ z → ampᴸ st x z ≐ ψ z) →
           ∀ z → ampᴸ (stepH w st) x z ≐ gateᴬ (H w) ψ z
  H-step w st x ψ h z i = trans (ampᴸ-H w st x z i)
    (sum-cong (ampᴸ st x (z [ w ≔ false ])) (ψ (z [ w ≔ false ]))
              (ampᴸ st x (z [ w ≔ true ])) (ψ (z [ w ≔ true ]))
              (½ * [ z w ]ᶻ) (½ * [ z w ]ᶻ)
              (h (z [ w ≔ false ])) refl (h (z [ w ≔ true ])) i)

  run-amp : (C : Circuit n) (st : State n m) (x : Assign n)
            (ψ : Column n) → (∀ z → ampᴸ st x z ≐ ψ z) →
            ∀ z → ampᴸ (proj₂ (run C st)) x z ≐ applyᴬ C ψ z
  run-amp []               st x ψ h = h
  run-amp (H w ∷ C)        st x ψ h =
    run-amp C (stepH w st) x (gateᴬ (H w) ψ) (H-step w st x ψ h)
  run-amp (CNOT c t p ∷ C) st x ψ h =
    run-amp C (stepCNOT c t st) x (gateᴬ (CNOT c t p) ψ)
            (CNOT-step c t p st x ψ h)
  run-amp (R k w ∷ C)      st x ψ h =
    run-amp C (stepR k w st) x (gateᴬ (R k w) ψ) (R-step k w st x ψ h)
  run-amp (R† k w ∷ C)     st x ψ h =
    run-amp C (stepR† k w st) x (gateᴬ (R† k w) ψ) (R†-step k w st x ψ h)

-- The path-sum of a circuit computes its matrix: the amplitude of
-- ⟦ C ⟧ from x to z is the entry at z of C applied to |x⟩.

prop-2-10 : (C : Circuit n) (x z : Assign n) →
            amp ⟦ C ⟧ x z ≐ applyᴬ C (δ x) z
prop-2-10 C x = run-amp C init x (δ x) (ampᴸ-init x)


------------------------------------------------------------------------
-- The columns of ⟦ C ⟧ are unit vectors

-- The squared norm of a column, summed over its entries.

private
  colN : Column n → ℤ
  colN ψ = Σᶻ (λ z → ‖ ψ z ‖²)

  -- Phase gates multiply every entry by a power of ζ.

  colN-R : (k : ℕ) (w : Fin n) (ψ : Column n) →
           colN (gateᴬ (R k w) ψ) ≡ colN ψ
  colN-R k w ψ = Σᶻ-cong (λ z → trans
    (‖‖²-cong {gateᴬ (R k w) ψ z} {rot (pow (M ∸ k) * [ z w ]ᶻ) (ψ z)}
              (λ _ → refl))
    (‖‖²-rot (pow (M ∸ k) * [ z w ]ᶻ) (ψ z)))

  colN-R† : (k : ℕ) (w : Fin n) (ψ : Column n) →
            colN (gateᴬ (R† k w) ψ) ≡ colN ψ
  colN-R† k w ψ = Σᶻ-cong (λ z → trans
    (‖‖²-cong {gateᴬ (R† k w) ψ z} {rot (- (pow (M ∸ k) * [ z w ]ᶻ)) (ψ z)}
              (λ _ → refl))
    (‖‖²-rot (- (pow (M ∸ k) * [ z w ]ᶻ)) (ψ z)))

  -- CNOT pairs the assignments z[t≔0] and z[t≔1], and sends the pair
  -- to itself -- swapped when the control reads 1 -- so the norms of
  -- the pair add up to what they did.

  colN-CNOT : (c t : Fin n) (p : c ≢ t) (ψ : Column n) → Respects ψ →
              colN (gateᴬ (CNOT c t p) ψ) ≡ colN ψ
  colN-CNOT {n} c t p ψ resp =
    trans (Σᶻ-at t F respF)
      (trans (Σᶻ-cong (λ z → cong (λ s → if z t then 0ℤ else s) (pair z)))
             (sym (Σᶻ-at t G respG)))
    where
    F G : Assign n → ℤ
    F z = ‖ gateᴬ (CNOT c t p) ψ z ‖²
    G z = ‖ ψ z ‖²

    respF : RespectsZ F
    respF z z′ zz = ‖‖²-cong (gateᴬ-resp (CNOT c t p) resp z z′ zz)

    respG : RespectsZ G
    respG z z′ zz = ‖‖²-cong (resp z z′ zz)

    -- After setting the target to b, the gate reads the entry with
    -- the target set to b ⊕ z_c.

    at : ∀ z b → F (z [ t ≔ b ]) ≡ G (z [ t ≔ b xor z c ])
    at z b = ‖‖²-cong (resp _ _ (λ j →
      trans (≔-≔ z t b ((z [ t ≔ b ]) t xor (z [ t ≔ b ]) c) j)
            (cong (λ u → (z [ t ≔ u ]) j)
                  (cong₂ _xor_ (≔-here z t b) (≔-there z b p)))))

    swap : ∀ z (b : Bool) →
           G (z [ t ≔ b ]) + G (z [ t ≔ not b ]) ≡
           G (z [ t ≔ false ]) + G (z [ t ≔ true ])
    swap z false = refl
    swap z true  = +-comm (G (z [ t ≔ true ])) (G (z [ t ≔ false ]))

    pair : ∀ z → F (z [ t ≔ false ]) + F (z [ t ≔ true ]) ≡
                 G (z [ t ≔ false ]) + G (z [ t ≔ true ])
    pair z = trans (cong₂ _+_ (at z false) (at z true)) (swap z (z c))

  -- A Hadamard on w pairs the assignments z[w≔0] and z[w≔1].  Its new
  -- entries there are a + b and a - b, a and b the old ones, and by
  -- the parallelogram law their norms add up to twice those of a and
  -- b.  Summing over the pairs doubles the norm of the column.

  pair-norm : (X₀ X₁ a b : Amp) → X₀ ≐ (a +ᴬ b) → X₁ ≐ (a -ᴬ b) →
              ‖ X₀ ‖² + ‖ X₁ ‖² ≡ (+ 2) * (‖ a ‖² + ‖ b ‖²)
  pair-norm X₀ X₁ a b p q = trans
    (cong₂ _+_ (‖‖²-cong {X₀} {a +ᴬ b} p) (‖‖²-cong {X₁} {a -ᴬ b} q))
    (parallelogram a b)

  if-double : (b : Bool) {X Y : ℤ} → X ≡ (+ 2) * Y →
              (if b then 0ℤ else X) ≡ (+ 2) * (if b then 0ℤ else Y)
  if-double true  _ = sym (*-zeroʳ (+ 2))
  if-double false p = p

  colN-H : (w : Fin n) (ψ : Column n) → Respects ψ →
           colN (gateᴬ (H w) ψ) ≡ (+ 2) * colN ψ
  colN-H w ψ resp =
    trans (Σᶻ-at w (λ z → ‖ gateᴬ (H w) ψ z ‖²) respF)
      (trans (Σᶻ-cong (λ z → if-double (z w) (pair z)))
        (trans (Σᶻ-* (+ 2) (λ z → if z w then 0ℤ else
                               (‖ ψ (z [ w ≔ false ]) ‖² +
                                ‖ ψ (z [ w ≔ true ]) ‖²)))
               (cong (λ u → (+ 2) * u)
                     (sym (Σᶻ-at w (λ z → ‖ ψ z ‖²) respG)))))
    where
    respF : RespectsZ (λ z → ‖ gateᴬ (H w) ψ z ‖²)
    respF z z′ zz = ‖‖²-cong (gateᴬ-resp (H w) resp z z′ zz)

    respG : RespectsZ (λ z → ‖ ψ z ‖²)
    respG z z′ zz = ‖‖²-cong (resp z z′ zz)

    e₀ : ∀ z → ½ * [ (z [ w ≔ false ]) w ]ᶻ ≡ 0ℤ
    e₀ z =
      trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w false)) (*-zeroʳ ½)

    e₁ : ∀ z → ½ * [ (z [ w ≔ true ]) w ]ᶻ ≡ 0ℤ + (+ rank)
    e₁ z = trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w true))
                 (trans (*-identityʳ ½) (sym (+-identityˡ ½)))

    pair : ∀ z → ‖ gateᴬ (H w) ψ (z [ w ≔ false ]) ‖² +
                 ‖ gateᴬ (H w) ψ (z [ w ≔ true ]) ‖² ≡
                 (+ 2) * (‖ ψ (z [ w ≔ false ]) ‖² +
                          ‖ ψ (z [ w ≔ true ]) ‖²)
    pair z = pair-norm
      (gateᴬ (H w) ψ (z [ w ≔ false ])) (gateᴬ (H w) ψ (z [ w ≔ true ]))
      (ψ (z [ w ≔ false ])) (ψ (z [ w ≔ true ]))
      (sign-0 (ψ (z [ w ≔ false ] [ w ≔ false ])) (ψ (z [ w ≔ false ]))
              (ψ (z [ w ≔ false ] [ w ≔ true ])) (ψ (z [ w ≔ true ]))
              (½ * [ (z [ w ≔ false ]) w ]ᶻ)
              (resp _ _ (≔-≔ z w false false)) (e₀ z)
              (resp _ _ (≔-≔ z w false true)))
      (sign-1 (ψ (z [ w ≔ true ] [ w ≔ false ])) (ψ (z [ w ≔ false ]))
              (ψ (z [ w ≔ true ] [ w ≔ true ])) (ψ (z [ w ≔ true ]))
              (½ * [ (z [ w ≔ true ]) w ]ᶻ)
              (resp _ _ (≔-≔ z w true false)) (e₁ z)
              (resp _ _ (≔-≔ z w true true)))

  -- So a circuit multiplies the norm of a column by 2^k, k the number
  -- of its Hadamards.

  twice : ∀ k c → + (2 ^ k) * ((+ 2) * c) ≡ + (2 ^ suc k) * c
  twice k c = trans (sym (*-assoc (+ (2 ^ k)) (+ 2) c))
    (cong (_* c) (trans (*-comm (+ (2 ^ k)) (+ 2))
                        (sym (pos-* 2 (2 ^ k)))))

  colN-apply : (C : Circuit n) (ψ : Column n) → Respects ψ →
               colN (applyᴬ C ψ) ≡ + (2 ^ norm C) * colN ψ
  colN-apply []               ψ resp = sym (*-identityˡ (colN ψ))
  colN-apply (H w ∷ C)        ψ resp =
    trans (colN-apply C (gateᴬ (H w) ψ) (gateᴬ-resp (H w) resp))
      (trans (cong (λ u → + (2 ^ norm C) * u) (colN-H w ψ resp))
             (twice (norm C) (colN ψ)))
  colN-apply (CNOT c t p ∷ C) ψ resp =
    trans (colN-apply C (gateᴬ (CNOT c t p) ψ)
                      (gateᴬ-resp (CNOT c t p) resp))
          (cong (λ u → + (2 ^ norm C) * u) (colN-CNOT c t p ψ resp))
  colN-apply (R k w ∷ C)      ψ resp =
    trans (colN-apply C (gateᴬ (R k w) ψ) (gateᴬ-resp (R k w) resp))
          (cong (λ u → + (2 ^ norm C) * u) (colN-R k w ψ))
  colN-apply (R† k w ∷ C)     ψ resp =
    trans (colN-apply C (gateᴬ (R† k w) ψ) (gateᴬ-resp (R† k w) resp))
          (cong (λ u → + (2 ^ norm C) * u) (colN-R† k w ψ))

  -- The basis column is a unit vector: its entry at x is ζ^0, and
  -- every other entry is 0.

  colN-δ : (x : Assign n) → colN (δ x) ≡ 1ℤ
  colN-δ x =
    trans (Σᶻ-point (λ z → ‖ δ x z ‖²)
                    (λ z z′ zz → ‖‖²-cong (δ-resp x z z′ zz)) x)
      (trans (cong₂ _+_ here rest) (+-identityʳ 1ℤ))
    where
    here : ‖ δ x x ‖² ≡ 1ℤ
    here = trans
      (‖‖²-cong {δ x x} {zpow 0ℤ}
        (λ i → cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) (same-refl x)))
      ‖zpow0‖²

    off : (b : Bool) →
          (if b then 0ℤ else ‖ (if b then zpow 0ℤ else 0ᴬ) ‖²) ≡ 0ℤ
    off true  = refl
    off false = ‖0ᴬ‖²

    rest : Σᶻ (λ z → if same x z then 0ℤ else ‖ δ x z ‖²) ≡ 0ℤ
    rest = trans (Σᶻ-cong (λ z → off (same x z))) Σᶻ-0

-- Every column of ⟦ C ⟧ has trace-form norm 2^k, k = norm C: a unit
-- vector once normalised by 1/√2^k.  (That ⟦ C ⟧ is unitary is not
-- needed and not stated.)

⟦⟧-unit-columns : (C : Circuit n) (x : Assign n) →
                  Σᶻ (λ z → ‖ amp ⟦ C ⟧ x z ‖²) ≡ + (2 ^ norm C)
⟦⟧-unit-columns C x =
  trans (Σᶻ-cong (λ z →
          ‖‖²-cong {amp ⟦ C ⟧ x z} {applyᴬ C (δ x) z} (prop-2-10 C x z)))
    (trans (colN-apply C (δ x) (δ-resp x))
      (trans (cong (λ u → + (2 ^ norm C) * u) (colN-δ x))
             (*-identityʳ (+ (2 ^ norm C)))))
