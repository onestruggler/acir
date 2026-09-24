------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix of a Clifford circuit, and its isometry restriction
-- (Amy, QPL 2018, proposition 2.10 and section 4.1)
--
-- Proposition 2.10 says that the path-sum of a circuit computes the
-- circuit's matrix.  Over {H , S , CZ} that matrix is built a column
-- at a time: a column is a vector of amplitudes indexed by the output
-- assignments, and each gate acts on it by its own unnormalised
-- matrix.  S and CZ multiply the entry at z by a power of ζ read off
-- z, and a Hadamard on w sends the entry at z to the sum of the old
-- entries at z[w≔0] and z[w≔1], the second signed by (-1)^(z_w).
-- PathSum.CircuitAmp shows that each gate changes the amplitudes of an
-- interpretation state by exactly that matrix, so the amplitudes of
-- ⟦ C ⟧ at the input x are the gates of C applied in turn to the basis
-- column δ x.
--
-- Every column of ⟦ C ⟧ is a unit vector once normalised, the norm
-- being PathSum.Norm's trace form ‖ a ‖² = Σ_i a_i² = Tr(a·ā)/H --
-- the constant coefficient of Σ_z |amp|², which is the form lemma 4.1
-- asks about (PathSum.Isometry).  S and CZ preserve the squared norm of
-- each entry, and a Hadamard doubles the
-- norm of a column: it turns the entries a and b at z[w≔0] and z[w≔1]
-- into a + b and a - b, and the parallelogram law adds those norms up
-- to twice those of a and b.  The basis column has norm 1, so a column
-- of ⟦ C ⟧ has norm 2^k, k the number of Hadamards, which is what the
-- normalisation 1/√2^k divides out.
--
-- ⟦ C ⟧ᴿ differs from ⟦ C ⟧ only at the last Hadamard on each wire,
-- where the restriction keeps the entries whose value on that wire is
-- the input's.  No later gate is a Hadamard on the wire, so the
-- projection commutes with all of them -- S and CZ are diagonal, and a
-- Hadamard elsewhere reads only assignments that agree with z on the
-- wire.  The column of ⟦ C ⟧ᴿ at x is therefore that of ⟦ C ⟧ with
-- every wire a Hadamard touches projected onto x, and at z = x no
-- projection removes anything: the two have the same diagonal.  Every
-- output of ⟦ C ⟧ᴿ is its input, so off that diagonal no path hits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc; _^_)

module PathSum.CircuitSemantics (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; *-zeroʳ; *-assoc;
   *-comm; pos-*)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-cong; _=ᵇ_; =ᵇ-refl; =ᵇ-true;
   same; same-refl; same-intro; same-≗)
open import PathSum.AssignSum using
  (Σᶻ; RespectsZ; Σᶻ-cong; Σᶻ-*; Σᶻ-0; Σᶻ-point; Σᶻ-at)
open import PathSum.Circuit M using
  (Gate; H; S; CZ; Circuit; norm; hasH; State; sig; init; stepS; stepCZ;
   allocH; finalH; stepH; run; runᵁ; ⟦_⟧; ⟦_⟧ᴿ; ⟦⟧ᴿ-sig)
open import PathSum.CircuitAmp M₀ using
  (ampˢ; ampˢ-init; ampˢ-S; ampˢ-CZ; ampˢ-allocH; ampˢ-finalH)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _-ᴬ_; _≐_; zpow; rot; rot-map; rot-exp; rot-0;
   rot-anti; rot-0ᴬ; Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; hits-elim; outBit-μ)
open import PathSum.Norm M₀ using
  (‖_‖²; ‖‖²-cong; ‖‖²-rot; parallelogram; ‖zpow0‖²; ‖0ᴬ‖²)
open import PathSum.Polynomial.Properties using (valᵛ)
open import PathSum.Reduction M using (¼; ½)

import Data.Fin.Properties as Fin

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Columns and the matrices of the gates

-- A column of amplitudes, one for each output assignment.

Column : ℕ → Set
Column n = Assign n → Amp

-- The column of the basis state |x⟩.

δ : Assign n → Column n
δ x z = if same x z then zpow 0ℤ else 0ᴬ

-- Each gate's matrix, unnormalised, acting on a column: the entry at z
-- of the new column.  A Hadamard's normalisation 1/√2 is left to the
-- path-sum's.

gateᴬ : Gate n → Column n → Column n
gateᴬ (H w)    ψ z =
  ψ (z [ w ≔ false ]) +ᴬ rot (½ * [ z w ]ᶻ) (ψ (z [ w ≔ true ]))
gateᴬ (S w)    ψ z = rot (¼ * [ z w ]ᶻ) (ψ z)
gateᴬ (CZ w v) ψ z = rot (½ * [ z w ∧ z v ]ᶻ) (ψ z)

-- The gates of a circuit act first to last.

applyᴬ : Circuit n → Column n → Column n
applyᴬ []      ψ = ψ
applyᴬ (g ∷ C) ψ = applyᴬ C (gateᴬ g ψ)


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

  -- Entries kept only under a condition.

  if-map : (c : Bool) {a b : Amp} → a ≐ b →
           (if c then a else 0ᴬ) ≐ (if c then b else 0ᴬ)
  if-map true  ab = ab
  if-map false _  = λ _ → refl

  if-and : (c g : Bool) (a : Amp) →
           (if g then (if c then a else 0ᴬ) else 0ᴬ) ≐
           (if (c ∧ g) then a else 0ᴬ)
  if-and true  true  a _ = refl
  if-and true  false a _ = refl
  if-and false true  a _ = refl
  if-and false false a _ = refl

  rot-guard : (c : Bool) (e : ℤ) (a : Amp) →
              rot e (if c then a else 0ᴬ) ≐ (if c then rot e a else 0ᴬ)
  rot-guard true  e a = λ _ → refl
  rot-guard false e a = rot-0ᴬ e

  sum-guard : (c₀ c₁ c : Bool) (a b : Amp) (e : ℤ) → c₀ ≡ c → c₁ ≡ c →
              ((if c₀ then a else 0ᴬ) +ᴬ rot e (if c₁ then b else 0ᴬ)) ≐
              (if c then (a +ᴬ rot e b) else 0ᴬ)
  sum-guard _ _ true  a b e refl refl = λ _ → refl
  sum-guard _ _ false a b e refl refl =
    λ i → trans (+-identityˡ (rot e 0ᴬ i)) (rot-0ᴬ e i)


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
             (resp (z [ w ≔ false ]) (z′ [ w ≔ false ])
                   (≔-cong w false zz))
             (cong (λ b → ½ * [ b ]ᶻ) (zz w))
             (resp (z [ w ≔ true ]) (z′ [ w ≔ true ]) (≔-cong w true zz))
  gateᴬ-resp (S w) {ψ} resp z z′ zz =
    rot-cong (ψ z) (ψ z′) (¼ * [ z w ]ᶻ) (¼ * [ z′ w ]ᶻ)
             (cong (λ b → ¼ * [ b ]ᶻ) (zz w)) (resp z z′ zz)
  gateᴬ-resp (CZ w v) {ψ} resp z z′ zz =
    rot-cong (ψ z) (ψ z′) (½ * [ z w ∧ z v ]ᶻ) (½ * [ z′ w ∧ z′ v ]ᶻ)
             (cong₂ (λ a b → ½ * [ a ∧ b ]ᶻ) (zz w) (zz v))
             (resp z z′ zz)

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
  gateᴬ-cong (S w)    h z = rot-map (¼ * [ z w ]ᶻ) (h z)
  gateᴬ-cong (CZ w v) h z = rot-map (½ * [ z w ∧ z v ]ᶻ) (h z)

  applyᴬ-cong : (C : Circuit n) {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
                ∀ z → applyᴬ C φ z ≐ applyᴬ C φ′ z
  applyᴬ-cong []      h = h
  applyᴬ-cong (g ∷ C) {φ} {φ′} h =
    applyᴬ-cong C {gateᴬ g φ} {gateᴬ g φ′} (gateᴬ-cong g h)


------------------------------------------------------------------------
-- Proposition 2.10

-- The amplitudes of an interpretation state at the input x, as a
-- column, after each gate: the gate's matrix applied to the column
-- before it.  These are PathSum.CircuitAmp's step lemmas, read through
-- a column the old amplitudes are equal to.

private
  S-step : (w : Fin n) (st : State n m) (x : Assign n) (ψ : Column n) →
           (∀ z → ampˢ st x z ≐ ψ z) →
           ∀ z → ampˢ (stepS w st) x z ≐ gateᴬ (S w) ψ z
  S-step w st x ψ h z i =
    trans (ampˢ-S w st x z i) (rot-map (¼ * [ z w ]ᶻ) (h z) i)

  CZ-step : (w v : Fin n) (st : State n m) (x : Assign n)
            (ψ : Column n) → (∀ z → ampˢ st x z ≐ ψ z) →
            ∀ z → ampˢ (stepCZ w v st) x z ≐ gateᴬ (CZ w v) ψ z
  CZ-step w v st x ψ h z i =
    trans (ampˢ-CZ w v st x z i) (rot-map (½ * [ z w ∧ z v ]ᶻ) (h z) i)

  alloc-step : (w : Fin n) (st : State n m) (x : Assign n)
               (ψ : Column n) → (∀ z → ampˢ st x z ≐ ψ z) →
               ∀ z → ampˢ (allocH w st) x z ≐ gateᴬ (H w) ψ z
  alloc-step w st x ψ h z i = trans (ampˢ-allocH w st x z i)
    (sum-cong (ampˢ st x (z [ w ≔ false ])) (ψ (z [ w ≔ false ]))
              (ampˢ st x (z [ w ≔ true ])) (ψ (z [ w ≔ true ]))
              (½ * [ z w ]ᶻ) (½ * [ z w ]ᶻ)
              (h (z [ w ≔ false ])) refl (h (z [ w ≔ true ])) i)

  -- The run of every Hadamard allocating a path variable.

  runᵁ-amp : (C : Circuit n) (st : State n m) (x : Assign n)
             (ψ : Column n) → (∀ z → ampˢ st x z ≐ ψ z) →
             ∀ z → ampˢ (proj₂ (runᵁ C st)) x z ≐ applyᴬ C ψ z
  runᵁ-amp []           st x ψ h = h
  runᵁ-amp (H w ∷ C)    st x ψ h =
    runᵁ-amp C (allocH w st) x (gateᴬ (H w) ψ) (alloc-step w st x ψ h)
  runᵁ-amp (S w ∷ C)    st x ψ h =
    runᵁ-amp C (stepS w st) x (gateᴬ (S w) ψ) (S-step w st x ψ h)
  runᵁ-amp (CZ w v ∷ C) st x ψ h =
    runᵁ-amp C (stepCZ w v st) x (gateᴬ (CZ w v) ψ)
             (CZ-step w v st x ψ h)

-- The path-sum of a circuit computes its matrix: the amplitude of
-- ⟦ C ⟧ from x to z is the entry at z of C applied to |x⟩.

prop-2-10 : (C : Circuit n) (x z : Assign n) →
            amp ⟦ C ⟧ x z ≐ applyᴬ C (δ x) z
prop-2-10 C x = runᵁ-amp C init x (δ x) (ampˢ-init x)


------------------------------------------------------------------------
-- ⟦ C ⟧ is an isometry

-- The squared norm of a column, summed over its entries.

private
  colN : Column n → ℤ
  colN ψ = Σᶻ (λ z → ‖ ψ z ‖²)

  -- Phase gates multiply every entry by a power of ζ.

  colN-S : (w : Fin n) (ψ : Column n) → colN (gateᴬ (S w) ψ) ≡ colN ψ
  colN-S w ψ = Σᶻ-cong (λ z → trans
    (‖‖²-cong {gateᴬ (S w) ψ z} {rot (¼ * [ z w ]ᶻ) (ψ z)} (λ _ → refl))
    (‖‖²-rot (¼ * [ z w ]ᶻ) (ψ z)))

  colN-CZ : (w v : Fin n) (ψ : Column n) →
            colN (gateᴬ (CZ w v) ψ) ≡ colN ψ
  colN-CZ w v ψ = Σᶻ-cong (λ z → trans
    (‖‖²-cong {gateᴬ (CZ w v) ψ z} {rot (½ * [ z w ∧ z v ]ᶻ) (ψ z)}
              (λ _ → refl))
    (‖‖²-rot (½ * [ z w ∧ z v ]ᶻ) (ψ z)))

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

  colN-apply : (C : Circuit n) (ψ : Column n) → Respects ψ →
               colN (applyᴬ C ψ) ≡ + (2 ^ norm C) * colN ψ
  colN-apply []           ψ resp = sym (*-identityˡ (colN ψ))
  colN-apply (H w ∷ C)    ψ resp =
    trans (colN-apply C (gateᴬ (H w) ψ) (gateᴬ-resp (H w) resp))
      (trans (cong (λ u → + (2 ^ norm C) * u) (colN-H w ψ resp))
             (twice (norm C) (colN ψ)))
    where
    twice : ∀ k c → + (2 ^ k) * ((+ 2) * c) ≡ + (2 ^ suc k) * c
    twice k c = trans (sym (*-assoc (+ (2 ^ k)) (+ 2) c))
      (cong (_* c) (trans (*-comm (+ (2 ^ k)) (+ 2))
                          (sym (pos-* 2 (2 ^ k)))))
  colN-apply (S w ∷ C)    ψ resp =
    trans (colN-apply C (gateᴬ (S w) ψ) (gateᴬ-resp (S w) resp))
          (cong (λ u → + (2 ^ norm C) * u) (colN-S w ψ))
  colN-apply (CZ w v ∷ C) ψ resp =
    trans (colN-apply C (gateᴬ (CZ w v) ψ) (gateᴬ-resp (CZ w v) resp))
          (cong (λ u → + (2 ^ norm C) * u) (colN-CZ w v ψ))

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

-- Every column of ⟦ C ⟧ has norm 2^k, k = norm C: an isometry, once
-- normalised by 1/√2^k.

⟦⟧-isometry : (C : Circuit n) (x : Assign n) →
              Σᶻ (λ z → ‖ amp ⟦ C ⟧ x z ‖²) ≡ + (2 ^ norm C)
⟦⟧-isometry C x =
  trans (Σᶻ-cong (λ z →
          ‖‖²-cong {amp ⟦ C ⟧ x z} {applyᴬ C (δ x) z} (prop-2-10 C x z)))
    (trans (colN-apply C (δ x) (δ-resp x))
      (trans (cong (λ u → + (2 ^ norm C) * u) (colN-δ x))
             (*-identityʳ (+ (2 ^ norm C)))))


------------------------------------------------------------------------
-- The restricted run

-- At a Hadamard that is the last on its wire, ⟦ C ⟧ᴿ reads x_w where
-- ⟦ C ⟧ reads z_w, and keeps only the entries with z_w = x_w.

private
  finalᴬ : Assign n → Fin n → Column n → Column n
  finalᴬ x w ψ z =
    if (z w =ᵇ x w)
    then (ψ (z [ w ≔ false ]) +ᴬ rot (½ * [ x w ]ᶻ) (ψ (z [ w ≔ true ])))
    else 0ᴬ

  stepᴿ : Assign n → Bool → Fin n → Column n → Column n
  stepᴿ x true  w ψ = gateᴬ (H w) ψ
  stepᴿ x false w ψ = finalᴬ x w ψ

  applyᴿ : Assign n → Circuit n → Column n → Column n
  applyᴿ x []           ψ = ψ
  applyᴿ x (H w ∷ C)    ψ = applyᴿ x C (stepᴿ x (hasH w C) w ψ)
  applyᴿ x (S w ∷ C)    ψ = applyᴿ x C (gateᴬ (S w) ψ)
  applyᴿ x (CZ w v ∷ C) ψ = applyᴿ x C (gateᴬ (CZ w v) ψ)

  final-step : (w : Fin n) (st : State n m) (x : Assign n)
               (ψ : Column n) → (∀ z → ampˢ st x z ≐ ψ z) →
               ∀ z → ampˢ (finalH w st) x z ≐ finalᴬ x w ψ z
  final-step w st x ψ h z i = trans (ampˢ-finalH w st x z i)
    (if-map (z w =ᵇ x w)
      (sum-cong (ampˢ st x (z [ w ≔ false ])) (ψ (z [ w ≔ false ]))
                (ampˢ st x (z [ w ≔ true ])) (ψ (z [ w ≔ true ]))
                (½ * [ x w ]ᶻ) (½ * [ x w ]ᶻ)
                (h (z [ w ≔ false ])) refl (h (z [ w ≔ true ]))) i)

  -- The amplitudes of ⟦ C ⟧ᴿ, computed a column at a time as those of
  -- ⟦ C ⟧ are.

  run-amp : (C : Circuit n) (st : State n m) (x : Assign n)
            (ψ : Column n) → (∀ z → ampˢ st x z ≐ ψ z) →
            ∀ z → ampˢ (proj₂ (run C st)) x z ≐ applyᴿ x C ψ z
  run-amp []           st x ψ h = h
  run-amp (H w ∷ C)    st x ψ h = by (hasH w C)
    where
    by : (b : Bool) →
         ∀ z → ampˢ (proj₂ (run C (proj₂ (stepH b w st)))) x z ≐
               applyᴿ x C (stepᴿ x b w ψ) z
    by true  =
      run-amp C (allocH w st) x (gateᴬ (H w) ψ) (alloc-step w st x ψ h)
    by false =
      run-amp C (finalH w st) x (finalᴬ x w ψ) (final-step w st x ψ h)
  run-amp (S w ∷ C)    st x ψ h =
    run-amp C (stepS w st) x (gateᴬ (S w) ψ) (S-step w st x ψ h)
  run-amp (CZ w v ∷ C) st x ψ h =
    run-amp C (stepCZ w v st) x (gateᴬ (CZ w v) ψ)
            (CZ-step w v st x ψ h)


------------------------------------------------------------------------
-- Projecting a wire onto the input

-- Keeping only the entries whose value on w is the input's.  The
-- Hadamard that is the last on w does this to its own output.

private
  project : Assign n → Fin n → Column n → Column n
  project x w φ z = if (z w =ᵇ x w) then φ z else 0ᴬ

  final-project : (x : Assign n) (w : Fin n) (ψ : Column n) →
                  ∀ z → finalᴬ x w ψ z ≐ project x w (gateᴬ (H w) ψ) z
  final-project x w ψ z = at (z w =ᵇ x w) refl
    where
    at : (c : Bool) → (z w =ᵇ x w) ≡ c →
         (if c then (ψ (z [ w ≔ false ]) +ᴬ
                     rot (½ * [ x w ]ᶻ) (ψ (z [ w ≔ true ])))
          else 0ᴬ) ≐
         (if c then gateᴬ (H w) ψ z else 0ᴬ)
    at true  eq = sum-cong
      (ψ (z [ w ≔ false ])) (ψ (z [ w ≔ false ]))
      (ψ (z [ w ≔ true ])) (ψ (z [ w ≔ true ]))
      (½ * [ x w ]ᶻ) (½ * [ z w ]ᶻ)
      (λ _ → refl)
      (cong (λ b → ½ * [ b ]ᶻ) (sym (=ᵇ-true {z w} {x w} eq)))
      (λ _ → refl)
    at false _  = λ _ → refl

  -- A projection on w commutes with a gate that is not a Hadamard on
  -- w.  S and CZ act entry by entry; a Hadamard on another wire v reads
  -- the entries at z[v≔b], which have z's value on w.

  project-S : (x : Assign n) (w v : Fin n) (φ : Column n) →
              ∀ z → gateᴬ (S v) (project x w φ) z ≐
                    project x w (gateᴬ (S v) φ) z
  project-S x w v φ z = rot-guard (z w =ᵇ x w) (¼ * [ z v ]ᶻ) (φ z)

  project-CZ : (x : Assign n) (w v u : Fin n) (φ : Column n) →
               ∀ z → gateᴬ (CZ v u) (project x w φ) z ≐
                     project x w (gateᴬ (CZ v u) φ) z
  project-CZ x w v u φ z =
    rot-guard (z w =ᵇ x w) (½ * [ z v ∧ z u ]ᶻ) (φ z)

  project-H : (x : Assign n) (w v : Fin n) → w ≢ v → (φ : Column n) →
              ∀ z → gateᴬ (H v) (project x w φ) z ≐
                    project x w (gateᴬ (H v) φ) z
  project-H x w v w≢v φ z = sum-guard
    ((z [ v ≔ false ]) w =ᵇ x w) ((z [ v ≔ true ]) w =ᵇ x w) (z w =ᵇ x w)
    (φ (z [ v ≔ false ])) (φ (z [ v ≔ true ])) (½ * [ z v ]ᶻ)
    (cong (_=ᵇ x w) (≔-there z {v} {w} false w≢v))
    (cong (_=ᵇ x w) (≔-there z {v} {w} true w≢v))

  -- Reading hasH: no Hadamard on w among H v ∷ C means w ≢ v and none
  -- in C.

  true≢false : true ≢ false
  true≢false ()

  ⌊≟⌋-refl : (w : Fin n) → ⌊ w Fin.≟ w ⌋ ≡ true
  ⌊≟⌋-refl w with w Fin.≟ w
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  ≢-of : (w v : Fin n) → ⌊ w Fin.≟ v ⌋ ≡ false → w ≢ v
  ≢-of w _ eq refl = true≢false (trans (sym (⌊≟⌋-refl w)) eq)

  ∨-falseˡ : (a : Bool) {b : Bool} → (a ∨ b) ≡ false → a ≡ false
  ∨-falseˡ false _ = refl
  ∨-falseˡ true  ()

  ∨-falseʳ : (a : Bool) {b : Bool} → (a ∨ b) ≡ false → b ≡ false
  ∨-falseʳ false eq = eq
  ∨-falseʳ true  ()

  -- So a projection on w commutes with a circuit that has no Hadamard
  -- on w.

  project-comm : (C : Circuit n) (x : Assign n) (w : Fin n) →
                 hasH w C ≡ false → (φ : Column n) →
                 ∀ z → applyᴬ C (project x w φ) z ≐
                       project x w (applyᴬ C φ) z
  project-comm []           x w _  φ z = λ _ → refl
  project-comm (H v ∷ C)    x w nh φ z i = trans
    (applyᴬ-cong C
      (project-H x w v
        (≢-of w v (∨-falseˡ ⌊ w Fin.≟ v ⌋ {hasH w C} nh)) φ) z i)
    (project-comm C x w (∨-falseʳ ⌊ w Fin.≟ v ⌋ {hasH w C} nh)
                  (gateᴬ (H v) φ) z i)
  project-comm (S v ∷ C)    x w nh φ z i = trans
    (applyᴬ-cong C (project-S x w v φ) z i)
    (project-comm C x w nh (gateᴬ (S v) φ) z i)
  project-comm (CZ v u ∷ C) x w nh φ z i = trans
    (applyᴬ-cong C (project-CZ x w v u φ) z i)
    (project-comm C x w nh (gateᴬ (CZ v u) φ) z i)


------------------------------------------------------------------------
-- ⟦ C ⟧ᴿ is the isometry restriction of ⟦ C ⟧

-- Whether z agrees with x on every wire that C applies a Hadamard to.

private
  guard : Assign n → Circuit n → Assign n → Bool
  guard x []           z = true
  guard x (H w ∷ C)    z =
    if hasH w C then guard x C z else ((z w =ᵇ x w) ∧ guard x C z)
  guard x (S _ ∷ C)    z = guard x C z
  guard x (CZ _ _ ∷ C) z = guard x C z

  guard-if : (b : Bool) {u t : Bool} → u ≡ true → t ≡ true →
             (if b then t else (u ∧ t)) ≡ true
  guard-if true  refl refl = refl
  guard-if false refl refl = refl

  guard-refl : (C : Circuit n) (x : Assign n) → guard x C x ≡ true
  guard-refl []           x = refl
  guard-refl (H w ∷ C)    x =
    guard-if (hasH w C) (=ᵇ-refl (x w)) (guard-refl C x)
  guard-refl (S _ ∷ C)    x = guard-refl C x
  guard-refl (CZ _ _ ∷ C) x = guard-refl C x

  -- Each last Hadamard projects its wire, and the projection passes
  -- through the rest of the circuit: the restricted column is the
  -- full one, kept where z agrees with x on every Hadamard's wire.

  restrict : (C : Circuit n) (x : Assign n) (ψ : Column n) →
             ∀ z → applyᴿ x C ψ z ≐
                   (if guard x C z then applyᴬ C ψ z else 0ᴬ)
  restrict []           x ψ z = λ _ → refl
  restrict (H w ∷ C)    x ψ z = at (hasH w C) refl
    where
    at : (b : Bool) → hasH w C ≡ b →
         applyᴿ x C (stepᴿ x b w ψ) z ≐
         (if (if b then guard x C z else ((z w =ᵇ x w) ∧ guard x C z))
          then applyᴬ C (gateᴬ (H w) ψ) z else 0ᴬ)
    at true  _  = restrict C x (gateᴬ (H w) ψ) z
    at false nh i = trans (restrict C x (finalᴬ x w ψ) z i)
      (trans (if-map (guard x C z) (λ j →
               trans (applyᴬ-cong C (final-project x w ψ) z j)
                     (project-comm C x w nh (gateᴬ (H w) ψ) z j)) i)
             (if-and (z w =ᵇ x w) (guard x C z)
                     (applyᴬ C (gateᴬ (H w) ψ) z) i))
  restrict (S w ∷ C)    x ψ z = restrict C x (gateᴬ (S w) ψ) z
  restrict (CZ w v ∷ C) x ψ z = restrict C x (gateᴬ (CZ w v) ψ) z

-- At z = x the guard holds, so ⟦ C ⟧ᴿ has the diagonal of ⟦ C ⟧.

⟦⟧ᴿ-restricts : (C : Circuit n) (x : Assign n) →
                amp ⟦ C ⟧ᴿ x x ≐ amp ⟦ C ⟧ x x
⟦⟧ᴿ-restricts C x i =
  trans (run-amp C init x (δ x) (ampˢ-init x) x i)
    (trans (restrict C x (δ x) x i)
      (trans (cong (λ b → (if b then applyᴬ C (δ x) x else 0ᴬ) i)
                   (guard-refl C x))
             (sym (prop-2-10 C x x i))))

-- Every output of ⟦ C ⟧ᴿ is its input, so a path hits only x.

⟦⟧ᴿ-diagonal : (C : Circuit n) →
               ∀ x y z → hits ⟦ C ⟧ᴿ x y z ≡ true → same x z ≡ true
⟦⟧ᴿ-diagonal {n} C x y z h = same-intro x z (λ w →
  trans (sym (cong (λ v → valᵛ v x y) (⟦⟧ᴿ-sig C w)))
    (trans (sym (outBit-μ ⟦ C ⟧ᴿ x y w
                          (sig (proj₂ (run C (init {n}))) w) refl))
           (hits-elim ⟦ C ⟧ᴿ x y z h w)))
