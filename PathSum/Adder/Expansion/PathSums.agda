------------------------------------------------------------------------
-- Presentations of groups
--
-- The output polynomials of every classical adder specification are
-- exponentially large (Amy, QPL 2018, sections 2 and 5.2)
--
-- Section 2 lifts the polynomial representation of a classical
-- function f to the path-sum |x⟩|0⟩ ↦ |x⟩|f(x)⟩, whose output
-- signature is f written as Boolean polynomials, and remarks that
-- "the polynomial representation of a classical function may grow
-- exponentially large, as in the case of addition".  Here that is read
-- off the output polynomials of path-sums, through
-- PathSum.Adder.Expansion's normal forms.
--
-- The registers.  On an adder layout (PathSum.Adder.Layout) with
-- n = m + 1 bits, regs L interleaves the wires of the input registers,
-- x_i at 2i and y_i at 2i + 1, injectively (regs-injective); a monomial
-- S in those 2n variables is the monomial reg L S over the wires.  On
-- an input that is 0 off the registers (PathSum.Polynomial.Restrict's
-- ext), the registers read the operands (ext-x, ext-y) and the output
-- register 0 (ext-z).
--
-- The theorems.  A path-sum without path variables "adds" (Adds ξ)
-- when, on those inputs, its output on z_j is the bit j of x + y.  Any
-- path-sum computing PathSum.Adder.Ripple's addition (|z⟩ ↦ |z ⊕ (x +
-- y)⟩) or PathSum.Adder.Spec's addition₀ (|z⟩ ↦ |x + y⟩) adds
-- (computes-adds, computes₀-adds), adderˢ and adder₀ˢ in particular.
-- Then, by PathSum.Polynomial.Restrict and Möbius inversion modulo 2:
--
-- * adds-carry: the polynomial of the output z_n has an odd
--   coefficient on the register monomial reg L S exactly when S is a
--   monomial of the carry's normal form -- 2^n − 1 of them, pairwise
--   distinct -- and adds-sumbit likewise on z_i, with 2^i + 1;
-- * register-carry-terms: any polynomial over the wires written as a
--   list of terms, whose values on those inputs are the carry modulo
--   2, has at least 2^n − 1 terms; adds-carry-terms: in particular any
--   list of terms representing the output polynomial of z_n, modulo
--   2 as an output is read, whatever ξ computing the addition it comes
--   from; adds-top-terms: 2^(n−1) + 1 for the top sum bit.
--   adderˢ-carry-terms and adder₀ˢ-carry-terms are the instances at
--   the specification of section 5.2, in the tool's form and in the
--   paper's.
--
-- * adds-carry-lift, adds-carry-lift-count: if the carry output is
--   Boolean-valued -- a lift, as the specifications' outputs are --
--   its coefficients on the register monomials are exactly those of
--   PathSum.Adder.Expansion.Lift's pseudo-Boolean carry, (3^n − 1)/2
--   of them non-zero; adderˢ-carry-lift and adder₀ˢ-carry-lift are the
--   instances.
--
-- So no classical specification of the adder -- a path-sum without
-- path variables -- has output polynomials of fewer than 2^n − 1 terms,
-- however its polynomials are written.  Nothing here bounds path-sums
-- with path variables: the circuit's own (PathSum.Adder) has linear
-- outputs and, by corollary 2.15 (PathSum.Size), a representation of
-- polynomial size, the carries living in its path variables -- in the
-- spirit of the paper's closing suggestion of outputs as "primed"
-- variables related by equations.  (A remark; not formalised here.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Adder.Expansion.PathSums (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; inject₁; fromℕ)
open import Data.Fin.Properties using (toℕ-fromℕ)
open import Data.Fin.Subset using (Subset)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (zero; suc; _*_; _^_; _≤_; s≤s)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using ([])
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Adder.Binary using
  (maj; add; carry-out; sumbit; add-carry-out; add-sumbit)
open import PathSum.Adder.Expansion using
  (dbl; ix; iy; xs; ys; cmon; smon; carry-anf; sumbit-anf; count-cmon;
   count-smon; nonzero)
open import PathSum.Adder.Expansion.Lift using (cZ; carry-exact; count-cZ)
open import PathSum.Adder.Layout using
  (Wire; xw; yw; zw; Layout; wire; wire-inj)
open import PathSum.Adder.Ripple using
  (xbits; ybits; out?; addition; addition-out)
open import PathSum.Adder.Spec M₀ using
  (adderᵉ; adderˢ; adderˢ-computes; adder₀ᵉ; adder₀ˢ; adder₀ˢ-computes;
   addition₀;
   addition₀-out)
open import PathSum.Assign using (same-refl; [_]ᶻ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; amp-computes; none; outBit-none)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; scale; scale-map; scale-injective; √2·-map;
   √2·-0ᴬ; zpow-0≢0ᴬ)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; hits-elim)
open import PathSum.Mobius using (evalˢ; eval-nested)
open import PathSum.Polynomial using (Poly; Mon; _≟ᵐ_; eval; _≈[_]_)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Boolean using
  (IsBit; BoolValued; BoolValued-liftᵉ)
open import PathSum.Polynomial.Count using (count; count-cong; module Terms)
open import PathSum.Polynomial.Parity using (≡-odd; odd-0; odd-[])
open import PathSum.Polynomial.Properties using (eval-≈)
open import PathSum.Polynomial.Restrict using
  (Injective′; img; ext; restrict; eval-restrict; img-injective; ext-ι;
   ext-off)

private
  variable
    m N k : ℕ


------------------------------------------------------------------------
-- The registers, interleaved

-- Two families of n things, interleaved: a i at 2i, b i at 2i + 1.

pairs : {W : Set} {n : ℕ} → (Fin n → W) → (Fin n → W) → Fin (dbl n) → W
pairs {n = zero}  a b ()
pairs {n = suc n} a b zero          = a zero
pairs {n = suc n} a b (suc zero)    = b zero
pairs {n = suc n} a b (suc (suc p)) =
  pairs (λ j → a (suc j)) (λ j → b (suc j)) p

pairs-ix : {W : Set} {n : ℕ} (a b : Fin n → W) (i : Fin n) →
           pairs a b (ix i) ≡ a i
pairs-ix {n = suc n} a b zero    = refl
pairs-ix {n = suc n} a b (suc i) =
  pairs-ix (λ j → a (suc j)) (λ j → b (suc j)) i

pairs-iy : {W : Set} {n : ℕ} (a b : Fin n → W) (i : Fin n) →
           pairs a b (iy i) ≡ b i
pairs-iy {n = suc n} a b zero    = refl
pairs-iy {n = suc n} a b (suc i) =
  pairs-iy (λ j → a (suc j)) (λ j → b (suc j)) i

-- Every variable is some x_i or some y_i.

ix-or-iy : {n : ℕ} (p : Fin (dbl n)) →
           (∃ λ i → ix i ≡ p) ⊎ (∃ λ i → iy i ≡ p)
ix-or-iy {n = suc n} zero          = inj₁ (zero , refl)
ix-or-iy {n = suc n} (suc zero)    = inj₂ (zero , refl)
ix-or-iy {n = suc n} (suc (suc p)) with ix-or-iy p
... | inj₁ (i , e) = inj₁ (suc i , cong (λ q → suc (suc q)) e)
... | inj₂ (i , e) = inj₂ (suc i , cong (λ q → suc (suc q)) e)

-- The register wires of a layout, x_i at 2i and y_i at 2i + 1.

regs : Layout (Wire false m) N → Fin (dbl (suc m)) → Fin N
regs L p = wire L (pairs xw yw p)

private
  xw-inj : ∀ {i j} → xw {false} {m} i ≡ xw j → i ≡ j
  xw-inj refl = refl

  yw-inj : ∀ {i j} → yw {false} {m} i ≡ yw j → i ≡ j
  yw-inj refl = refl

  -- Where a variable sits: an x or a y wire.

  at : (p : Fin (dbl (suc m))) →
       (∃ λ i → (ix i ≡ p) × (pairs (xw {false} {m}) yw p ≡ xw i)) ⊎
       (∃ λ i → (iy i ≡ p) × (pairs (xw {false} {m}) yw p ≡ yw i))
  at p with ix-or-iy p
  ... | inj₁ (i , refl) = inj₁ (i , refl , pairs-ix xw yw i)
  ... | inj₂ (i , refl) = inj₂ (i , refl , pairs-iy xw yw i)

regs-injective : (L : Layout (Wire false m) N) → Injective′ (regs L)
regs-injective L p q e
  with at p | at q | wire-inj L (pairs xw yw p) (pairs xw yw q) e
... | inj₁ (i , ip , ep) | inj₁ (j , jq , eq) | e′ =
      trans (sym ip)
            (trans (cong ix (xw-inj (trans (sym ep) (trans e′ eq)))) jq)
... | inj₁ (i , ip , ep) | inj₂ (j , jq , eq) | e′ =
      contradiction (trans (sym ep) (trans e′ eq)) λ ()
... | inj₂ (i , ip , ep) | inj₁ (j , jq , eq) | e′ =
      contradiction (trans (sym ep) (trans e′ eq)) λ ()
... | inj₂ (i , ip , ep) | inj₂ (j , jq , eq) | e′ =
      trans (sym ip)
            (trans (cong iy (yw-inj (trans (sym ep) (trans e′ eq)))) jq)

-- The monomial S of the 2n register variables, over the wires.

reg : Layout (Wire false m) N → Subset (dbl (suc m)) → Mon N 0
reg L S = img (regs L) S , []

reg-injective : (L : Layout (Wire false m) N)
                (S S′ : Subset (dbl (suc m))) →
                reg L S ≡ reg L S′ → S ≡ S′
reg-injective L S S′ e =
  img-injective (regs L) (regs-injective L) S S′ (cong proj₁ e)

-- The wire of the carry out, z_n, the last of the output register.

carry-wire : Layout (Wire false m) N → Fin N
carry-wire {m} L = wire L (zw (fromℕ (suc m)))


------------------------------------------------------------------------
-- Inputs that are 0 off the registers

module _ (L : Layout (Wire false m) N) where

  ext-x : (v : Fin (dbl (suc m)) → Bool) (i : Fin (suc m)) →
          ext (regs L) v (wire L (xw i)) ≡ xs v i
  ext-x v i =
    trans (cong (λ w → ext (regs L) v (wire L w)) (sym (pairs-ix xw yw i)))
          (ext-ι (regs L) (regs-injective L) v (ix i))

  ext-y : (v : Fin (dbl (suc m)) → Bool) (i : Fin (suc m)) →
          ext (regs L) v (wire L (yw i)) ≡ ys v i
  ext-y v i =
    trans (cong (λ w → ext (regs L) v (wire L w)) (sym (pairs-iy xw yw i)))
          (ext-ι (regs L) (regs-injective L) v (iy i))

  ext-z : (v : Fin (dbl (suc m)) → Bool) (j : Fin (suc (suc m))) →
          ext (regs L) v (wire L (zw j)) ≡ false
  ext-z v j = ext-off (regs L) v (wire L (zw j)) never
    where
    never : ∀ p → ¬ (regs L p ≡ wire L (zw j))
    never p e with at p
    ... | inj₁ (i , _ , ep) = contradiction
          (trans (sym ep) (wire-inj L (pairs xw yw p) (zw j) e)) λ ()
    ... | inj₂ (i , _ , ep) = contradiction
          (trans (sym ep) (wire-inj L (pairs xw yw p) (zw j) e)) λ ()


------------------------------------------------------------------------
-- Adding

private
  -- Addition reads its operands through their values.

  add-cong : ∀ {n} {a a′ b b′ : Fin n → Bool} →
             (∀ i → a i ≡ a′ i) → (∀ i → b i ≡ b′ i) →
             ∀ c j → add a b c j ≡ add a′ b′ c j
  add-cong {zero}  ha hb c zero    = refl
  add-cong {zero}  ha hb c (suc ())
  add-cong {suc n} ha hb c zero    =
    cong₂ (λ p q → p xor q xor c) (ha zero) (hb zero)
  add-cong {suc n} {a} {a′} {b} {b′} ha hb c (suc j) = trans
    (add-cong (λ i → ha (suc i)) (λ i → hb (suc i))
              (maj (a zero) (b zero) c) j)
    (cong (λ d → add (λ i → a′ (suc i)) (λ i → b′ (suc i)) d j)
          (cong₂ (λ p q → maj p q c) (ha zero) (hb zero)))

  -- A path-sum without path variables that computes F outputs F: its
  -- single path must hit F x, where the amplitude is not 0.  (As
  -- computes-outputs in PathSum.Hardness.Conditional.)

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  scale-0ᴬ : ∀ i → scale i 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    c = refl
  scale-0ᴬ (suc i) c = trans (√2·-map (scale-0ᴬ i) c) (√2·-0ᴬ c)

  computes-outputs : (ξ : PathSum N k 0) {F : Assign N → Assign N} →
                     ξ computes F → ∀ x w → outBit ξ x none w ≡ F x w
  computes-outputs {k = k} ξ {F} c x w =
    at0 (λ ()) (amp-computes c x (F x))
    where
    unit : δ (F x) (F x) ≐ zpow 0ℤ
    unit i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) (same-refl (F x))

    at0 : (y : Assign 0) →
          (if hits ξ x y (F x) then zpow (eval (phase ξ) x y) else 0ᴬ) ≐
          scale k (δ (F x) (F x)) →
          outBit ξ x none w ≡ F x w
    at0 y eq = go (hits ξ x y (F x)) refl
      where
      go : ∀ b → hits ξ x y (F x) ≡ b → outBit ξ x none w ≡ F x w
      go true  h =
        trans (sym (outBit-none ξ x y w)) (hits-elim ξ x y (F x) h w)
      go false h = contradiction
        (scale-injective k (zpow 0ℤ) 0ᴬ
           (≐-sym (scale-map k unit) ∙ ≐-sym eq ∙ gone ∙ ≐-sym (scale-0ᴬ k)))
        zpow-0≢0ᴬ
        where
        gone : (if hits ξ x y (F x) then zpow (eval (phase ξ) x y)
                else 0ᴬ) ≐ 0ᴬ
        gone i =
          cong (λ b → (if b then zpow (eval (phase ξ) x y) else 0ᴬ) i) h

  -- A bit of known parity is known.

  bit-value : ∀ {z} → IsBit z → ∀ b → odd z ≡ b → z ≡ [ b ]ᶻ
  bit-value (inj₁ refl) false _ = refl
  bit-value (inj₁ refl) true  e = contradiction (trans (sym e) odd-0) λ ()
  bit-value (inj₂ refl) true  _ = refl
  bit-value (inj₂ refl) false e =
    contradiction (trans (sym (odd-[] true)) e) λ ()

module _ (L : Layout (Wire false m) N) where

  private
    -- The operands of an input that is 0 off the registers.

    add-ext : (v : Fin (dbl (suc m)) → Bool) (j : Fin (suc (suc m))) →
              add (xbits L (ext (regs L) v)) (ybits L (ext (regs L) v))
                  false j ≡
              add (xs v) (ys v) false j
    add-ext v j = add-cong (ext-x L v) (ext-y L v) false j

  -- ξ adds: on every input that is 0 off the registers its output
  -- register reads the bits of x + y.

  Adds : PathSum N k 0 → Set
  Adds ξ = ∀ (v : Fin (dbl (suc m)) → Bool) (j : Fin (suc (suc m))) →
           odd (eval (out ξ (wire L (zw j))) (ext (regs L) v) none) ≡
           add (xs v) (ys v) false j

  -- So does everything computing the addition, in either form.

  computes-adds : (ξ : PathSum N k 0) → ξ computes addition L → Adds ξ
  computes-adds ξ c v j =
    trans (computes-outputs ξ c (ext (regs L) v) (wire L (zw j)))
    (trans (addition-out L (ext (regs L) v) j)
    (trans (cong (_xor add (xbits L (ext (regs L) v))
                           (ybits L (ext (regs L) v)) false j)
                 (ext-z L v j))
           (add-ext v j)))

  computes₀-adds : (ξ : PathSum N k 0) → ξ computes addition₀ L → Adds ξ
  computes₀-adds ξ c v j =
    trans (computes-outputs ξ c (ext (regs L) v) (wire L (zw j)))
    (trans (addition₀-out L (ext (regs L) v) j) (add-ext v j))

  -- The section 5.2 specifications add.

  adderˢ-adds : Adds (adderˢ L)
  adderˢ-adds = computes-adds (adderˢ L) (adderˢ-computes L)

  adder₀ˢ-adds : Adds (adder₀ˢ L)
  adder₀ˢ-adds = computes₀-adds (adder₀ˢ L) (adder₀ˢ-computes L)


  ----------------------------------------------------------------------
  -- The normal forms on the register monomials

  private
    -- The values of the restriction to the registers.

    values : (P : Poly N 0) (v : Fin (dbl (suc m)) → Bool) →
             evalˢ (λ S → P (reg L S)) v ≡ eval P (ext (regs L) v) none
    values P v = trans (sym (eval-nested (restrict (regs L) P) v none))
                       (eval-restrict (regs L) (regs-injective L) P v none)

  -- A polynomial over the wires whose values on the inputs 0 off the
  -- registers are the carry out has, on the register monomials, the
  -- carry's normal form modulo 2 ...

  register-carry : (P : Poly N 0) →
                   (∀ v → odd (eval P (ext (regs L) v) none) ≡
                          carry-out (xs v) (ys v) false) →
                   ∀ S → odd (P (reg L S)) ≡ cmon S
  register-carry P h = carry-anf (λ S → P (reg L S)) λ v →
    trans (cong odd (values P v)) (h v)

  -- ... likewise for the sum bits ...

  register-sumbit : (i : Fin (suc m)) (P : Poly N 0) →
                    (∀ v → odd (eval P (ext (regs L) v) none) ≡
                           sumbit (xs v) (ys v) false i) →
                    ∀ S → odd (P (reg L S)) ≡ smon i S
  register-sumbit i P h = sumbit-anf i (λ S → P (reg L S)) λ v →
    trans (cong odd (values P v)) (h v)

  -- ... and, if it is Boolean-valued -- a lift, as outputs enter
  -- phases -- it is the pseudo-Boolean carry, (3^n − 1)/2 terms.

  register-carry-lift : (P : Poly N 0) → BoolValued P →
                        (∀ v → odd (eval P (ext (regs L) v) none) ≡
                               carry-out (xs v) (ys v) false) →
                        ∀ S → P (reg L S) ≡ cZ S
  register-carry-lift P bP h = carry-exact (λ S → P (reg L S)) λ v →
    trans (values P v)
          (bit-value (bP (ext (regs L) v) none)
                     (carry-out (xs v) (ys v) false) (h v))

  -- Every path-sum that adds has them in its output polynomials: on
  -- z_n the 2^n − 1 monomials of the carry ...

  adds-carry : (ξ : PathSum N k 0) → Adds ξ →
               ∀ S → odd (out ξ (carry-wire L) (reg L S)) ≡ cmon S
  adds-carry ξ a = register-carry (out ξ (carry-wire L)) λ v →
    trans (a v (fromℕ (suc m))) (add-carry-out (xs v) (ys v) false)

  -- ... and on z_i the 2^i + 1 of the sum bit i.

  adds-sumbit : (ξ : PathSum N k 0) → Adds ξ → (i : Fin (suc m)) →
                ∀ S → odd (out ξ (wire L (zw (inject₁ i))) (reg L S)) ≡
                      smon i S
  adds-sumbit ξ a i =
    register-sumbit i (out ξ (wire L (zw (inject₁ i)))) λ v →
      trans (a v (inject₁ i)) (add-sumbit (xs v) (ys v) false i)

  -- If the carry output is a lift, it is the pseudo-Boolean carry on
  -- the registers, with (3^n − 1)/2 non-zero coefficients there.

  adds-carry-lift : (ξ : PathSum N k 0) → Adds ξ →
                    BoolValued (out ξ (carry-wire L)) →
                    ∀ S → out ξ (carry-wire L) (reg L S) ≡ cZ S
  adds-carry-lift ξ a bP =
    register-carry-lift (out ξ (carry-wire L)) bP λ v →
      trans (a v (fromℕ (suc m))) (add-carry-out (xs v) (ys v) false)

  adds-carry-lift-count :
    (ξ : PathSum N k 0) → Adds ξ → BoolValued (out ξ (carry-wire L)) →
    suc (2 * count (λ S → nonzero (out ξ (carry-wire L) (reg L S)))) ≡
    3 ^ suc m
  adds-carry-lift-count ξ a bP =
    trans (cong (λ c → suc (2 * c))
                (count-cong (λ S → cong nonzero (adds-carry-lift ξ a bP S))))
          (count-cZ {suc m})


  ----------------------------------------------------------------------
  -- Every representation is large

  -- A polynomial over the wires written down as a list of terms.

  ⟦_⟧ᵐ : List (Mon N 0 × ℤ) → Poly N 0
  ⟦_⟧ᵐ = Terms.⟦_⟧ᵗ _≟ᵐ_

  -- If its values on the inputs 0 off the registers are the carry out
  -- modulo 2, it has at least 2^n − 1 terms ...

  register-carry-terms : (ts : List (Mon N 0 × ℤ)) →
                         (∀ v → odd (eval ⟦ ts ⟧ᵐ (ext (regs L) v) none) ≡
                                carry-out (xs v) (ys v) false) →
                         2 ^ suc m ≤ suc (length ts)
  register-carry-terms ts h =
    subst (_≤ suc (length ts)) (count-cmon {suc m})
      (s≤s (Terms.terms-cover _≟ᵐ_ cmon (reg L) (reg-injective L) ts
              (λ S c → trans (register-carry ⟦ ts ⟧ᵐ h S) c)))

  -- ... and if they are the sum bit i, at least 2^i + 1.

  register-sumbit-terms : (i : Fin (suc m)) (ts : List (Mon N 0 × ℤ)) →
                          (∀ v → odd (eval ⟦ ts ⟧ᵐ (ext (regs L) v) none) ≡
                                 sumbit (xs v) (ys v) false i) →
                          suc (2 ^ toℕ i) ≤ length ts
  register-sumbit-terms i ts h = subst (_≤ length ts) (count-smon i)
    (Terms.terms-cover _≟ᵐ_ (smon i) (reg L) (reg-injective L) ts
       (λ S c → trans (register-sumbit i ⟦ ts ⟧ᵐ h S) c))

  -- So every list of terms representing the carry output of a path-sum
  -- that adds -- the output polynomial read modulo 2, as outputs are --
  -- has at least 2^n − 1 terms ...

  private
    agree : (ξ : PathSum N k 0) (w : Fin N) (ts : List (Mon N 0 × ℤ)) →
            ⟦ ts ⟧ᵐ ≈[ + 2 ] out ξ w → ∀ x →
            odd (eval ⟦ ts ⟧ᵐ x none) ≡ odd (eval (out ξ w) x none)
    agree ξ w ts r x =
      ≡-odd (eval ⟦ ts ⟧ᵐ x none) (eval (out ξ w) x none)
            (eval-≈ ⟦ ts ⟧ᵐ (out ξ w) r x none)

  adds-carry-terms : (ξ : PathSum N k 0) → Adds ξ →
                     (ts : List (Mon N 0 × ℤ)) →
                     ⟦ ts ⟧ᵐ ≈[ + 2 ] out ξ (carry-wire L) →
                     2 ^ suc m ≤ suc (length ts)
  adds-carry-terms ξ a ts r = register-carry-terms ts λ v →
    trans (agree ξ (carry-wire L) ts r (ext (regs L) v))
          (trans (a v (fromℕ (suc m))) (add-carry-out (xs v) (ys v) false))

  -- ... that of the sum bit i at least 2^i + 1, the top one 2^(n−1) + 1.

  adds-sumbit-terms : (ξ : PathSum N k 0) → Adds ξ → (i : Fin (suc m))
                      (ts : List (Mon N 0 × ℤ)) →
                      ⟦ ts ⟧ᵐ ≈[ + 2 ] out ξ (wire L (zw (inject₁ i))) →
                      suc (2 ^ toℕ i) ≤ length ts
  adds-sumbit-terms ξ a i ts r = register-sumbit-terms i ts λ v →
    trans (agree ξ (wire L (zw (inject₁ i))) ts r (ext (regs L) v))
          (trans (a v (inject₁ i)) (add-sumbit (xs v) (ys v) false i))

  adds-top-terms : (ξ : PathSum N k 0) → Adds ξ →
                   (ts : List (Mon N 0 × ℤ)) →
                   ⟦ ts ⟧ᵐ ≈[ + 2 ] out ξ (wire L (zw (inject₁ (fromℕ m)))) →
                   suc (2 ^ m) ≤ length ts
  adds-top-terms ξ a ts r =
    subst (λ t → suc (2 ^ t) ≤ length ts) (toℕ-fromℕ m)
          (adds-sumbit-terms ξ a (fromℕ m) ts r)

  -- The specification of section 5.2, in the tool's form (the output
  -- register gains x + y) and in the paper's (it is overwritten by it):
  -- every list of terms representing its carry output has at least
  -- 2^n − 1 terms; and the carry output itself, a lift, has exactly
  -- (3^n − 1)/2 non-zero coefficients on the register monomials.

  adderˢ-carry-terms : (ts : List (Mon N 0 × ℤ)) →
                       ⟦ ts ⟧ᵐ ≈[ + 2 ] out (adderˢ L) (carry-wire L) →
                       2 ^ suc m ≤ suc (length ts)
  adderˢ-carry-terms = adds-carry-terms (adderˢ L) adderˢ-adds

  adder₀ˢ-carry-terms : (ts : List (Mon N 0 × ℤ)) →
                        ⟦ ts ⟧ᵐ ≈[ + 2 ] out (adder₀ˢ L) (carry-wire L) →
                        2 ^ suc m ≤ suc (length ts)
  adder₀ˢ-carry-terms = adds-carry-terms (adder₀ˢ L) adder₀ˢ-adds

  adderˢ-carry-lift :
    suc (2 * count (λ S → nonzero (out (adderˢ L) (carry-wire L) (reg L S))))
    ≡ 3 ^ suc m
  adderˢ-carry-lift =
    adds-carry-lift-count (adderˢ L) adderˢ-adds
      (BoolValued-liftᵉ (adderᵉ L (carry-wire L) (out? L (carry-wire L))))

  adder₀ˢ-carry-lift :
    suc (2 * count (λ S → nonzero (out (adder₀ˢ L) (carry-wire L) (reg L S))))
    ≡ 3 ^ suc m
  adder₀ˢ-carry-lift =
    adds-carry-lift-count (adder₀ˢ L) adder₀ˢ-adds
      (BoolValued-liftᵉ (adder₀ᵉ L (carry-wire L) (out? L (carry-wire L))))
