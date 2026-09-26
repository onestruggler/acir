------------------------------------------------------------------------
-- Presentations of groups
--
-- The miter of a Clifford circuit (Amy, QPL 2018, section 3)
--
-- Section 3 reduces checking a circuit C against a specification ξ to
-- checking that the miter ⟦ C† ⟧ ∘ ξ is the identity.  The reduction
-- rests on one fact: C† inverts C.  Here that is proved on the
-- matrices of PathSum.CircuitSemantics, a column at a time, and gate
-- by gate, with no appeal to unitarity: H H = 2, S S S S = 1 and
-- CZ CZ = 1 as unnormalised matrices, so C† C and C C† are 2^k, k the
-- number of Hadamards in C (†-cancelʳ, †-cancelˡ).
--
-- Two facts about the matrices carry the rest.  The gates of a circuit
-- run first to last, so C ++ D acts as C then D.  And a circuit
-- commutes with any map on amplitudes that is additive and commutes
-- with rotations, applied entry by entry (PathSum.AmpLinear); the
-- normalisations √2^k and 2^k are such maps, so they can be moved
-- through a circuit.  With these, the miter at one pair of columns is
-- miterᶜ: a column ψ with normalisation k is C applied to the column φ
-- exactly when C† sends ψ back to φ, the normalisations of ψ and of C
-- both carried over to φ's side.
--
-- The cancellations need the column to see assignments only through
-- their values (Respects): H H reads z[w≔b][w≔b′] where it should read
-- z[w≔b′], and assignments are functions, equal only pointwise.
--
-- Read at the basis columns through proposition 2.10, miterᶜ gives
-- the headline results.  spec-miter: ⟦ C ⟧ ≋ ξ exactly when C† sends
-- every column of ξ to the matching basis column, scaled by the
-- normalisations of ξ and C.  This holds for any path-sum ξ, well
-- formed or not.  miter: two circuits are equivalent exactly when
-- ⟦ C₁ ++ C₂ † ⟧ ≋ idPS.  The paper's miter ⟦ C₂† ⟧ ∘ ⟦ C₁ ⟧ runs C₁
-- first, so for two circuits it is the circuit C₁ ++ C₂ †, and no
-- composition of path-sums is needed.  Consequences: C† is a
-- two-sided inverse and an involution up to ≋, and appending a
-- circuit on the right both preserves and reflects ≋ (++-congʳ,
-- ++-cancelʳ).
--
-- The paper's miter against a general ξ is a composition of path-sums
-- (definition 2.6).  Here ⟦ C† ⟧ ∘ ξ appears only as C† acting on the
-- columns of ξ; the composite itself is PathSum.Miter.Compose
-- (spec-miter-∘), which also shows that prepending a circuit respects
-- and reflects ≋ (++-congˡ, ++-cancelˡ; see ++-congʳ for why that
-- needs composition).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Miter (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityˡ; *-identityˡ; *-identityʳ; *-zeroʳ; neg-involutive)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint M using (inv; _†; norm-++; norm-†)
open import PathSum.AmpLinear M₀ using
  (Linear; ·ᴬ-linear; scale-linear; scale-+; scale-exp; scale-comm;
   scale-twice; pow-·ᴬ)
open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-≔; ≔-self)
open import PathSum.Base using (PathSum; idPS)
open import PathSum.Circuit M using (Gate; H; S; CZ; Circuit; norm; ⟦_⟧)
open import PathSum.CircuitSemantics M₀ using
  (Column; δ; gateᴬ; applyᴬ; prop-2-10; δ-resp; gateᴬ-resp;
   applyᴬ-resp; applyᴬ-cong; sign-0; sign-1)
open import PathSum.Corollary M₀ using (circuit-≋-id)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; _+ᴬ_; _-ᴬ_; _·ᴬ_; rot; rot-map; rot-exp; rot-comp; rot-0;
   rot-anti; scale; scale-map; scale-injective; Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using
  (amp; _≋_; ≋-refl; ≋-sym; ≋-trans; amp-≗)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Reduction M using (¼; ½)

import Data.Nat.Properties as ℕ

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Circuits commute with linear maps

-- A gate builds each new entry from old ones by sums and rotations, so
-- a linear map applied to every entry before the gate may as well be
-- applied after it.

gateᴬ-linear : ∀ {f} → Linear f → (g : Gate n) (ψ : Column n) →
               ∀ z → gateᴬ g (λ u → f (ψ u)) z ≐ f (gateᴬ g ψ z)
gateᴬ-linear {f = f} lin (H w) ψ z i =
  trans (cong (λ u → f (ψ (z [ w ≔ false ])) i + u)
              (sym (Linear.map-rot lin (½ * [ z w ]ᶻ)
                                   (ψ (z [ w ≔ true ])) i)))
        (sym (Linear.map-+ᴬ lin (ψ (z [ w ≔ false ]))
               (rot (½ * [ z w ]ᶻ) (ψ (z [ w ≔ true ]))) i))
gateᴬ-linear lin (S w)    ψ z i =
  sym (Linear.map-rot lin (¼ * [ z w ]ᶻ) (ψ z) i)
gateᴬ-linear lin (CZ w v) ψ z i =
  sym (Linear.map-rot lin (½ * [ z w ∧ z v ]ᶻ) (ψ z) i)

applyᴬ-linear : ∀ {f} → Linear f → (C : Circuit n) (ψ : Column n) →
                ∀ z → applyᴬ C (λ u → f (ψ u)) z ≐ f (applyᴬ C ψ z)
applyᴬ-linear         lin []      ψ z _ = refl
applyᴬ-linear {f = f} lin (g ∷ C) ψ z i =
  trans (applyᴬ-cong C {gateᴬ g (λ u → f (ψ u))} {λ u → f (gateᴬ g ψ u)}
                     (gateᴬ-linear lin g ψ) z i)
        (applyᴬ-linear lin C (gateᴬ g ψ) z i)


------------------------------------------------------------------------
-- Concatenation

-- The gates of C ++ D act first to last: those of C, then those of D.

applyᴬ-++ : (C D : Circuit n) (ψ : Column n) →
            applyᴬ (C ++ D) ψ ≡ applyᴬ D (applyᴬ C ψ)
applyᴬ-++ []      D ψ = refl
applyᴬ-++ (g ∷ C) D ψ = applyᴬ-++ C D (gateᴬ g ψ)

private
  -- The same, at one entry.

  ++-at : (C D : Circuit n) (ψ : Column n) →
          ∀ z → applyᴬ (C ++ D) ψ z ≐ applyᴬ D (applyᴬ C ψ) z
  ++-at C D ψ z i = cong (λ F → F z i) (applyᴬ-++ C D ψ)


------------------------------------------------------------------------
-- Rotation cycles

-- S⁴ = 1 and CZ² = 1: at a wire value 0 every rotation is by 0, and at
-- 1 the rotations add up to 2H = N, the order of ζ, which is two
-- negations.  The wire value is taken as an argument b and its
-- equation, so that each exponent is met only syntactically, and
-- changed only by rot-exp.

private
  ¼+¼ : ¼ + ¼ ≡ ½
  ¼+¼ = trans (double ¼) (sym (pow-suc (suc M₀)))
    where
    double : ∀ u → u + u ≡ u * (+ 2)
    double = solve 1 (λ u → u :+ u := u :* con (+ 2)) refl

  four-¼ : ∀ q → q ≡ ¼ → q + (q + (q + q)) ≡ (0ℤ + ½) + ½
  four-¼ q eq =
    trans (cong (λ u → u + (u + (u + u))) eq)
      (trans (regroup ¼)
        (trans (cong (λ u → u + u) ¼+¼)
               (cong (λ u → u + ½) (sym (+-identityˡ ½)))))
    where
    regroup : ∀ u → u + (u + (u + u)) ≡ (u + u) + (u + u)
    regroup = solve 1 (λ u → u :+ (u :+ (u :+ u)) := (u :+ u) :+ (u :+ u))
                refl

  two-½ : ∀ q → q ≡ ½ → q + q ≡ (0ℤ + ½) + ½
  two-½ q eq = trans (cong (λ u → u + u) eq)
                     (cong (λ u → u + ½) (sym (+-identityˡ ½)))

  -- ζ^N = 1, as two negations.

  rot-N : (a : Amp) → rot ((0ℤ + (+ rank)) + (+ rank)) a ≐ a
  rot-N a i =
    trans (rot-anti (0ℤ + (+ rank)) a i)
      (trans (cong -_ (rot-anti 0ℤ a i))
        (trans (neg-involutive (rot 0ℤ a i)) (rot-0 a i)))

  cycle⁴ : (e : ℤ) (b : Bool) → e ≡ ¼ * [ b ]ᶻ → (a : Amp) →
           rot (e + (e + (e + e))) a ≐ a
  cycle⁴ e false eq a i =
    trans (rot-exp {e + (e + (e + e))} {0ℤ} a
                   (cong (λ u → u + (u + (u + u)))
                         (trans eq (*-zeroʳ ¼))) i)
          (rot-0 a i)
  cycle⁴ e true  eq a i =
    trans (rot-exp {e + (e + (e + e))} {(0ℤ + (+ rank)) + (+ rank)} a
                   (four-¼ e (trans eq (*-identityʳ ¼))) i)
          (rot-N a i)

  cycle² : (e : ℤ) (b : Bool) → e ≡ ½ * [ b ]ᶻ → (a : Amp) →
           rot (e + e) a ≐ a
  cycle² e false eq a i =
    trans (rot-exp {e + e} {0ℤ} a
                   (cong (λ u → u + u) (trans eq (*-zeroʳ ½))) i)
          (rot-0 a i)
  cycle² e true  eq a i =
    trans (rot-exp {e + e} {(0ℤ + (+ rank)) + (+ rank)} a
                   (two-½ e (trans eq (*-identityʳ ½))) i)
          (rot-N a i)

  -- Folding the rotations into one.

  fold⁴ : (e : ℤ) (a : Amp) →
          rot e (rot e (rot e (rot e a))) ≐ rot (e + (e + (e + e))) a
  fold⁴ e a i =
    trans (rot-map e (rot-map e (rot-comp e e a)) i)
      (trans (rot-map e (rot-comp e (e + e) a) i)
             (rot-comp e (e + (e + e)) a i))

  rot⁴ : (b : Bool) (a : Amp) →
         rot (¼ * [ b ]ᶻ) (rot (¼ * [ b ]ᶻ)
           (rot (¼ * [ b ]ᶻ) (rot (¼ * [ b ]ᶻ) a))) ≐ a
  rot⁴ b a i =
    trans (fold⁴ (¼ * [ b ]ᶻ) a i) (cycle⁴ (¼ * [ b ]ᶻ) b refl a i)

  rot² : (b : Bool) (a : Amp) →
         rot (½ * [ b ]ᶻ) (rot (½ * [ b ]ᶻ) a) ≐ a
  rot² b a i =
    trans (rot-comp (½ * [ b ]ᶻ) (½ * [ b ]ᶻ) a i)
          (cycle² (½ * [ b ]ᶻ) b refl a i)


------------------------------------------------------------------------
-- H H = 2

-- The inner Hadamard sends the entries a and b at z[w≔0] and z[w≔1]
-- to a + b and a - b there, and the outer one adds the two, or
-- subtracts them, according as z_w is 0 or 1: 2a or 2b, twice the
-- old entry at z.

private
  sum-diff : ∀ p q → (p + q) + (p - q) ≡ (+ 2) * p
  sum-diff = solve 2 (λ p q → (p :+ q) :+ (p :- q) := con (+ 2) :* p) refl

  diff-diff : ∀ p q → (p + q) - (p - q) ≡ (+ 2) * q
  diff-diff = solve 2 (λ p q → (p :+ q) :- (p :- q) := con (+ 2) :* q)
                refl

HH : (w : Fin n) (ψ : Column n) → Respects ψ →
     ∀ z → gateᴬ (H w) (gateᴬ (H w) ψ) z ≐ (+ 2) ·ᴬ ψ z
HH w ψ resp z = at (z w) refl
  where
  e₀ : ½ * [ (z [ w ≔ false ]) w ]ᶻ ≡ 0ℤ
  e₀ = trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w false)) (*-zeroʳ ½)

  e₁ : ½ * [ (z [ w ≔ true ]) w ]ᶻ ≡ 0ℤ + (+ rank)
  e₁ = trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w true))
             (trans (*-identityʳ ½) (sym (+-identityˡ ½)))

  -- The inner Hadamard, at the two assignments the outer one reads.

  in₀ : gateᴬ (H w) ψ (z [ w ≔ false ]) ≐
        (ψ (z [ w ≔ false ]) +ᴬ ψ (z [ w ≔ true ]))
  in₀ = sign-0 (ψ (z [ w ≔ false ] [ w ≔ false ])) (ψ (z [ w ≔ false ]))
               (ψ (z [ w ≔ false ] [ w ≔ true ])) (ψ (z [ w ≔ true ]))
               (½ * [ (z [ w ≔ false ]) w ]ᶻ)
               (resp _ _ (≔-≔ z w false false)) e₀
               (resp _ _ (≔-≔ z w false true))

  in₁ : gateᴬ (H w) ψ (z [ w ≔ true ]) ≐
        (ψ (z [ w ≔ false ]) -ᴬ ψ (z [ w ≔ true ]))
  in₁ = sign-1 (ψ (z [ w ≔ true ] [ w ≔ false ])) (ψ (z [ w ≔ false ]))
               (ψ (z [ w ≔ true ] [ w ≔ true ])) (ψ (z [ w ≔ true ]))
               (½ * [ (z [ w ≔ true ]) w ]ᶻ)
               (resp _ _ (≔-≔ z w true false)) e₁
               (resp _ _ (≔-≔ z w true true))

  -- Writing z's own value on w back gives z.

  back : (b : Bool) → z w ≡ b → ψ (z [ w ≔ b ]) ≐ ψ z
  back b eq = resp (z [ w ≔ b ]) z (λ j →
    trans (cong (λ u → (z [ w ≔ u ]) j) (sym eq)) (≔-self z w j))

  at : (b : Bool) → z w ≡ b →
       gateᴬ (H w) (gateᴬ (H w) ψ) z ≐ (+ 2) ·ᴬ ψ z
  at false eq i =
    trans (sign-0 (gateᴬ (H w) ψ (z [ w ≔ false ]))
                  (ψ (z [ w ≔ false ]) +ᴬ ψ (z [ w ≔ true ]))
                  (gateᴬ (H w) ψ (z [ w ≔ true ]))
                  (ψ (z [ w ≔ false ]) -ᴬ ψ (z [ w ≔ true ]))
                  (½ * [ z w ]ᶻ) in₀
                  (trans (cong (λ b → ½ * [ b ]ᶻ) eq) (*-zeroʳ ½)) in₁ i)
      (trans (sum-diff (ψ (z [ w ≔ false ]) i) (ψ (z [ w ≔ true ]) i))
             (cong (λ u → (+ 2) * u) (back false eq i)))
  at true  eq i =
    trans (sign-1 (gateᴬ (H w) ψ (z [ w ≔ false ]))
                  (ψ (z [ w ≔ false ]) +ᴬ ψ (z [ w ≔ true ]))
                  (gateᴬ (H w) ψ (z [ w ≔ true ]))
                  (ψ (z [ w ≔ false ]) -ᴬ ψ (z [ w ≔ true ]))
                  (½ * [ z w ]ᶻ) in₀
                  (trans (cong (λ b → ½ * [ b ]ᶻ) eq)
                         (trans (*-identityʳ ½) (sym (+-identityˡ ½))))
                  in₁ i)
      (trans (diff-diff (ψ (z [ w ≔ false ]) i) (ψ (z [ w ≔ true ]) i))
             (cong (λ u → (+ 2) * u) (back true eq i)))


------------------------------------------------------------------------
-- Each gate is inverted by inv

-- On both sides, up to the gate's own normalisation: 2 for a
-- Hadamard, 1 for S and CZ.  After the split on the gate, inv g after
-- g and g after inv g are the same matrix.

inv-cancelʳ : (g : Gate n) (ψ : Column n) → Respects ψ →
              ∀ z → applyᴬ (inv g) (gateᴬ g ψ) z ≐
                    pow (norm (g ∷ [])) ·ᴬ ψ z
inv-cancelʳ (H w)    ψ resp z   = HH w ψ resp z
inv-cancelʳ (S w)    ψ resp z i =
  trans (rot⁴ (z w) (ψ z) i) (sym (*-identityˡ (ψ z i)))
inv-cancelʳ (CZ w v) ψ resp z i =
  trans (rot² (z w ∧ z v) (ψ z) i) (sym (*-identityˡ (ψ z i)))

inv-cancelˡ : (g : Gate n) (ψ : Column n) → Respects ψ →
              ∀ z → gateᴬ g (applyᴬ (inv g) ψ) z ≐
                    pow (norm (g ∷ [])) ·ᴬ ψ z
inv-cancelˡ (H w)    ψ resp z   = HH w ψ resp z
inv-cancelˡ (S w)    ψ resp z i =
  trans (rot⁴ (z w) (ψ z) i) (sym (*-identityˡ (ψ z i)))
inv-cancelˡ (CZ w v) ψ resp z i =
  trans (rot² (z w ∧ z v) (ψ z) i) (sym (*-identityˡ (ψ z i)))


------------------------------------------------------------------------
-- C† inverts C

-- By induction on C, peeling its first gate g: C† ends with inv g, so
-- inv g is the first thing to meet g on one side, and the last on the
-- other.  The normalisation 2^(norm C) accumulated so far is an integer
-- multiple, and passes through the remaining gates by linearity.

†-cancelʳ : (C : Circuit n) (ψ : Column n) → Respects ψ →
            ∀ z → applyᴬ (C †) (applyᴬ C ψ) z ≐ pow (norm C) ·ᴬ ψ z
†-cancelʳ []      ψ resp z i = sym (*-identityˡ (ψ z i))
†-cancelʳ (g ∷ C) ψ resp z i =
  trans (cong (λ F → F z i)
              (applyᴬ-++ (C †) (inv g) (applyᴬ C (gateᴬ g ψ))))
  (trans (applyᴬ-cong (inv g) {applyᴬ (C †) (applyᴬ C (gateᴬ g ψ))}
                      {λ u → pow (norm C) ·ᴬ gateᴬ g ψ u}
                      (†-cancelʳ C (gateᴬ g ψ) (gateᴬ-resp g resp)) z i)
  (trans (applyᴬ-linear (·ᴬ-linear (pow (norm C))) (inv g) (gateᴬ g ψ)
                        z i)
  (trans (cong (λ u → pow (norm C) * u) (inv-cancelʳ g ψ resp z i))
  (trans (pow-·ᴬ (norm C) (norm (g ∷ [])) (ψ z) i)
         (cong (λ k → pow k * ψ z i)
               (trans (ℕ.+-comm (norm C) (norm (g ∷ [])))
                      (sym (norm-++ (g ∷ []) C))))))))

†-cancelˡ : (C : Circuit n) (ψ : Column n) → Respects ψ →
            ∀ z → applyᴬ C (applyᴬ (C †) ψ) z ≐ pow (norm C) ·ᴬ ψ z
†-cancelˡ []      ψ resp z i = sym (*-identityˡ (ψ z i))
†-cancelˡ (g ∷ C) ψ resp z i =
  trans (cong (λ F → applyᴬ C (gateᴬ g F) z i)
              (applyᴬ-++ (C †) (inv g) ψ))
  (trans (applyᴬ-cong C {gateᴬ g (applyᴬ (inv g) (applyᴬ (C †) ψ))}
                      {λ u → pow (norm (g ∷ [])) ·ᴬ applyᴬ (C †) ψ u}
                      (inv-cancelˡ g (applyᴬ (C †) ψ)
                                   (applyᴬ-resp (C †) resp)) z i)
  (trans (applyᴬ-linear (·ᴬ-linear (pow (norm (g ∷ [])))) C
                        (applyᴬ (C †) ψ) z i)
  (trans (cong (λ u → pow (norm (g ∷ [])) * u) (†-cancelˡ C ψ resp z i))
  (trans (pow-·ᴬ (norm (g ∷ [])) (norm C) (ψ z) i)
         (cong (λ k → pow k * ψ z i) (sym (norm-++ (g ∷ []) C)))))))


------------------------------------------------------------------------
-- The miter at one pair of columns

-- ψ is a column read with normalisation 1/√2^k, φ one fed to C, which
-- normalises by 1/√2^j, j = norm C.  That ψ is C applied to φ says
-- √2^j ψ = √2^k C φ, cross-multiplied as PathSum.Denotation's ≋ is.
-- Applying C† and cancelling C† C = 2^j = √2^j √2^j turns this into
-- C† ψ = √2^(k+j) φ, and applying C and cancelling C C† turns it back:
-- both directions end with an equation between multiples by √2^j,
-- which cancel (Cyclotomic's scale-injective).

miterᶜ : (C : Circuit n) (k : ℕ) (ψ φ : Column n) → Respects ψ →
         Respects φ →
         ((∀ z → scale (norm C) (ψ z) ≐ scale k (applyᴬ C φ z)) ⇔
          (∀ z → applyᴬ (C †) ψ z ≐ scale (k ℕ+ norm C) (φ z)))
miterᶜ C k ψ φ rψ rφ = mk⇔ to from
  where
  to : (∀ z → scale (norm C) (ψ z) ≐ scale k (applyᴬ C φ z)) →
       ∀ z → applyᴬ (C †) ψ z ≐ scale (k ℕ+ norm C) (φ z)
  to E z = scale-injective (norm C) (applyᴬ (C †) ψ z)
                           (scale (k ℕ+ norm C) (φ z)) chain
    where
    chain : scale (norm C) (applyᴬ (C †) ψ z) ≐
            scale (norm C) (scale (k ℕ+ norm C) (φ z))
    chain i =
      trans (sym (applyᴬ-linear (scale-linear (norm C)) (C †) ψ z i))
      (trans (applyᴬ-cong (C †) {λ u → scale (norm C) (ψ u)}
                          {λ u → scale k (applyᴬ C φ u)} E z i)
      (trans (applyᴬ-linear (scale-linear k) (C †) (applyᴬ C φ) z i)
      (trans (scale-map k (†-cancelʳ C φ rφ z) i)
      (trans (sym (scale-map k (scale-twice (norm C) (φ z)) i))
      (trans (scale-+ k (norm C) (scale (norm C) (φ z)) i)
             (scale-comm (k ℕ+ norm C) (norm C) (φ z) i))))))

  from : (∀ z → applyᴬ (C †) ψ z ≐ scale (k ℕ+ norm C) (φ z)) →
         ∀ z → scale (norm C) (ψ z) ≐ scale k (applyᴬ C φ z)
  from F z = scale-injective (norm C) (scale (norm C) (ψ z))
                             (scale k (applyᴬ C φ z)) chain
    where
    chain : scale (norm C) (scale (norm C) (ψ z)) ≐
            scale (norm C) (scale k (applyᴬ C φ z))
    chain i =
      trans (scale-twice (norm C) (ψ z) i)
      (trans (sym (†-cancelˡ C ψ rψ z i))
      (trans (applyᴬ-cong C {applyᴬ (C †) ψ}
                          {λ u → scale (k ℕ+ norm C) (φ u)} F z i)
      (trans (applyᴬ-linear (scale-linear (k ℕ+ norm C)) C φ z i)
      (trans (sym (scale-+ k (norm C) (applyᴬ C φ z) i))
             (scale-comm k (norm C) (applyᴬ C φ z) i)))))


------------------------------------------------------------------------
-- Circuits against circuits, on matrices

-- ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ multiplies each side by the other's normalisation;
-- by proposition 2.10 it says the same of the circuits' matrices,
-- column by column.

circuit-≋ : (C₁ C₂ : Circuit n) →
            (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔
             (∀ x z → scale (norm C₂) (applyᴬ C₁ (δ x) z) ≐
                      scale (norm C₁) (applyᴬ C₂ (δ x) z)))
circuit-≋ C₁ C₂ = mk⇔
  (λ eq x z i → trans (sym (scale-map (norm C₂) (prop-2-10 C₁ x z) i))
    (trans (eq x z i) (scale-map (norm C₁) (prop-2-10 C₂ x z) i)))
  (λ eq x z i → trans (scale-map (norm C₂) (prop-2-10 C₁ x z) i)
    (trans (eq x z i) (sym (scale-map (norm C₁) (prop-2-10 C₂ x z) i))))


------------------------------------------------------------------------
-- The miter against a specification

-- Section 3: ⟦ C ⟧ ≡ ξ exactly when C† undoes ξ, with ξ's normalisation
-- and C's both carried to the other side.  Stated on columns -- C†
-- applied to each column of ξ gives the basis column -- since the
-- composition ⟦ C† ⟧ ∘ ξ is not formalised.  Nothing is assumed of ξ:
-- the columns of any path-sum see assignments only through their
-- values (Denotation's amp-≗), which is all miterᶜ needs.

spec-miter : (C : Circuit n) (ξ : PathSum n k m) →
             (⟦ C ⟧ ≋ ξ ⇔
              (∀ x z → applyᴬ (C †) (amp ξ x) z ≐
                       scale (k ℕ+ norm C) (δ x z)))
spec-miter {k = k} C ξ = mk⇔
  (λ eq x → Equivalence.to (at x) (λ z i →
     trans (sym (eq x z i)) (scale-map k (prop-2-10 C x z) i)))
  (λ eq x z i → trans (scale-map k (prop-2-10 C x z) i)
     (sym (Equivalence.from (at x) (eq x) z i)))
  where
  at : ∀ x →
       (∀ z → scale (norm C) (amp ξ x z) ≐ scale k (applyᴬ C (δ x) z)) ⇔
       (∀ z → applyᴬ (C †) (amp ξ x) z ≐ scale (k ℕ+ norm C) (δ x z))
  at x = miterᶜ C k (amp ξ x) (δ x)
                (λ z z′ zz → amp-≗ ξ x {z} {z′} zz) (δ-resp x)


------------------------------------------------------------------------
-- The miter of two circuits

-- The paper's miter ⟦ C₂† ⟧ ∘ ⟦ C₁ ⟧ runs C₁ first, so it is the
-- circuit C₁ ++ C₂ †, interpreted directly: no composition of
-- path-sums is needed.  Its normalisation is the two circuits'
-- together, which the identity must match.

private
  norm-miter : (C₁ C₂ : Circuit n) →
               norm C₁ ℕ+ norm C₂ ≡ norm (C₁ ++ C₂ †)
  norm-miter C₁ C₂ =
    sym (trans (norm-++ C₁ (C₂ †))
               (cong (λ u → norm C₁ ℕ+ u) (norm-† C₂)))

miter : (C₁ C₂ : Circuit n) → (⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ ⇔ ⟦ C₁ ++ C₂ † ⟧ ≋ idPS)
miter C₁ C₂ = mk⇔ to from
  where
  -- miterᶜ at the column C₁ makes of each basis state.

  at : ∀ x →
       (∀ z → scale (norm C₂) (applyᴬ C₁ (δ x) z) ≐
              scale (norm C₁) (applyᴬ C₂ (δ x) z)) ⇔
       (∀ z → applyᴬ (C₂ †) (applyᴬ C₁ (δ x)) z ≐
              scale (norm C₁ ℕ+ norm C₂) (δ x z))
  at x = miterᶜ C₂ (norm C₁) (applyᴬ C₁ (δ x)) (δ x)
                (applyᴬ-resp C₁ (δ-resp x)) (δ-resp x)

  to : ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ → ⟦ C₁ ++ C₂ † ⟧ ≋ idPS
  to eq = Equivalence.from (circuit-≋-id (C₁ ++ C₂ †)) (λ x z i →
    trans (++-at C₁ (C₂ †) (δ x) z i)
      (trans (Equivalence.to (at x)
                (Equivalence.to (circuit-≋ C₁ C₂) eq x) z i)
             (scale-exp (δ x z) (norm-miter C₁ C₂) i)))

  from : ⟦ C₁ ++ C₂ † ⟧ ≋ idPS → ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧
  from eq = Equivalence.from (circuit-≋ C₁ C₂) (λ x →
    Equivalence.from (at x) (λ z i →
      trans (sym (++-at C₁ (C₂ †) (δ x) z i))
        (trans (Equivalence.to (circuit-≋-id (C₁ ++ C₂ †)) eq x z i)
               (sym (scale-exp (δ x z) (norm-miter C₁ C₂) i)))))


------------------------------------------------------------------------
-- C† is a two-sided inverse, and an involution, up to ≋

-- On the right it is the miter of C against itself; on the left it is
-- †-cancelˡ at the basis columns.

†-inverseʳ : (C : Circuit n) → ⟦ C ++ C † ⟧ ≋ idPS
†-inverseʳ C = Equivalence.to (miter C C) (≋-refl {ξ = ⟦ C ⟧})

†-inverseˡ : (C : Circuit n) → ⟦ C † ++ C ⟧ ≋ idPS
†-inverseˡ C = Equivalence.from (circuit-≋-id (C † ++ C)) (λ x z i →
  trans (++-at (C †) C (δ x) z i)
  (trans (†-cancelˡ C (δ x) (δ-resp x) z i)
  (trans (sym (scale-twice (norm C) (δ x z) i))
  (trans (scale-+ (norm C) (norm C) (δ x z) i)
         (scale-exp (δ x z) norm-twice i)))))
  where
  norm-twice : norm C ℕ+ norm C ≡ norm (C † ++ C)
  norm-twice = sym (trans (norm-++ (C †) C)
                          (cong (λ u → u ℕ+ norm C) (norm-† C)))

-- C † † is C again as an operator (not as a list: S† † is S⁹).

†-involutive : (C : Circuit n) → ⟦ C † † ⟧ ≋ ⟦ C ⟧
†-involutive C = Equivalence.from (miter (C † †) C) (†-inverseˡ (C †))


------------------------------------------------------------------------
-- Appending a circuit respects ≋

-- The circuit D appended after C and C′ commutes with the
-- normalisations, so it carries their equation along.  The other
-- side, D ++ C against D ++ C′, is not proved here: there C and C′
-- act on the columns of D, which are not basis states, and
-- ⟦ C ⟧ ≋ ⟦ C′ ⟧ speaks only of basis states.  Composition of
-- path-sums reads those columns path by path, and
-- PathSum.Miter.Compose's ++-congˡ proves it that way.

++-congʳ : (C C′ D : Circuit n) → ⟦ C ⟧ ≋ ⟦ C′ ⟧ →
           ⟦ C ++ D ⟧ ≋ ⟦ C′ ++ D ⟧
++-congʳ C C′ D eq =
  Equivalence.from (circuit-≋ (C ++ D) (C′ ++ D)) cols
  where
  E : ∀ x z → scale (norm C′) (applyᴬ C (δ x) z) ≐
              scale (norm C) (applyᴬ C′ (δ x) z)
  E = Equivalence.to (circuit-≋ C C′) eq

  -- Through D, at the columns of C and C′ on the basis state x.

  through : ∀ x z →
            scale (norm C′) (applyᴬ D (applyᴬ C (δ x)) z) ≐
            scale (norm C) (applyᴬ D (applyᴬ C′ (δ x)) z)
  through x z i =
    trans (sym (applyᴬ-linear (scale-linear (norm C′)) D
                              (applyᴬ C (δ x)) z i))
      (trans (applyᴬ-cong D {λ u → scale (norm C′) (applyᴬ C (δ x) u)}
                            {λ u → scale (norm C) (applyᴬ C′ (δ x) u)}
                            (E x) z i)
             (applyᴬ-linear (scale-linear (norm C)) D
                            (applyᴬ C′ (δ x)) z i))

  cols : ∀ x z → scale (norm (C′ ++ D)) (applyᴬ (C ++ D) (δ x) z) ≐
                 scale (norm (C ++ D)) (applyᴬ (C′ ++ D) (δ x) z)
  cols x z i =
    trans (scale-map (norm (C′ ++ D)) split i)
    (trans (scale-exp A (norm-++ C′ D) i)
    (trans (sym (scale-+ (norm C′) (norm D) A i))
    (trans (scale-comm (norm C′) (norm D) A i)
    (trans (scale-map (norm D) (through x z) i)
    (trans (scale-comm (norm D) (norm C) A′ i)
    (trans (scale-+ (norm C) (norm D) A′ i)
    (trans (scale-exp A′ (sym (norm-++ C D)) i)
           (sym (scale-map (norm (C ++ D)) split′ i)))))))))
    where
    A  = applyᴬ D (applyᴬ C (δ x)) z
    A′ = applyᴬ D (applyᴬ C′ (δ x)) z
    split  = ++-at C D (δ x) z
    split′ = ++-at C′ D (δ x) z

-- And D can be cancelled again, by appending D†: after any prefix C,
-- D followed by D† acts as nothing.

++-†-cancel : (C D : Circuit n) → ⟦ (C ++ D) ++ D † ⟧ ≋ ⟦ C ⟧
++-†-cancel C D =
  Equivalence.from (circuit-≋ ((C ++ D) ++ D †) C) (λ x z i →
    let X = applyᴬ C (δ x) z in
    trans (scale-map (norm C) (back x z) i)
    (trans (scale-map (norm C)
              (†-cancelʳ D (applyᴬ C (δ x)) (applyᴬ-resp C (δ-resp x))
                         z) i)
    (trans (sym (scale-map (norm C) (scale-twice (norm D) X) i))
    (trans (scale-+ (norm C) (norm D) (scale (norm D) X) i)
    (trans (scale-+ (norm C ℕ+ norm D) (norm D) X i)
           (scale-exp X norm-thrice i))))))
  where
  back : ∀ x z → applyᴬ ((C ++ D) ++ D †) (δ x) z ≐
                 applyᴬ (D †) (applyᴬ D (applyᴬ C (δ x))) z
  back x z i =
    trans (++-at (C ++ D) (D †) (δ x) z i)
          (cong (λ F → applyᴬ (D †) F z i) (applyᴬ-++ C D (δ x)))

  norm-thrice : (norm C ℕ+ norm D) ℕ+ norm D ≡ norm ((C ++ D) ++ D †)
  norm-thrice =
    sym (trans (norm-++ (C ++ D) (D †))
               (trans (cong (λ u → u ℕ+ norm (D †)) (norm-++ C D))
                      (cong (λ u → (norm C ℕ+ norm D) ℕ+ u)
                            (norm-† D))))

++-cancelʳ : (C C′ D : Circuit n) → ⟦ C ++ D ⟧ ≋ ⟦ C′ ++ D ⟧ →
             ⟦ C ⟧ ≋ ⟦ C′ ⟧
++-cancelʳ C C′ D eq =
  ≋-trans {ξ = ⟦ C ⟧} {ζ = ⟦ (C ++ D) ++ D † ⟧} {χ = ⟦ C′ ⟧}
    (≋-sym {ξ = ⟦ (C ++ D) ++ D † ⟧} {ζ = ⟦ C ⟧} (++-†-cancel C D))
    (≋-trans {ξ = ⟦ (C ++ D) ++ D † ⟧} {ζ = ⟦ (C′ ++ D) ++ D † ⟧}
             {χ = ⟦ C′ ⟧}
             (++-congʳ (C ++ D) (C′ ++ D) (D †) eq) (++-†-cancel C′ D))
