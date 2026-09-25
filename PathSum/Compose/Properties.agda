------------------------------------------------------------------------
-- Presentations of groups
--
-- What a composite path-sum denotes (Amy, QPL 2018, proposition 2.7)
--
-- Proposition 2.7 says U_{ξ′∘ξ} = U_ξ′ U_ξ.  It holds here with no
-- hypothesis at all -- neither well-formedness nor compatibility, the
-- latter being vacuous since every input is a variable -- and exactly,
-- on unnormalised amplitudes: the composite's normalisation k + k′ is
-- the sum of the two, so 1/√2^(k+k′) = 1/√2^k · 1/√2^k′ and the
-- identity between operators is one between the amplitudes of
-- PathSum.Denotation.
--
-- This module does without the product of Z[ζ] (PathSum.Ring), in two
-- ways.  The first writes every entry of U_ξ out as the sum of powers
-- of ζ it is: prop-2-7ʳ says the entry of ξ′∘ξ from x to z is
-- Σ_y ζ^{P(x,y)} · U_ξ′(f(x,y), z), multiplication by ζ^{P(x,y)} being
-- rot.  Since U_ξ(x, w) = Σ_y ζ^{P(x,y)} [f(x,y) = w] (amp-Σδ), that is
-- Σ_w U_ξ(x, w) U_ξ′(w, z) with the sum over w collapsed.
--
-- Everything goes through three facts about the definitions, each
-- proved by evaluating the substitution feed ξ (eval-feed): on the
-- concatenation y ++ᵃ y′ of a path of ξ and one of ξ′, the composite's
-- phase takes the value P(x,y) + P′(f(x,y), y′) (eval-∘), its outputs
-- the bits of ξ′'s at the input f(x,y) (outBit-∘), and so the path hits
-- z exactly when ξ′'s path y′ from f(x,y) does (hits-∘).  The
-- composite's coefficients are never computed.
--
-- The second form is by operators.  applyᴾ ξ is U_ξ acting on a
-- column ψ (a vector indexed by basis states, unnormalised): each
-- input w sends ψ(w), rotated by ζ^{P(w,y)}, along each path y to the
-- state that path hits.  It is built from sums, guards and rotations
-- alone, so it commutes with every linear map of PathSum.AmpLinear
-- (applyᴾ-linear), in particular with powers of √2 (applyᴾ-scale),
-- and with sums of columns (applyᴾ-Σᴮ).  On a basis column δ x it
-- gives the column of U_ξ at x (amp-applyᴾ), and it is functorial:
-- applyᴾ (ξ′ ∘ᴾ ξ) = applyᴾ ξ′ ∘ applyᴾ ξ on every column (applyᴾ-∘),
-- which is U_{ξ′∘ξ} = U_ξ′ U_ξ as an identity of operators.  Read at
-- a basis column it is prop-2-7ᶜ: the column of ξ′ ∘ ξ at x is U_ξ′
-- applied to the column of ξ at x.  Proposition 2.7 as a literal
-- product of matrices over Z[ζ] is PathSum.Compose.Matrix, and the
-- laws of ∘ᴾ that follow (identity, associativity, congruence, all up
-- to ≋) are PathSum.Compose.Laws.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Properties (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; 0ℤ; _+_; _-_)
open import Data.Integer.Properties using (+-identityʳ; +-inverseʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.AmpLinear M₀ using (Linear; scale-linear)
open import PathSum.Assign using ([_]ᶻ; same; same-true; same-intro)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.Compose using (inˡ; feed; _∘ᴾ_)
open import PathSum.Compose.Sum M₀ using
  (_++ᵃ_; ++ᵃ-↑ˡ; ++ᵃ-↑ʳ; Σᴮ-++; Σᴮ-swap; Σᴮ-δ; rot-comm; bool-iff;
   if-cong; zpow-≡; rot-if; if-Σᴮ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; extend; Σᴮ; Σᴮ-cong; zpow; rot; rot-map; rot-exp;
   rot-comp; rot-zpow; rot-0ᴬ; rot-Σᴮ; scale; Respects)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; hits-intro; hits-elim; hits-≗³)
open import PathSum.Polynomial using (Var; x[_]; y[_]; eval)
open import PathSum.Polynomial.Bind using
  (bind; rename; eval-bind; eval-rename; odd; eval-liftᴮ)
open import PathSum.Polynomial.Boolean using (liftᴮ)
open import PathSum.Polynomial.Product using (eval-μᴾ)
open import PathSum.Polynomial.Properties using (valᵛ; eval-+ᴾ; eval-cong)

open +-*-Solver using (solve; _:+_; _:-_; _:=_)

private
  variable
    n k k′ m m′ j : ℕ


------------------------------------------------------------------------
-- Evaluating the composite

-- On the concatenation of a path of ξ and one of ξ′, the substitution
-- feed ξ gives ξ′'s input x′ᵢ the bit of ξ's i-th output -- the lift
-- takes exactly that value, lemma 2.5 -- and ξ′'s path variable y′ⱼ
-- the value of y′ⱼ.

eval-feed : (ξ : PathSum n k m) (x : Assign n) (y : Assign m)
            (y′ : Assign m′) (v : Var n m′) →
            eval (feed ξ v) x (y ++ᵃ y′) ≡ [ valᵛ v (outBit ξ x y) y′ ]ᶻ
eval-feed {m′ = m′} ξ x y y′ x[ i ] = trans
  (eval-rename (inˡ m′) (liftᴮ (out ξ i)) x (y ++ᵃ y′))
  (trans (eval-cong (liftᴮ (out ξ i))
            {x = λ j → x j} {x′ = x}
            {y = λ j → (y ++ᵃ y′) (j ↑ˡ m′)} {y′ = y}
            (λ _ → refl) (λ j → ++ᵃ-↑ˡ y y′ j))
         (eval-liftᴮ (out ξ i) x y))
eval-feed {m = m} ξ x y y′ y[ j ] = trans
  (eval-μᴾ y[ m ↑ʳ j ] x (y ++ᵃ y′))
  (cong [_]ᶻ (++ᵃ-↑ʳ y y′ j))

-- The composite's phase: ξ's, plus ξ′'s at the input ξ's path reaches.

eval-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
         (x : Assign n) (y : Assign m) (y′ : Assign m′) →
         eval (phase (ξ′ ∘ᴾ ξ)) x (y ++ᵃ y′) ≡
         eval (phase ξ) x y + eval (phase ξ′) (outBit ξ x y) y′
eval-∘ {m′ = m′} ξ′ ξ x y y′ = trans
  (eval-+ᴾ (rename (inˡ m′) (phase ξ)) (bind (phase ξ′) (feed ξ)) x
           (y ++ᵃ y′))
  (cong₂ _+_ first
    (eval-bind (phase ξ′) (feed ξ) x (y ++ᵃ y′) (outBit ξ x y) y′
               (eval-feed ξ x y y′)))
  where
  first : eval (rename (inˡ m′) (phase ξ)) x (y ++ᵃ y′) ≡ eval (phase ξ) x y
  first = trans (eval-rename (inˡ m′) (phase ξ) x (y ++ᵃ y′))
    (eval-cong (phase ξ)
      {x = λ j → x j} {x′ = x}
      {y = λ j → (y ++ᵃ y′) (j ↑ˡ m′)} {y′ = y}
      (λ _ → refl) (λ j → ++ᵃ-↑ˡ y y′ j))

-- The composite's outputs read, along that path, ξ′'s outputs at that
-- input.  outBit is odd ∘ eval by definition, so this is a single
-- congruence.

outBit-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
           (x : Assign n) (y : Assign m) (y′ : Assign m′) (w : Fin n) →
           outBit (ξ′ ∘ᴾ ξ) x (y ++ᵃ y′) w ≡ outBit ξ′ (outBit ξ x y) y′ w
outBit-∘ ξ′ ξ x y y′ w = cong odd
  (eval-bind (out ξ′ w) (feed ξ) x (y ++ᵃ y′) (outBit ξ x y) y′
             (eval-feed ξ x y y′))


------------------------------------------------------------------------
-- Hitting an output

-- Paths whose outputs read the same bits hit the same states.

hits-outBit : (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
              (x x′ : Assign n) (y : Assign m) (y′ : Assign m′)
              (z : Assign n) →
              (∀ w → outBit ξ x y w ≡ outBit ζ x′ y′ w) →
              hits ξ x y z ≡ hits ζ x′ y′ z
hits-outBit ξ ζ x x′ y y′ z h = bool-iff
  (λ e → hits-intro ζ x′ y′ z (λ w → trans (sym (h w)) (hits-elim ξ x y z e w)))
  (λ e → hits-intro ξ x y z (λ w → trans (h w) (hits-elim ζ x′ y′ z e w)))

hits-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
         (x : Assign n) (y : Assign m) (y′ : Assign m′) (z : Assign n) →
         hits (ξ′ ∘ᴾ ξ) x (y ++ᵃ y′) z ≡ hits ξ′ (outBit ξ x y) y′ z
hits-∘ ξ′ ξ x y y′ z = hits-outBit (ξ′ ∘ᴾ ξ) ξ′ x (outBit ξ x y) (y ++ᵃ y′) y′ z
  (outBit-∘ ξ′ ξ x y y′)

-- A path hits z exactly when its output bits are z's.

hits-same : (ξ : PathSum n k m) (x : Assign n) (y : Assign m)
            (z : Assign n) → hits ξ x y z ≡ same (outBit ξ x y) z
hits-same ξ x y z = bool-iff
  (λ e → same-intro (outBit ξ x y) z (hits-elim ξ x y z e))
  (λ e → hits-intro ξ x y z (same-true (outBit ξ x y) z e))


------------------------------------------------------------------------
-- Amplitudes

-- Only the values of the input are read.

amp-≗ˣ : (ξ : PathSum n k m) {x x′ : Assign n} → (∀ i → x i ≡ x′ i) →
         ∀ z → amp ξ x z ≐ amp ξ x′ z
amp-≗ˣ ξ {x} {x′} x≗x′ z = Σᴮ-cong (λ y → if-cong
  (hits-≗³ ξ {x} {x′} {y} {y} {z} {z} x≗x′ (λ _ → refl) (λ _ → refl))
  (zpow-≡ (eval-cong (phase ξ) {x} {x′} {y} {y} x≗x′ (λ _ → refl))))

-- The entry of U_ξ from x to z as a sum of powers of ζ, one for each
-- path, guarded by whether the path's output is z: U_ξ(x, ·) is
-- Σ_y ζ^{P(x,y)} |f(x,y)⟩.

amp-Σδ : (ξ : PathSum n k m) (x z : Assign n) →
         amp ξ x z ≐
         Σᴮ (λ y → rot (eval (phase ξ) x y) (δ (outBit ξ x y) z))
amp-Σδ ξ x z = Σᴮ-cong (λ y i → trans
  (if-cong (hits-same ξ x y z)
           (zpow-≡ (sym (+-identityʳ (eval (phase ξ) x y)))) i)
  (sym (rot-if (same (outBit ξ x y) z) (eval (phase ξ) x y) 0ℤ i)))


------------------------------------------------------------------------
-- Proposition 2.7

-- U_{ξ′∘ξ} = U_ξ′ U_ξ, with U_ξ's entries written as sums of powers of
-- ζ: split the composite's paths into ξ's and ξ′'s, read the guard and
-- the phase of each by hits-∘ and eval-∘, and pull ζ^{P(x,y)} out of
-- the inner sum, which is then ξ′'s amplitude from f(x,y) to z.

prop-2-7ʳ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) (x z : Assign n) →
            amp (ξ′ ∘ᴾ ξ) x z ≐
            Σᴮ (λ y → rot (eval (phase ξ) x y) (amp ξ′ (outBit ξ x y) z))
prop-2-7ʳ {m′ = m′} {m = m} ξ′ ξ x z i = trans
  (Σᴮ-++ m m′ (λ Y → if hits (ξ′ ∘ᴾ ξ) x Y z
                     then zpow (eval (phase (ξ′ ∘ᴾ ξ)) x Y) else 0ᴬ) i)
  (Σᴮ-cong per i)
  where
  e : Assign m → ℤ
  e y = eval (phase ξ) x y

  -- ξ′'s amplitude from the input ξ's path y reaches, path by path.
  inner : Assign m → Assign m′ → Amp
  inner y y′ = if hits ξ′ (outBit ξ x y) y′ z
               then zpow (eval (phase ξ′) (outBit ξ x y) y′) else 0ᴬ

  point : ∀ y y′ →
          (if hits (ξ′ ∘ᴾ ξ) x (y ++ᵃ y′) z
           then zpow (eval (phase (ξ′ ∘ᴾ ξ)) x (y ++ᵃ y′)) else 0ᴬ) ≐
          rot (e y) (inner y y′)
  point y y′ j = trans
    (if-cong (hits-∘ ξ′ ξ x y y′ z) (zpow-≡ (eval-∘ ξ′ ξ x y y′)) j)
    (sym (rot-if (hits ξ′ (outBit ξ x y) y′ z) (e y)
                 (eval (phase ξ′) (outBit ξ x y) y′) j))

  per : ∀ y →
        Σᴮ (λ y′ → if hits (ξ′ ∘ᴾ ξ) x (y ++ᵃ y′) z
                   then zpow (eval (phase (ξ′ ∘ᴾ ξ)) x (y ++ᵃ y′)) else 0ᴬ) ≐
        rot (e y) (amp ξ′ (outBit ξ x y) z)
  per y j = trans (Σᴮ-cong (point y) j)
                  (sym (rot-Σᴮ (e y) (inner y) j))


------------------------------------------------------------------------
-- The operator of a path-sum

-- U_ξ on a column ψ: every input w sends ψ(w) along every path y,
-- rotated by ζ^{P(w,y)}, to the state f(w,y) that the path hits.

applyᴾ : PathSum n k m → Column n → Column n
applyᴾ ξ ψ z = Σᴮ (λ w → Σᴮ (λ y →
  if hits ξ w y z then rot (eval (phase ξ) w y) (ψ w) else 0ᴬ))

-- It respects equality of columns.

applyᴾ-cong : (ξ : PathSum n k m) {ψ ψ′ : Column n} →
              (∀ w → ψ w ≐ ψ′ w) → ∀ z → applyᴾ ξ ψ z ≐ applyᴾ ξ ψ′ z
applyᴾ-cong ξ ψ≐ψ′ z = Σᴮ-cong (λ w → Σᴮ-cong (λ y →
  if-cong {p = hits ξ w y z} refl
          (rot-map (eval (phase ξ) w y) (ψ≐ψ′ w))))

-- A linear map (PathSum.AmpLinear) kills 0ᴬ, since f 0 = f 0 + f 0,
-- and so passes through every guard; it is additive, and so passes
-- through every sum.  Hence it passes through the operator.

private
  double-zero : ∀ a → a ≡ a + a → a ≡ 0ℤ
  double-zero a h =
    trans (sym (cancel a)) (trans (cong (_- a) (sym h)) (+-inverseʳ a))
    where
    cancel : ∀ a → (a + a) - a ≡ a
    cancel = solve 1 (λ a → (a :+ a) :- a := a) refl

  map-0ᴬ : ∀ {f} → Linear f → f 0ᴬ ≐ 0ᴬ
  map-0ᴬ {f} lin i = double-zero (f 0ᴬ i)
    (trans (Linear.map-≐ lin {0ᴬ} {0ᴬ +ᴬ 0ᴬ} (λ _ → refl) i)
           (Linear.map-+ᴬ lin 0ᴬ 0ᴬ i))

  map-if : ∀ {f} → Linear f → (c : Bool) (a : Amp) →
           f (if c then a else 0ᴬ) ≐ (if c then f a else 0ᴬ)
  map-if lin true  a _ = refl
  map-if lin false a   = map-0ᴬ lin

  map-Σᴮ : ∀ {f} → Linear f → (g : (Fin j → Bool) → Amp) →
           f (Σᴮ g) ≐ Σᴮ (λ y → f (g y))
  map-Σᴮ {j = zero}  lin g _ = refl
  map-Σᴮ {j = suc j} lin g i = trans
    (Linear.map-+ᴬ lin (Σᴮ (λ y → g (extend true y)))
                       (Σᴮ (λ y → g (extend false y))) i)
    (cong₂ _+_ (map-Σᴮ lin (λ y → g (extend true y)) i)
               (map-Σᴮ lin (λ y → g (extend false y)) i))

applyᴾ-linear : ∀ {f} → Linear f → (ξ : PathSum n k m) (ψ : Column n) →
                ∀ z → applyᴾ ξ (λ w → f (ψ w)) z ≐ f (applyᴾ ξ ψ z)
applyᴾ-linear {f = f} lin ξ ψ z i = sym (trans
  (map-Σᴮ lin (λ w → Σᴮ (λ y → if hits ξ w y z
                              then rot (eval (phase ξ) w y) (ψ w) else 0ᴬ)) i)
  (Σᴮ-cong (λ w l → trans
    (map-Σᴮ lin (λ y → if hits ξ w y z
                       then rot (eval (phase ξ) w y) (ψ w) else 0ᴬ) l)
    (Σᴮ-cong (λ y o → trans
      (map-if lin (hits ξ w y z) (rot (eval (phase ξ) w y) (ψ w)) o)
      (if-cong {p = hits ξ w y z} refl
               (Linear.map-rot lin (eval (phase ξ) w y) (ψ w)) o)) l)) i))

-- In particular powers of √2 pass through it.

applyᴾ-scale : (ξ : PathSum n k m) (i : ℕ) (ψ : Column n) (z : Assign n) →
               scale i (applyᴾ ξ ψ z) ≐ applyᴾ ξ (λ w → scale i (ψ w)) z
applyᴾ-scale ξ i ψ z l = sym (applyᴾ-linear (scale-linear i) ξ ψ z l)

-- It is additive: a sum of columns goes to the sum of their images.

applyᴾ-Σᴮ : (ξ : PathSum n k m) (G : (Fin j → Bool) → Column n)
            (z : Assign n) →
            applyᴾ ξ (λ w → Σᴮ (λ t → G t w)) z ≐
            Σᴮ (λ t → applyᴾ ξ (G t) z)
applyᴾ-Σᴮ ξ G z i = trans
  (Σᴮ-cong (λ w l → trans
     (Σᴮ-cong (λ y o → trans
        (if-cong {p = hits ξ w y z} refl
                 (rot-Σᴮ (eval (phase ξ) w y) (λ t → G t w)) o)
        (if-Σᴮ (hits ξ w y z) (λ t → rot (eval (phase ξ) w y) (G t w)) o)) l)
     (Σᴮ-swap (λ y t → if hits ξ w y z
                       then rot (eval (phase ξ) w y) (G t w) else 0ᴬ) l)) i)
  (Σᴮ-swap (λ w t → Σᴮ (λ y → if hits ξ w y z
                              then rot (eval (phase ξ) w y) (G t w) else 0ᴬ))
           i)

-- The paths from an input w, each carrying a rotated copy of one
-- amplitude, read w only through its values.

paths-resp : (ξ : PathSum n k m) (a : Amp) (z : Assign n) →
             Respects (λ w → Σᴮ (λ y → if hits ξ w y z
                                       then rot (eval (phase ξ) w y) a
                                       else 0ᴬ))
paths-resp ξ a z g h g≗h = Σᴮ-cong (λ y → if-cong
  (hits-≗³ ξ {g} {h} {y} {y} {z} {z} g≗h (λ _ → refl) (λ _ → refl))
  (rot-exp {eval (phase ξ) g y} {eval (phase ξ) h y} a
           (eval-cong (phase ξ) {g} {h} {y} {y} g≗h (λ _ → refl))))

-- On a column supported at a single input v the operator collapses to
-- the paths from v: the guard of the column commutes with that of the
-- path, and the sum over inputs collapses against it (Σᴮ-δ).

private
  guard-swap : (h s : Bool) (e : ℤ) (a : Amp) →
               (if h then rot e (if s then a else 0ᴬ) else 0ᴬ) ≐
               (if s then (if h then rot e a else 0ᴬ) else 0ᴬ)
  guard-swap true  true  e a _ = refl
  guard-swap true  false e a   = rot-0ᴬ e
  guard-swap false true  e a _ = refl
  guard-swap false false e a _ = refl

applyᴾ-δ : (ξ : PathSum n k m) (v : Assign n) (a : Amp) (z : Assign n) →
           applyᴾ ξ (λ w → if same v w then a else 0ᴬ) z ≐
           Σᴮ (λ y → if hits ξ v y z then rot (eval (phase ξ) v y) a else 0ᴬ)
applyᴾ-δ ξ v a z i = trans
  (Σᴮ-cong (λ w l → trans
     (Σᴮ-cong (λ y → guard-swap (hits ξ w y z) (same v w)
                                (eval (phase ξ) w y) a) l)
     (sym (if-Σᴮ (same v w)
                 (λ y → if hits ξ w y z
                        then rot (eval (phase ξ) w y) a else 0ᴬ) l))) i)
  (Σᴮ-δ v (λ w → Σᴮ (λ y → if hits ξ w y z
                           then rot (eval (phase ξ) w y) a else 0ᴬ))
        (paths-resp ξ a z) i)

-- On the basis column δ x the operator gives the column of U_ξ at x.

amp-applyᴾ : (ξ : PathSum n k m) (x z : Assign n) →
             amp ξ x z ≐ applyᴾ ξ (δ x) z
amp-applyᴾ ξ x z i = sym (trans (applyᴾ-δ ξ x (zpow 0ℤ) z i)
  (Σᴮ-cong (λ y → if-cong {p = hits ξ x y z} refl (λ l → trans
     (rot-zpow (eval (phase ξ) x y) 0ℤ l)
     (zpow-≡ (+-identityʳ (eval (phase ξ) x y)) l))) i))


------------------------------------------------------------------------
-- Proposition 2.7, by operators

-- Functoriality: running ξ′ ∘ ξ on a column is running ξ, then ξ′.
-- On the left, split the composite's paths (Σᴮ-++) and read each by
-- hits-∘ and eval-∘.  On the right, read ξ's column as a sum of
-- columns each supported at the state one path hits (hits-same), push
-- U_ξ′ through the sums (applyᴾ-Σᴮ) and collapse each (applyᴾ-δ).
-- Both sides are then Σ_w Σ_y Σ_y′ of ψ(w) rotated by P(w,y) and by
-- P′(f(w,y),y′), in the two orders.

applyᴾ-∘ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) (ψ : Column n)
           (z : Assign n) →
           applyᴾ (ξ′ ∘ᴾ ξ) ψ z ≐ applyᴾ ξ′ (applyᴾ ξ ψ) z
applyᴾ-∘ {n = n} {m′ = m′} {m = m} ξ′ ξ ψ z i = trans left (sym right)
  where
  -- The composite's paths from w, as a path y of ξ followed by a path
  -- y′ of ξ′ from the state y hits.
  T : Assign n → Assign m → Assign m′ → Amp
  T w y y′ = if hits ξ′ (outBit ξ w y) y′ z
             then rot (eval (phase ξ′) (outBit ξ w y) y′)
                      (rot (eval (phase ξ) w y) (ψ w))
             else 0ᴬ

  point : ∀ w y y′ →
          (if hits (ξ′ ∘ᴾ ξ) w (y ++ᵃ y′) z
           then rot (eval (phase (ξ′ ∘ᴾ ξ)) w (y ++ᵃ y′)) (ψ w) else 0ᴬ) ≐
          T w y y′
  point w y y′ = if-cong (hits-∘ ξ′ ξ w y y′ z) (λ o → trans
    (rot-exp {eval (phase (ξ′ ∘ᴾ ξ)) w (y ++ᵃ y′)}
             {eval (phase ξ) w y + eval (phase ξ′) (outBit ξ w y) y′}
             (ψ w) (eval-∘ ξ′ ξ w y y′) o)
    (trans (sym (rot-comp (eval (phase ξ) w y)
                          (eval (phase ξ′) (outBit ξ w y) y′) (ψ w) o))
           (rot-comm (eval (phase ξ) w y)
                     (eval (phase ξ′) (outBit ξ w y) y′) (ψ w) o)))

  left : applyᴾ (ξ′ ∘ᴾ ξ) ψ z i ≡
         Σᴮ (λ w → Σᴮ (λ y → Σᴮ (λ y′ → T w y y′))) i
  left = Σᴮ-cong (λ w l → trans
    (Σᴮ-++ m m′ (λ Y → if hits (ξ′ ∘ᴾ ξ) w Y z
                       then rot (eval (phase (ξ′ ∘ᴾ ξ)) w Y) (ψ w)
                       else 0ᴬ) l)
    (Σᴮ-cong (λ y → Σᴮ-cong (point w y)) l)) i

  -- ξ's column, as a sum of columns each supported at one state.
  D : Assign n → Assign m → Column n
  D w y u = if same (outBit ξ w y) u
            then rot (eval (phase ξ) w y) (ψ w) else 0ᴬ

  column : ∀ u → applyᴾ ξ ψ u ≐ Σᴮ (λ w → Σᴮ (λ y → D w y u))
  column u = Σᴮ-cong (λ w → Σᴮ-cong (λ y →
    if-cong (hits-same ξ w y u) (λ _ → refl)))

  right : applyᴾ ξ′ (applyᴾ ξ ψ) z i ≡
          Σᴮ (λ w → Σᴮ (λ y → Σᴮ (λ y′ → T w y y′))) i
  right = trans
    (applyᴾ-cong ξ′ {applyᴾ ξ ψ} {λ u → Σᴮ (λ w → Σᴮ (λ y → D w y u))}
                 column z i)
    (trans (applyᴾ-Σᴮ ξ′ (λ w u → Σᴮ (λ y → D w y u)) z i)
      (Σᴮ-cong (λ w l → trans (applyᴾ-Σᴮ ξ′ (λ y u → D w y u) z l)
        (Σᴮ-cong (λ y → applyᴾ-δ ξ′ (outBit ξ w y)
                           (rot (eval (phase ξ) w y) (ψ w)) z) l)) i))

-- Proposition 2.7, column by column: the column of ξ′ ∘ ξ at x is U_ξ′
-- applied to the column of ξ at x.

prop-2-7ᶜ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m) (x z : Assign n) →
            amp (ξ′ ∘ᴾ ξ) x z ≐ applyᴾ ξ′ (amp ξ x) z
prop-2-7ᶜ ξ′ ξ x z i = trans (amp-applyᴾ (ξ′ ∘ᴾ ξ) x z i)
  (trans (applyᴾ-∘ ξ′ ξ (δ x) z i)
         (applyᴾ-cong ξ′ {applyᴾ ξ (δ x)} {amp ξ x}
                      (λ w l → sym (amp-applyᴾ ξ x w l)) z i))
