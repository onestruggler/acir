------------------------------------------------------------------------
-- Presentations of groups
--
-- The rewrite rules find |s⟩|s⟩: reductions of the symbolic-shift
-- circuit (Amy, QPL 2018, section 5.2)
--
-- The paper reports that its calculus "finds the correct output |s⟩ or
-- |s⟩|s⟩ even without providing the specification".  For |s⟩, the
-- circuit of figure 3(a), that is PathSum.HiddenShift.Circuit's
-- circuit-reduces.  For |s⟩|s⟩ the specification has symbolic outputs:
-- the shift is the input of the second register, and the path-sum to
-- be found is |x_d, x_s⟩ ↦ |x_s, x_s⟩ (PathSum.HiddenShift.Symbolic's
-- specSᴾ).
--
-- A functional specification.  Let funᴾ F be the path-sum with no
-- path variables, phase 0 and outputs F, a list of integer polynomials
-- in the inputs whose values are bits: F computes a classical map f,
-- eval (F w) x = f(x)_w.  Its column at x is |f(x)⟩ (amp-funᴾ).  Any
-- path-sum ζ with no path variables equivalent to it is it,
-- syntactically (fun-only-if): normalisation 0, outputs F coefficient
-- by coefficient modulo 2, phase 0 modulo 1.  The argument is
-- PathSum.HiddenShift.Simulation's spec-only-if, which is the case of
-- a constant f: at each input x the single path of ζ must reach f(x),
-- since the specification's entry there is not 0, and must carry its
-- amplitude, a power of ζ equal to √2^k ζ^0; Möbius inversion turns
-- the values into coefficients.  The copy specification specSᴾ is such
-- a funᴾ (specSᴾ-fun), and so every complete reduction by figure 2's
-- rules, at any path variables, of the symbolic-shift circuit with its
-- data register read as 0 ends at |x_d, x_s⟩ ↦ |x_s, x_s⟩
-- syntactically (symbolic-reduces), as does every derivation in the
-- paper's style (symbolic-derives), for every m and g.  That a
-- complete reduction exists is not proved here, for either figure.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Reduces (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣m∣n⇒∣m-n)
open import Data.Integer.Properties using
  (+-comm; +-identityʳ; +-inverseˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List)
open import Data.Nat.Base using (zero; suc; s≤s; z≤n) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Ancilla.Register M₀ using (set0ᶜ)
open import PathSum.Assign using ([_]ᶻ; same; same-refl; same-≗)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Compose.Properties M₀ using (hits-same)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _·ᴬ_; _≐_; H; N; c; Σᴮ-cong; zpow; χ; χ--1; χ-0; rot;
   rot-map; rot-exp; rot-zpow; rot-+ᴬ; rot-comp; rot-·ᴬ; √2·; √2·-map;
   √2·-twice; √2·-0ᴬ; √2·-injective; scale; scale-map;
   zpow-0≢0ᴬ; 2·≢scale-zpow0; 0ᶠ; zpow0-at-0)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; _≋_; ≋-sym; ≋-trans; hits-elim; hits-≗³)
open import PathSum.HiddenShift M₀ using (none; eval-none; Σᴮ-none)
open import PathSum.HiddenShift.Gates M₀ using (Term)
open import PathSum.HiddenShift.Sign M₀ using (1ᴬ; halve; odd-[])
open import PathSum.HiddenShift.Symbolic M₀ using
  (SSᶜ; specSᴾ; copy; dataMask; symbolic-shift-set0)
open import PathSum.HiddenShift.Walsh using (0ᵃ)
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Polynomial using
  (Poly; x[_]; 0ᴾ; _-ᴾ_; μ; eval; _≈[_]_)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Product using (eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using (eval-−ᴾ)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using (⟦_⟧)
open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Order M using (pow)
open import PathSum.Reduction.Derivation M₀ using
  (Derivation; derivation-sound)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Powers of ζ against normalisations

-- These are PathSum.HiddenShift.Simulation's (and PathSum.Identity's),
-- which keep them private.

private
  rot-√2 : ∀ e a → rot e (√2· a) ≐ √2· (rot e a)
  rot-√2 e a i = trans (rot-+ᴬ e (rot (+ c) a) (rot (- (+ c)) a) i)
                       (cong₂ _+_ (swap (+ c)) (swap (- (+ c))))
    where
    swap : ∀ d → rot e (rot d a) i ≡ rot d (rot e a) i
    swap d = trans (rot-comp e d a i)
      (trans (rot-exp a (+-comm e d) i) (sym (rot-comp d e a i)))

  rot-back : ∀ e → rot (- e) (zpow e) ≐ zpow 0ℤ
  rot-back e i =
    trans (rot-zpow (- e) e i) (cong (λ z → zpow z i) (+-inverseˡ e))

  -- √2^j ζ^0 is never zero.

  scale-zpow0≢0 : ∀ j → ¬ (scale j (zpow 0ℤ) ≐ 0ᴬ)
  scale-zpow0≢0 zero    eq = zpow-0≢0ᴬ eq
  scale-zpow0≢0 (suc j) eq = scale-zpow0≢0 j
    (√2·-injective (scale j (zpow 0ℤ)) 0ᴬ
      (λ i → trans (eq i) (sym (√2·-0ᴬ i))))

  -- Nor is a power of ζ ever √2^j for j at least one.

  zpow≢scale : ∀ (e : ℤ) j → ¬ (zpow e ≐ scale (suc j) (zpow 0ℤ))
  zpow≢scale e zero eq =
    2·≢scale-zpow0 (zpow (- e)) 1 (s≤s (s≤s z≤n)) two
    where
    rotated : zpow 0ℤ ≐ √2· (zpow (- e))
    rotated i = trans (sym (rot-back e i))
      (trans (rot-map (- e) eq i)
        (trans (rot-√2 (- e) (zpow 0ℤ) i)
          (√2·-map (λ i′ → trans (rot-zpow (- e) 0ℤ i′)
            (cong (λ z → zpow z i′) (+-identityʳ (- e)))) i)))

    two : ((+ 2) ·ᴬ zpow (- e)) ≐ scale 1 (zpow 0ℤ)
    two i = trans (sym (√2·-twice (zpow (- e)) i))
                  (√2·-map (λ i′ → sym (rotated i′)) i)
  zpow≢scale e (suc j) eq =
    2·≢scale-zpow0 (rot (- e) (scale j (zpow 0ℤ))) 0 (s≤s z≤n) two
    where
    two : ((+ 2) ·ᴬ rot (- e) (scale j (zpow 0ℤ))) ≐ scale 0 (zpow 0ℤ)
    two i = trans (sym (rot-·ᴬ (- e) (+ 2) (scale j (zpow 0ℤ)) i))
      (trans (sym (rot-map (- e)
        (λ i′ → trans (eq i′) (√2·-twice (scale j (zpow 0ℤ)) i′)) i))
        (rot-back e i))

  -- A coefficient of 1 means the exponent is a multiple of N.

  χ≡1 : ∀ z → χ z ≡ 1ℤ → (+ N) ∣ z
  χ≡1 z eq = aux ((+ N) ∣? z) ((+ N) ∣? (z - (+ H)))
    where
    aux : Dec ((+ N) ∣ z) → Dec ((+ N) ∣ (z - (+ H))) → (+ N) ∣ z
    aux (yes d) _       = d
    aux (no ¬d) (yes b) = contradiction (trans (sym (χ--1 ¬d b)) eq) λ ()
    aux (no ¬d) (no ¬b) = contradiction (trans (sym (χ-0 ¬d ¬b)) eq) λ ()

  -- ζ^e = √2^k ζ^0 forces k = 0 and e ≡ 0 modulo N.

  norm-zero : ∀ {k} (e : ℤ) → zpow e ≐ scale k (zpow 0ℤ) → k ≡ 0
  norm-zero {zero}  e _  = refl
  norm-zero {suc j} e eq = ⊥-elim (zpow≢scale e j eq)

  exponent-zero : ∀ {k} (e : ℤ) → zpow e ≐ scale k (zpow 0ℤ) → (+ N) ∣ e
  exponent-zero {suc j} e eq = ⊥-elim (zpow≢scale e j eq)
  exponent-zero {zero}  e eq =
    subst ((+ N) ∣_) (shape e index)
          (∣m∣n⇒∣m-n (χ≡1 _ (trans (eq 0ᶠ) zpow0-at-0)) (χ≡1 _ zpow0-at-0))
    where
    index : ℤ
    index = + toℕ 0ᶠ

    shape : ∀ u v → (u - v) - (0ℤ - v) ≡ u
    shape = solve 2 (λ u v → (u :- v) :- (con 0ℤ :- v) := u) refl

  -- A guarded amplitude whose guard is decided.

  if-true : {b : Bool} {a : Amp} → b ≡ true → (if b then a else 0ᴬ) ≐ a
  if-true {true} _ _ = refl

  if-false : {b : Bool} {a : Amp} → b ≡ false → (if b then a else 0ᴬ) ≐ 0ᴬ
  if-false {false} _ _ = refl

  -- A value of parity b differs from b by an even number.

  even-diff : ∀ v b → odd v ≡ b → (+ 2) ∣ (v - [ b ]ᶻ)
  even-diff v b eq with halve v
  ... | r , e = divides r (trans (cong (λ t → v - [ t ]ᶻ) (sym eq))
    (trans (cong (_- [ odd v ]ᶻ) e) (shape r [ odd v ]ᶻ)))
    where
    shape : ∀ u t → (u * (+ 2) + t) - t ≡ u * (+ 2)
    shape = solve 2 (λ u t → (u :* con (+ 2) :+ t) :- t := u :* con (+ 2))
                    refl

  -- The single path of a path-sum with no path variables.

  amp₀ : (ζ : PathSum n k 0) (x z : Assign n) →
         amp ζ x z ≐
         (if hits ζ x none z then zpow (eval (phase ζ) x none) else 0ᴬ)
  amp₀ ζ x z = Σᴮ-none
    (λ y → if hits ζ x y z then zpow (eval (phase ζ) x y) else 0ᴬ)
    (λ y → if-cong
      (hits-≗³ ζ {x} {x} {y} {none} {z} {z} (λ _ → refl) (λ ())
               (λ _ → refl))
      (zpow-≡ (eval-none (phase ζ) x y)))




------------------------------------------------------------------------
-- A functional specification

-- No path variables, phase 0, and the outputs F.

funᴾ : (Fin n → Poly n 0) → PathSum n 0 0
funᴾ F = ⟨ 0ᴾ , F ⟩

-- If F computes f, its column at x is |f(x)⟩.

amp-funᴾ : (F : Fin n → Poly n 0) (f : Assign n → Assign n) →
           (∀ x y w → eval (F w) x y ≡ [ f x w ]ᶻ) →
           (x z : Assign n) →
           amp (funᴾ F) x z ≐ (if same (f x) z then 1ᴬ else 0ᴬ)
amp-funᴾ F f hF x z = Σᴮ-none
  (λ y → if hits (funᴾ F) x y z then zpow (eval (phase (funᴾ F)) x y)
         else 0ᴬ)
  (λ y → if-cong (guard y) (zpow-≡ (eval-0ᴾ x y)))
  where
  guard : ∀ y → hits (funᴾ F) x y z ≡ same (f x) z
  guard y = trans (hits-same (funᴾ F) x y z)
    (same-≗ {x = outBit (funᴾ F) x y} {x′ = f x} {z = z} {z′ = z}
            (λ w → trans (cong odd (hF x y w)) (odd-[] (f x w)))
            (λ _ → refl))

-- A path-sum with no path variables equivalent to funᴾ F is funᴾ F,
-- coefficient by coefficient.

fun-only-if : (F : Fin n → Poly n 0) (f : Assign n → Assign n) →
              (∀ x y w → eval (F w) x y ≡ [ f x w ]ᶻ) →
              (ζ : PathSum n k 0) → ζ ≋ funᴾ F →
              (k ≡ 0) ×
              (∀ w → out ζ w ≈[ + 2 ] F w) ×
              (phase ζ ≈[ pow M ] 0ᴾ)
fun-only-if {n} {k} F f hF ζ ζ≋ = norm , outs , phs
  where
  column : ∀ x → amp ζ x (f x) ≐ scale k 1ᴬ
  column x i = trans (ζ≋ x (f x) i)
    (scale-map k (λ l → trans (amp-funᴾ F f hF x (f x) l)
                              (if-true (same-refl (f x)) l)) i)

  e : Assign n → ℤ
  e x = eval (phase ζ) x none

  both : ∀ x → (hits ζ x none (f x) ≡ true) × (zpow (e x) ≐ scale k 1ᴬ)
  both x = go (hits ζ x none (f x)) refl
    where
    go : ∀ b → hits ζ x none (f x) ≡ b →
         (hits ζ x none (f x) ≡ true) × (zpow (e x) ≐ scale k 1ᴬ)
    go true  eq = eq , (λ i → trans (sym (if-true eq i))
                                    (trans (sym (amp₀ ζ x (f x) i))
                                           (column x i)))
    go false eq = ⊥-elim (scale-zpow0≢0 k (λ i → trans (sym (column x i))
                            (trans (amp₀ ζ x (f x) i) (if-false eq i))))

  norm : k ≡ 0
  norm = norm-zero {k} (e 0ᵃ) (proj₂ (both 0ᵃ))

  outs : ∀ w → out ζ w ≈[ + 2 ] F w
  outs w = values⇒coefficientsᵐ (+ 2) (out ζ w -ᴾ F w) value
    where
    value : ∀ x y → (+ 2) ∣ eval (out ζ w -ᴾ F w) x y
    value x y = subst ((+ 2) ∣_)
      (sym (trans (eval-−ᴾ (out ζ w) (F w) x y)
                  (cong₂ _-_ (eval-none (out ζ w) x y) (hF x y w))))
      (even-diff (eval (out ζ w) x none) (f x w)
                 (hits-elim ζ x none (f x) (proj₁ (both x)) w))

  phs : phase ζ ≈[ pow M ] 0ᴾ
  phs = values⇒coefficientsᵐ (pow M) (phase ζ -ᴾ 0ᴾ) value
    where
    value : ∀ x y → pow M ∣ eval (phase ζ -ᴾ 0ᴾ) x y
    value x y = subst (pow M ∣_)
      (sym (trans (eval-−ᴾ (phase ζ) 0ᴾ x y)
        (trans (cong₂ _-_ (eval-none (phase ζ) x y) (eval-0ᴾ x y))
               (+-identityʳ (e x)))))
      (exponent-zero {k} (e x) (proj₂ (both x)))


------------------------------------------------------------------------
-- The symbolic shift

-- The copy specification is the functional specification of
-- x ↦ (x_s, x_s).

specSᴾ-fun : ∀ n → specSᴾ n ≡ funᴾ (λ w → μ x[ copy n w ])
specSᴾ-fun n = refl

copy-values : ∀ n (x : Assign (n ℕ+ n)) (y : Assign 0) (w : Fin (n ℕ+ n)) →
              eval (μ x[ copy n w ]) x y ≡ [ x (copy n w) ]ᶻ
copy-values n x y w = eval-μᴾ x[ copy n w ] x y

-- Every complete reduction of the circuit with its data register read
-- as 0 ends at |x_d, x_s⟩ ↦ |x_s, x_s⟩: normalisation 0, the output on
-- every wire the matching input of the shift register modulo 2, phase
-- 0 modulo 1.

symbolic-reduces : (gs : List (Term m)) {k′ : ℕ}
                   {ζ : PathSum ((m ℕ+ m) ℕ+ (m ℕ+ m)) k′ 0} →
                   set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧ ⟶ᶠ* ζ →
                   (k′ ≡ 0) ×
                   (∀ w → out ζ w ≈[ + 2 ] μ x[ copy (m ℕ+ m) w ]) ×
                   (phase ζ ≈[ pow M ] 0ᴾ)
symbolic-reduces {m} gs {k′} {ζ} steps =
  fun-only-if (λ w → μ x[ copy (m ℕ+ m) w ])
              (λ x w → x (copy (m ℕ+ m) w))
              (copy-values (m ℕ+ m)) ζ
    (≋-trans {ξ = ζ} {ζ = set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧}
             {χ = specSᴾ (m ℕ+ m)}
      (≋-sym {ξ = set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧} {ζ = ζ}
             (⟶ᶠ*-sound steps))
      (symbolic-shift-set0 gs))

-- The same for a derivation in the paper's style.

symbolic-derives : (gs : List (Term m)) {k′ : ℕ}
                   {ζ : PathSum ((m ℕ+ m) ℕ+ (m ℕ+ m)) k′ 0} →
                   Derivation (set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧) ζ →
                   (k′ ≡ 0) ×
                   (∀ w → out ζ w ≈[ + 2 ] μ x[ copy (m ℕ+ m) w ]) ×
                   (phase ζ ≈[ pow M ] 0ᴾ)
symbolic-derives {m} gs {k′} {ζ} d =
  fun-only-if (λ w → μ x[ copy (m ℕ+ m) w ])
              (λ x w → x (copy (m ℕ+ m) w))
              (copy-values (m ℕ+ m)) ζ
    (≋-trans {ξ = ζ} {ζ = set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧}
             {χ = specSᴾ (m ℕ+ m)}
      (≋-sym {ξ = set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧} {ζ = ζ}
             (derivation-sound d))
      (symbolic-shift-set0 gs))
