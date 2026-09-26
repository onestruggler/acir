------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford circuits with CNOT, compiled to {H, S, CZ} (Amy, QPL 2018,
-- the characterisation in the proof of corollary 4.4, by another route)
--
-- Corollary 4.4 decides whether a Clifford circuit is the identity by
-- reducing the isometry restriction of its path-sum.  Over {H, S, CZ}
-- that restriction is reified by construction (PathSum.Circuit.⟦_⟧ᴿ,
-- and PathSum.Corollary carries the corollary to the circuit).  After
-- a CNOT the outputs of ⟦ C ⟧ are sums of variables, and the paper's
-- proof reifies the restriction by Gaussian elimination (formalised
-- as PathSum.Gauss).  This module takes another route for the Clifford
-- circuits of the gate set {H, CNOT, R_k, R_k†} -- those of level at
-- most 2, whose R_k and R_k† all have k ≤ 2.  It compiles them to
-- {H, S, CZ} and reduces the compiled circuit's restriction instead.
--
-- CNOT c t becomes H_t ; CZ_{c,t} ; H_t, whose unnormalised matrix is
-- twice CNOT's (cnot-matrix).  R_0 is the identity and becomes nothing;
-- R_1 = Z becomes S ; S and R_2 = S becomes S; R_1† = Z becomes S ; S
-- and R_2† = S† becomes S ; S ; S.  So the matrix of the compiled
-- circuit is 2^c times the circuit's, c the number of CNOTs
-- (compile-apply), while its normalisation is larger by 2c; the two
-- path-sums are therefore equivalent (compile-≋), and the corollary
-- transfers.  ⟦ C ⟧ is the identity exactly when a chain of reductions
-- of the compiled circuit's restriction that ends without path
-- variables ends at a path-sum that is syntactically |x⟩ ↦ |x⟩
-- (corollary-4-4-syntactic-compiled; for every such chain,
-- corollary-4-4-any-compiled).
--
-- This is not the paper's proof: the reduction runs on the restriction
-- of the compiled circuit's path-sum, not on that of ⟦ C ⟧, and no
-- complexity bound is stated.  R_k with k ≥ 3 is not Clifford; compile
-- drops it, and every result here assumes level C ≤ 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _∸_; _^_; s≤s)

module PathSum.CRK.Compile (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-identityʳ)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (divides)
open import Data.Integer.Properties using
  (+-identityˡ; *-identityˡ; *-identityʳ; *-zeroʳ; *-assoc; *-comm;
   *-distribˡ-+; *-distribʳ-+; pos-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_; contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; same-≗)
open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.CRK.Circuit M using
  (Gate; H; CNOT; R; R†; Circuit; norm; level; ⟦_⟧)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; gateᴬ-resp; applyᴬ-cong; prop-2-10)
open import PathSum.Cyclotomic M₀ using
  (Amp; N; 0ᴬ; _+ᴬ_; _-ᴬ_; -ᴬ_; _·ᴬ_; _≐_; zpow; rot; rot-map; rot-exp;
   rot-0; rot-anti; rot-comp; rot-·ᴬ; coeff-cong; √2·-map; √2·-twice;
   scale; scale-map; scale-·ᴬ; Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using (μ; x[_]; 0ᴾ; _≈[_]_)
open import PathSum.Reduction M using (¼; ½; _⟶*_)

import Data.Nat.Properties as ℕ
import PathSum.Circuit
import PathSum.CircuitSemantics
import PathSum.Corollary
import PathSum.Denotation

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  module Circ = PathSum.Circuit M
  module CSem = PathSum.CircuitSemantics M₀
  module Cor  = PathSum.Corollary M₀
  module Den  = PathSum.Denotation M₀

  variable
    n k′ : ℕ


------------------------------------------------------------------------
-- The compilation

-- The number of CNOTs.

cnots : Circuit n → ℕ
cnots []               = 0
cnots (H _ ∷ C)        = cnots C
cnots (CNOT _ _ _ ∷ C) = suc (cnots C)
cnots (R _ _ ∷ C)      = cnots C
cnots (R† _ _ ∷ C)     = cnots C

-- Each gate of level at most 2 as a circuit over {H, S, CZ}.  A gate
-- of higher level has no such circuit; it is dropped, and the results
-- below exclude it.

compile : Circuit n → Circ.Circuit n
compile []                             = []
compile (H w ∷ C)                      = Circ.H w ∷ compile C
compile (CNOT c t _ ∷ C)               =
  Circ.H t ∷ Circ.CZ c t ∷ Circ.H t ∷ compile C
compile (R zero w ∷ C)                 = compile C
compile (R (suc zero) w ∷ C)           = Circ.S w ∷ Circ.S w ∷ compile C
compile (R (suc (suc zero)) w ∷ C)     = Circ.S w ∷ compile C
compile (R (suc (suc (suc _))) _ ∷ C)  = compile C
compile (R† zero w ∷ C)                = compile C
compile (R† (suc zero) w ∷ C)          = Circ.S w ∷ Circ.S w ∷ compile C
compile (R† (suc (suc zero)) w ∷ C)    =
  Circ.S w ∷ Circ.S w ∷ Circ.S w ∷ compile C
compile (R† (suc (suc (suc _))) _ ∷ C) = compile C


------------------------------------------------------------------------
-- Amplitude algebra

-- As in PathSum.CRK.Semantics, a rotation is compared only with a
-- rotation by the same exponent, and an exponent is changed only by
-- rot-exp, or by rot-mod below, with both exponents written out.

private
  rot-cong : (a a′ : Amp) (e e′ : ℤ) → e ≡ e′ → a ≐ a′ →
             rot e a ≐ rot e′ a′
  rot-cong a a′ e e′ ee aa i =
    trans (rot-map e aa i) (rot-exp {e} {e′} a′ ee i)

  sum-cong : (a a′ b b′ : Amp) (e e′ : ℤ) → a ≐ a′ → e ≡ e′ → b ≐ b′ →
             (a +ᴬ rot e b) ≐ (a′ +ᴬ rot e′ b′)
  sum-cong a a′ b b′ e e′ aa ee bb i =
    cong₂ _+_ (aa i) (rot-cong b b′ e e′ ee bb i)

  -- The two signs of a Hadamard: ½ is the exponent H of ζ^H = -1
  -- (Cyclotomic's H, imported as rank).

  sign-0 : (a a′ b b′ : Amp) (e : ℤ) → a ≐ a′ → e ≡ 0ℤ → b ≐ b′ →
           (a +ᴬ rot e b) ≐ (a′ +ᴬ b′)
  sign-0 a a′ b b′ e aa ee bb i = cong₂ _+_ (aa i)
    (trans (rot-exp {e} {0ℤ} b ee i) (trans (rot-0 b i) (bb i)))

  sign-1 : (a a′ b b′ : Amp) (e : ℤ) → a ≐ a′ → e ≡ 0ℤ + (+ rank) →
           b ≐ b′ → (a +ᴬ rot e b) ≐ (a′ -ᴬ b′)
  sign-1 a a′ b b′ e aa ee bb i = cong₂ _+_ (aa i)
    (trans (rot-exp {e} {0ℤ + (+ rank)} b ee i)
      (trans (rot-anti 0ℤ b i) (cong -_ (trans (rot-0 b i) (bb i)))))

  -- (-1)^b, as a function of b.

  sgn : Bool → Amp → Amp
  sgn false a = a
  sgn true  a = -ᴬ a

  rot-½ : (b : Bool) (a : Amp) → rot (½ * [ b ]ᶻ) a ≐ sgn b a
  rot-½ false a i =
    trans (rot-exp {½ * [ false ]ᶻ} {0ℤ} a (*-zeroʳ ½) i) (rot-0 a i)
  rot-½ true  a i = trans
    (rot-exp {½ * [ true ]ᶻ} {0ℤ + (+ rank)} a
             (trans (*-identityʳ ½) (sym (+-identityˡ ½))) i)
    (trans (rot-anti 0ℤ a i) (cong -_ (rot-0 a i)))

  -- ζ^N = 1: exponents that differ by a multiple of N rotate alike.

  rot-mod : (e e′ q : ℤ) (a : Amp) → e ≡ e′ + q * (+ N) → rot e a ≐ rot e′ a
  rot-mod e e′ q a eq i =
    coeff-cong a ((+ toℕ i) - e) ((+ toℕ i) - e′) (divides (- q)
      (trans (cong (λ f → ((+ toℕ i) - f) - ((+ toℕ i) - e′)) eq)
             (shape (+ toℕ i) e′ q (+ N))))
    where
    shape : ∀ u v r s → (u - (v + r * s)) - (u - v) ≡ (- r) * s
    shape = solve 4 (λ u v r s → (u :- (v :+ r :* s)) :- (u :- v)
                                 := (:- r) :* s) refl

  -- The exponents: ½ = ¼ + ¼, and N = 4 · ¼.

  twice : ∀ a → a * (+ 2) ≡ a + a
  twice = solve 1 (λ a → a :* con (+ 2) := a :+ a) refl

  ½≡¼+¼ : ½ ≡ ¼ + ¼
  ½≡¼+¼ = trans (pow-suc (suc M₀)) (twice ¼)

  N≡4¼ : + N ≡ (¼ + ¼) + (¼ + ¼)
  N≡4¼ = trans (pow-suc (suc (suc M₀)))
    (trans (twice ½) (cong₂ _+_ ½≡¼+¼ ½≡¼+¼))

  -- Scalars.

  ·ᴬ-2^ : ∀ j a → + (2 ^ j) * ((+ 2) * a) ≡ + (2 ^ suc j) * a
  ·ᴬ-2^ j a = trans (sym (*-assoc (+ (2 ^ j)) (+ 2) a))
    (cong (_* a) (trans (*-comm (+ (2 ^ j)) (+ 2))
                        (sym (pos-* 2 (2 ^ j)))))


------------------------------------------------------------------------
-- The gates' matrices

-- The column action of PathSum.CRK.Semantics is linear.

private
  gateᴬ-· : (g : Gate n) (s : ℤ) (χ : Column n) →
            ∀ z → gateᴬ g (λ u → s ·ᴬ χ u) z ≐ s ·ᴬ gateᴬ g χ z
  gateᴬ-· (H w) s χ z i = trans
    (cong (λ u → s * χ (z [ w ≔ false ]) i + u)
          (rot-·ᴬ (½ * [ z w ]ᶻ) s (χ (z [ w ≔ true ])) i))
    (sym (*-distribˡ-+ s (χ (z [ w ≔ false ]) i)
                         (rot (½ * [ z w ]ᶻ) (χ (z [ w ≔ true ])) i)))
  gateᴬ-· (CNOT c t _) s χ z i = refl
  gateᴬ-· (R k w)  s χ z = rot-·ᴬ (pow (M ∸ k) * [ z w ]ᶻ) s (χ z)
  gateᴬ-· (R† k w) s χ z =
    rot-·ᴬ (- (pow (M ∸ k) * [ z w ]ᶻ)) s (χ z)

  applyᴬ-· : (C : Circuit n) (s : ℤ) (χ : Column n) →
             ∀ z → applyᴬ C (λ u → s ·ᴬ χ u) z ≐ s ·ᴬ applyᴬ C χ z
  applyᴬ-· []      s χ z i = refl
  applyᴬ-· (g ∷ C) s χ z i = trans
    (applyᴬ-cong C {gateᴬ g (λ u → s ·ᴬ χ u)} {λ u → s ·ᴬ gateᴬ g χ u}
                 (gateᴬ-· g s χ) z i)
    (applyᴬ-· C s (gateᴬ g χ) z i)

  resp-≐ : {φ χ : Column n} → (∀ z → φ z ≐ χ z) → Respects χ → Respects φ
  resp-≐ φχ rχ z z′ zz i =
    trans (φχ z i) (trans (rχ z z′ zz i) (sym (φχ z′ i)))

  resp-· : (s : ℤ) {χ : Column n} → Respects χ → Respects (λ u → s ·ᴬ χ u)
  resp-· s rχ z z′ zz i = cong (s *_) (rχ z z′ zz i)

-- H_t ; CZ_{c,t} ; H_t is twice CNOT.  The first Hadamard turns the
-- entries a and b at z[t≔0] and z[t≔1] into a + b and a - b, CZ signs
-- the second by (-1)^(z_c), and the last Hadamard adds the two with the
-- sign (-1)^(z_t): 2a when z_t ⊕ z_c = 0, and 2b when it is 1.

private
  fin : (p q : Bool) (A B : Amp) →
        ∀ i → (A i + B i) + sgn p (sgn q (A -ᴬ B)) i ≡
              (+ 2) * (if (p xor q) then B else A) i
  fin false false A B i = e₀ (A i) (B i)
    where
    e₀ : ∀ a b → (a + b) + (a - b) ≡ (+ 2) * a
    e₀ = solve 2 (λ a b → (a :+ b) :+ (a :- b) := con (+ 2) :* a) refl
  fin false true  A B i = e₁ (A i) (B i)
    where
    e₁ : ∀ a b → (a + b) + (- (a - b)) ≡ (+ 2) * b
    e₁ = solve 2 (λ a b → (a :+ b) :+ (:- (a :- b)) := con (+ 2) :* b) refl
  fin true  false A B i = e₁ (A i) (B i)
    where
    e₁ : ∀ a b → (a + b) + (- (a - b)) ≡ (+ 2) * b
    e₁ = solve 2 (λ a b → (a :+ b) :+ (:- (a :- b)) := con (+ 2) :* b) refl
  fin true  true  A B i = e₂ (A i) (B i)
    where
    e₂ : ∀ a b → (a + b) + (- (- (a - b))) ≡ (+ 2) * a
    e₂ = solve 2 (λ a b → (a :+ b) :+ (:- (:- (a :- b)))
                          := con (+ 2) :* a) refl

cnot-matrix : (c t : Fin n) → c ≢ t → (ψ : Column n) → Respects ψ →
              ∀ z → CSem.applyᴬ (Circ.H t ∷ Circ.CZ c t ∷ Circ.H t ∷ []) ψ z
                    ≐ (+ 2) ·ᴬ ψ (z [ t ≔ z t xor z c ])
cnot-matrix {n} c t c≢t ψ resp z i =
  trans (outer i)
    (trans (cong (λ u → (ψ₀ i + ψ₁ i) + u) (signs i))
      (trans (fin (z t) (z c) ψ₀ ψ₁ i)
             (cong (λ u → (+ 2) * u) (sym (pick (z t xor z c))))))
  where
  φ₁ φ₂ : Column n
  φ₁ = CSem.gateᴬ (Circ.H t) ψ
  φ₂ = CSem.gateᴬ (Circ.CZ c t) φ₁

  ψ₀ ψ₁ : Amp
  ψ₀ = ψ (z [ t ≔ false ])
  ψ₁ = ψ (z [ t ≔ true ])

  -- The first Hadamard.

  A : φ₁ (z [ t ≔ false ]) ≐ (ψ₀ +ᴬ ψ₁)
  A = sign-0 (ψ (z [ t ≔ false ] [ t ≔ false ])) ψ₀
             (ψ (z [ t ≔ false ] [ t ≔ true ])) ψ₁
             (½ * [ (z [ t ≔ false ]) t ]ᶻ)
             (resp _ _ (≔-≔ z t false false))
             (trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z t false)) (*-zeroʳ ½))
             (resp _ _ (≔-≔ z t false true))

  B : φ₁ (z [ t ≔ true ]) ≐ (ψ₀ -ᴬ ψ₁)
  B = sign-1 (ψ (z [ t ≔ true ] [ t ≔ false ])) ψ₀
             (ψ (z [ t ≔ true ] [ t ≔ true ])) ψ₁
             (½ * [ (z [ t ≔ true ]) t ]ᶻ)
             (resp _ _ (≔-≔ z t true false))
             (trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z t true))
                    (trans (*-identityʳ ½) (sym (+-identityˡ ½))))
             (resp _ _ (≔-≔ z t true true))

  -- CZ: nothing at z[t≔0], the sign (-1)^(z_c) at z[t≔1].

  C₀ : φ₂ (z [ t ≔ false ]) ≐ (ψ₀ +ᴬ ψ₁)
  C₀ j = trans
    (rot-exp {½ * [ (z [ t ≔ false ]) c ∧ (z [ t ≔ false ]) t ]ᶻ} {0ℤ}
             (φ₁ (z [ t ≔ false ])) e j)
    (trans (rot-0 (φ₁ (z [ t ≔ false ])) j) (A j))
    where
    e : ½ * [ (z [ t ≔ false ]) c ∧ (z [ t ≔ false ]) t ]ᶻ ≡ 0ℤ
    e = trans (cong (λ b → ½ * [ (z [ t ≔ false ]) c ∧ b ]ᶻ)
                    (≔-here z t false))
      (trans (cong (λ b → ½ * [ b ]ᶻ) (∧-zeroʳ ((z [ t ≔ false ]) c)))
             (*-zeroʳ ½))

  C₁ : φ₂ (z [ t ≔ true ]) ≐ rot (½ * [ z c ]ᶻ) (ψ₀ -ᴬ ψ₁)
  C₁ = rot-cong (φ₁ (z [ t ≔ true ])) (ψ₀ -ᴬ ψ₁)
    (½ * [ (z [ t ≔ true ]) c ∧ (z [ t ≔ true ]) t ]ᶻ) (½ * [ z c ]ᶻ)
    (trans (cong₂ (λ a b → ½ * [ a ∧ b ]ᶻ)
                  (≔-there z true c≢t) (≔-here z t true))
           (cong (λ a → ½ * [ a ]ᶻ) (∧-identityʳ (z c))))
    B

  -- The last Hadamard.

  outer : CSem.gateᴬ (Circ.H t) φ₂ z ≐
          ((ψ₀ +ᴬ ψ₁) +ᴬ rot (½ * [ z t ]ᶻ) (rot (½ * [ z c ]ᶻ) (ψ₀ -ᴬ ψ₁)))
  outer = sum-cong (φ₂ (z [ t ≔ false ])) (ψ₀ +ᴬ ψ₁)
                   (φ₂ (z [ t ≔ true ])) (rot (½ * [ z c ]ᶻ) (ψ₀ -ᴬ ψ₁))
                   (½ * [ z t ]ᶻ) (½ * [ z t ]ᶻ) C₀ refl C₁

  signs : rot (½ * [ z t ]ᶻ) (rot (½ * [ z c ]ᶻ) (ψ₀ -ᴬ ψ₁)) ≐
          sgn (z t) (sgn (z c) (ψ₀ -ᴬ ψ₁))
  signs j = trans (rot-map (½ * [ z t ]ᶻ) (rot-½ (z c) (ψ₀ -ᴬ ψ₁)) j)
                  (rot-½ (z t) (sgn (z c) (ψ₀ -ᴬ ψ₁)) j)

  pick : (b : Bool) → ψ (z [ t ≔ b ]) i ≡ (if b then ψ₁ else ψ₀) i
  pick true  = refl
  pick false = refl

-- The phase gates of level at most 2: R_0 is the identity, R_1 = S², R_2
-- = S, R_1† = S² and R_2† = S³.

R₀-matrix : (w : Fin n) (ψ : Column n) → ∀ z → ψ z ≐ gateᴬ (R 0 w) ψ z
R₀-matrix w ψ z i = sym (trans
  (rot-mod (pow (M ∸ 0) * [ z w ]ᶻ) 0ℤ [ z w ]ᶻ (ψ z)
    (trans (*-comm (pow (M ∸ 0)) [ z w ]ᶻ)
           (sym (+-identityˡ ([ z w ]ᶻ * (+ N)))))
    i)
  (rot-0 (ψ z) i))

R₁-matrix : (w : Fin n) (ψ : Column n) →
            ∀ z → CSem.applyᴬ (Circ.S w ∷ Circ.S w ∷ []) ψ z ≐
                  gateᴬ (R 1 w) ψ z
R₁-matrix w ψ z i = trans (rot-comp (¼ * [ z w ]ᶻ) (¼ * [ z w ]ᶻ) (ψ z) i)
  (rot-exp {¼ * [ z w ]ᶻ + ¼ * [ z w ]ᶻ} {pow (M ∸ 1) * [ z w ]ᶻ}
    (ψ z)
    (trans (sym (*-distribʳ-+ [ z w ]ᶻ ¼ ¼))
           (cong (_* [ z w ]ᶻ) (sym ½≡¼+¼)))
    i)

R₂-matrix : (w : Fin n) (ψ : Column n) →
            ∀ z → CSem.applyᴬ (Circ.S w ∷ []) ψ z ≐ gateᴬ (R 2 w) ψ z
R₂-matrix w ψ z =
  rot-exp {¼ * [ z w ]ᶻ} {pow (M ∸ 2) * [ z w ]ᶻ} (ψ z) refl

R†₀-matrix : (w : Fin n) (ψ : Column n) → ∀ z → ψ z ≐ gateᴬ (R† 0 w) ψ z
R†₀-matrix w ψ z i = sym (trans
  (rot-mod (- (pow (M ∸ 0) * [ z w ]ᶻ)) 0ℤ (- [ z w ]ᶻ) (ψ z)
    (e (+ N) [ z w ]ᶻ) i)
  (rot-0 (ψ z) i))
  where
  e : ∀ s b → - (s * b) ≡ 0ℤ + (- b) * s
  e = solve 2 (λ s b → :- (s :* b) := con 0ℤ :+ (:- b) :* s) refl

R†₁-matrix : (w : Fin n) (ψ : Column n) →
             ∀ z → CSem.applyᴬ (Circ.S w ∷ Circ.S w ∷ []) ψ z ≐
                   gateᴬ (R† 1 w) ψ z
R†₁-matrix w ψ z i = trans (rot-comp (¼ * [ z w ]ᶻ) (¼ * [ z w ]ᶻ) (ψ z) i)
  (rot-mod (¼ * [ z w ]ᶻ + ¼ * [ z w ]ᶻ)
           (- (pow (M ∸ 1) * [ z w ]ᶻ)) [ z w ]ᶻ (ψ z)
    (trans (e ¼ [ z w ]ᶻ)
           (cong₂ (λ h f → - (h * [ z w ]ᶻ) + [ z w ]ᶻ * f)
                  (sym ½≡¼+¼) (sym N≡4¼)))
    i)
  where
  e : ∀ q b → q * b + q * b ≡ - ((q + q) * b) + b * ((q + q) + (q + q))
  e = solve 2 (λ q b → q :* b :+ q :* b
                       := :- ((q :+ q) :* b) :+ b :* ((q :+ q) :+ (q :+ q)))
                refl

R†₂-matrix : (w : Fin n) (ψ : Column n) →
             ∀ z → CSem.applyᴬ (Circ.S w ∷ Circ.S w ∷ Circ.S w ∷ []) ψ z ≐
                   gateᴬ (R† 2 w) ψ z
R†₂-matrix w ψ z i = trans
  (rot-map (¼ * [ z w ]ᶻ) (rot-comp (¼ * [ z w ]ᶻ) (¼ * [ z w ]ᶻ) (ψ z)) i)
  (trans (rot-comp (¼ * [ z w ]ᶻ) (¼ * [ z w ]ᶻ + ¼ * [ z w ]ᶻ) (ψ z) i)
    (rot-mod (¼ * [ z w ]ᶻ + (¼ * [ z w ]ᶻ + ¼ * [ z w ]ᶻ))
             (- (pow (M ∸ 2) * [ z w ]ᶻ)) [ z w ]ᶻ (ψ z)
      (trans (e ¼ [ z w ]ᶻ)
             (cong (λ f → - (¼ * [ z w ]ᶻ) + [ z w ]ᶻ * f) (sym N≡4¼)))
      i))
  where
  e : ∀ q b → q * b + (q * b + q * b) ≡
              - (q * b) + b * ((q + q) + (q + q))
  e = solve 2 (λ q b → q :* b :+ (q :* b :+ q :* b)
                       := :- (q :* b) :+ b :* ((q :+ q) :+ (q :+ q)))
                refl


------------------------------------------------------------------------
-- The compiled circuit computes 2^(cnots C) times the circuit's matrix

private
  Computes : Circuit n → Set
  Computes {n} C = (ψ : Column n) → Respects ψ →
    ∀ z → CSem.applyᴬ (compile C) ψ z ≐ (+ (2 ^ cnots C)) ·ᴬ applyᴬ C ψ z

  -- A compiled gate that computes the gate's matrix, up to the scalar
  -- s, followed by the rest of the circuit.

  via : (C : Circuit n) → Computes C → (s : ℤ) (φ χ : Column n) →
        Respects χ → (∀ z → φ z ≐ s ·ᴬ χ z) →
        ∀ z → CSem.applyᴬ (compile C) φ z ≐
              (+ (2 ^ cnots C)) ·ᴬ (s ·ᴬ applyᴬ C χ z)
  via C ih s φ χ rχ φχ z i = trans (ih φ (resp-≐ φχ (resp-· s rχ)) z i)
    (cong (λ u → + (2 ^ cnots C) * u)
          (trans (applyᴬ-cong C φχ z i) (applyᴬ-· C s χ z i)))

  -- The same without a scalar.

  via₁ : (C : Circuit n) → Computes C → (φ χ : Column n) → Respects χ →
         (∀ z → φ z ≐ χ z) →
         ∀ z → CSem.applyᴬ (compile C) φ z ≐
               (+ (2 ^ cnots C)) ·ᴬ applyᴬ C χ z
  via₁ C ih φ χ rχ φχ z i = trans (ih φ (resp-≐ φχ rχ) z i)
    (cong (λ u → + (2 ^ cnots C) * u) (applyᴬ-cong C φχ z i))

  ¬3≤2 : ∀ {k} → ¬ (suc (suc (suc k)) ≤ 2)
  ¬3≤2 (s≤s (s≤s ()))

compile-apply : (C : Circuit n) → level C ≤ 2 → (ψ : Column n) →
                Respects ψ → ∀ z →
                CSem.applyᴬ (compile C) ψ z ≐
                (+ (2 ^ cnots C)) ·ᴬ applyᴬ C ψ z
compile-apply [] lv ψ resp z i = sym (*-identityˡ (ψ z i))
compile-apply (H w ∷ C) lv ψ resp =
  compile-apply C lv (gateᴬ (H w) ψ) (gateᴬ-resp (H w) resp)
compile-apply (CNOT c t p ∷ C) lv ψ resp z i = trans
  (via C (compile-apply C lv) (+ 2)
       (CSem.applyᴬ (Circ.H t ∷ Circ.CZ c t ∷ Circ.H t ∷ []) ψ)
       (gateᴬ (CNOT c t p) ψ) (gateᴬ-resp (CNOT c t p) resp)
       (cnot-matrix c t p ψ resp) z i)
  (·ᴬ-2^ (cnots C) (applyᴬ C (gateᴬ (CNOT c t p) ψ) z i))
compile-apply (R zero w ∷ C) lv ψ resp =
  via₁ C (compile-apply C lv) ψ (gateᴬ (R 0 w) ψ)
       (gateᴬ-resp (R 0 w) resp) (R₀-matrix w ψ)
compile-apply (R (suc zero) w ∷ C) lv ψ resp =
  via₁ C (compile-apply C (ℕ.m⊔n≤o⇒n≤o 1 (level C) lv))
       (CSem.applyᴬ (Circ.S w ∷ Circ.S w ∷ []) ψ) (gateᴬ (R 1 w) ψ)
       (gateᴬ-resp (R 1 w) resp) (R₁-matrix w ψ)
compile-apply (R (suc (suc zero)) w ∷ C) lv ψ resp =
  via₁ C (compile-apply C (ℕ.m⊔n≤o⇒n≤o 2 (level C) lv))
       (CSem.applyᴬ (Circ.S w ∷ []) ψ) (gateᴬ (R 2 w) ψ)
       (gateᴬ-resp (R 2 w) resp) (R₂-matrix w ψ)
compile-apply (R (suc (suc (suc k))) w ∷ C) lv =
  contradiction (ℕ.m⊔n≤o⇒m≤o (suc (suc (suc k))) (level C) lv) ¬3≤2
compile-apply (R† zero w ∷ C) lv ψ resp =
  via₁ C (compile-apply C lv) ψ (gateᴬ (R† 0 w) ψ)
       (gateᴬ-resp (R† 0 w) resp) (R†₀-matrix w ψ)
compile-apply (R† (suc zero) w ∷ C) lv ψ resp =
  via₁ C (compile-apply C (ℕ.m⊔n≤o⇒n≤o 1 (level C) lv))
       (CSem.applyᴬ (Circ.S w ∷ Circ.S w ∷ []) ψ) (gateᴬ (R† 1 w) ψ)
       (gateᴬ-resp (R† 1 w) resp) (R†₁-matrix w ψ)
compile-apply (R† (suc (suc zero)) w ∷ C) lv ψ resp =
  via₁ C (compile-apply C (ℕ.m⊔n≤o⇒n≤o 2 (level C) lv))
       (CSem.applyᴬ (Circ.S w ∷ Circ.S w ∷ Circ.S w ∷ []) ψ)
       (gateᴬ (R† 2 w) ψ)
       (gateᴬ-resp (R† 2 w) resp) (R†₂-matrix w ψ)
compile-apply (R† (suc (suc (suc k))) w ∷ C) lv =
  contradiction (ℕ.m⊔n≤o⇒m≤o (suc (suc (suc k))) (level C) lv) ¬3≤2


------------------------------------------------------------------------
-- The two path-sums are equivalent

-- The compiled circuit's normalisation is larger by two for each CNOT,
-- which pays for the factor 2 in each CNOT's matrix.

private
  ·ᴬ-2^′ : ∀ j a → (+ 2) * (+ (2 ^ j) * a) ≡ + (2 ^ suc j) * a
  ·ᴬ-2^′ j a = trans (sym (*-assoc (+ 2) (+ (2 ^ j)) a))
                     (cong (_* a) (sym (pos-* 2 (2 ^ j))))

  scale-compile : (C : Circuit n) (A : Amp) →
                  scale (Circ.norm (compile C)) A ≐
                  scale (norm C) ((+ (2 ^ cnots C)) ·ᴬ A)
  scale-compile []                A i = sym (*-identityˡ (A i))
  scale-compile (H w ∷ C)         A   = √2·-map (scale-compile C A)
  scale-compile (CNOT c t p ∷ C)  A i =
    trans (√2·-twice (scale (Circ.norm (compile C)) A) i)
      (trans (cong (λ u → (+ 2) * u) (scale-compile C A i))
        (trans (sym (scale-·ᴬ (norm C) (+ 2) ((+ (2 ^ cnots C)) ·ᴬ A) i))
               (scale-map (norm C) (λ j → ·ᴬ-2^′ (cnots C) (A j)) i)))
  scale-compile (R zero w ∷ C)                A = scale-compile C A
  scale-compile (R (suc zero) w ∷ C)          A = scale-compile C A
  scale-compile (R (suc (suc zero)) w ∷ C)    A = scale-compile C A
  scale-compile (R (suc (suc (suc _))) _ ∷ C) A = scale-compile C A
  scale-compile (R† zero w ∷ C)               A = scale-compile C A
  scale-compile (R† (suc zero) w ∷ C)         A = scale-compile C A
  scale-compile (R† (suc (suc zero)) w ∷ C)   A = scale-compile C A
  scale-compile (R† (suc (suc (suc _))) _ ∷ C) A = scale-compile C A

  δ-resp : (x : Assign n) → Respects (δ x)
  δ-resp x z z′ zz i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
    (same-≗ {x = x} {x′ = x} {z = z} {z′ = z′} (λ _ → refl) zz)

-- Proposition 2.10 on both sides: the amplitudes of the compiled
-- circuit are 2^(cnots C) times those of the circuit.

compile-≋ : (C : Circuit n) → level C ≤ 2 → ⟦ C ⟧ ≋ Circ.⟦ compile C ⟧
compile-≋ C lv x z i = trans (scale-compile C (amp ⟦ C ⟧ x z) i)
  (scale-map (norm C) (λ j → trans
    (cong (λ u → + (2 ^ cnots C) * u) (prop-2-10 C x z j))
    (trans (sym (compile-apply C lv (δ x) (δ-resp x) z j))
           (sym (CSem.prop-2-10 (compile C) x z j)))) i)


------------------------------------------------------------------------
-- Corollary 4.4, through the compiled circuit

private
  ⇔-trans : {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
  ⇔-trans ab bc = mk⇔ (λ a → Equivalence.to bc (Equivalence.to ab a))
                      (λ c → Equivalence.from ab (Equivalence.from bc c))

compile-id : (C : Circuit n) → level C ≤ 2 →
             (⟦ C ⟧ ≋ idPS ⇔ Circ.⟦ compile C ⟧ ≋ idPS)
compile-id C lv = mk⇔
  (λ eq → Den.≋-trans {ξ = Circ.⟦ compile C ⟧} {ζ = ⟦ C ⟧} {χ = idPS}
            (Den.≋-sym {ξ = ⟦ C ⟧} {ζ = Circ.⟦ compile C ⟧} (compile-≋ C lv))
            eq)
  (λ eq → Den.≋-trans {ξ = ⟦ C ⟧} {ζ = Circ.⟦ compile C ⟧} {χ = idPS}
            (compile-≋ C lv) eq)

-- Reducing the compiled circuit's restriction either refutes the
-- circuit or ends without path variables, at a path-sum whose being the
-- identity is exactly the circuit's.

corollary-4-4-compiled : (C : Circuit n) → level C ≤ 2 →
  (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
     (Circ.⟦ compile C ⟧ᴿ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
  ⊎ ¬ (⟦ C ⟧ ≋ idPS)
corollary-4-4-compiled {n} C lv = go (Cor.corollary-4-4-⟦⟧ (compile C))
  where
  go : (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
          (Circ.⟦ compile C ⟧ᴿ ⟶* ξ′) ×
          (Circ.⟦ compile C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
       ⊎ ¬ (Circ.⟦ compile C ⟧ ≋ idPS) →
       (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ 0) →
          (Circ.⟦ compile C ⟧ᴿ ⟶* ξ′) × (⟦ C ⟧ ≋ idPS ⇔ ξ′ ≋ idPS))
       ⊎ ¬ (⟦ C ⟧ ≋ idPS)
  go (inj₁ (k′ , ξ′ , steps , iff)) =
    inj₁ (k′ , ξ′ , steps , ⇔-trans (compile-id C lv) iff)
  go (inj₂ ¬id) = inj₂ (λ eq → ¬id (Equivalence.to (compile-id C lv) eq))

-- Whatever chain of reductions of the compiled circuit's restriction
-- ends without path variables, ⟦ C ⟧ is the identity exactly when that
-- endpoint is syntactically |x⟩ ↦ |x⟩.

corollary-4-4-any-compiled : (C : Circuit n) → level C ≤ 2 →
  {ξ′ : PathSum n k′ 0} → Circ.⟦ compile C ⟧ᴿ ⟶* ξ′ →
  (⟦ C ⟧ ≋ idPS ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ))
corollary-4-4-any-compiled C lv steps =
  ⇔-trans (compile-id C lv) (Cor.corollary-4-4-any (compile C) steps)

-- In particular such a chain ends at the identity's polynomials
-- exactly for the identity circuits.

corollary-4-4-syntactic-compiled : (C : Circuit n) → level C ≤ 2 →
  (⟦ C ⟧ ≋ idPS ⇔
   ∃ λ (ξ′ : PathSum n 0 0) →
     (Circ.⟦ compile C ⟧ᴿ ⟶* ξ′) ×
     (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow M ] 0ᴾ)
corollary-4-4-syntactic-compiled C lv =
  ⇔-trans (compile-id C lv) (Cor.corollary-4-4-syntactic (compile C))
