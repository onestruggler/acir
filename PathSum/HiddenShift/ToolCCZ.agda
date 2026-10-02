------------------------------------------------------------------------
-- Presentations of groups
--
-- The doubly controlled Z gate of the paper's tool is the diagonal
-- (-1)^{abc} (Amy, QPL 2018, section 5.2)
--
-- The random oracles of the paper's hidden shift benchmarks contain
-- "a random doubly controlled-Z gate, expanded out to Clifford+T".
-- The paper's tool, Feynman, expands it by its function ccz
-- (src/Feynman/Core.hs, as of the paper):
--
--    ccz x y z = T x; T y; T z; CNOT x y; CNOT y z; CNOT z x;
--                T† x; T† y; T z; CNOT y x; T† x;
--                CNOT y z; CNOT z x; CNOT x y
--
-- -- its sixteen-gate Toffoli circuit (PathSum.Toffoli.Depth3's tof₃)
-- without the two Hadamards on the target.  Here it is as cczᶜ a b c,
-- over {H, CNOT, R_k, R_k†} with T = R₃ (on any three distinct wires),
-- and the theorem that it is the diagonal ζ^(½ z_a z_b z_c), i.e.
-- (-1)^{abc}, in the form of PathSum.HiddenShift.Gates (Diag-ccz,
-- Signs-ccz).  Gates's own CCZᶜ computes each parity with its own CNOTs
-- and uncomputes it at once, so Gates's Diag-conj builds its diagonal
-- one conjugated phase at a time; the tool's network shares its CNOTs,
-- so its intermediate gates are not diagonal, and a different argument
-- is needed.
--
-- The argument.  The column entries at assignments that agree off the
-- three wires a, b, c are only permuted among themselves by a CNOT on
-- those wires and only rotated by a T or T†.  So write z ◂ (α, β, γ)
-- for z with α, β, γ on a, b, c (PathSum.Toffoli.Gate's three-wire
-- assignments w3), and say that a circuit is the monomial matrix
-- (f, k) on the three wires (Mon3) when, for every column ψ that reads
-- assignments only through their values,
--
--    (C ψ)(z ◂ τ) = ζ^(2^(M-3) · k(τ)) ψ(z ◂ f(τ))
--
-- for every z and every triple τ.  A CNOT is (its reversible map on
-- the triple, 0), a T or T† on one of the wires (the identity, ±that
-- bit), and monomial matrices compose (Mon3-∷) by composing the maps
-- and adding the phases.  The fourteen gates compose to the map
-- f(τ) = τ and the phase k(τ) = 4 τ_a τ_b τ_c, both checked on the
-- eight triples by evaluation; 2^(M-3) · 4 = ½.  Every z is
-- z ◂ (z_a, z_b, z_c), so the circuit multiplies the entry at z by
-- ζ^(½ z_a z_b z_c).  As Gates's Diag-CCZ, the phase is exact, an
-- integer equation and not merely one modulo 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.ToolCCZ (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (*-zeroʳ; *-distribˡ-+; neg-distribʳ-*; *-assoc)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-≔; ≔-comm; ≔-cong; ≔-self)
open import PathSum.CircuitSemantics M₀ using (Column)
open import PathSum.Cyclotomic M₀ using
  (_≐_; rot; rot-map; rot-exp; rot-0; rot-comp; Respects)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Gates M₀ using
  (Diag; diag; Signs; Diag⇒Signs)
open import PathSum.Toffoli.Gate M₀ using (module Wires)

open +-*-Solver using (solve; con; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using (Gate; CNOT; R; R†; Circuit)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; applyᴬ-resp; gateᴬ-resp)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Reduction M using (½)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The circuit

-- The tool's ccz x y z with x, y, z = a, b, c; T = R₃, T† = R₃†.  The
-- head of the list is applied first.

cczᶜ : (a b c : Fin n) → a ≢ b → a ≢ c → b ≢ c → Circuit n
cczᶜ a b c a≢b a≢c b≢c =
  R 3 a ∷ R 3 b ∷ R 3 c ∷
  CNOT a b a≢b ∷ CNOT b c b≢c ∷ CNOT c a (λ e → a≢c (sym e)) ∷
  R† 3 a ∷ R† 3 b ∷ R 3 c ∷
  CNOT b a (λ e → a≢b (sym e)) ∷ R† 3 a ∷
  CNOT b c b≢c ∷ CNOT c a (λ e → a≢c (sym e)) ∷ CNOT a b a≢b ∷ []


------------------------------------------------------------------------
-- Triples

-- The bits on the three wires.

Tri : Set
Tri = Bool × Bool × Bool

-- A property of all eight triples, from each.

all-tri : {P : Tri → Set} →
          P (false , false , false) → P (false , false , true) →
          P (false , true , false) → P (false , true , true) →
          P (true , false , false) → P (true , false , true) →
          P (true , true , false) → P (true , true , true) →
          ∀ τ → P τ
all-tri p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ (false , false , false) = p₀
all-tri p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ (false , false , true)  = p₁
all-tri p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ (false , true , false)  = p₂
all-tri p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ (false , true , true)   = p₃
all-tri p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ (true , false , false)  = p₄
all-tri p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ (true , false , true)   = p₅
all-tri p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ (true , true , false)   = p₆
all-tri p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇ (true , true , true)    = p₇

-- Their product, the monomial of CCZ.

and₃ : Tri → Bool
and₃ (α , β , γ) = α ∧ (β ∧ γ)


------------------------------------------------------------------------
-- Arithmetic

private
  -- T is 2^(M-3), and four of them are ½.

  T : ℤ
  T = pow M₀

  ⅛·4 : T * (+ 4) ≡ ½
  ⅛·4 = trans (shape T)
    (trans (cong (_* (+ 2)) (sym (pow-suc M₀))) (sym (pow-suc (suc M₀))))
    where
    shape : ∀ q → q * (+ 4) ≡ (q * (+ 2)) * (+ 2)
    shape = solve 1 (λ q → q :* con (+ 4) := (q :* con (+ 2)) :* con (+ 2))
                    refl

  -- No phase.

  rot-zero : ∀ a → rot (T * 0ℤ) a ≐ a
  rot-zero a i = trans (rot-exp {T * 0ℤ} {0ℤ} a (*-zeroʳ T) i) (rot-0 a i)


------------------------------------------------------------------------
-- Monomial matrices on three wires

module Three {a b c : Fin n} (a≢b : a ≢ b) (a≢c : a ≢ c) (b≢c : b ≢ c)
  where

  private
    module W = Wires a≢b a≢c b≢c

  -- z with the triple τ on a, b, c.

  infixl 9 _◂_

  _◂_ : Assign n → Tri → Assign n
  z ◂ (α , β , γ) = W.w3 z α β γ

  -- Every assignment is itself with its own bits written back.

  ◂-self : (z : Assign n) → ∀ j → z j ≡ (z ◂ (z a , z b , z c)) j
  ◂-self z j = trans (sym (≔-self z c j)) (W.w3-x z (z c) j)

  -- Overwriting a, and so a CNOT onto a, on such an assignment.

  w3-set-a : ∀ z α β γ α′ u →
             (W.w3 z α β γ [ a ≔ α′ ]) u ≡ W.w3 z α′ β γ u
  w3-set-a z α β γ α′ u =
    trans (≔-comm (z [ a ≔ α ] [ b ≔ β ]) γ α′ (λ e → a≢c (sym e)) u)
          (≔-cong c γ (λ v →
             trans (≔-comm (z [ a ≔ α ]) β α′ (λ e → a≢b (sym e)) v)
                   (≔-cong b β (≔-≔ z a α α′) v)) u)

  cnot-a : (z : Assign n) (w : Fin n) (α β γ v : Bool) → W.w3 z α β γ w ≡ v →
           ∀ u → (W.w3 z α β γ [ a ≔ W.w3 z α β γ a xor W.w3 z α β γ w ]) u ≡
                 W.w3 z (α xor v) β γ u
  cnot-a z w α β γ v eq u =
    trans (cong (λ x → (W.w3 z α β γ [ a ≔ x ]) u)
                (cong₂ _xor_ (W.w3-c₁ z α β γ) eq))
          (w3-set-a z α β γ (α xor v) u)

  -- C is the monomial matrix (f, k): on every column, the entry at
  -- z ◂ τ is ζ^(T k(τ)) times the entry at z ◂ f(τ).

  record Mon3 (C : Circuit n) (f : Tri → Tri) (k : Tri → ℤ) : Set where
    constructor mon3
    field
      monomial : (ψ : Column n) → Respects ψ → ∀ z τ →
                 applyᴬ C ψ (z ◂ τ) ≐ rot (T * k τ) (ψ (z ◂ f τ))

  open Mon3 public

  -- The empty circuit, and a gate followed by a circuit.

  Mon3-[] : Mon3 [] (λ τ → τ) (λ _ → 0ℤ)
  Mon3-[] = mon3 λ ψ r z τ i → sym (rot-zero (ψ (z ◂ τ)) i)

  Mon3-∷ : {g : Gate n} {C : Circuit n} {f f′ : Tri → Tri}
           {k k′ : Tri → ℤ} →
           Mon3 (g ∷ []) f k → Mon3 C f′ k′ →
           Mon3 (g ∷ C) (λ τ → f (f′ τ)) (λ τ → k′ τ + k (f′ τ))
  Mon3-∷ {g = g} {C} {f} {f′} {k} {k′} mg mC = mon3 λ ψ r z τ i →
    trans (monomial mC (gateᴬ g ψ) (gateᴬ-resp g r) z τ i)
      (trans (rot-map (T * k′ τ) (monomial mg ψ r z (f′ τ)) i)
        (trans (rot-comp (T * k′ τ) (T * k (f′ τ)) (ψ (z ◂ f (f′ τ))) i)
               (rot-exp {T * k′ τ + T * k (f′ τ)} {T * (k′ τ + k (f′ τ))}
                        (ψ (z ◂ f (f′ τ)))
                        (sym (*-distribˡ-+ T (k′ τ) (k (f′ τ)))) i)))

  -- The map and the phase may be rewritten.

  Mon3-cong : {C : Circuit n} {f f′ : Tri → Tri} {k k′ : Tri → ℤ} →
              Mon3 C f k → (∀ τ → f τ ≡ f′ τ) → (∀ τ → k τ ≡ k′ τ) →
              Mon3 C f′ k′
  Mon3-cong {f = f} {f′} {k} {k′} m hf hk = mon3 λ ψ r z τ i →
    trans (monomial m ψ r z τ i)
      (trans (rot-map (T * k τ) (λ l → cong (λ t → ψ (z ◂ t) l) (hf τ)) i)
             (rot-exp {T * k τ} {T * k′ τ} (ψ (z ◂ f′ τ))
                      (cong (T *_) (hk τ)) i))

  -- T and T† on each wire.

  Mon3-Ta : Mon3 (R 3 a ∷ []) (λ τ → τ) (λ { (α , _ , _) → [ α ]ᶻ })
  Mon3-Ta = mon3 λ { ψ r z (α , β , γ) →
    rot-exp {T * [ W.w3 z α β γ a ]ᶻ} {T * [ α ]ᶻ} (ψ (W.w3 z α β γ))
            (cong (λ x → T * [ x ]ᶻ) (W.w3-c₁ z α β γ)) }

  Mon3-Tb : Mon3 (R 3 b ∷ []) (λ τ → τ) (λ { (_ , β , _) → [ β ]ᶻ })
  Mon3-Tb = mon3 λ { ψ r z (α , β , γ) →
    rot-exp {T * [ W.w3 z α β γ b ]ᶻ} {T * [ β ]ᶻ} (ψ (W.w3 z α β γ))
            (cong (λ x → T * [ x ]ᶻ) (W.w3-c₂ z α β γ)) }

  Mon3-Tc : Mon3 (R 3 c ∷ []) (λ τ → τ) (λ { (_ , _ , γ) → [ γ ]ᶻ })
  Mon3-Tc = mon3 λ { ψ r z (α , β , γ) →
    rot-exp {T * [ W.w3 z α β γ c ]ᶻ} {T * [ γ ]ᶻ} (ψ (W.w3 z α β γ))
            (cong (λ x → T * [ x ]ᶻ) (W.w3-t z α β γ)) }

  Mon3-T†a : Mon3 (R† 3 a ∷ []) (λ τ → τ) (λ { (α , _ , _) → - [ α ]ᶻ })
  Mon3-T†a = mon3 λ { ψ r z (α , β , γ) →
    rot-exp { - (T * [ W.w3 z α β γ a ]ᶻ)} {T * (- [ α ]ᶻ)}
            (ψ (W.w3 z α β γ))
            (trans (cong (λ x → - (T * [ x ]ᶻ)) (W.w3-c₁ z α β γ))
                   (neg-distribʳ-* T [ α ]ᶻ)) }

  Mon3-T†b : Mon3 (R† 3 b ∷ []) (λ τ → τ) (λ { (_ , β , _) → - [ β ]ᶻ })
  Mon3-T†b = mon3 λ { ψ r z (α , β , γ) →
    rot-exp { - (T * [ W.w3 z α β γ b ]ᶻ)} {T * (- [ β ]ᶻ)}
            (ψ (W.w3 z α β γ))
            (trans (cong (λ x → - (T * [ x ]ᶻ)) (W.w3-c₂ z α β γ))
                   (neg-distribʳ-* T [ β ]ᶻ)) }

  -- The four CNOTs of the circuit: each adds one bit of the triple to
  -- another.

  Mon3-ab : (p : a ≢ b) →
            Mon3 (CNOT a b p ∷ []) (λ { (α , β , γ) → (α , β xor α , γ) })
                 (λ _ → 0ℤ)
  Mon3-ab p = mon3 λ { ψ r z (α , β , γ) i →
    trans (r _ _ (W.cnot-c₂ z α β γ) i)
          (sym (rot-zero (ψ (W.w3 z α (β xor α) γ)) i)) }

  Mon3-bc : (p : b ≢ c) →
            Mon3 (CNOT b c p ∷ []) (λ { (α , β , γ) → (α , β , γ xor β) })
                 (λ _ → 0ℤ)
  Mon3-bc p = mon3 λ { ψ r z (α , β , γ) i →
    trans (r _ _ (W.cnot-t z b α β γ β (W.w3-c₂ z α β γ)) i)
          (sym (rot-zero (ψ (W.w3 z α β (γ xor β))) i)) }

  Mon3-ca : (p : c ≢ a) →
            Mon3 (CNOT c a p ∷ []) (λ { (α , β , γ) → (α xor γ , β , γ) })
                 (λ _ → 0ℤ)
  Mon3-ca p = mon3 λ { ψ r z (α , β , γ) i →
    trans (r _ _ (cnot-a z c α β γ γ (W.w3-t z α β γ)) i)
          (sym (rot-zero (ψ (W.w3 z (α xor γ) β γ)) i)) }

  Mon3-ba : (p : b ≢ a) →
            Mon3 (CNOT b a p ∷ []) (λ { (α , β , γ) → (α xor β , β , γ) })
                 (λ _ → 0ℤ)
  Mon3-ba p = mon3 λ { ψ r z (α , β , γ) i →
    trans (r _ _ (cnot-a z b α β γ β (W.w3-c₂ z α β γ)) i)
          (sym (rot-zero (ψ (W.w3 z (α xor β) β γ)) i)) }

  -- The fourteen gates: the identity map on the triple, and the phase
  -- 4 τ_a τ_b τ_c (both by evaluation on the eight triples).

  Mon3-ccz : Mon3 (cczᶜ a b c a≢b a≢c b≢c) (λ τ → τ)
                  (λ τ → (+ 4) * [ and₃ τ ]ᶻ)
  Mon3-ccz = Mon3-cong {f′ = λ τ → τ} {k′ = λ τ → (+ 4) * [ and₃ τ ]ᶻ}
    (Mon3-∷ Mon3-Ta (Mon3-∷ Mon3-Tb (Mon3-∷ Mon3-Tc
     (Mon3-∷ (Mon3-ab a≢b) (Mon3-∷ (Mon3-bc b≢c)
      (Mon3-∷ (Mon3-ca (λ e → a≢c (sym e)))
       (Mon3-∷ Mon3-T†a (Mon3-∷ Mon3-T†b (Mon3-∷ Mon3-Tc
        (Mon3-∷ (Mon3-ba (λ e → a≢b (sym e))) (Mon3-∷ Mon3-T†a
         (Mon3-∷ (Mon3-bc b≢c) (Mon3-∷ (Mon3-ca (λ e → a≢c (sym e)))
          (Mon3-∷ (Mon3-ab a≢b) Mon3-[]))))))))))))))
    (all-tri refl refl refl refl refl refl refl refl)
    (all-tri refl refl refl refl refl refl refl refl)

  -- So the circuit is the diagonal ζ^(½ z_a z_b z_c).

  Diag-ccz : Diag (cczᶜ a b c a≢b a≢c b≢c) (λ z → ½ * [ z a ∧ (z b ∧ z c) ]ᶻ)
  Diag-ccz = diag λ ψ r z i →
    trans (applyᴬ-resp (cczᶜ a b c a≢b a≢c b≢c) r z (z ◂ τ z) (◂-self z) i)
      (trans (monomial Mon3-ccz ψ r z (τ z) i)
        (trans (rot-map (T * ((+ 4) * [ and₃ (τ z) ]ᶻ))
                        (r (z ◂ τ z) z (λ j → sym (◂-self z j))) i)
               (rot-exp {T * ((+ 4) * [ and₃ (τ z) ]ᶻ)}
                        {½ * [ z a ∧ (z b ∧ z c) ]ᶻ} (ψ z)
                        (trans (sym (*-assoc T (+ 4) [ and₃ (τ z) ]ᶻ))
                               (cong (_* [ and₃ (τ z) ]ᶻ) ⅛·4)) i)))
    where
    τ : Assign n → Tri
    τ z = z a , z b , z c


------------------------------------------------------------------------
-- The tool's ccz on any three distinct wires

Diag-ccz : (a b c : Fin n) (p : a ≢ b) (q : a ≢ c) (r : b ≢ c) →
           Diag (cczᶜ a b c p q r) (λ z → ½ * [ z a ∧ (z b ∧ z c) ]ᶻ)
Diag-ccz a b c p q r = Three.Diag-ccz p q r

-- Its sign is the monomial z_a z_b z_c, as for Gates's CCZᶜ.

Signs-ccz : (a b c : Fin n) (p : a ≢ b) (q : a ≢ c) (r : b ≢ c) →
            Signs (cczᶜ a b c p q r) (λ z → z a ∧ (z b ∧ z c))
Signs-ccz a b c p q r = Diag⇒Signs (Diag-ccz a b c p q r)
