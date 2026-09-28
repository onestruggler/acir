------------------------------------------------------------------------
-- Presentations of groups
--
-- The qubits of a circuit over {H, CNOT, R_k, R_k†}: the wires its
-- gates touch (Amy, QPL 2018, table 2)
--
-- Table 2's first column is the number of qubits of each benchmark,
-- and the paper's tool computes it from the circuit: the number of
-- distinct wires its gates touch (printVerStats, in Feynman's
-- src/Feynman/Verification/SOP.hs: a Hadamard or a phase gate touches
-- its wire, a CNOT its control and its target).  Here is that count,
-- for a circuit C on n wires:
--
--    qubits C = the number of wires u of Fin n that some gate of C
--               touches
--
-- (#ʷ counts the wires a Boolean test holds of, touches and touched
-- are the tests, so the count is decidable and computed from the
-- circuit).  The test is exactly membership: touched C u is true
-- precisely when u ∈ᶜ C, u being a wire (wiresᶜ) of some gate of C
-- (touched⇔∈ᶜ).  So qubits C ≤ n (qubits-≤), with equality exactly
-- when every wire is touched (qubits-all, qubits-all⁻¹); C† touches
-- what C does (∈ᶜ-†), so has as many qubits (qubits-†); and a
-- concatenation touches what its parts touch (∈ᶜ-++ˡ, ∈ᶜ-++ʳ).
--
-- A netlist of Toffoli and CNOT gates expanded into Clifford+T
-- touches every wire of the netlist (∈ᶜ-expand, for
-- PathSum.Reversible.Expand's expansion: the seven-T Toffoli circuit
-- touches its three wires, ∈ᶜ-tof); PathSum.Adder.Tool proves the
-- same for the expansion by the tool's own Toffoli circuit.  With
-- PathSum.Adder.Wires, which shows that the adders' netlists touch
-- every wire of their layouts, this gives table 2's qubit column as a
-- count taken from the circuit itself.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.Qubits (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat.Base using (zero; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; 1+n≰n; suc-injective)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)

import Data.Fin.Properties as Fin
import Data.List.Relation.Unary.Any.Properties as Any

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Adjoint M using (inv; _†; †-involutive)
open import PathSum.CRK.Path M₀ using (Gate; H; CNOT; R; R†; Circuit)
open import PathSum.Reversible using (ccx; cx; recover)
  renaming (Gate to Gateᴿ)
open import PathSum.Reversible.Expand M₀ using (expand)
open import PathSum.Reversible.Wires using (wiresᴿ; _∈ᴿ_)
open import PathSum.Toffoli M₀ using (tof)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Counting wires

-- The number of wires u of Fin n with f u.

#ʷ : (Fin n → Bool) → ℕ
#ʷ {zero}  f = 0
#ʷ {suc n} f = (if f zero then 1 else 0) + #ʷ (λ u → f (suc u))

-- At most n ...

#ʷ-≤ : (f : Fin n → Bool) → #ʷ f ≤ n
#ʷ-≤ {zero}  f = z≤n
#ʷ-≤ {suc n} f = go (f zero)
  where
  go : (b : Bool) → (if b then 1 else 0) + #ʷ (λ u → f (suc u)) ≤ suc n
  go true  = s≤s (#ʷ-≤ (λ u → f (suc u)))
  go false = m≤n⇒m≤1+n (#ʷ-≤ (λ u → f (suc u)))

-- ... and n exactly when it holds of every wire.

#ʷ-all : (f : Fin n → Bool) → (∀ u → f u ≡ true) → #ʷ f ≡ n
#ʷ-all {zero}  f h = refl
#ʷ-all {suc n} f h =
  cong₂ _+_ (cong (λ b → if b then 1 else 0) (h zero))
            (#ʷ-all (λ u → f (suc u)) (λ u → h (suc u)))

#ʷ-all⁻¹ : (f : Fin n → Bool) → #ʷ f ≡ n → ∀ u → f u ≡ true
#ʷ-all⁻¹ {zero}  f e ()
#ʷ-all⁻¹ {suc n} f e = go (f zero) refl e
  where
  go : (b : Bool) → f zero ≡ b →
       (if b then 1 else 0) + #ʷ (λ u → f (suc u)) ≡ suc n →
       ∀ u → f u ≡ true
  go true  fz e zero    = fz
  go true  fz e (suc u) = #ʷ-all⁻¹ (λ u → f (suc u)) (suc-injective e) u
  go false fz e u       =
    ⊥-elim (1+n≰n (subst (_≤ n) e (#ʷ-≤ (λ u → f (suc u)))))

-- Only the values of the test count.

#ʷ-cong : {f g : Fin n → Bool} → (∀ u → f u ≡ g u) → #ʷ f ≡ #ʷ g
#ʷ-cong {zero}  h = refl
#ʷ-cong {suc n} h =
  cong₂ _+_ (cong (λ b → if b then 1 else 0) (h zero))
            (#ʷ-cong (λ u → h (suc u)))


------------------------------------------------------------------------
-- The wires a circuit touches

-- A gate's wires: a Hadamard's or a phase gate's one wire, a CNOT's
-- control and target.

wiresᶜ : Gate n → List (Fin n)
wiresᶜ (H w)        = w ∷ []
wiresᶜ (CNOT c t _) = c ∷ t ∷ []
wiresᶜ (R _ w)      = w ∷ []
wiresᶜ (R† _ w)     = w ∷ []

-- u is a wire of some gate of C.

infix 4 _∈ᶜ_

_∈ᶜ_ : Fin n → Circuit n → Set
u ∈ᶜ C = Any (λ g → u ∈ wiresᶜ g) C

-- As tests: whether u is among some wires, whether a gate touches u,
-- whether a circuit does.

private
  _≟ʷ_ : Fin n → Fin n → Bool
  u ≟ʷ w = ⌊ u Fin.≟ w ⌋

  ≟ʷ-refl : (u : Fin n) → u ≟ʷ u ≡ true
  ≟ʷ-refl u = go (u Fin.≟ u)
    where
    go : (d : Dec (u ≡ u)) → ⌊ d ⌋ ≡ true
    go (yes _) = refl
    go (no ¬p) = ⊥-elim (¬p refl)

  ≟ʷ-true : (u w : Fin n) → u ≟ʷ w ≡ true → u ≡ w
  ≟ʷ-true u w = go (u Fin.≟ w)
    where
    go : (d : Dec (u ≡ w)) → ⌊ d ⌋ ≡ true → u ≡ w
    go (yes p) _  = p
    go (no _)  ()

  ∨-introˡ : (a b : Bool) → a ≡ true → a ∨ b ≡ true
  ∨-introˡ .true b refl = refl

  ∨-introʳ : (a b : Bool) → b ≡ true → a ∨ b ≡ true
  ∨-introʳ a .true refl = ∨-zeroʳ a

  ∨-elim : (a b : Bool) → a ∨ b ≡ true → a ≡ true ⊎ b ≡ true
  ∨-elim true  b _ = inj₁ refl
  ∨-elim false b e = inj₂ e

elem : List (Fin n) → Fin n → Bool
elem []       u = false
elem (w ∷ ws) u = u ≟ʷ w ∨ elem ws u

touches : Gate n → Fin n → Bool
touches g u = elem (wiresᶜ g) u

touched : Circuit n → Fin n → Bool
touched []      u = false
touched (g ∷ C) u = touches g u ∨ touched C u

-- The tests decide membership.

private
  elem-∈ : (ws : List (Fin n)) (u : Fin n) → elem ws u ≡ true → u ∈ ws
  elem-∈ []       u ()
  elem-∈ (w ∷ ws) u e with ∨-elim (u ≟ʷ w) (elem ws u) e
  ... | inj₁ e₁ = here (≟ʷ-true u w e₁)
  ... | inj₂ e₂ = there (elem-∈ ws u e₂)

  ∈-elem : (ws : List (Fin n)) (u : Fin n) → u ∈ ws → elem ws u ≡ true
  ∈-elem (w ∷ ws) u (here refl) = ∨-introˡ (u ≟ʷ u) (elem ws u) (≟ʷ-refl u)
  ∈-elem (w ∷ ws) u (there p)   = ∨-introʳ (u ≟ʷ w) (elem ws u) (∈-elem ws u p)

touched-∈ᶜ : (C : Circuit n) (u : Fin n) → touched C u ≡ true → u ∈ᶜ C
touched-∈ᶜ []      u ()
touched-∈ᶜ (g ∷ C) u e with ∨-elim (touches g u) (touched C u) e
... | inj₁ e₁ = here (elem-∈ (wiresᶜ g) u e₁)
... | inj₂ e₂ = there (touched-∈ᶜ C u e₂)

∈ᶜ-touched : (C : Circuit n) (u : Fin n) → u ∈ᶜ C → touched C u ≡ true
∈ᶜ-touched (g ∷ C) u (here p)  =
  ∨-introˡ (touches g u) (touched C u) (∈-elem (wiresᶜ g) u p)
∈ᶜ-touched (g ∷ C) u (there p) =
  ∨-introʳ (touches g u) (touched C u) (∈ᶜ-touched C u p)

touched⇔∈ᶜ : (C : Circuit n) (u : Fin n) → touched C u ≡ true ⇔ u ∈ᶜ C
touched⇔∈ᶜ C u = mk⇔ (touched-∈ᶜ C u) (∈ᶜ-touched C u)


------------------------------------------------------------------------
-- The number of qubits

-- The number of wires the circuit touches.

qubits : Circuit n → ℕ
qubits C = #ʷ (touched C)

-- At most the width, and the width exactly when every wire is touched.

qubits-≤ : (C : Circuit n) → qubits C ≤ n
qubits-≤ C = #ʷ-≤ (touched C)

qubits-all : (C : Circuit n) → (∀ u → u ∈ᶜ C) → qubits {n} C ≡ n
qubits-all C h = #ʷ-all (touched C) (λ u → ∈ᶜ-touched C u (h u))

qubits-all⁻¹ : (C : Circuit n) → qubits {n} C ≡ n → ∀ u → u ∈ᶜ C
qubits-all⁻¹ C e u = touched-∈ᶜ C u (#ʷ-all⁻¹ (touched C) e u)


------------------------------------------------------------------------
-- Concatenation and inversion

-- A concatenation touches what its parts touch.

∈ᶜ-++ˡ : (C D : Circuit n) {u : Fin n} → u ∈ᶜ C → u ∈ᶜ C ++ D
∈ᶜ-++ˡ C D p = Any.++⁺ˡ {xs = C} {ys = D} p

∈ᶜ-++ʳ : (C D : Circuit n) {u : Fin n} → u ∈ᶜ D → u ∈ᶜ C ++ D
∈ᶜ-++ʳ C D p = Any.++⁺ʳ C {ys = D} p

-- Inverting a gate keeps its wires, so C† touches what C does, and so
-- has as many qubits.

private
  wires-inv : (g : Gate n) → wiresᶜ (inv g) ≡ wiresᶜ g
  wires-inv (H _)        = refl
  wires-inv (CNOT _ _ _) = refl
  wires-inv (R _ _)      = refl
  wires-inv (R† _ _)     = refl

∈ᶜ-† : (C : Circuit n) {u : Fin n} → u ∈ᶜ C → u ∈ᶜ C †
∈ᶜ-† (g ∷ C) {u} (here p)  =
  ∈ᶜ-++ʳ (C †) (inv g ∷ [])
         (here (subst (u ∈_) (sym (wires-inv g)) p))
∈ᶜ-† (g ∷ C)     (there p) = ∈ᶜ-++ˡ (C †) (inv g ∷ []) (∈ᶜ-† C p)

∈ᶜ-†⁻ : (C : Circuit n) {u : Fin n} → u ∈ᶜ C † → u ∈ᶜ C
∈ᶜ-†⁻ C {u} p = subst (u ∈ᶜ_) (†-involutive C) (∈ᶜ-† (C †) p)

private
  bool-≡ : {a b : Bool} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) →
           a ≡ b
  bool-≡ {true}  {true}  _ _ = refl
  bool-≡ {true}  {false} f _ = sym (f refl)
  bool-≡ {false} {true}  _ g = g refl
  bool-≡ {false} {false} _ _ = refl

touched-† : (C : Circuit n) (u : Fin n) → touched (C †) u ≡ touched C u
touched-† C u =
  bool-≡ (λ e → ∈ᶜ-touched C u (∈ᶜ-†⁻ C (touched-∈ᶜ (C †) u e)))
         (λ e → ∈ᶜ-touched (C †) u (∈ᶜ-† C (touched-∈ᶜ C u e)))

qubits-† : (C : Circuit n) → qubits (C †) ≡ qubits C
qubits-† C = #ʷ-cong (touched-† C)


------------------------------------------------------------------------
-- Expanding a netlist into Clifford+T

-- The seven-T Toffoli circuit touches its three wires: t with its
-- first gate, c₂ with its second, c₁ with its fourth.

∈ᶜ-tof : (c₁ c₂ t : Fin n) (p : c₁ ≢ c₂) (q : c₁ ≢ t) (r : c₂ ≢ t)
         {u : Fin n} → u ∈ c₁ ∷ c₂ ∷ t ∷ [] → u ∈ᶜ tof c₁ c₂ t p q r
∈ᶜ-tof c₁ c₂ t p q r (here refl)                 =
  there (there (there (here (here refl))))
∈ᶜ-tof c₁ c₂ t p q r (there (here refl))         = there (here (here refl))
∈ᶜ-tof c₁ c₂ t p q r (there (there (here refl))) = here (here refl)

-- So the expansion of a netlist touches every wire of the netlist.

∈ᶜ-expand : (gs : List (Gateᴿ n)) {u : Fin n} → u ∈ᴿ gs → u ∈ᶜ expand gs
∈ᶜ-expand (ccx c₁ c₂ t p q r ∷ gs) (here m)  =
  ∈ᶜ-++ˡ (tof c₁ c₂ t (recover p) (recover q) (recover r)) (expand gs)
         (∈ᶜ-tof c₁ c₂ t (recover p) (recover q) (recover r) m)
∈ᶜ-expand (ccx c₁ c₂ t p q r ∷ gs) (there m) =
  ∈ᶜ-++ʳ (tof c₁ c₂ t (recover p) (recover q) (recover r)) (expand gs)
         (∈ᶜ-expand gs m)
∈ᶜ-expand (cx c t p ∷ gs)          (here m)  = here m
∈ᶜ-expand (cx c t p ∷ gs)          (there m) = there (∈ᶜ-expand gs m)
