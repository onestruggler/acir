------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits over {H, X, CNOT, R_k, R_k†}: definition 2.9 and
-- proposition 2.10 with the Pauli X gate
--
-- Definition 2.9 of Amy's QPL 2018 paper interprets circuits over
-- {H, CNOT, R_k} (PathSum.CRK.Circuit, with R_k† as well), but the
-- Clifford+T identity of section 4 is drawn with X gates too.  Its
-- printed path-sum is the one definition 2.9 gives when X is read as
--
--    ⟦X⟧ = |x⟩ ↦ |1 ⊕ x⟩ ,
--
-- the path-sum with no path variable whose output is the affine form
-- 1 ⊕ x (PathSum.Examples.Incomplete checks this).  The constant 2 of
-- the printed phase comes from the two T gates that act on a form with
-- constant 1 -- a negation X puts on the first wire, which a CNOT
-- carries to the second -- each contributing the constant 1 of the
-- lifting of 1 ⊕ S.  This module adds that gate.  Writing X as H Z H
-- over the old gate set would give a different path-sum, with two more
-- path variables per X, that only [HH] brings back to this one.
--
-- An interpretation state already holds on each wire a form c ⊕ S with
-- a constant c (PathSum.Linear), so X is one more step on the states
-- of PathSum.CRK.Circuit: it negates the constant of the form on its
-- wire (stepX) and leaves the phase alone.  On circuits without X the
-- interpretation is PathSum.CRK.Circuit's (run-embed, norm-embed).
--
-- Proposition 2.10 carries over (prop-2-10): X permutes the entries of
-- a column, the new entry at z being the old one at z with its bit on
-- the wire negated (ampᴸ-X, the argument of PathSum.CRK.Amp.ampᴸ-CNOT
-- with the control replaced by the constant 1), and the other gates
-- change amplitudes by PathSum.CRK.Amp's lemmas.  So a circuit is the
-- identity exactly when its matrix, computed gate by gate, is
-- (circuit-≋-id); for a closed circuit that is a finite computation
-- (matrix-id?, circuit-id!, circuit-not-id!), which is how a
-- Clifford+T identity that no rule of figure 2 proves is checked
-- (PathSum.Examples.Incomplete).  It is not the paper's method, and it
-- is exponential in the number of qubits and of Hadamards.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.CRK.WithX (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_; _xor_)
open import Data.Bool.Properties using (not-distribˡ-xor; not-involutive)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (ℤ; 0ℤ; -_; _*_; _+_)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Nat.Base using (zero; _∸_) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using ([_,_]′)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; True; False; toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-cong; same-≗)
open import PathSum.Base using (PathSum; ⟨_,_⟩; idPS)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.Compose.Laws M₀ using (amp-idPS-δ)
open import PathSum.CRK.Amp M₀ using
  (toPS; ampᴸ; outBit-liftᴸ; ampᴸ-init; ampᴸ-R; ampᴸ-R†; ampᴸ-CNOT;
   ampᴸ-H)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; zpow; _+ᴬ_; _≐_; rot; rot-map; Σᴮ-cong; scale; scale-map;
   Respects)
open import PathSum.Decide M₀ using (search)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; _≋_; hits-intro; hits-elim)
open import PathSum.Linear using (Lin; valᴸ; liftᴸ; parᵐ)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (eval)
open import PathSum.Reduction M using (½)

import PathSum.CRK.Circuit
import PathSum.CRK.Semantics

private
  module CRK  = PathSum.CRK.Circuit M
  module CRKˢ = PathSum.CRK.Semantics M₀

open CRK using
  (State; state; poly; sig; init; stepR; stepR†; stepCNOT; stepH;
   _[_↦_]; ↦-here; ↦-there)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- Circuits

data Gate (n : ℕ) : Set where
  H    : Fin n → Gate n
  X    : Fin n → Gate n
  CNOT : (c t : Fin n) → c ≢ t → Gate n
  R    : ℕ → Fin n → Gate n
  R†   : ℕ → Fin n → Gate n

Circuit : ℕ → Set
Circuit n = List (Gate n)

-- One factor of 1/√2 for each Hadamard.

norm : Circuit n → ℕ
norm []                = 0
norm (H _ ∷ C)         = suc (norm C)
norm (X _ ∷ C)         = norm C
norm (CNOT _ _ _ ∷ C)  = norm C
norm (R _ _ ∷ C)       = norm C
norm (R† _ _ ∷ C)      = norm C


------------------------------------------------------------------------
-- The X gate on interpretation states

-- X negates the constant of the form on its wire: 1 ⊕ (c ⊕ S) is
-- (1 ⊕ c) ⊕ S.

notᴸ : ∀ {n m} → Lin n m → Lin n m
notᴸ (c , S) = not c , S

valᴸ-not : ∀ {n m} (l : Lin n m) (x : Assign n) (y : Assign m) →
           valᴸ (notᴸ l) x y ≡ not (valᴸ l x y)
valᴸ-not (c , S) x y = sym (not-distribˡ-xor c (parᵐ S x y))

stepX : Fin n → State n m → State n m
stepX w st = state (poly st) (sig st [ w ↦ notᴸ (sig st w) ])


------------------------------------------------------------------------
-- The path-sum of a circuit

-- As PathSum.CRK.Circuit.run, with X.

run : Circuit n → State n m → ∃ (State n)
run []                 st = _ , st
run (H w ∷ C)          st = run C (stepH w st)
run (X w ∷ C)          st = run C (stepX w st)
run (CNOT c t _ ∷ C)   st = run C (stepCNOT c t st)
run (R k w ∷ C)        st = run C (stepR k w st)
run (R† k w ∷ C)       st = run C (stepR† k w st)

paths : Circuit n → ℕ
paths {n} C = proj₁ (run C (init {n}))

-- Definition 2.9.

⟦_⟧ : (C : Circuit n) → PathSum n (norm C) (paths C)
⟦_⟧ {n} C = ⟨ poly result , (λ w → liftᴸ (sig result w)) ⟩
  where
  result : State n (paths C)
  result = proj₂ (run C init)

-- One path variable for each Hadamard.

paths≡norm : (C : Circuit n) → paths C ≡ norm C
paths≡norm {n} C = trans (count C (init {n})) (ℕ.+-identityʳ (norm C))
  where
  count : ∀ {m} (C : Circuit n) (st : State n m) →
          proj₁ (run C st) ≡ norm C ℕ+ m
  count []                st = refl
  count (H w ∷ C)         st =
    trans (count C (stepH w st)) (ℕ.+-suc (norm C) _)
  count (X w ∷ C)         st = count C (stepX w st)
  count (CNOT c t _ ∷ C)  st = count C (stepCNOT c t st)
  count (R k w ∷ C)       st = count C (stepR k w st)
  count (R† k w ∷ C)      st = count C (stepR† k w st)

run-++ : (C D : Circuit n) (st : State n m) →
         run (C ++ D) st ≡ run D (proj₂ (run C st))
run-++ []                D st = refl
run-++ (H w ∷ C)         D st = run-++ C D (stepH w st)
run-++ (X w ∷ C)         D st = run-++ C D (stepX w st)
run-++ (CNOT c t _ ∷ C)  D st = run-++ C D (stepCNOT c t st)
run-++ (R k w ∷ C)       D st = run-++ C D (stepR k w st)
run-++ (R† k w ∷ C)      D st = run-++ C D (stepR† k w st)


------------------------------------------------------------------------
-- Circuits without X

-- The old gates, and on circuits made of them the old interpretation.

embed : CRK.Gate n → Gate n
embed (CRK.H w)        = H w
embed (CRK.CNOT c t p) = CNOT c t p
embed (CRK.R k w)      = R k w
embed (CRK.R† k w)     = R† k w

run-embed : (C : CRK.Circuit n) (st : State n m) →
            run (map embed C) st ≡ CRK.run C st
run-embed []                    st = refl
run-embed (CRK.H w ∷ C)         st = run-embed C (stepH w st)
run-embed (CRK.CNOT c t _ ∷ C)  st = run-embed C (stepCNOT c t st)
run-embed (CRK.R k w ∷ C)       st = run-embed C (stepR k w st)
run-embed (CRK.R† k w ∷ C)      st = run-embed C (stepR† k w st)

norm-embed : (C : CRK.Circuit n) → norm (map embed C) ≡ CRK.norm C
norm-embed []                   = refl
norm-embed (CRK.H w ∷ C)        = cong suc (norm-embed C)
norm-embed (CRK.CNOT c t _ ∷ C) = norm-embed C
norm-embed (CRK.R k w ∷ C)      = norm-embed C
norm-embed (CRK.R† k w ∷ C)     = norm-embed C


------------------------------------------------------------------------
-- The matrices of the gates

-- X moves the entry at z with the bit on its wire negated to z; the
-- other gates act as in PathSum.CRK.Semantics.

gateᴬ : Gate n → Column n → Column n
gateᴬ (H w)        ψ z = CRKˢ.gateᴬ (CRK.H w) ψ z
gateᴬ (X w)        ψ z = ψ (z [ w ≔ not (z w) ])
gateᴬ (CNOT c t p) ψ z = CRKˢ.gateᴬ (CRK.CNOT c t p) ψ z
gateᴬ (R k w)      ψ z = CRKˢ.gateᴬ (CRK.R k w) ψ z
gateᴬ (R† k w)     ψ z = CRKˢ.gateᴬ (CRK.R† k w) ψ z

applyᴬ : Circuit n → Column n → Column n
applyᴬ []      ψ = ψ
applyᴬ (g ∷ C) ψ = applyᴬ C (gateᴬ g ψ)

applyᴬ-++ : (C D : Circuit n) (ψ : Column n) →
            applyᴬ (C ++ D) ψ ≡ applyᴬ D (applyᴬ C ψ)
applyᴬ-++ []      D ψ = refl
applyᴬ-++ (g ∷ C) D ψ = applyᴬ-++ C D (gateᴬ g ψ)

-- The gates act entry by entry, and read assignments only through
-- their values.

gateᴬ-cong : (g : Gate n) {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
             ∀ z → gateᴬ g φ z ≐ gateᴬ g φ′ z
gateᴬ-cong (H w)        h z = CRKˢ.gateᴬ-cong (CRK.H w) h z
gateᴬ-cong (X w)        h z = h (z [ w ≔ not (z w) ])
gateᴬ-cong (CNOT c t p) h z = CRKˢ.gateᴬ-cong (CRK.CNOT c t p) h z
gateᴬ-cong (R k w)      h z = CRKˢ.gateᴬ-cong (CRK.R k w) h z
gateᴬ-cong (R† k w)     h z = CRKˢ.gateᴬ-cong (CRK.R† k w) h z

applyᴬ-cong : (C : Circuit n) {φ φ′ : Column n} → (∀ z → φ z ≐ φ′ z) →
              ∀ z → applyᴬ C φ z ≐ applyᴬ C φ′ z
applyᴬ-cong []      h = h
applyᴬ-cong (g ∷ C) {φ} {φ′} h =
  applyᴬ-cong C {gateᴬ g φ} {gateᴬ g φ′} (gateᴬ-cong g h)

gateᴬ-resp : (g : Gate n) {ψ : Column n} → Respects ψ →
             Respects (gateᴬ g ψ)
gateᴬ-resp (H w)        resp = CRKˢ.gateᴬ-resp (CRK.H w) resp
gateᴬ-resp (X w) {ψ}    resp z z′ zz =
  resp (z [ w ≔ not (z w) ]) (z′ [ w ≔ not (z′ w) ]) (λ j →
    trans (≔-cong w (not (z w)) zz j)
          (cong (λ b → (z′ [ w ≔ b ]) j) (cong not (zz w))))
gateᴬ-resp (CNOT c t p) resp = CRKˢ.gateᴬ-resp (CRK.CNOT c t p) resp
gateᴬ-resp (R k w)      resp = CRKˢ.gateᴬ-resp (CRK.R k w) resp
gateᴬ-resp (R† k w)     resp = CRKˢ.gateᴬ-resp (CRK.R† k w) resp

applyᴬ-resp : (C : Circuit n) {ψ : Column n} → Respects ψ →
              Respects (applyᴬ C ψ)
applyᴬ-resp []      resp = resp
applyᴬ-resp (g ∷ C) resp = applyᴬ-resp C (gateᴬ-resp g resp)


------------------------------------------------------------------------
-- The amplitudes after an X

private
  bool-iff : {a b : Bool} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) →
             a ≡ b
  bool-iff {true}  {true}  _ _ = refl
  bool-iff {true}  {false} f _ = sym (f refl)
  bool-iff {false} {true}  _ g = g refl
  bool-iff {false} {false} _ _ = refl

  -- A property of every wire, from the wire w and all the others.

  at-wire : (P : Fin n → Set) (w : Fin n) → P w → (∀ u → u ≢ w → P u) →
            ∀ u → P u
  at-wire P w pw off u with u Fin.≟ w
  ... | yes u≡w = Eq.subst P (sym u≡w) pw
  ... | no  u≢w = off u u≢w

  -- Along a path each wire reads the value of its form, so the path
  -- hits z exactly when every wire reads z's value.

  hits-val : (st : State n m) (x : Assign n) (y : Assign m) (z : Assign n) →
             hits (toPS {k = 0} st) x y z ≡ true →
             ∀ u → valᴸ (sig st u) x y ≡ z u
  hits-val st x y z h u =
    trans (sym (outBit-liftᴸ (toPS {k = 0} st) x y u (sig st u) refl))
          (hits-elim (toPS {k = 0} st) x y z h u)

  val-hits : (st : State n m) (x : Assign n) (y : Assign m) (z : Assign n) →
             (∀ u → valᴸ (sig st u) x y ≡ z u) →
             hits (toPS {k = 0} st) x y z ≡ true
  val-hits st x y z h = hits-intro (toPS {k = 0} st) x y z (λ u →
    trans (outBit-liftᴸ (toPS {k = 0} st) x y u (sig st u) refl) (h u))

-- The phase is unchanged, and the wire w now holds the negation of its
-- old form: a path hits z after the gate exactly when it hit z with
-- the bit on w negated before.

ampᴸ-X : ∀ {n m} (w : Fin n) (st : State n m) (x z : Assign n) →
         ampᴸ (stepX w st) x z ≐ ampᴸ st x (z [ w ≔ not (z w) ])
ampᴸ-X {n} {m} w st x z i = Σᴮ-cong per i
  where
  z′ : Assign n
  z′ = z [ w ≔ not (z w) ]

  new : State n m
  new = stepX w st

  new-w : (y : Assign m) →
          valᴸ (sig new w) x y ≡ not (valᴸ (sig st w) x y)
  new-w y = trans
    (cong (λ l → valᴸ l x y) (↦-here (sig st) w (notᴸ (sig st w))))
    (valᴸ-not (sig st w) x y)

  new-off : (y : Assign m) (u : Fin n) → u ≢ w →
            valᴸ (sig new u) x y ≡ valᴸ (sig st u) x y
  new-off y u u≢w =
    cong (λ l → valᴸ l x y) (↦-there (sig st) (notᴸ (sig st w)) u≢w)

  z′-off : (u : Fin n) → u ≢ w → z′ u ≡ z u
  z′-off u u≢w = ≔-there z (not (z w)) u≢w

  to : (y : Assign m) → hits (toPS {k = 0} new) x y z ≡ true →
       hits (toPS {k = 0} st) x y z′ ≡ true
  to y h = val-hits st x y z′
    (at-wire (λ u → valᴸ (sig st u) x y ≡ z′ u) w tgt off)
    where
    hn : ∀ u → valᴸ (sig new u) x y ≡ z u
    hn = hits-val new x y z h

    tgt : valᴸ (sig st w) x y ≡ z′ w
    tgt = trans (sym (not-involutive (valᴸ (sig st w) x y)))
      (trans (cong not (trans (sym (new-w y)) (hn w)))
             (sym (≔-here z w (not (z w)))))

    off : ∀ u → u ≢ w → valᴸ (sig st u) x y ≡ z′ u
    off u u≢w =
      trans (sym (new-off y u u≢w)) (trans (hn u) (sym (z′-off u u≢w)))

  from : (y : Assign m) → hits (toPS {k = 0} st) x y z′ ≡ true →
         hits (toPS {k = 0} new) x y z ≡ true
  from y h = val-hits new x y z
    (at-wire (λ u → valᴸ (sig new u) x y ≡ z u) w tgt off)
    where
    ho : ∀ u → valᴸ (sig st u) x y ≡ z′ u
    ho = hits-val st x y z′ h

    tgt : valᴸ (sig new w) x y ≡ z w
    tgt = trans (new-w y)
      (trans (cong not (trans (ho w) (≔-here z w (not (z w)))))
             (not-involutive (z w)))

    off : ∀ u → u ≢ w → valᴸ (sig new u) x y ≡ z u
    off u u≢w = trans (new-off y u u≢w) (trans (ho u) (z′-off u u≢w))

  per : ∀ y →
        (if hits (toPS {k = 0} new) x y z
         then zpow (eval (poly st) x y) else 0ᴬ) ≐
        (if hits (toPS {k = 0} st) x y z′
         then zpow (eval (poly st) x y) else 0ᴬ)
  per y j = cong (λ p → (if p then zpow (eval (poly st) x y) else 0ᴬ) j)
                 (bool-iff (to y) (from y))


------------------------------------------------------------------------
-- Proposition 2.10

-- The amplitudes of the state after each gate are the gate's matrix
-- applied to the column of the amplitudes before it.

private
  step-amp : (g : Gate n) (st : State n m) (x : Assign n) (ψ : Column n) →
             (∀ z → ampᴸ st x z ≐ ψ z) →
             ∀ z → ampᴸ (proj₂ (run (g ∷ []) st)) x z ≐ gateᴬ g ψ z
  step-amp (H w) st x ψ h z i = trans (ampᴸ-H w st x z i)
    (cong₂ _+_ (h (z [ w ≔ false ]) i)
               (rot-map (½ * [ z w ]ᶻ) (h (z [ w ≔ true ])) i))
  step-amp (X w) st x ψ h z i =
    trans (ampᴸ-X w st x z i) (h (z [ w ≔ not (z w) ]) i)
  step-amp (CNOT c t p) st x ψ h z i =
    trans (ampᴸ-CNOT c t p st x z i) (h (z [ t ≔ z t xor z c ]) i)
  step-amp (R k w) st x ψ h z i = trans (ampᴸ-R k w st x z i)
    (rot-map (pow (M ∸ k) * [ z w ]ᶻ) (h z) i)
  step-amp (R† k w) st x ψ h z i = trans (ampᴸ-R† k w st x z i)
    (rot-map (- (pow (M ∸ k) * [ z w ]ᶻ)) (h z) i)

  run-amp : (C : Circuit n) (st : State n m) (x : Assign n)
            (ψ : Column n) → (∀ z → ampᴸ st x z ≐ ψ z) →
            ∀ z → ampᴸ (proj₂ (run C st)) x z ≐ applyᴬ C ψ z
  run-amp []               st x ψ h = h
  run-amp (H w ∷ C)        st x ψ h =
    run-amp C (stepH w st) x (gateᴬ (H w) ψ) (step-amp (H w) st x ψ h)
  run-amp (X w ∷ C)        st x ψ h =
    run-amp C (stepX w st) x (gateᴬ (X w) ψ) (step-amp (X w) st x ψ h)
  run-amp (CNOT c t p ∷ C) st x ψ h =
    run-amp C (stepCNOT c t st) x (gateᴬ (CNOT c t p) ψ)
            (step-amp (CNOT c t p) st x ψ h)
  run-amp (R k w ∷ C)      st x ψ h =
    run-amp C (stepR k w st) x (gateᴬ (R k w) ψ)
            (step-amp (R k w) st x ψ h)
  run-amp (R† k w ∷ C)     st x ψ h =
    run-amp C (stepR† k w st) x (gateᴬ (R† k w) ψ)
            (step-amp (R† k w) st x ψ h)

-- The amplitude of ⟦ C ⟧ from x to z is the entry at z of C applied
-- to |x⟩.

prop-2-10 : (C : Circuit n) (x z : Assign n) →
            amp ⟦ C ⟧ x z ≐ applyᴬ C (δ x) z
prop-2-10 C x = run-amp C init x (δ x) (ampᴸ-init x)

-- Hence a circuit is the identity exactly when its matrix is.

MatrixId : Circuit n → Set
MatrixId C = ∀ x z → applyᴬ C (δ x) z ≐ scale (norm C) (δ x z)

circuit-≋-id : (C : Circuit n) → (⟦ C ⟧ ≋ idPS ⇔ MatrixId C)
circuit-≋-id C = mk⇔
  (λ eq x z i → trans (sym (prop-2-10 C x z i))
    (trans (eq x z i) (scale-map (norm C) (amp-idPS-δ x z) i)))
  (λ eq x z i → trans (prop-2-10 C x z i)
    (trans (eq x z i) (sym (scale-map (norm C) (amp-idPS-δ x z) i))))


------------------------------------------------------------------------
-- Checking a closed circuit by computing its matrix

private
  -- A decidable property that reads assignments only through their
  -- values holds everywhere or fails somewhere (PathSum.Decide.search).

  every? : {P : Assign n → Set} → (∀ x → Dec (P x)) →
           (∀ {x x′} → (∀ i → x i ≡ x′ i) → P x → P x′) →
           Dec (∀ x → P x)
  every? {P = P} P? resp =
    [ yes , (λ (x , ¬p) → no (λ h → ¬p (h x))) ]′ (search P P? resp)

  coords? : (a b : Amp) → Dec (a ≐ b)
  coords? a b = all? (λ i → a i ≟ℤ b i)

  δ-resp : (x : Assign n) → Respects (δ x)
  δ-resp x z z′ zz i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
    (same-≗ {x = x} {x′ = x} {z = z} {z′ = z′} (λ _ → refl) zz)

  δ-≗ : {x x′ : Assign n} → (∀ i → x i ≡ x′ i) → ∀ z → δ x z ≐ δ x′ z
  δ-≗ {x = x} {x′} xx z i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
    (same-≗ {x = x} {x′ = x′} {z = z} {z′ = z} xx (λ _ → refl))

-- Every entry, every coordinate.

matrix-id? : (C : Circuit n) → Dec (MatrixId C)
matrix-id? {n} C = every? (λ x → every? (entry? x) (resp-z x)) resp-x
  where
  Entry : Assign n → Assign n → Set
  Entry x z = applyᴬ C (δ x) z ≐ scale (norm C) (δ x z)

  entry? : ∀ x z → Dec (Entry x z)
  entry? x z = coords? (applyᴬ C (δ x) z) (scale (norm C) (δ x z))

  resp-z : ∀ x {z z′} → (∀ w → z w ≡ z′ w) → Entry x z → Entry x z′
  resp-z x {z} {z′} zz e i =
    trans (sym (applyᴬ-resp C (δ-resp x) z z′ zz i))
      (trans (e i) (scale-map (norm C) (δ-resp x z z′ zz) i))

  resp-x : ∀ {x x′} → (∀ i → x i ≡ x′ i) →
           (∀ z → Entry x z) → ∀ z → Entry x′ z
  resp-x {x} {x′} xx h z i =
    trans (sym (applyᴬ-cong C {δ x} {δ x′} (δ-≗ xx) z i))
      (trans (h z i) (scale-map (norm C) (δ-≗ xx z) i))

-- A closed circuit whose matrix computes to the identity is the
-- identity, and one whose matrix computes to something else is not.

circuit-id! : (C : Circuit n) → {True (matrix-id? C)} → ⟦ C ⟧ ≋ idPS
circuit-id! C {t} =
  Equivalence.from (circuit-≋-id C) (toWitness {a? = matrix-id? C} t)

circuit-not-id! : (C : Circuit n) → {False (matrix-id? C)} →
                  ¬ (⟦ C ⟧ ≋ idPS)
circuit-not-id! C {f} eq =
  toWitnessFalse {a? = matrix-id? C} f (Equivalence.to (circuit-≋-id C) eq)
