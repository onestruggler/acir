------------------------------------------------------------------------
-- Presentations of groups
--
-- Deciding compatibility decides whether ancillas are clean (Amy, QPL
-- 2018, footnote 1)
--
-- Footnote 1: "Determining compatibility is at least as hard as
-- detecting whether an ancilla is clean and is hence non-trivial in
-- general."  An ancilla is clean when a circuit started with it in |0⟩
-- always returns it to |0⟩: from every input whose ancillas are 0, no
-- amplitude reaches an output with an ancilla at 1.  That is the
-- conclusion PathSum.Ancillas.clean-ancillas draws (LeavesClean, for a
-- family of ancillas) and PathSum.Ancilla.clean-ancilla for one
-- (LeavesClean₁).
--
-- The reduction is the identity on path-sums.  Sign ξ with the
-- constant 0 on its ancillas, and ask whether its output is compatible
-- with that same signature: the range of U_ξ, from the clean inputs,
-- lies in the span of the clean outputs exactly when ξ leaves its
-- ancillas clean (clean⇔compatible; clean₁⇔compatible for one ancilla,
-- the signature at i 0).  So a decision procedure for compatibility,
-- in the operator form of PathSum.Signature.Compose, decides
-- cleanliness, with no overhead (decide-clean); and conversely the
-- library's way of verifying a clean ancilla, an equivalence on the
-- clean inputs to a path-sum whose outputs there are 0 on the
-- ancillas, certifies compatibility (verified⇒compatible).  This is
-- the footnote's claim for the notion of compatibility under which
-- proposition 2.7 holds exactly (PathSum.Signature.Compose's
-- compatible⇔prop-2-7).  Reading the footnote this way is an
-- interpretation: the paper's syntactic notion is decided by one scan
-- of the coefficients (in time linear in the size of the
-- representation -- an informal remark, since running time is not
-- formalised here), and it is only a sufficient condition (Compose's
-- range⇏path, path-not-invariant), so it is unlikely to be what the
-- footnote calls hard.
--
-- "Hence non-trivial": cleanliness is as hard as unsatisfiability.
-- PathSum.Hardness reduces a CNF formula φ to a Clifford+T circuit
-- computing |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ φ(x)⟩.  Its ancillas alone are
-- always left clean, so the circuit prepared with them at 0 is always
-- compatible with that preparation (circuit-ancillas-compatible).
-- Watching its ancillas and its target wire t together (watched φ),
-- the circuit leaves them all clean exactly when φ is unsatisfiable
-- (clean⇔unsat), and so its path-sum, prepared with all of them at 0,
-- is compatible with that preparation exactly when φ is unsatisfiable
-- (compatible⇔unsat).  A decision procedure for compatibility therefore
-- decides unsatisfiability (decide-unsat), through PathSum.Hardness's
-- reduction.  Its circuit has size linear in φ (circuit-length-bound,
-- circuit-paths, wires-bound), but those bound the circuit: the
-- decider is handed its path-sum ⟦ circuit φ ⟧, which in the dense
-- representation of this library is a table exponential in the numbers
-- of wires and path variables, and no bound on a sparse representation
-- of that path-sum is combined with the reduction here.  That
-- unsatisfiability is co-NP-complete, and so that compatibility is
-- co-NP-hard, is the informal step: as in PathSum.Hardness, complexity
-- classes and running times are not formalised.  Compatibility is
-- decidable (Compose.compatible?, by brute force, exponential), so
-- "non-trivial" is a statement about cost, and what is formalised is
-- the reduction.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Signature.Clean (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _xor_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Fin.Base using (Fin; zero; suc; _↑ʳ_)
open import Data.Integer.Base using (0ℤ)
open import Data.Nat.Base using (suc; _+_)
open import Data.Product.Base using (∃; _,_)
open import Data.Sum.Base using ([_,_]′)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (Dec; yes; no; map)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Fin.Properties as Fin

open import PathSum.Ancillas M₀ using (Clean; _≋[_]₀*_; clean-ancillas)
open import PathSum.Assign using
  (≔-here; ≔-there; same; same-refl; same-true)
open import PathSum.Base using (PathSum)
open import PathSum.Classical M₀ using (amp-computes)
open import PathSum.CRK.Path M₀ using (⟦_⟧; norm)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; zpow-0≢0ᴬ; scale-map; scale-injective)
open import PathSum.Denotation M₀ using (Assign; amp; outBit)
open import PathSum.Hardness M₀ using
  (circuit; circuit-computes; circuit-clean)
open import PathSum.Hardness.CNF using
  (CNF; ⟦_⟧ᶠ; ⟦⟧ᶠ-cong; cnf; nodes; Unsatisfiable)
open import PathSum.Hardness.Netlist using
  (runᴺ; wires; inputs; ancillas; tgt; netlist; netlist-correct; blank;
   blank-inp; blank-clean; tgtʷ; anc≢tgtʷ)
open import PathSum.Signature M₀ using
  (Signature; Agrees; agrees?; Signed; _⊢_; ampˢ; ampˢ-in; ampˢ-out;
   scale-0ᴬ; zeros; image; at; Agrees-at; Clean⇔Agrees)
open import PathSum.Signature.Compose M₀ using (Compatible)

private
  variable
    n j k m k′ m′ : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  infixr 5 _⟨⇔⟩_

  _⟨⇔⟩_ : {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
  f ⟨⇔⟩ g = mk⇔ (λ a → Equivalence.to g (Equivalence.to f a))
                (λ c → Equivalence.from f (Equivalence.from g c))

  sym⇔ : {A B : Set} → A ⇔ B → B ⇔ A
  sym⇔ f = mk⇔ (Equivalence.from f) (Equivalence.to f)

  false≢true : false ≢ true
  false≢true ()

  false-if : ∀ c → ¬ (c ≡ true) → c ≡ false
  false-if true  f = contradiction refl f
  false-if false _ = refl

  true-if : ∀ c → ¬ (c ≡ false) → c ≡ true
  true-if true  _ = refl
  true-if false f = contradiction refl f


------------------------------------------------------------------------
-- Clean ancillas

-- From every input whose ancillas are 0, no amplitude reaches an output
-- with an ancilla at 1: PathSum.Ancillas.clean-ancillas's conclusion,
-- and PathSum.Ancilla.clean-ancilla's for a single ancilla.

LeavesClean : PathSum n k m → (Fin j → Fin n) → Set
LeavesClean ξ a =
  ∀ x z → Clean a x → (i : Fin _) → z (a i) ≡ true → amp ξ x z ≐ 0ᴬ

LeavesClean₁ : PathSum n k m → Fin n → Set
LeavesClean₁ ξ i = ∀ x z → x i ≡ false → z i ≡ true → amp ξ x z ≐ 0ᴬ

-- The signature preparing the ancillas in |0⟩.

prepare : (Fin j → Fin n) → Signature n
prepare a = zeros (image a)


------------------------------------------------------------------------
-- Cleanliness is compatibility

-- ξ leaves its ancillas clean exactly when, prepared with them at 0,
-- its output is compatible with that preparation.

clean⇔compatible : (ξ : PathSum n k m) (a : Fin j → Fin n) →
                   LeavesClean ξ a ⇔ Compatible (prepare a ⊢ ξ) (prepare a)
clean⇔compatible {j = j} ξ a = mk⇔ to from
  where
  to : LeavesClean ξ a → Compatible (prepare a ⊢ ξ) (prepare a)
  to lc x z na = go (agrees? (prepare a) x)
    where
    -- Some ancilla of z is 1.
    dirty : ¬ Clean a z
    dirty cl = na (Equivalence.to (Clean⇔Agrees a z) cl)

    one : ∃ (λ i → ¬ (z (a i) ≡ false))
    one = Fin.¬∀⇒∃¬ j (λ i → z (a i) ≡ false) (λ i → z (a i) ≟ᵇ false)
                     dirty

    at1 : Agrees (prepare a) x → ∃ (λ i → ¬ (z (a i) ≡ false)) →
          amp ξ x z ≐ 0ᴬ
    at1 ag (i , ¬0) =
      lc x z (Equivalence.from (Clean⇔Agrees a x) ag) i
         (true-if (z (a i)) ¬0)

    go : Dec (Agrees (prepare a) x) → ampˢ (prepare a ⊢ ξ) x z ≐ 0ᴬ
    go (no na₀) = ampˢ-out (prepare a ⊢ ξ) na₀ z
    go (yes ag) = ampˢ-in (prepare a ⊢ ξ) ag z ∙ at1 ag one

  from : Compatible (prepare a ⊢ ξ) (prepare a) → LeavesClean ξ a
  from c x z cl i e =
    ≐-sym (ampˢ-in (prepare a ⊢ ξ)
             (Equivalence.to (Clean⇔Agrees a x) cl) z)
    ∙ c x z (λ ag → false≢true
        (trans (sym (Equivalence.from (Clean⇔Agrees a z) ag i)) e))

-- For one ancilla, the signature at i 0.

clean₁⇔compatible : (ξ : PathSum n k m) (i : Fin n) →
                    LeavesClean₁ ξ i ⇔
                    Compatible (at i false ⊢ ξ) (at i false)
clean₁⇔compatible ξ i = mk⇔
  (λ lc x z na → go lc x z na (agrees? (at i false) x))
  (λ c x z x₀ z₁ →
     ≐-sym (ampˢ-in (at i false ⊢ ξ)
              (Equivalence.from (Agrees-at i false x) x₀) z)
     ∙ c x z (λ ag → false≢true
         (trans (sym (Equivalence.to (Agrees-at i false z) ag)) z₁)))
  where
  go : LeavesClean₁ ξ i → ∀ x z → ¬ Agrees (at i false) z →
       Dec (Agrees (at i false) x) → ampˢ (at i false ⊢ ξ) x z ≐ 0ᴬ
  go lc x z na (no na₀) = ampˢ-out (at i false ⊢ ξ) na₀ z
  go lc x z na (yes ag) = ampˢ-in (at i false ⊢ ξ) ag z
    ∙ lc x z (Equivalence.to (Agrees-at i false x) ag)
             (true-if (z i) (λ e →
                na (Equivalence.from (Agrees-at i false z) e)))

-- So deciding compatibility decides cleanliness.

decide-clean : (ξ : PathSum n k m) (a : Fin j → Fin n) →
               Dec (Compatible (prepare a ⊢ ξ) (prepare a)) →
               Dec (LeavesClean ξ a)
decide-clean ξ a = map (sym⇔ (clean⇔compatible ξ a))

-- And verifying a clean ancilla as the library does -- equivalence on
-- the clean inputs to a path-sum whose outputs there are 0 on the
-- ancillas (PathSum.Ancillas.clean-ancillas) -- certifies
-- compatibility.

verified⇒compatible : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
                      (a : Fin j → Fin n) → ξ ≋[ a ]₀* ζ →
                      (∀ x (y : Assign m′) → Clean a x →
                       ∀ i → outBit ζ x y (a i) ≡ false) →
                      Compatible (prepare a ⊢ ξ) (prepare a)
verified⇒compatible {ξ = ξ} a eq out0 =
  Equivalence.to (clean⇔compatible ξ a) (clean-ancillas a eq out0)


------------------------------------------------------------------------
-- Cleanliness is as hard as unsatisfiability

-- The wires of PathSum.Hardness's circuit that start in |0⟩: the
-- target, then the ancillas.

watched : (φ : CNF n) → Fin (suc (suc (nodes (cnf φ)))) → Fin (wires φ)
watched φ zero    = tgt φ
watched φ (suc i) = ancillas φ i

-- The ancillas alone are always left clean (PathSum.Hardness's
-- circuit-clean): the circuit prepared with them at 0 is compatible
-- with that preparation, whatever φ.

circuit-ancillas-compatible :
  (φ : CNF n) →
  Compatible (prepare (ancillas φ) ⊢ ⟦ circuit φ ⟧) (prepare (ancillas φ))
circuit-ancillas-compatible φ =
  Equivalence.to (clean⇔compatible ⟦ circuit φ ⟧ (ancillas φ))
                 (circuit-clean φ)

private
  -- The input |v⟩|0⟩|0⟩ has its target at 0.

  blank-tgt : ∀ {n} s (v : Assign n) → blank s v (tgtʷ n s) ≡ false
  blank-tgt {n} s v =
    cong [ v , (λ _ → false) ]′
         (Fin.splitAt-↑ʳ n (suc s + 1) (suc s ↑ʳ zero))

-- The circuit leaves its target and ancillas clean exactly when φ is
-- unsatisfiable.  On a clean input it writes φ(x) on the target and
-- leaves everything else; so it can reach an output with a watched
-- wire at 1 only by φ(x) = 1, and at the input |v⟩|0⟩|0⟩ it does reach
-- |v⟩|0⟩|φ(v)⟩, with an amplitude that is not 0.

clean⇔unsat : (φ : CNF n) →
              LeavesClean ⟦ circuit φ ⟧ (watched φ) ⇔ Unsatisfiable φ
clean⇔unsat {n = n} φ = mk⇔ to from
  where
  F : Assign (wires φ) → Assign (wires φ)
  F = runᴺ (netlist φ)

  -- The bit φ writes on the target.
  φ-of : Assign (wires φ) → Bool
  φ-of x = ⟦ φ ⟧ᶠ (λ v → x (inputs φ v))

  out-tgt : ∀ x → Clean (watched φ) x → F x (tgt φ) ≡ φ-of x
  out-tgt x cl = trans
    (netlist-correct φ x (λ i → cl (suc i)) (tgt φ))
    (trans (≔-here x (tgt φ) (x (tgt φ) xor φ-of x))
           (cong (_xor φ-of x) (cl zero)))

  out-anc : ∀ x → Clean (watched φ) x → ∀ i → F x (ancillas φ i) ≡ false
  out-anc x cl i = trans
    (netlist-correct φ x (λ i′ → cl (suc i′)) (ancillas φ i))
    (trans (≔-there x (x (tgt φ) xor φ-of x)
                    (anc≢tgtʷ n (nodes (cnf φ)) i))
           (cl (suc i)))

  -- The entry of the circuit from x to z, which is 0 unless z = F x.
  entry : ∀ x z → same (F x) z ≡ false → amp ⟦ circuit φ ⟧ x z ≐ 0ᴬ
  entry x z e =
    amp-computes (circuit-computes φ) x z
    ∙ scale-map (norm (circuit φ))
        (λ i → cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) e)
    ∙ scale-0ᴬ (norm (circuit φ))

  from : Unsatisfiable φ → LeavesClean ⟦ circuit φ ⟧ (watched φ)
  from u x z cl i e = entry x z (false-if (same (F x) z) (λ s →
    false≢true (trans (sym (watched-out i))
                      (trans (same-true (F x) z s (watched φ i)) e))))
    where
    watched-out : ∀ i → F x (watched φ i) ≡ false
    watched-out zero    = trans (out-tgt x cl) (u (λ v → x (inputs φ v)))
    watched-out (suc i) = out-anc x cl i

  to : LeavesClean ⟦ circuit φ ⟧ (watched φ) → Unsatisfiable φ
  to lc v = false-if (⟦ φ ⟧ᶠ v) (λ sat → zpow-0≢0ᴬ
    (scale-injective (norm (circuit φ)) (zpow 0ℤ) 0ᴬ
      (scale-map (norm (circuit φ))
         (λ i → cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
                     (sym (same-refl (F x))))
       ∙ ≐-sym (amp-computes (circuit-computes φ) x (F x))
       ∙ lc x (F x) cl zero
           (trans (out-tgt x cl)
                  (trans (⟦⟧ᶠ-cong φ (blank-inp (nodes (cnf φ)) v)) sat))
       ∙ ≐-sym (scale-0ᴬ (norm (circuit φ))))))
    where
    x : Assign (wires φ)
    x = blank (nodes (cnf φ)) v

    cl : Clean (watched φ) x
    cl zero    = blank-tgt (nodes (cnf φ)) v
    cl (suc i) = blank-clean (nodes (cnf φ)) v i

-- So the circuit's path-sum, prepared with its target and ancillas at
-- 0, is compatible with that preparation exactly when φ is
-- unsatisfiable ...

compatible⇔unsat : (φ : CNF n) →
                   Compatible (prepare (watched φ) ⊢ ⟦ circuit φ ⟧)
                              (prepare (watched φ)) ⇔
                   Unsatisfiable φ
compatible⇔unsat φ =
  sym⇔ (clean⇔compatible ⟦ circuit φ ⟧ (watched φ)) ⟨⇔⟩ clean⇔unsat φ

-- ... and a decision procedure for compatibility decides
-- unsatisfiability.

CompatibilityDecider : Set
CompatibilityDecider =
  ∀ {n k m} (ξ : Signed n k m) (σ′ : Signature n) → Dec (Compatible ξ σ′)

decide-unsat : CompatibilityDecider → (φ : CNF n) → Dec (Unsatisfiable φ)
decide-unsat d φ =
  map (compatible⇔unsat φ)
      (d (prepare (watched φ) ⊢ ⟦ circuit φ ⟧) (prepare (watched φ)))
