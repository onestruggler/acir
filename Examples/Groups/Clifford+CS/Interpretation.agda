------------------------------------------------------------------------
-- Presentations of groups
--
-- The interpretation of Clifford+CS circuits as matrices over ℤ[½,i]:
-- ⟦_⟧ : Circuit n → Scaled n
--
-- This is Real-Clifford+CH.Interpretation with γ for √2, and a clause
-- for the 0-ary gate, which is the scalar γ i at every width.
--
-- A generator denotes γ times its gate matrix (Semantics), a word of ℓ
-- letters denotes (ℓ , M) with M the product of its letters' matrices,
-- read left to right: the matrix γ^(−ℓ) M.  The number of letters is
-- `len`; the operator is ⟦_⟧ₒ, which is ABSTRACT.  That is the one
-- design decision of this module, and it is what keeps the checker
-- alive: operators are functions, so Agda decides whether two of them
-- are equal by applying them to arguments and normalising, and the
-- product of forty gate matrices applied to arguments is a sum over
-- every intermediate index — exponential in the length of the word.
-- Agda has to do that whenever two readings of a long word are not
-- syntactically identical, which happens for reasons invisible in the
-- source (a width elaborated as 3 here and as ₃₊ 0 there).  With ⟦_⟧ₒ
-- abstract the checker cannot unfold it, so two readings ⟦ w ⟧ₒ and
-- ⟦ w′ ⟧ₒ are compared by comparing the WORDS w and w′, which is
-- linear.  The defining equations are available as the lemmas
-- ⟦⟧ₒ-gen, ⟦⟧ₒ-ε and ⟦⟧ₒ-• (and their three- and four-fold forms),
-- and every proof downstream rewrites with them explicitly.
--
-- The library's StarInterp reading, built from the target monoid, is
-- Ext.⟦_⟧ᴱ; it equals ⟦_⟧ (⟦⟧ᴱ-def), and it is what the presentation
-- machinery of StarPresentation consumes, and what proofs that need
-- ⟦ w • v ⟧ to be ⟦ w ⟧ ∙ ⟦ v ⟧ on the nose (a homomorphism law) use.
--
-- A circuit is also read as a stored trie, ⟦_⟧M: the same product
-- tabulated after every letter, where the relations are checked.
-- `localise` connects the two.  A relation of Syntactics is stated at the
-- width it is drawn on and lifted to every width by cong↑; its two
-- sides only mention the bottom wires, and the relator at width k + n
-- is the relator at width k with idle wires padded on top (_↓ᵏ_).  So
--
--     ⟦ w ↓ᵏ n ⟧ₒ ≐ emb ⟦ w ⟧M,
--
-- and an axiom at any width follows from ONE equation of matrices at
-- the width the axiom is written for (by-matrix).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Interpretation where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Clifford+CS.Semantics
open import Examples.Groups.Clifford+CS.Syntactics

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Denotation of generators and words

-- γ times the gate, on its wires.
⟦_⟧ᵍ : Gen n → Op n
⟦ I-gen  ⟧ᵍ = iOp
⟦ S-gen  ⟧ᵍ = emb sM
⟦ K-gen  ⟧ᵍ = emb kM
⟦ CS-gen ⟧ᵍ = emb csM
⟦ g ↥    ⟧ᵍ = up ⟦ g ⟧ᵍ

-- The number of letters.
len : Circuit n → ℕ
len [ g ]ʷ  = 1
len ε       = 0
len (w • v) = len w +ℕ len v

-- The product of the scaled gate matrices, read left to right: w • v
-- applies w first, then v.  Abstract (see the header); its defining
-- equations follow, as lemmas.
abstract
  ⟦_⟧ₒ : Circuit n → Op n
  ⟦ [ g ]ʷ ⟧ₒ = ⟦ g ⟧ᵍ
  ⟦ ε ⟧ₒ      = Idₒ
  ⟦ w • v ⟧ₒ  = ⟦ w ⟧ₒ ⊙ ⟦ v ⟧ₒ

  ⟦⟧ₒ-gen : (g : Gen n) → ⟦ [ g ]ʷ ⟧ₒ ≐ ⟦ g ⟧ᵍ
  ⟦⟧ₒ-gen g = ≐-refl ⟦ g ⟧ᵍ

  ⟦⟧ₒ-ε : ⟦_⟧ₒ {n} ε ≐ Idₒ
  ⟦⟧ₒ-ε = ≐-refl Idₒ

  ⟦⟧ₒ-• : (w v : Circuit n) → ⟦ w • v ⟧ₒ ≐ (⟦ w ⟧ₒ ⊙ ⟦ v ⟧ₒ)
  ⟦⟧ₒ-• w v = ≐-refl (⟦ w ⟧ₒ ⊙ ⟦ v ⟧ₒ)

  ⟦⟧ₒ-•₃ : (a b c : Circuit n) → ⟦ a • (b • c) ⟧ₒ ≐ (⟦ a ⟧ₒ ⊙ (⟦ b ⟧ₒ ⊙ ⟦ c ⟧ₒ))
  ⟦⟧ₒ-•₃ a b c = ≐-refl (⟦ a ⟧ₒ ⊙ (⟦ b ⟧ₒ ⊙ ⟦ c ⟧ₒ))

  ⟦⟧ₒ-•₄ : (a b c d : Circuit n) →
           ⟦ a • (b • (c • d)) ⟧ₒ ≐ (⟦ a ⟧ₒ ⊙ (⟦ b ⟧ₒ ⊙ (⟦ c ⟧ₒ ⊙ ⟦ d ⟧ₒ)))
  ⟦⟧ₒ-•₄ a b c d = ≐-refl (⟦ a ⟧ₒ ⊙ (⟦ b ⟧ₒ ⊙ (⟦ c ⟧ₒ ⊙ ⟦ d ⟧ₒ)))

-- The denotation: the matrix γ^(−len w) · ⟦ w ⟧ₒ.
⟦_⟧ : Circuit n → Scaled n
⟦ w ⟧ = len w , ⟦ w ⟧ₒ

-- The same reading as StarInterp builds it from the monoid, for the
-- presentation machinery; the two agree on the nose.
module Ext (n : ℕ) where
  open import Normalization.StarInterp (n VRel,_===_)
  open Extend (Scaled-monoid n) (λ g → 1 , ⟦ g ⟧ᵍ) public
    renaming (⟦_⟧ to ⟦_⟧ᴱ)

abstract
  ⟦⟧ᴱ-def : (w : Circuit n) → Ext.⟦_⟧ᴱ n w ≡ ⟦ w ⟧
  ⟦⟧ᴱ-def [ g ]ʷ  = Eq.refl
  ⟦⟧ᴱ-def ε       = Eq.refl
  ⟦⟧ᴱ-def (w • v) = Eq.cong₂ _∙_ (⟦⟧ᴱ-def w) (⟦⟧ᴱ-def v)

-- Facts about ⟦_⟧ᴱ are facts about ⟦_⟧, and back.
⟦⟧ᴱ-~ : {w v : Circuit n} → ⟦ w ⟧ ~ ⟦ v ⟧ → Ext.⟦_⟧ᴱ n w ~ Ext.⟦_⟧ᴱ n v
⟦⟧ᴱ-~ {w = w} {v} = Eq.subst₂ _~_ (Eq.sym (⟦⟧ᴱ-def w)) (Eq.sym (⟦⟧ᴱ-def v))

~-⟦⟧ᴱ : {w v : Circuit n} → Ext.⟦_⟧ᴱ n w ~ Ext.⟦_⟧ᴱ n v → ⟦ w ⟧ ~ ⟦ v ⟧
~-⟦⟧ᴱ {w = w} {v} = Eq.subst₂ _~_ (⟦⟧ᴱ-def w) (⟦⟧ᴱ-def v)

------------------------------------------------------------------------
-- The stored reading

valMat : Gen k → Mat k
valMat I-gen  = iM
valMat S-gen  = tenM sM idM
valMat K-gen  = tenM kM idM
valMat CS-gen = tenM csM idM
valMat (g ↥)  = tenM (idM {1}) (valMat g)

⟦_⟧M : Circuit k → Mat k
⟦ [ g ]ʷ ⟧M = valMat g
⟦ ε ⟧M      = idM
⟦ w • v ⟧M  = mulM ⟦ w ⟧M ⟦ v ⟧M

------------------------------------------------------------------------
-- Localisation
--
-- A circuit written at width k, read at width k + n, is its own matrix
-- acting on the bottom k wires, with as many letters.

localise-gen : (g : Gen k) → ⟦ g ↧ᵏ n ⟧ᵍ ≐ emb {k} {n} (valMat g)
localise-gen {k} {n} I-gen =
  ≐-trans (≐-sym (scal-tensor {k} {n} γⅈ))
          (tensor-cong (≐-sym (ix-matOf (iOp {k}))) (≐-refl Idₒ))
localise-gen S-gen  = emb-pad₁ sM
localise-gen K-gen  = emb-pad₁ kM
localise-gen CS-gen = emb-pad₂ csM
localise-gen (g ↥)  =
  ≐-trans (up-cong (localise-gen g)) (up-emb (valMat g))

-- At its own width, a generator's operator is its stored matrix.
gen-ix : (g : Gen k) → ⟦ g ⟧ᵍ ≐ ix (valMat g)
gen-ix {k} I-gen = ≐-sym (ix-matOf (iOp {k}))
gen-ix S-gen  = ≐-trans (tensor-cong (≐-refl (ix sM)) (≐-sym ix-id)) (≐-sym (ix-tenM sM idM))
gen-ix K-gen  = ≐-trans (tensor-cong (≐-refl (ix kM)) (≐-sym ix-id)) (≐-sym (ix-tenM kM idM))
gen-ix CS-gen = ≐-trans (tensor-cong (≐-refl (ix csM)) (≐-sym ix-id)) (≐-sym (ix-tenM csM idM))
gen-ix (g ↥)  =
  ≐-trans (tensor-cong (≐-sym ix-id) (gen-ix g)) (≐-sym (ix-tenM (idM {1}) (valMat g)))

-- The three inductions on words that need the operator to unfold.
abstract
  localise : (w : Circuit k) → ⟦ w ↓ᵏ n ⟧ₒ ≐ emb {k} {n} ⟦ w ⟧M
  localise [ g ]ʷ      = localise-gen g
  localise {k} {n} ε   = ≐-sym (emb-id {k} {n})
  localise (w • v) =
    ≐-trans (⊙-cong (localise w) (localise v)) (emb-⊙ ⟦ w ⟧M ⟦ v ⟧M)

  -- At its own width, a circuit's operator is its stored matrix.
  ⟦⟧-ix : (w : Circuit k) → ⟦ w ⟧ₒ ≐ ix ⟦ w ⟧M
  ⟦⟧-ix [ g ]ʷ  = gen-ix g
  ⟦⟧-ix ε       = ≐-sym ix-id
  ⟦⟧-ix (w • v) =
    ≐-trans (⊙-cong (⟦⟧-ix w) (⟦⟧-ix v)) (≐-sym (ix-mul ⟦ w ⟧M ⟦ v ⟧M))

  -- Shifting a circuit is tensoring with I₂ on the new wire.
  up-word : (w : Circuit n) → ⟦ w ↑ ⟧ₒ ≐ up ⟦ w ⟧ₒ
  up-word [ g ]ʷ  = ≐-refl (up ⟦ g ⟧ᵍ)
  up-word ε       = ≐-sym up-Id
  up-word (w • v) =
    ≐-trans (⊙-cong (up-word w) (up-word v)) (up-⊙ ⟦ w ⟧ₒ ⟦ v ⟧ₒ)

-- Padding and shifting keep the number of letters.
len-↓ᵏ : (w : Circuit k) → len (w ↓ᵏ n) ≡ len w
len-↓ᵏ [ g ]ʷ  = Eq.refl
len-↓ᵏ ε       = Eq.refl
len-↓ᵏ (w • v) = Eq.cong₂ _+ℕ_ (len-↓ᵏ w) (len-↓ᵏ v)

len-↑ : (w : Circuit n) → len (w ↑) ≡ len w
len-↑ [ g ]ʷ  = Eq.refl
len-↑ ε       = Eq.refl
len-↑ (w • v) = Eq.cong₂ _+ℕ_ (len-↑ w) (len-↑ v)

------------------------------------------------------------------------
-- One matrix identity, at every width
--
-- Two circuits of the same width denote the same matrix over ℤ[½,i]
-- when their stored matrices agree once each is scaled by the other's
-- power of γ — an equation of Gaussian-integer tries, checked by `refl`.

-- A scalar passes into a local gate.
·-emb : (c : 𝔽) (M : Mat k) → (c · emb {k} {n} M) ≐ emb (scaleM c M)
·-emb {k} {n} c M x y =
  Eq.trans (Eq.sym (tensor-scaleˡ c (ix M) Idₒ x y))
           (Eq.sym (tensor-cong {m = k} {n = n} (ix-scaleM c M) (≐-refl Idₒ) x y))

by-matrix : (u v : Circuit k) →
            scaleM (γ^ len v) ⟦ u ⟧M ≡ scaleM (γ^ len u) ⟦ v ⟧M →
            ⟦ u ↓ᵏ n ⟧ ~ ⟦ v ↓ᵏ n ⟧
by-matrix {k} {n} u v eq =
  ≐-trans (·-cong (Eq.cong γ^_ (len-↓ᵏ v)) (localise u))
    (≐-trans (·-emb (γ^ len v) ⟦ u ⟧M)
      (≐-trans (emb-≡ eq)
        (≐-trans (≐-sym (·-emb (γ^ len u) ⟦ v ⟧M))
                 (·-cong (Eq.cong γ^_ (Eq.sym (len-↓ᵏ u))) (≐-sym (localise v))))))
  where
  emb-≡ : {M N : Mat k} → M ≡ N → emb {k} {n} M ≐ emb N
  emb-≡ {M = M} Eq.refl = ≐-refl (emb M)

-- The same, for an axiom spelled at its own width: the two words are
-- the padded relators, an equation of WORDS decided on data.  (With
-- ⟦_⟧ₒ abstract the checker would also identify the two readings by
-- comparing the words; the equations keep that explicit.)
by-relator : (u v : Circuit k) {u′ v′ : Circuit (k +ℕ n)} →
             u ↓ᵏ n ≡ u′ → v ↓ᵏ n ≡ v′ →
             scaleM (γ^ len v) ⟦ u ⟧M ≡ scaleM (γ^ len u) ⟦ v ⟧M →
             ⟦ u′ ⟧ ~ ⟦ v′ ⟧
by-relator u v Eq.refl Eq.refl eq = by-matrix u v eq
