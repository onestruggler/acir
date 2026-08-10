------------------------------------------------------------------------
-- Presentations of groups
--
-- The wreath product ℤ/Nℤ ≀ Sₙ as a group presentation.
--
-- The normal factor is the n-fold direct product (ℤ/Nℤ)ⁿ (presented via
-- the n-fold direct-product construction), the acting factor is the
-- symmetric group Sₙ (the Coxeter presentation), and Sₙ acts by
-- permuting the n coordinates.  Feeding the two factor presentations and
-- this (word-valued) coordinate action into the semi-direct-product
-- construction yields a presentation of the wreath-product group.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Construct.SemiDirectProduct.SnD where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Function using (id ; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base
open import Word.Properties using (wmap-∘)

open import Algebra.Bundles using (Group)
open import Level using (0ℓ)
open import Presentation.Construct.Base
  using (_⊎^_ ; _⊕^_ ; [_]ₗ ; [_]ᵣ ; _⋄_⋄_ ; left ; right ; mid ; CommRel ; comm
        ; ConjRelʷ ; module LeftRightCongruence)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Normalization.NormalForm.Propositional
  using (NormalFormInjective ; NormalForm)
import Presentation.Base as PB
import Presentation.Construct.Properties.NDirectProduct as NDP
-- Primed: the construction itself.  SDP below is this instance of it.
import Presentation.Construct.Properties.SemiDirectProduct as SDP'
open import Examples.Groups.Cyclic.Normalization as Cyc using (_Cn,_===_)
open import Examples.Groups.Cyclic.Semantics using (Cn-group)
import Examples.Groups.Cyclic.Presentation as CyP
open import Examples.Groups.Symmetric.Tight.Semantics using (Permutation′-group)
import Examples.Groups.Symmetric.Tight.Presentation as ST
import Examples.Groups.Symmetric.Normalization as SN

private
  -- The base factor: ℤ/(suc m)ℤ, a single generator of order suc m.
  Γ₀ : ℕ → WRel ⊤
  Γ₀ m = suc m Cn,_===_
open import Examples.Groups.Symmetric.Syntactics
  using (Gate ; σ-gate ; Gen ; gate₀ ; gate₁ ; gate₂ ; _↥ ; _↑ ; σ ; _SRel,_===_
        ; order ; yang-baxter ; srel ; cong↑ ; comm₁ ; comm₂ ; _VRel,_===_)

------------------------------------------------------------------------
-- The coordinate action of Sₙ on (ℤ/Nℤ)ⁿ
--
-- A coordinate is an element of ⊤ ⊎^ n (n copies of the single cyclic
-- generator).  A wire-transposition swaps two adjacent coordinates; a
-- shifted generator acts on the shifted coordinates.

-- The transposition of the bottom two coordinates.
sw₂ : ∀ {n} → ⊤ ⊎^ (₂₊ n) → ⊤ ⊎^ (₂₊ n)
sw₂ {zero}  (inj₁ tt)        = inj₂ tt
sw₂ {zero}  (inj₂ tt)        = inj₁ tt
sw₂ {₁₊ n}  (inj₁ tt)        = inj₂ (inj₁ tt)
sw₂ {₁₊ n}  (inj₂ (inj₁ tt)) = inj₁ tt
sw₂ {₁₊ n}  (inj₂ (inj₂ y))  = inj₂ (inj₂ y)

-- The permutation of coordinates induced by a generator.
act : ∀ {n} → Gen n → ⊤ ⊎^ n → ⊤ ⊎^ n
act        (gate₂ σ-gate) x        = sw₂ x
act {₂₊ n} (g ↥) (inj₁ tt)         = inj₁ tt
act {₂₊ n} (g ↥) (inj₂ y)          = inj₂ (act g y)
-- Gen 0 holds only gate₀, and this gate set has no 0-ary gate.  These
-- come LAST: an absurd clause ahead of the computational ones would
-- split the case tree on gate₀ first and stop act from reducing on a
-- variable generator.
act        (gate₀ ())
act        (gate₀ () ↥)

-- The word-valued conjugation action: each generator is sent to a
-- single (permuted) coordinate.
conj : ∀ {n} → Gen n → ⊤ ⊎^ n → Word (⊤ ⊎^ n)
conj g x = [ act g x ]ʷ

-- The permutation induced by a word of generators (composed left to
-- right, matching the fold order of conj ʰ').
actw : ∀ {n} → Word (Gen n) → ⊤ ⊎^ n → ⊤ ⊎^ n
actw [ g ]ʷ   x = act g x
actw ε        x = x
actw (c • c') x = actw c (actw c' x)

------------------------------------------------------------------------
-- The word-valued operators are wmap of the element-valued action

private
  wmap-id : ∀ {A : Set} (w : Word A) → wmap id w ≡ w
  wmap-id [ x ]ʷ   = Eq.refl
  wmap-id ε        = Eq.refl
  wmap-id (w • w') = Eq.cong₂ _•_ (wmap-id w) (wmap-id w')

  wmap-cong : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x)
            → ∀ (w : Word A) → wmap f w ≡ wmap g w
  wmap-cong f≗g [ x ]ʷ   = Eq.cong [_]ʷ (f≗g x)
  wmap-cong f≗g ε        = Eq.refl
  wmap-cong f≗g (w • w') = Eq.cong₂ _•_ (wmap-cong f≗g w) (wmap-cong f≗g w')

-- conj ⁿ' g is wmap of act g.
conjⁿ-wmap : ∀ {n} (g : Gen n) (ns : Word (⊤ ⊎^ n))
           → (conj ⁿ') g ns ≡ wmap (act g) ns
conjⁿ-wmap g [ x ]ʷ   = Eq.refl
conjⁿ-wmap g ε        = Eq.refl
conjⁿ-wmap g (w • w') = Eq.cong₂ _•_ (conjⁿ-wmap g w) (conjⁿ-wmap g w')

-- conj ʰ' c is wmap of actw c.
conjʰ-wmap : ∀ {n} (c : Word (Gen n)) (ns : Word (⊤ ⊎^ n))
           → (conj ʰ') c ns ≡ wmap (actw c) ns
conjʰ-wmap [ g ]ʷ ns = conjⁿ-wmap g ns
conjʰ-wmap ε      ns = Eq.sym (wmap-id ns)
conjʰ-wmap (c • c') ns = begin
  (conj ʰ') c ((conj ʰ') c' ns)   ≡⟨ conjʰ-wmap c ((conj ʰ') c' ns) ⟩
  wmap (actw c) ((conj ʰ') c' ns) ≡⟨ Eq.cong (wmap (actw c)) (conjʰ-wmap c' ns) ⟩
  wmap (actw c) (wmap (actw c') ns) ≡⟨ Eq.sym (wmap-∘ ns) ⟩
  wmap (actw c ∘ actw c') ns      ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Pointwise permutation identities matching the Coxeter relations

-- The bottom transposition is an involution (matches: order σ² = ε).
sw₂-invol : ∀ {n} (x : ⊤ ⊎^ (₂₊ n)) → sw₂ (sw₂ x) ≡ x
sw₂-invol {zero} (inj₁ tt)        = Eq.refl
sw₂-invol {zero} (inj₂ tt)        = Eq.refl
sw₂-invol {₁₊ n} (inj₁ tt)        = Eq.refl
sw₂-invol {₁₊ n} (inj₂ (inj₁ tt)) = Eq.refl
sw₂-invol {₁₊ n} (inj₂ (inj₂ y))  = Eq.refl

-- A doubly-shifted generator commutes with the bottom transposition
-- (matches: comm₂).
comm₂-pt : ∀ {n} (g : Gen n) (x : ⊤ ⊎^ (₂₊ n))
         → act (g ↥ ↥) (sw₂ x) ≡ sw₂ (act (g ↥ ↥) x)
comm₂-pt {₀} (gate₀ ())
comm₂-pt {₁₊ n} g (inj₁ tt)        = Eq.refl
comm₂-pt {₁₊ n} g (inj₂ (inj₁ tt)) = Eq.refl
comm₂-pt {₁₊ n} g (inj₂ (inj₂ y))  = Eq.refl

-- The braid identity on coordinates (matches: yang-baxter).  Writing a
-- for the once-shifted transposition σ↑.
braid : ∀ {n} (x : ⊤ ⊎^ (₃₊ n)) →
  sw₂ (act ((gate₂ σ-gate) ↥) (sw₂ x))
    ≡ act ((gate₂ σ-gate) ↥) (sw₂ (act ((gate₂ σ-gate) ↥) x))
braid {zero} (inj₁ tt)               = Eq.refl
braid {zero} (inj₂ (inj₁ tt))        = Eq.refl
braid {zero} (inj₂ (inj₂ tt))        = Eq.refl
braid {₁₊ n} (inj₁ tt)               = Eq.refl
braid {₁₊ n} (inj₂ (inj₁ tt))        = Eq.refl
braid {₁₊ n} (inj₂ (inj₂ (inj₁ tt))) = Eq.refl
braid {₁₊ n} (inj₂ (inj₂ (inj₂ y)))  = Eq.refl

------------------------------------------------------------------------
-- Shifting the action (matches: cong↑)

actw-↑-inj₁ : ∀ {n} (w : Word (Gen (₁₊ n))) → actw (w ↑) (inj₁ tt) ≡ inj₁ tt
actw-↑-inj₁ [ g ]ʷ   = Eq.refl
actw-↑-inj₁ ε        = Eq.refl
actw-↑-inj₁ (w • w') =
  Eq.trans (Eq.cong (actw (w ↑)) (actw-↑-inj₁ w')) (actw-↑-inj₁ w)

actw-↑-inj₂ : ∀ {n} (w : Word (Gen (₁₊ n))) (y : ⊤ ⊎^ (₁₊ n))
            → actw (w ↑) (inj₂ y) ≡ inj₂ (actw w y)
actw-↑-inj₂ [ g ]ʷ   y = Eq.refl
actw-↑-inj₂ ε        y = Eq.refl
actw-↑-inj₂ (w • w') y =
  Eq.trans (Eq.cong (actw (w ↑)) (actw-↑-inj₂ w' y))
           (actw-↑-inj₂ w (actw w' y))

------------------------------------------------------------------------
-- The action respects the Coxeter relations, pointwise on coordinates

actw-eq : ∀ {n} {c d : Word (Gen n)} → (n VRel, c === d)
        → ∀ x → actw c x ≡ actw d x
actw-eq (srel order)       x = sw₂-invol x
actw-eq (srel yang-baxter) x = braid x
actw-eq (cong↑ {n = zero}  e) x = Eq.refl
actw-eq (cong↑ {n = ₁₊ m} {w = w} {v} e) (inj₁ tt) =
  Eq.trans (actw-↑-inj₁ w) (Eq.sym (actw-↑-inj₁ v))
actw-eq (cong↑ {n = ₁₊ m} {w = w} {v} e) (inj₂ y) =
  Eq.trans (actw-↑-inj₂ w y)
    (Eq.trans (Eq.cong inj₂ (actw-eq e y)) (Eq.sym (actw-↑-inj₂ v y)))
actw-eq (comm₁ () g) x
actw-eq (comm₂ σ-gate g) x = comm₂-pt g x

------------------------------------------------------------------------
-- How a shifted generator's action interacts with the ⊕-embeddings

-- A shifted generator fixes the left (coord-0) factor.
act↥-l : ∀ {n} (g : Gen (₁₊ n)) (u : Word ⊤)
       → (conj ⁿ') (g ↥) ([_]ₗ {B = ⊤ ⊎^ (₁₊ n)} u) ≡ [ u ]ₗ
act↥-l {n} g u = begin
  (conj ⁿ') (g ↥) (wmap inj₁ u)  ≡⟨ conjⁿ-wmap (g ↥) (wmap inj₁ u) ⟩
  wmap (act (g ↥)) (wmap inj₁ u) ≡⟨ Eq.sym (wmap-∘ u) ⟩
  wmap (act (g ↥) ∘ inj₁) u      ≡⟨ wmap-cong (λ { tt → Eq.refl }) u ⟩
  wmap inj₁ u                    ∎
  where open Eq.≡-Reasoning

-- On the right factor, a shifted generator acts by the unshifted action.
act↥-r : ∀ {n} (g : Gen (₁₊ n)) (u : Word (⊤ ⊎^ (₁₊ n)))
       → (conj ⁿ') (g ↥) [ u ]ᵣ ≡ [ (conj ⁿ') g u ]ᵣ
act↥-r {n} g u = begin
  (conj ⁿ') (g ↥) (wmap inj₂ u)    ≡⟨ conjⁿ-wmap (g ↥) (wmap inj₂ u) ⟩
  wmap (act (g ↥)) (wmap inj₂ u)   ≡⟨ Eq.sym (wmap-∘ u) ⟩
  wmap (act (g ↥) ∘ inj₂) u        ≡⟨ wmap-cong (λ y → Eq.refl) u ⟩
  wmap (inj₂ ∘ act g) u            ≡⟨ wmap-∘ u ⟩
  wmap inj₂ (wmap (act g) u)       ≡⟨ Eq.cong (wmap inj₂) (Eq.sym (conjⁿ-wmap g u)) ⟩
  wmap inj₂ ((conj ⁿ') g u)        ∎
  where open Eq.≡-Reasoning

-- The bottom transposition fixes coordinates ≥ 2 (doubly right-embedded).
sw₂-rr : ∀ {n} (u : Word (⊤ ⊎^ (₁₊ n)))
       → (conj ⁿ') (gate₂ σ-gate) ([_]ᵣ {A = ⊤} ([_]ᵣ {A = ⊤} u)) ≡ [ [ u ]ᵣ ]ᵣ
sw₂-rr {n} u = begin
  (conj ⁿ') (gate₂ σ-gate) (wmap inj₂ (wmap inj₂ u))
                                         ≡⟨ conjⁿ-wmap (gate₂ σ-gate) (wmap inj₂ (wmap inj₂ u)) ⟩
  wmap sw₂ (wmap inj₂ (wmap inj₂ u))     ≡⟨ Eq.sym (wmap-∘ (wmap inj₂ u)) ⟩
  wmap (sw₂ ∘ inj₂) (wmap inj₂ u)        ≡⟨ Eq.sym (wmap-∘ u) ⟩
  wmap (sw₂ ∘ inj₂ ∘ inj₂) u             ≡⟨ wmap-cong (λ y → Eq.refl) u ⟩
  wmap (inj₂ ∘ inj₂) u                   ≡⟨ wmap-∘ u ⟩
  wmap inj₂ (wmap inj₂ u)                ∎
  where open Eq.≡-Reasoning

-- The bottom transposition moves a coordinate-0 word to coordinate 1 and
-- back.  Needed once the cyclic order is a variable: the order word is a
-- symbolic power, so these no longer hold by computation.  Two boundary
-- versions each: at the very bottom (⊤ ⊎^ 1) and higher up.
sw₂-l→r₀ : (u : Word ⊤)
         → (conj ⁿ') (gate₂ σ-gate) ([_]ₗ {B = ⊤ ⊎^ 1} u) ≡ [_]ᵣ {A = ⊤} {B = ⊤ ⊎^ 1} u
sw₂-l→r₀ u = begin
  (conj ⁿ') (gate₂ σ-gate) (wmap inj₁ u) ≡⟨ conjⁿ-wmap (gate₂ σ-gate) (wmap inj₁ u) ⟩
  wmap sw₂ (wmap inj₁ u)                 ≡⟨ Eq.sym (wmap-∘ u) ⟩
  wmap (sw₂ ∘ inj₁) u                    ≡⟨ wmap-cong (λ { tt → Eq.refl }) u ⟩
  wmap inj₂ u                            ∎
  where open Eq.≡-Reasoning

sw₂-r→l₀ : (u : Word ⊤)
         → (conj ⁿ') (gate₂ σ-gate) ([_]ᵣ {A = ⊤} {B = ⊤ ⊎^ 1} u) ≡ [_]ₗ {B = ⊤ ⊎^ 1} u
sw₂-r→l₀ u = begin
  (conj ⁿ') (gate₂ σ-gate) (wmap inj₂ u) ≡⟨ conjⁿ-wmap (gate₂ σ-gate) (wmap inj₂ u) ⟩
  wmap sw₂ (wmap inj₂ u)                 ≡⟨ Eq.sym (wmap-∘ u) ⟩
  wmap (sw₂ ∘ inj₂) u                    ≡⟨ wmap-cong (λ { tt → Eq.refl }) u ⟩
  wmap inj₁ u                            ∎
  where open Eq.≡-Reasoning

sw₂-l→rl : ∀ {n} (u : Word ⊤)
         → (conj ⁿ') (gate₂ σ-gate) ([_]ₗ {B = ⊤ ⊎^ (₂₊ n)} u)
           ≡ [ [_]ₗ {B = ⊤ ⊎^ (₁₊ n)} u ]ᵣ
sw₂-l→rl {n} u = begin
  (conj ⁿ') (gate₂ σ-gate) (wmap inj₁ u) ≡⟨ conjⁿ-wmap (gate₂ σ-gate) (wmap inj₁ u) ⟩
  wmap sw₂ (wmap inj₁ u)                 ≡⟨ Eq.sym (wmap-∘ u) ⟩
  wmap (sw₂ ∘ inj₁) u                    ≡⟨ wmap-cong (λ { tt → Eq.refl }) u ⟩
  wmap (inj₂ ∘ inj₁) u                   ≡⟨ wmap-∘ u ⟩
  wmap inj₂ (wmap inj₁ u)                ∎
  where open Eq.≡-Reasoning

sw₂-rl→l : ∀ {n} (u : Word ⊤)
         → (conj ⁿ') (gate₂ σ-gate) [ [_]ₗ {B = ⊤ ⊎^ (₁₊ n)} u ]ᵣ
           ≡ [_]ₗ {B = ⊤ ⊎^ (₂₊ n)} u
sw₂-rl→l {n} u = begin
  (conj ⁿ') (gate₂ σ-gate) (wmap inj₂ (wmap inj₁ u)) ≡⟨ conjⁿ-wmap (gate₂ σ-gate) _ ⟩
  wmap sw₂ (wmap inj₂ (wmap inj₁ u))     ≡⟨ Eq.sym (wmap-∘ (wmap inj₁ u)) ⟩
  wmap (sw₂ ∘ inj₂) (wmap inj₁ u)        ≡⟨ Eq.sym (wmap-∘ u) ⟩
  wmap (sw₂ ∘ inj₂ ∘ inj₁) u             ≡⟨ wmap-cong (λ { tt → Eq.refl }) u ⟩
  wmap inj₁ u                            ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The action respects the base-product (ℤ/4ℤ)ⁿ relations
--
-- Since conj ⁿ' c = wmap (act c) and act c permutes coordinates, an
-- axiom at coordinate i is carried to the same axiom at coordinate
-- act c i.  The structure mirrors the old inductive-Sₙ proof, with the
-- bottom transposition gate₂ σ-gate playing the role of swap and the
-- wire shift ↥ that of ₛ.

conj-hypn : ∀ {n m} (c : Gen n) {w v} → (Γ₀ m ⊕^ n) w v
          → PB._≈_ (Γ₀ m ⊕^ n) ((conj ⁿ') c w) ((conj ⁿ') c v)
-- The bottom transposition swaps coordinates 0 and 1.
conj-hypn {₁} (gate₀ () ↥)
conj-hypn {₂₊ zero}   {m} (gate₂ σ-gate) (left Cyc.order)
  rewrite sw₂-l→r₀ (Cyc.T ^' suc m)                              = PB._≈_.axiom (right Cyc.order)
conj-hypn {₂₊ (₁₊ n)} {m} (gate₂ σ-gate) (left Cyc.order)
  rewrite sw₂-l→rl {n} (Cyc.T ^' suc m)                          = PB._≈_.axiom (right (left Cyc.order))
conj-hypn {₂₊ zero}   {m} (gate₂ σ-gate) (right Cyc.order)
  rewrite sw₂-r→l₀ (Cyc.T ^' suc m)                              = PB._≈_.axiom (left Cyc.order)
conj-hypn {₂₊ (₁₊ n)} {m} (gate₂ σ-gate) (right (left Cyc.order))
  rewrite sw₂-rl→l {n} (Cyc.T ^' suc m)                          = PB._≈_.axiom (left Cyc.order)
conj-hypn {₂₊ (₁₊ n)}  (gate₂ σ-gate) (right (right {u} {v} x))
  rewrite sw₂-rr {n} u | sw₂-rr {n} v                            = PB._≈_.axiom (right (right x))
conj-hypn {₂₊ (₁₊ n)}  (gate₂ σ-gate) (right (mid (comm a b)))  = PB._≈_.axiom (mid (comm tt (inj₂ b)))
conj-hypn {₂₊ zero}    (gate₂ σ-gate) (mid (comm a b))          = PB._≈_.sym (PB._≈_.axiom (mid (comm tt tt)))
conj-hypn {₂₊ (₁₊ n)}  (gate₂ σ-gate) (mid (comm tt (inj₁ x)))  = PB._≈_.sym (PB._≈_.axiom (mid (comm tt (inj₁ tt))))
conj-hypn {₂₊ (₁₊ n)}  (gate₂ σ-gate) (mid (comm tt (inj₂ y)))  = PB._≈_.axiom (right (mid (comm tt y)))
-- A shifted generator fixes coordinate 0 and acts on the rest.
conj-hypn {₂₊ n} {m} (g ↥) (left Cyc.order)
  rewrite act↥-l g (Cyc.T ^' suc m)       = PB._≈_.axiom (left Cyc.order)
conj-hypn {₂₊ n} {m} (g ↥) (right {u} {v} x)
  rewrite act↥-r g u | act↥-r g v         = rights (conj-hypn g x)
  where open LeftRightCongruence (Γ₀ m) (Γ₀ m ⊕^ ₁₊ n) CommRel
conj-hypn {₂₊ n} (g ↥) (mid (comm a b))   = PB._≈_.axiom (mid (comm tt (act g b)))

------------------------------------------------------------------------
-- The action respects the Coxeter relations (word-level)
--
-- conj ʰ' c = wmap (actw c), so pointwise coordinate-equality (actw-eq)
-- lifts to a propositional equality of words, hence to ≈.

conj-hyph : ∀ {n m} {c d : Word (Gen n)} (ns : Word (⊤ ⊎^ n))
          → (n VRel, c === d)
          → PB._≈_ (Γ₀ m ⊕^ n) ((conj ʰ') c ns) ((conj ʰ') d ns)
conj-hyph {n} {m} {c} {d} ns rel =
  PB.refl' (Γ₀ m ⊕^ n)
    (Eq.trans (conjʰ-wmap c ns)
     (Eq.trans (wmap-cong (actw-eq rel) ns)
               (Eq.sym (conjʰ-wmap d ns))))

------------------------------------------------------------------------
-- The wreath-product presentation
--
-- Feed the n-fold (ℤ/4ℤ)ⁿ presentation and the Coxeter Sₙ presentation,
-- together with the coordinate action, into the semi-direct-product
-- construction: Γ₀ ⊕^ n ⋊ Sₙ presents (ℤ/4ℤ)ⁿ ⋊ Sₙ = ℤ/4ℤ ≀ Sₙ.

module Wreath (n m : ℕ) where

  private
    module ND⊗ = NDP.Presentation (Γ₀ m) (Cn-group (suc m)) (CyP.presentation {m})
    module SDP = SDP' (Γ₀ m ⊕^ n) (n VRel,_===_) (conj {n})
    module SDPP =
      SDP.Presentation (conj-hyph {n} {m}) (conj-hypn {n} {m})
        (ND⊗.⊗-group n) (Permutation′-group n)
        (ND⊗.presentation n) (ST.presentation {n})

  -- The semantic wreath-product group (ℤ/(suc m)ℤ)ⁿ ⋊ Sₙ.
  wreath-group : Group 0ℓ 0ℓ
  wreath-group = SDPP.G1⋊G2

  -- The wreath-product relation itself.  Named, because Γ₀ is private
  -- and clients cannot otherwise spell it.
  pres : WRel ((⊤ ⊎^ n) ⊎ Gen n)
  pres = (Γ₀ m ⊕^ n) ⋄ (n VRel,_===_) ⋄ ConjRelʷ (conj {n})

  -- Γ₀ ⊕^ n ⋊ (n VRel) ⋆ conj presents it.
  presentation : pres IsPresentationOf wreath-group
  presentation = SDPP.dpres

  ------------------------------------------------------------------
  -- The normal form
  --
  -- Both factors have one — the n-fold product of ℤ/(suc m)ℤ from
  -- NDirectProduct, and Sₙ's coset tower from Symmetric.Normalization —
  -- and the semi-direct-product construction transfers them to the
  -- wreath product, on exactly the two hypotheses the presentation
  -- already needed.  So this costs no new proof obligation.
  --
  -- Why it is worth having alongside `presentation`: the two say
  -- different things.  `presentation` is semantic — it identifies the
  -- presented group with wreath-group — whereas a normal form is
  -- syntactic, and it is what the amalgamation machinery consumes
  -- (Presentation.Construct.Properties.Amalgamation's AmalDataNF).
  -- Without it this module could not have replaced the hand-rolled
  -- wreath product that Examples.Amalgamations.U33Di used to import,
  -- which carried both.

  private
    module NFP₀  = SDP.NFP  (conj-hyph {n} {m}) (conj-hypn {n} {m})
    module NFP'₀ = SDP.NFP' (conj-hyph {n} {m}) (conj-hypn {n} {m})

  -- Carrier: the n-fold product of ℤ/(suc m)ℤ normal forms, paired
  -- with Sₙ's.
  SnD-NF : Set
  SnD-NF = NDP.⊗-carrier (Γ₀ m) n (Cyc.NF (suc m)) × SN.NF n

  nfp : NormalFormInjective pres SnD-NF
  nfp = NFP₀.nfp (NDP.nfp (Γ₀ m) n (Cyc.nfp (suc m))) (SN.nfp n)

  -- Like nfp, but also carrying the section.
  nfp' : NormalForm pres SnD-NF
  nfp' = NFP'₀.nfp' (NDP.nfp' (Γ₀ m) n (Cyc.nfp' (suc m))) (SN.nfp'-t n)
