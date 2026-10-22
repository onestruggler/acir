------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows on five wires, by tables of letters
--
-- A derivation on five wires (scratchpad/five/lower5.py) rewrites a run
-- of letters that leaves a wire i idle by one with the same operator:
-- Lemma 5.1 with completeness on four wires.  Two forms:
--
--  * `lwin`: every letter is spelled off wire i, so the run is its
--    placement by `Windows.ins` (Windows.win).  A table gives, for each
--    letter that is, the four-wire word u with ⟪ g ⟫ ≡ insʷ i u.
--  * `pwin`: every letter avoids wire i semantically, but some are
--    spelled across it (a gate on wires 0 and 4 is conjugated by the
--    swaps of the wires between).  A table gives for each letter a word
--    u with ⟪ g ⟫ ≈ place i u — by `Windows.place-ins` for a letter
--    spelled off i, by a respelling lemma for the others — and `place-•`
--    puts them together.
--
-- A step is then `lwin c₄ xs ys tt tt Eq.refl`, c₄ the swap rules and
-- completeness on four wires (Windows.Base, an argument of the window
-- libraries): the two `tt` say that the table has every letter, and
-- `Eq.refl` is the one evaluation of the two four-wire words
-- (SemanticSteps.Same).  The module is generic in
-- the letters and in the idle wire; Five.Windows instantiates it.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Notations using (₁₊)

module Examples.Groups.Clifford+CS.Five.Win
  (i r : ℕ) (Mac : Set) (⟪_⟫ : Mac → Circuit (₁₊ (i +ℕ r))) where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; T)
open import Data.List using (List ; [] ; _∷_)
open import Data.Maybe using (Maybe ; just ; nothing ; is-just)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics using (_↑)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Complete ; Same ; same-sem)
open import Examples.Groups.Clifford+CS.SwapFacts using (SwapFacts)
open import Examples.Groups.Clifford+CS.Windows using (insʷ ; avoidsʷ ; Base ; win)
  renaming (module Laws to WinLaws)
open import Examples.Groups.Clifford+CS.Place using (place ; lemma-5-1)
  renaming (module Laws to PlaceLaws)
open import Examples.Groups.Clifford+CS.Five.Rules using (_XVRel,_===_ ; _⊢ₓ_≈_ ; embed)
open import Examples.Groups.Clifford+CS.Five.Lines (₁₊ (i +ℕ r)) Mac ⟪_⟫ using (⟪_⟫ʷ)

private
  W : ℕ
  W = ₁₊ (i +ℕ r)
  module PX = PB (_XVRel,_===_ W)

------------------------------------------------------------------------
-- Tables

data Ents (F : Mac → Set) : List Mac → Set where
  []  : Ents F []
  _∷_ : ∀ {x xs} → F x → Ents F xs → Ents F (x ∷ xs)

okᵗ : {F : Mac → Set} → ((g : Mac) → Maybe (F g)) → List Mac → Bool
okᵗ t []       = true
okᵗ t (x ∷ xs) = is-just (t x) ∧ okᵗ t xs

get : {F : Mac → Set} (t : (g : Mac) → Maybe (F g)) (xs : List Mac) → T (okᵗ t xs) → Ents F xs
get t []       _ = []
get {F} t (x ∷ xs) p = get₁ (t x) p
  where
  get₁ : (m : Maybe (F x)) → T (is-just m ∧ okᵗ t xs) → Ents F (x ∷ xs)
  get₁ (just e) q = e ∷ get t xs q
  get₁ nothing  ()

private
  ∧-intro : ∀ {a b : Bool} → T a → T b → T (a ∧ b)
  ∧-intro {true} _ q = q

------------------------------------------------------------------------
-- Literal windows

record Lit (g : Mac) : Set where
  constructor lit
  field
    u  : Circuit (i +ℕ r)
    av : T (avoidsʷ i u)
    sp : ⟪ g ⟫ ≡ insʷ i u

catL : ∀ {xs} → Ents Lit xs → Circuit (i +ℕ r)
catL []             = ε
catL (e ∷ [])       = Lit.u e
catL (e ∷ (f ∷ es)) = Lit.u e • catL (f ∷ es)

private
  spL : ∀ {xs} (es : Ents Lit xs) → ⟪ xs ⟫ʷ ≡ insʷ i (catL es)
  spL []             = Eq.refl
  spL (e ∷ [])       = Lit.sp e
  spL (e ∷ (f ∷ es)) = Eq.cong₂ _•_ (Lit.sp e) (spL (f ∷ es))

  avL : ∀ {xs} (es : Ents Lit xs) → T (avoidsʷ i (catL es))
  avL []             = tt
  avL (e ∷ [])       = Lit.av e
  avL (e ∷ (f ∷ es)) = ∧-intro (Lit.av e) (avL (f ∷ es))

lwin : (t : (g : Mac) → Maybe (Lit g)) → Base (i +ℕ r) →
       (xs ys : List Mac) (px : T (okᵗ t xs)) (py : T (okᵗ t ys)) →
       Same (catL (get t xs px)) (catL (get t ys py)) →
       W ⊢ₓ ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
lwin t c₄ xs ys px py e =
  Eq.subst₂ (W ⊢ₓ_≈_) (Eq.sym (spL ex)) (Eq.sym (spL ey))
    (embed (win i r c₄ (catL ex) (catL ey) (avL ex) (avL ey) e))
  where
  ex = get t xs px
  ey = get t ys py

------------------------------------------------------------------------
-- Placed windows

-- A letter spelled off wire i (placed by Windows.place-ins, which pwin
-- applies: it uses the swap rules), or a word u with ⟪ g ⟫ ≈ place i u.
data Resp (g : Mac) : Set where
  fromLit : Lit g → Resp g
  resp    : (u : Circuit (i +ℕ r)) → W ⊢ₓ ⟪ g ⟫ ≈ place i u → Resp g

uR : ∀ {g} → Resp g → Circuit (i +ℕ r)
uR (fromLit l) = Lit.u l
uR (resp u _)  = u

catR : ∀ {xs} → Ents Resp xs → Circuit (i +ℕ r)
catR []             = ε
catR (e ∷ [])       = uR e
catR (e ∷ (f ∷ es)) = uR e • catR (f ∷ es)

private
  module _ (sf : SwapFacts) where
    open PlaceLaws sf using (place-• ; cyc⁻¹-cyc)
    open WinLaws sf using (place-ins)

    eqR₁ : ∀ {g} (e : Resp g) → W ⊢ₓ ⟪ g ⟫ ≈ place i (uR e)
    eqR₁ (fromLit (lit u av sp)) =
      Eq.subst (λ w → W ⊢ₓ w ≈ place i u) (Eq.sym sp) (PX.sym (embed (place-ins i r u av)))
    eqR₁ (resp u eq) = eq

    place-ε : W ⊢ₓ ε ≈ place i ε
    place-ε = PX.sym (PX.trans (PX.cong PX.refl PX.left-unit) (embed (cyc⁻¹-cyc i)))

    eqR : ∀ {xs} (es : Ents Resp xs) → W ⊢ₓ ⟪ xs ⟫ʷ ≈ place i (catR es)
    eqR []             = place-ε
    eqR (e ∷ [])       = eqR₁ e
    eqR (e ∷ (f ∷ es)) =
      PX.trans (PX.cong (eqR₁ e) (eqR (f ∷ es)))
               (PX.sym (embed (place-• i (uR e) (catR (f ∷ es)))))

pwin : (t : (g : Mac) → Maybe (Resp g)) → Base (i +ℕ r) →
       (xs ys : List Mac) (px : T (okᵗ t xs)) (py : T (okᵗ t ys)) →
       Same (catR (get t xs px)) (catR (get t ys py)) →
       W ⊢ₓ ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
pwin t b xs ys px py e =
  PX.trans (eqR (Base.facts b) ex)
    (PX.trans (embed (lemma-5-1 i (Base.complete b) (same-sem (catR ex) (catR ey) e)))
              (PX.sym (eqR (Base.facts b) ey)))
  where
  ex = get t xs px
  ey = get t ys py
