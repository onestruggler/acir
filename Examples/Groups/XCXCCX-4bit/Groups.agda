------------------------------------------------------------------------
-- Presentations of groups
--
-- The groups of circuits: G₁ ≅ Sym(2), G₂ ≅ Sym(4), G₃ ≅ Sym(8) and
-- G₄ ≅ Alt(16)
--
-- The paper's Propositions B.1–B.3 and Corollary 5.2: on k ≤ 3 wires
-- the theory presents the symmetric group of the 2ᵏ states, and on
-- four wires the alternating group of the sixteen states.  Each is
-- ByPerm at the numbering of the states that the completeness proof
-- used: a circuit is read as a Coxeter word (Width2/Width3's
-- translation; on four wires, the symbols of EvenRS 16 that Four
-- translates it to, as words of S₁₆), every permutation is the
-- circuit of a Coxeter word (Symmetric's Surjectivity; on four wires
-- an even word, rewritten into symbols by EvenRS's rs and realised by
-- Four's R), and every letter is an involution.  Every four-wire
-- circuit is even: its Coxeter word is a word of symbols, each of
-- two letters.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Groups where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_ ; _∧_)
open import Data.Bool.Properties using (not-involutive ; xor-assoc)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Permutation using (Permutation′ ; _⟨$⟩ʳ_)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; _ᵗ)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (Grouplike)

import Examples.Groups.Symmetric.Interpretation as SymI
import Examples.Groups.Symmetric.Semantics as SymSem
import Examples.Groups.Symmetric.Syntactics as Sym
open import Examples.Groups.Alternating.Parity using (parity)
open import Examples.Groups.Alternating.Semantics using (Alt-group)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (Bits ; ⟦_⟧ ; ⟦_⟧ᵍ ; _≐_ ; sound)
open import Examples.Groups.XCXCCX-4bit.Placed using (ι* ; ι*-sem)
open import Examples.Groups.XCXCCX-4bit.ToPlaced using (pg ; pg-ok)
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox
import Examples.Groups.XCXCCX-4bit.ByCoxeter as ByCoxeter
import Examples.Groups.XCXCCX-4bit.EvenRS as ERS
import Examples.Groups.XCXCCX-4bit.Width1 as W1
import Examples.Groups.XCXCCX-4bit.Width2 as W2
import Examples.Groups.XCXCCX-4bit.Width3 as W3
import Examples.Groups.XCXCCX-4bit.Four as Four
open import Examples.Groups.XCXCCX-4bit.KFaithful using (faithful₃)
open import Examples.Groups.XCXCCX-4bit.Completeness using (complete₄)
open import Examples.Groups.XCXCCX-4bit.ByPerm using (module ByPerm)

------------------------------------------------------------------------
-- Every letter is an involution

inv-sem : ∀ {n} (g : Gen n) (x : Bits n) → ⟦ g ⟧ᵍ (⟦ g ⟧ᵍ x) ≡ x
inv-sem (gate₀ ⌈ () ⌉)       x
inv-sem (gate₁ ⌈ X-gate ⌉)   (a ∷ x)         = Eq.cong (_∷ x) (not-involutive a)
inv-sem (gate₂ ⌈ CX-gate ⌉)  (a ∷ b ∷ x)     = Eq.cong (_∷ b ∷ x) (xx a b)
  where
  xx : ∀ a b → (a xor b) xor b ≡ a
  xx false false = Eq.refl
  xx false true  = Eq.refl
  xx true  false = Eq.refl
  xx true  true  = Eq.refl
inv-sem (gate₂ swap)         (a ∷ b ∷ x)     = Eq.refl
inv-sem (gate₃ ⌈ CCX-gate ⌉) (a ∷ b ∷ c ∷ x) = Eq.cong (_∷ b ∷ c ∷ x) (xx a (b ∧ c))
  where
  xx : ∀ a b → (a xor b) xor b ≡ a
  xx false false = Eq.refl
  xx false true  = Eq.refl
  xx true  false = Eq.refl
  xx true  true  = Eq.refl
inv-sem (g ↥)                (a ∷ x)         = Eq.cong (a ∷_) (inv-sem g x)

grouplike : ∀ {k} → (∀ {u v : Circuit k} → ⟦ u ⟧ ≐ ⟦ v ⟧ → k ⊢ u ≈ v) → Grouplike (k VRel,_===_)
grouplike complete g = [ g ]ʷ , complete (inv-sem g)

------------------------------------------------------------------------
-- One wire: Sym(2)

private
  module One where
    enc : Fin 2 → Bits 1
    enc zero       = false ∷ []
    enc (suc zero) = true ∷ []

    dec : Bits 1 → Fin 2
    dec (false ∷ []) = zero
    dec (true ∷ [])  = suc zero

    dec-enc : ∀ i → dec (enc i) ≡ i
    dec-enc zero       = Eq.refl
    dec-enc (suc zero) = Eq.refl

    enc-dec : ∀ x → enc (dec x) ≡ x
    enc-dec (false ∷ []) = Eq.refl
    enc-dec (true ∷ [])  = Eq.refl

    s₀ : Cox.SG 2
    s₀ = Sym.gate₂ Sym.σ-gate

    trB : Bool → Word (Cox.SG 2)
    trB false = ε
    trB true  = [ s₀ ]ʷ

    tr : Circuit 1 → Word (Cox.SG 2)
    tr u = trB (W1.par u)

    by : (b : Bool) (i : Fin 2) → ⟦ W1.nf b ⟧ (enc i) ≡ enc (SymI.⟦ trB b ⟧ ⟨$⟩ʳ i)
    by false zero       = Eq.refl
    by false (suc zero) = Eq.refl
    by true  zero       = Eq.refl
    by true  (suc zero) = Eq.refl

    at : ∀ u i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ tr u ⟧ ⟨$⟩ʳ i)
    at u i = Eq.trans (sound (W1.nf-ok u) (enc i)) (by (W1.par u) i)

    -- A Coxeter word of S₂ as a circuit: X for its one letter.
    circ : Word (Cox.SG 2) → Circuit 1
    circ [ _ ]ʷ   = X
    circ ε       = ε
    circ (u • v) = circ u • circ v

    circ-at : ∀ w i → ⟦ circ w ⟧ (enc i) ≡ enc (SymI.⟦ w ⟧ ⟨$⟩ʳ i)
    circ-at [ Sym.gate₀ () ]ʷ i
    circ-at [ Sym.gate₁ () ]ʷ i
    circ-at [ Sym.gate₂ Sym.σ-gate ]ʷ zero       = Eq.refl
    circ-at [ Sym.gate₂ Sym.σ-gate ]ʷ (suc zero) = Eq.refl
    circ-at [ Sym.gate₀ () Sym.↥ ]ʷ i
    circ-at [ Sym.gate₁ () Sym.↥ ]ʷ i
    circ-at [ Sym.gate₀ () Sym.↥ Sym.↥ ]ʷ i
    circ-at ε       i = Eq.refl
    circ-at (u • v) i =
      Eq.trans (Eq.cong ⟦ circ v ⟧ (circ-at u i)) (circ-at v (SymI.⟦ u ⟧ ⟨$⟩ʳ i))

    realise : (w : Word (Cox.SG 2)) → Σ (Circuit 1) (λ u → ∀ i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ w ⟧ ⟨$⟩ʳ i))
    realise w = circ w , circ-at w

    open ByPerm 1 2 enc dec dec-enc enc-dec tr at W1.complete₁ (grouplike W1.complete₁) public
    open Full realise public

-- Proposition B.1: one-wire circuits present Sym(2).
presentation₁ : (1 VRel,_===_) IsPresentationOf (SymSem.Permutation′-group 2)
presentation₁ = One.presentation

------------------------------------------------------------------------
-- Two and three wires: Sym(4), Sym(8)

private
  module Two where
    open W2 using (enc ; dec ; dec-enc)
    open ByCoxeter.Via 2 4 W2.T W2.cox enc dec dec-enc W2.T-act W2.tw W2.tw-ok
      using (Pc-sem ; translate ; translate-ok ; complete)

    enc-dec : ∀ x → enc (dec x) ≡ x
    enc-dec (false ∷ false ∷ []) = Eq.refl
    enc-dec (true  ∷ false ∷ []) = Eq.refl
    enc-dec (true  ∷ true  ∷ []) = Eq.refl
    enc-dec (false ∷ true  ∷ []) = Eq.refl

    at : ∀ u i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ translate u ⟧ ⟨$⟩ʳ i)
    at u i = Eq.trans (sound (translate-ok u) (enc i)) (Pc-sem (translate u) i)

    realise : (w : Word (Cox.SG 4)) → Σ (Circuit 2) (λ u → ∀ i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ w ⟧ ⟨$⟩ʳ i))
    realise w = Cox.Circuits.Pc 4 W2.T 0 w , Pc-sem w

    open ByPerm 2 4 enc dec dec-enc enc-dec translate at complete (grouplike complete) public
    open Full realise public

  module Three where
    open W3 using (enc ; dec ; dec-enc)
    open ByCoxeter.Via 3 8 W3.T W3.cox enc dec dec-enc W3.T-act W3.tw W3.tw-ok
      using (Pc-sem ; translate ; translate-ok ; complete)

    enc-dec : ∀ x → enc (dec x) ≡ x
    enc-dec (false ∷ false ∷ false ∷ []) = Eq.refl
    enc-dec (true  ∷ false ∷ false ∷ []) = Eq.refl
    enc-dec (true  ∷ true  ∷ false ∷ []) = Eq.refl
    enc-dec (false ∷ true  ∷ false ∷ []) = Eq.refl
    enc-dec (false ∷ true  ∷ true  ∷ []) = Eq.refl
    enc-dec (true  ∷ true  ∷ true  ∷ []) = Eq.refl
    enc-dec (true  ∷ false ∷ true  ∷ []) = Eq.refl
    enc-dec (false ∷ false ∷ true  ∷ []) = Eq.refl

    at : ∀ u i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ translate u ⟧ ⟨$⟩ʳ i)
    at u i = Eq.trans (sound (translate-ok u) (enc i)) (Pc-sem (translate u) i)

    realise : (w : Word (Cox.SG 8)) → Σ (Circuit 3) (λ u → ∀ i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ w ⟧ ⟨$⟩ʳ i))
    realise w = Cox.Circuits.Pc 8 W3.T 0 w , Pc-sem w

    open ByPerm 3 8 enc dec dec-enc enc-dec translate at complete (grouplike complete) public
    open Full realise public

-- Proposition B.2: two-wire circuits present Sym(4).
presentation₂ : (2 VRel,_===_) IsPresentationOf (SymSem.Permutation′-group 4)
presentation₂ = Two.presentation

-- Proposition B.3: three-wire circuits present Sym(8).
presentation₃ : (3 VRel,_===_) IsPresentationOf (SymSem.Permutation′-group 8)
presentation₃ = Three.presentation

------------------------------------------------------------------------
-- Four wires: Alt(16)

private
  module Fourw where
    module F = Four faithful₃
    open F using (enc ; dec ; dec-enc ; enc-dec)
    open F.RL using (R* ; R*-act)
    open F.RL.Complete F.R-rel F.tw F.tw-ok using (translate ; translate-ok)
    open ERS 16 using (Sch ; γ ; f ; h ; rs ; rs-sem)

    -- A circuit as the Coxeter word of its symbols.
    tr : Circuit 4 → Word (Cox.SG 16)
    tr u = (f ʷ) (translate (pg u))

    at : ∀ u i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ tr u ⟧ ⟨$⟩ʳ i)
    at u i =
      Eq.trans (sound (PB.trans (pg-ok u) (translate-ok (pg u))) (enc i))
        (Eq.trans (ι*-sem (R* (translate (pg u))) (enc i)) (R*-act (translate (pg u)) i))

    -- The Coxeter word of a word of symbols has even length.
    parity-f : (w : Word Sch) → parity ((f ʷ) w) ≡ false
    parity-f [ γ false d p q ]ʷ = Eq.refl
    parity-f [ γ true  d p q ]ʷ = Eq.refl
    parity-f ε                 = Eq.refl
    parity-f (u • v)           = Eq.cong₂ _xor_ (parity-f u) (parity-f v)

    open ByPerm 4 16 enc dec dec-enc enc-dec tr at complete₄ (grouplike complete₄) public

    even : ∀ u → parity (tr u) ≡ false
    even u = parity-f (translate (pg u))

    -- The coset rs reaches is the parity of the word.
    rs-parity : (c : Bool) (w : Word (Cox.SG 16)) → proj₂ (rs c w) ≡ c xor parity w
    rs-parity false [ g ]ʷ = Eq.refl
    rs-parity true  [ g ]ʷ = Eq.refl
    rs-parity false ε      = Eq.refl
    rs-parity true  ε      = Eq.refl
    rs-parity c (u • v) with (h ᵗ) c u | rs-parity c u
    ... | (u′ , c′) | e with (h ᵗ) c′ v | rs-parity c′ v
    ...   | (v′ , c″) | e′ =
      Eq.trans e′ (Eq.trans (Eq.cong (_xor parity v) e) (xor-assoc c (parity u) (parity v)))

    -- An even word is realised: rewritten into symbols.
    realise : (w : Word (Cox.SG 16)) → parity w ≡ false →
              Σ (Circuit 4) (λ u → ∀ i → ⟦ u ⟧ (enc i) ≡ enc (SymI.⟦ w ⟧ ⟨$⟩ʳ i))
    realise w pw = ι* (R* (proj₁ (rs false w))) , λ i →
      Eq.trans (ι*-sem (R* (proj₁ (rs false w))) (enc i))
        (Eq.trans (R*-act (proj₁ (rs false w)) i)
          (Eq.cong enc (rs-sem w (Eq.trans (rs-parity false w) (Eq.cong (false xor_) pw)) i)))

    open Even even realise public

-- Corollary 5.2: four-wire circuits present Alt(16).
presentation₄ : (4 VRel,_===_) IsPresentationOf (Alt-group 16)
presentation₄ = Fourw.presentation
