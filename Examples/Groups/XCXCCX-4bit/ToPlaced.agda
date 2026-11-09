------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire circuits as words of placed letters
--
-- Every letter of a four-wire circuit is a placed letter (Placed.PG):
-- X, CX and CCX shifted up are the letters on consecutive wires
-- (Placed.ιX₀ …), and the swap of the wires k and k + 1 is three CNOTs
-- by rule (3), the middle one with its control and target exchanged.
-- So every circuit is the circuit of its word of placed letters
-- (pg-ok), and a statement about words of placed letters is one about
-- circuits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.ToPlaced where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Placed
import Examples.Independence.Reasoning Gate as R
open R.Theory _SRel,_===_ using (ax-at ; lift)

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)
open Cx.Complete cox using (Fr-conj)

------------------------------------------------------------------------
-- The CNOTs pointing up

ιCX₀₁ : 4 ⊢ ι (CXᵖ ₀ ₁) ≈ CX↓
ιCX₀₁ = ι-CX ₀ ₁ [ s₀ ]ʷ Eq.refl Eq.refl

ιCX₁₂ : 4 ⊢ ι (CXᵖ ₁ ₂) ≈ CX↓ ↑
ιCX₁₂ = trans (ι-CX ₁ ₂ ([ s₁ ]ʷ • Fc) Eq.refl Eq.refl)
          (trans (sym (Fr-conj CX [ s₁ ]ʷ Fc)) (cong refl (cong (sym CX↑₁) refl)))

ιCX₂₃ : 4 ⊢ ι (CXᵖ ₂ ₃) ≈ CX↓ ↑ ↑
ιCX₂₃ = trans (ι-CX ₂ ₃ ([ s₂ ]ʷ • (Fc • Fc)) Eq.refl Eq.refl)
          (trans (sym (Fr-conj CX [ s₂ ]ʷ (Fc • Fc))) (cong refl (cong (sym CX↑₂) refl)))

------------------------------------------------------------------------
-- Letters

-- The placed letters of a letter; the swap of the wires k + 1, k is
-- three CNOTs (rule (3)).
pgl : Gen 4 → List PG
pgl (gate₀ ⌈ () ⌉)
pgl (gate₁ ⌈ X-gate ⌉)          = Xᵖ ₀ ∷ []
pgl (gate₂ ⌈ CX-gate ⌉)         = CXᵖ ₁ ₀ ∷ []
pgl (gate₂ swap)                = CXᵖ ₁ ₀ ∷ CXᵖ ₀ ₁ ∷ CXᵖ ₁ ₀ ∷ []
pgl (gate₃ ⌈ CCX-gate ⌉)        = CCXᵖ ₁ ₂ ₀ ∷ []
pgl (gate₀ ⌈ () ⌉ ↥)
pgl (gate₁ ⌈ X-gate ⌉ ↥)        = Xᵖ ₁ ∷ []
pgl (gate₂ ⌈ CX-gate ⌉ ↥)       = CXᵖ ₂ ₁ ∷ []
pgl (gate₂ swap ↥)              = CXᵖ ₂ ₁ ∷ CXᵖ ₁ ₂ ∷ CXᵖ ₂ ₁ ∷ []
pgl (gate₃ ⌈ CCX-gate ⌉ ↥)      = CCXᵖ ₂ ₃ ₁ ∷ []
pgl (gate₀ ⌈ () ⌉ ↥ ↥)
pgl (gate₁ ⌈ X-gate ⌉ ↥ ↥)      = Xᵖ ₂ ∷ []
pgl (gate₂ ⌈ CX-gate ⌉ ↥ ↥)     = CXᵖ ₃ ₂ ∷ []
pgl (gate₂ swap ↥ ↥)            = CXᵖ ₃ ₂ ∷ CXᵖ ₂ ₃ ∷ CXᵖ ₃ ₂ ∷ []
pgl (gate₀ ⌈ () ⌉ ↥ ↥ ↥)
pgl (gate₁ ⌈ X-gate ⌉ ↥ ↥ ↥)    = Xᵖ ₃ ∷ []
pgl (gate₀ ⌈ () ⌉ ↥ ↥ ↥ ↥)

private
  one : (g : PG) {w : Circuit 4} → 4 ⊢ ι g ≈ w → 4 ⊢ w ≈ ι* (g ∷ [])
  one g e = trans (sym right-unit) (cong (sym e) refl)

  three : (a b : PG) {u v : Circuit 4} → 4 ⊢ ι a ≈ u → 4 ⊢ ι b ≈ v →
          4 ⊢ u • v • u ≈ ι* (a ∷ b ∷ a ∷ [])
  three a b ea eb = cong (sym ea) (cong (sym eb) (one a ea))

pgl-ok : (g : Gen 4) → 4 ⊢ [ g ]ʷ ≈ ι* (pgl g)
pgl-ok (gate₀ ⌈ () ⌉)
pgl-ok (gate₁ ⌈ X-gate ⌉)       = one (Xᵖ ₀) ιX₀
pgl-ok (gate₂ ⌈ CX-gate ⌉)      = one (CXᵖ ₁ ₀) ιCX₁₀
pgl-ok (gate₂ swap)             = trans (sym (ax-at r3 2)) (three (CXᵖ ₁ ₀) (CXᵖ ₀ ₁) ιCX₁₀ ιCX₀₁)
pgl-ok (gate₃ ⌈ CCX-gate ⌉)     = one (CCXᵖ ₁ ₂ ₀) ιCCX₁₂₀
pgl-ok (gate₀ ⌈ () ⌉ ↥)
pgl-ok (gate₁ ⌈ X-gate ⌉ ↥)     = one (Xᵖ ₁) ιX₁
pgl-ok (gate₂ ⌈ CX-gate ⌉ ↥)    = one (CXᵖ ₂ ₁) ιCX₂₁
pgl-ok (gate₂ swap ↥)           = trans (sym (lift (ax-at r3 1))) (three (CXᵖ ₂ ₁) (CXᵖ ₁ ₂) ιCX₂₁ ιCX₁₂)
pgl-ok (gate₃ ⌈ CCX-gate ⌉ ↥)   = one (CCXᵖ ₂ ₃ ₁) ιCCX₂₃₁
pgl-ok (gate₀ ⌈ () ⌉ ↥ ↥)
pgl-ok (gate₁ ⌈ X-gate ⌉ ↥ ↥)   = one (Xᵖ ₂) ιX₂
pgl-ok (gate₂ ⌈ CX-gate ⌉ ↥ ↥)  = one (CXᵖ ₃ ₂) ιCX₃₂
pgl-ok (gate₂ swap ↥ ↥)         = trans (sym (lift (lift (ax-at r3 0)))) (three (CXᵖ ₃ ₂) (CXᵖ ₂ ₃) ιCX₃₂ ιCX₂₃)
pgl-ok (gate₀ ⌈ () ⌉ ↥ ↥ ↥)
pgl-ok (gate₁ ⌈ X-gate ⌉ ↥ ↥ ↥) = one (Xᵖ ₃) ιX₃
pgl-ok (gate₀ ⌈ () ⌉ ↥ ↥ ↥ ↥)

------------------------------------------------------------------------
-- Circuits

pg : Circuit 4 → List PG
pg [ g ]ʷ   = pgl g
pg ε       = []
pg (u • v) = pg u ++ pg v

ι*-++ : (xs ys : List PG) → 4 ⊢ ι* (xs ++ ys) ≈ ι* xs • ι* ys
ι*-++ []       ys = sym left-unit
ι*-++ (x ∷ xs) ys = trans (cong refl (ι*-++ xs ys)) (sym assoc)

-- Every circuit is the circuit of its placed letters.
pg-ok : (u : Circuit 4) → 4 ⊢ u ≈ ι* (pg u)
pg-ok [ g ]ʷ   = pgl-ok g
pg-ok ε       = refl
pg-ok (u • v) = trans (cong (pg-ok u) (pg-ok v)) (sym (ι*-++ (pg u) (pg v)))
