------------------------------------------------------------------------
-- Presentations of groups
--
-- The affine decoding on five wires, and its rules reduced to four
--
-- A gadget on two five-bit vectors p ≠ q is the four-wire gadget under
-- λ⁰ on wire 4, conjugated by an affine circuit sending 0 and e₀ to p
-- and q (`gad₅`); a letter of P′ decodes as the product of its gadgets
-- (Five.Decode.gl).  For an affine circuit β that sends every point of
-- a list of gadgets into the half where wire 4 reads 0, conjugating the
-- decoded product by β is λ⁰ of a four-wire product (`red-D`): each
-- gadget's affine circuit may be replaced by one fixing wire 4 (the
-- independence, a module parameter: Five.Gadget5), and conjugating λ⁰
-- by a circuit on the domain wires is λ⁰ of the conjugate (Five.Conj).
--
-- The four-wire words are given explicitly wherever they occur under
-- λ⁰: comparing two spellings of a gadget under λ⁰ would unfold its
-- five-wire spelling.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Primality using (prime[2])
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (_•_)
open import Examples.Groups.Clifford+CS.Five.Inputs using (Inputs)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)
open import Examples.Groups.Clifford+CS.Five.Affine using (τ)
open import Examples.Groups.Clifford+CS.Five.Stab using (e₀)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)
import Examples.Groups.Clifford+CS.Five.Calc as Calc
import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan 0 prime[2] 0 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2] using (adm)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹)

module Examples.Groups.Clifford+CS.Five.Dec5
  (I : Inputs)
  (F : Facts4)
  (cind : (V : Kind) (α β : B.Circuit 5) → fn α 0ᵛ ≡ fn β 0ᵛ → fn α e₀ ≡ fn β e₀ →
          5 ⊢ₓ τ α • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (α ⁻¹)
             ≈ τ β • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (β ⁻¹))
  where

open import Data.Bool using (true ; false)
open import Data.List using (List ; [] ; _∷_ ; map) renaming (_++_ to _++ˡ_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using ([] ; _∷_) renaming (_++_ to _++ᵥ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _ʷ)

open import Examples.Groups.Clifford+CS.Semantics using (Bits)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; _↓ᵏ_)
open import Examples.Groups.Clifford+CS.Five.Rules using (embed)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Affine using (aff⇒)
open import Examples.Groups.Clifford+CS.Five.Bot using (bot ; τ-bot ; bm-bot)
open import Examples.Groups.Clifford+CS.Five.Conj I using (conj⁰ ; bot-inv)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using () renaming (F to F⁰)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm ; Lv)
open import Examples.Groups.Clifford+CS.Five.Sem.Build using (α ; α-o ; α-e ; ze ; fn-bm)
open import Examples.Groups.Clifford+CS.Five.Sem.Core using (Pt ; low ; top)
open import Examples.Groups.Clifford+CS.Five.Sem.Gad4 (Facts4.G F) (Facts4.sem F) using (gad₄)
open import Examples.Groups.Clifford+CS.Encoding 1 using (N ; cod)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Five.Decode 1 using (Gd ; kind ; i ; j ; gl ; GL)

open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn-•)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (module Inv)

open Inputs I
open Facts4 F using (G)
open Calc F4ᵍ F5ᵍ x4x4 using (Λ⁰ ; hom⁰)

------------------------------------------------------------------------
-- The decoding

gad₅ : Kind → Bits 5 → Bits 5 → Circuit 5
gad₅ V p q = τ (α p q) • Λ⁰ (G V) • τ (α p q ⁻¹)

-- A list of gadgets on five-bit points.
Dg : List (Pt 5) → Circuit 5
Dg []                = ε
Dg ((V , p , q) ∷ L) = gad₅ V p q • Dg L

pts : List Gd → List (Pt 5)
pts = map (λ g → kind g , cod (i g) , cod (j g))

d : GenP N → Circuit 5
d x = Dg (pts (gl x))

-- The four-wire gadget on (a , b).
g₄ : Kind → Bits 4 → Bits 4 → Circuit 4
g₄ V a b = gad₄ V (α a b)

Dg₄ : List (Pt 4) → Circuit 4
Dg₄ []                = ε
Dg₄ ((V , a , b) ∷ Q) = g₄ V a b • Dg₄ Q

------------------------------------------------------------------------
-- One gadget

private
  ≡→ : ∀ {u v : Circuit 5} → u ≡ v → u ≈ v
  ≡→ refl = refl

red : (V : Kind) (β : B.Circuit 5) (p q : Bits 5) (a b : Bits 4) → p ≢ q → a ≢ b →
      bm β p ≡ a ++ᵥ F⁰ → bm β q ≡ b ++ᵥ F⁰ →
      τ β • gad₅ V p q • τ (β ⁻¹) ≈ Λ⁰ (g₄ V a b)
red V β p q a b p≢q a≢b hp hq = begin
  τ β • gad₅ V p q • τ (β ⁻¹)
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  τ (β • α p q) • Λ⁰ (G V) • τ ((β • α p q) ⁻¹)
    ≈⟨ cind V (β • α p q) (bot (α a b)) h0 h1 ⟩
  τ (bot (α a b)) • Λ⁰ (G V) • τ (bot (α a b) ⁻¹)
    ≈⟨ cong (≡→ (τ-bot (α a b))) (back (Λ⁰ (G V)) (bot-inv (α a b))) ⟩
  (τ (α a b) ↓ᵏ 1) • Λ⁰ (G V) • (τ (α a b ⁻¹) ↓ᵏ 1)
    ≈⟨ conj⁰ (τ (α a b)) (τ (α a b ⁻¹)) (G V) (aff⇒ (Inv.inverseʳ 4 {α a b})) ⟩
  Λ⁰ (τ (α a b) • G V • τ (α a b ⁻¹))
    ≈⟨ ≡→ (Eq.cong Λ⁰ g₄-def) ⟩
  Λ⁰ (g₄ V a b) ∎
  where
  g₄-def : τ (α a b) • G V • τ (α a b ⁻¹) ≡ g₄ V a b
  g₄-def = refl

  h0 : fn (β • α p q) 0ᵛ ≡ fn (bot (α a b)) 0ᵛ
  h0 = Eq.trans (fn-• β (α p q) 0ᵛ)
         (Eq.trans (Eq.cong (fn β) (Eq.trans (fn-bm (α p q) ze) (Eq.cong Lv (α-o p q))))
           (Eq.trans (fn-bm β p) (Eq.trans (Eq.cong Lv hp)
             (Eq.sym (Eq.trans (fn-bm (bot (α a b)) ze)
               (Eq.cong Lv (Eq.trans (bm-bot (α a b) ze false) (Eq.cong (_++ᵥ F⁰) (α-o a b)))))))))

  h1 : fn (β • α p q) e₀ ≡ fn (bot (α a b)) e₀
  h1 = Eq.trans (fn-• β (α p q) e₀)
         (Eq.trans (Eq.cong (fn β) (Eq.trans (fn-bm (α p q) (true ∷ ze)) (Eq.cong Lv (α-e p q p≢q))))
           (Eq.trans (fn-bm β q) (Eq.trans (Eq.cong Lv hq)
             (Eq.sym (Eq.trans (fn-bm (bot (α a b)) (true ∷ ze))
               (Eq.cong Lv (Eq.trans (bm-bot (α a b) (true ∷ ze) false) (Eq.cong (_++ᵥ F⁰) (α-e a b a≢b)))))))))

------------------------------------------------------------------------
-- A list of gadgets

-- The images of the points are distinct and on the half where wire 4
-- reads 0.
Good : B.Circuit 5 → Pt 5 → Set
Good β (V , p , q) =
  p ≢ q × low (bm β p) ≢ low (bm β q) × top (bm β p) ≡ false × top (bm β q) ≡ false

lowsβ : B.Circuit 5 → List (Pt 5) → List (Pt 4)
lowsβ β = map (λ { (V , p , q) → V , low (bm β p) , low (bm β q) })

private
  low-F : (y : Bits 5) → top y ≡ false → y ≡ low y ++ᵥ F⁰
  low-F (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ .false ∷ []) refl = refl

red-D : (β : B.Circuit 5) (L : List (Pt 5)) → All (Good β) L →
        τ β • Dg L • τ (β ⁻¹) ≈ Λ⁰ (Dg₄ (lowsβ β L))
red-D β [] [] = begin
  τ β • ε • τ (β ⁻¹)   ≈⟨ back (τ β) left-unit ⟩
  τ β • τ (β ⁻¹)       ≈⟨ embed (aff⇒ (Inv.inverseʳ 5 {β})) ⟩
  ε ∎
red-D β ((V , p , q) ∷ L) ((p≢q , a≢b , tp , tq) ∷ gs) = begin
  τ β • (gad₅ V p q • Dg L) • τ (β ⁻¹)
    ≈⟨ back (τ β) assoc ⟩
  τ β • gad₅ V p q • (Dg L • τ (β ⁻¹))
    ≈⟨ back (τ β) (back (gad₅ V p q) (sym left-unit)) ⟩
  τ β • gad₅ V p q • (ε • (Dg L • τ (β ⁻¹)))
    ≈⟨ back (τ β) (back (gad₅ V p q) (front _ (sym (embed (aff⇒ (Inv.inverseˡ 5 {β})))))) ⟩
  τ β • gad₅ V p q • ((τ (β ⁻¹) • τ β) • (Dg L • τ (β ⁻¹)))
    ≈⟨ by-passoc (□ • □ • ((□ • □) • (□ • □))) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (τ β • gad₅ V p q • τ (β ⁻¹)) • (τ β • Dg L • τ (β ⁻¹))
    ≈⟨ cong (red V β p q a b p≢q a≢b (low-F (bm β p) tp) (low-F (bm β q) tq)) (red-D β L gs) ⟩
  Λ⁰ (g₄ V a b) • Λ⁰ (Dg₄ (lowsβ β L))
    ≈⟨ sym (hom⁰ (g₄ V a b) (Dg₄ (lowsβ β L))) ⟩
  Λ⁰ (g₄ V a b • Dg₄ (lowsβ β L)) ∎
  where
  a b : Bits 4
  a = low (bm β p)
  b = low (bm β q)

------------------------------------------------------------------------
-- Words

private
  ≡→′ : ∀ {u v : Circuit 5} → u ≡ v → u ≈ v
  ≡→′ refl = refl

Dg-++ : (L L′ : List (Pt 5)) → Dg (L ++ˡ L′) ≈ Dg L • Dg L′
Dg-++ []                L′ = sym left-unit
Dg-++ ((V , p , q) ∷ L) L′ = trans (back (gad₅ V p q) (Dg-++ L L′)) (sym assoc)

pts-++ : (L L′ : List Gd) → pts (L ++ˡ L′) ≡ pts L ++ˡ pts L′
pts-++ []      L′ = refl
pts-++ (g ∷ L) L′ = Eq.cong (_ ∷_) (pts-++ L L′)

-- The decoding of a word is the decoding of its gadgets.
dʷ-D : (u : Word (GenP N)) → (d ʷ) u ≈ Dg (pts (GL u))
dʷ-D [ x ]ʷ  = refl
dʷ-D ε       = refl
dʷ-D (u • v) =
  trans (cong (dʷ-D u) (dʷ-D v))
    (sym (trans (≡→′ (Eq.cong Dg (pts-++ (GL u) (GL v)))) (Dg-++ (pts (GL u)) (pts (GL v)))))
