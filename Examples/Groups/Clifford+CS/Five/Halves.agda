------------------------------------------------------------------------
-- Presentations of groups
--
-- The two halves of five wires: four-wire words over P′, renamed
--
-- A word u over P′ on the sixteen indices of four wires, renamed into
-- the lower half of the five-wire numbering (the indices 0 … 15, whose
-- codes have wire 4 at 0: Five.Sem.Gray5), decodes to λ⁰ h for every
-- four-wire h with u's reading (`lower`): its gadgets are already on the
-- half where wire 4 reads 0, so Five.Dec5.red-D applies with the
-- identity, and the four-wire product of the gadgets has u's reading,
-- hence is h by completeness on four wires.  Renamed into the upper half
-- (16 + a, whose code is a's with wire 3 flipped and wire 4 at 1), it
-- decodes to λ¹ h when u reads as h conjugated by X on wire 3 (`upper`):
-- red-D with X on wires 3 and 4, then the X on wire 3 goes into λ⁰
-- (Five.Conj) and the one on wire 4 turns λ⁰ into λ¹ (Five.Calc).  So a
-- gate h on the wires 0 … 3 is the decoding of a word: λ⁰ h λ¹ h is h
-- (`below`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Primality using (prime[2])
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Word.Base using (_•_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
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

module Examples.Groups.Clifford+CS.Five.Halves
  (I : Inputs)
  (F : Facts4)
  (c4 : Complete 4)
  (cind : (V : Kind) (α β : B.Circuit 5) → fn α 0ᵛ ≡ fn β 0ᵛ → fn α e₀ ≡ fn β e₀ →
          5 ⊢ₓ τ α • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (α ⁻¹)
             ≈ τ β • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (β ⁻¹))
  where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Fin.Properties using (<⇒≢ ; ↑ˡ-injective ; ↑ʳ-injective)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product using (_,_)
open import Data.Vec using () renaming ([] to []ᵥ ; _∷_ to _∷ᵥ_ ; _++_ to _++ᵥ_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _ʷ)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; _≟_)
open import Data.Fin using (Fin)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; _VRel,_===_ ; _↓ᵏ_ ; _⊢_≈_)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦⟧ₒ-ε)
open import Examples.Groups.Clifford+CS.Five.Rules using (embed)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Affine using (aff⇒)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl) renaming (F to F⁰ ; T to T⁰)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm)
open import Examples.Groups.Clifford+CS.Five.Sem.Build using (α ; α-o ; α-e ; _⊕ᵥ_)
open import Examples.Groups.Clifford+CS.Five.Sem.Core using (Pt ; Πp ; low ; top)
open import Examples.Groups.Clifford+CS.Five.Sem.Gad4 (Facts4.G F) (Facts4.sem F) using (gad₄-sem)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (blkOf ; kpp ; krot ; kki)
open import Examples.Groups.Clifford+CS.Five.Sem.Gray5
  using (lo ; hi ; e₃ ; cod-lo ; cod-hi ; lo-mono ; hi-mono)
open import Examples.Groups.Clifford+CS.Five.Bot using (bot ; τ-bot ; bm-bot)
open import Examples.Groups.Clifford+CS.Five.Conj I using (conj⁰ ; bot-inv)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.BridgeGray 4 using () renaming (⟦_⟧PY to ⟦_⟧P4)
import Examples.Groups.Clifford+CS.Encoding 0 as E4
import Examples.Groups.Clifford+CS.Encoding 1 as E5
import Examples.Groups.Clifford+CS.Five.Decode 0 as D0
import Examples.Groups.Clifford+CS.Five.Decode 1 as D1
open import Examples.Groups.Clifford+CS.Five.Dec5 I F cind
  using (d ; Dg ; Dg₄ ; g₄ ; pts ; Good ; lowsβ ; red-D ; dʷ-D)
import Examples.Groups.Clifford+CS.Five.Ren as Ren
import Examples.Groups.Clifford+CS.Section8 0 as S8
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (module Inv)

open Inputs I using (F4ᵍ ; F5ᵍ ; x4x4 ; ok)
open Calc F4ᵍ F5ᵍ x4x4 using (Λ⁰ ; Λ¹ ; D ; X4w ; transport⁰ ; Λ⁰-X ; F5ʷ ; D-sp)

private
  module T4 = Tools (_VRel,_===_ 4)

  ≡→ : ∀ {u v : Circuit 5} → u ≡ v → u ≈ v
  ≡→ Eq.refl = refl

------------------------------------------------------------------------
-- The renamings

module L = Ren lo (λ {a} {b} e → ↑ˡ-injective 16 a b e) lo-mono
module H = Ren hi (λ {a} {b} e → ↑ʳ-injective 16 a b e) hi-mono

------------------------------------------------------------------------
-- Four wires

-- The points of four-wire gadgets.
pts₄ : List D0.Gd → List (Pt 4)
pts₄ = map (λ g → D0.kind g , E4.cod (D0.i g) , E4.cod (D0.j g))

private
  vne : ∀ G → D0.Valid G → D0.i G ≢ D0.j G
  vne (D0.gd kpp a b)  ne = ne
  vne (D0.gd krot a b) ne = ne
  vne (D0.gd kki a b)  lt = λ e → <⇒≢ lt (Eq.sym e)

  Dist : Pt 4 → Set
  Dist (V , a , b) = a ≢ b

  dist₄ : ∀ Gs → All D0.Valid Gs → All Dist (pts₄ Gs)
  dist₄ []       []        = []
  dist₄ (G ∷ Gs) (vG ∷ vs) = (λ e → vne G vG (E4.cod-inj e)) ∷ dist₄ Gs vs

  g₄-sem : ∀ V a b → a ≢ b → ⟦ g₄ V a b ⟧ ~ tl (blkOf V) a b
  g₄-sem V a b ne =
    Eq.subst₂ (λ x y → ⟦ g₄ V a b ⟧ ~ tl (blkOf V) x y) (α-o a b) (α-e a b ne) (gad₄-sem V (α a b))

  sem4 : ∀ Q → All Dist Q → ⟦ Dg₄ Q ⟧ ~ Πp Q
  sem4 []                []        = ~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {4} ε} {Idₒ} Eq.refl ⟦⟧ₒ-ε
  sem4 ((V , a , b) ∷ Q) (ne ∷ ds) =
    ~-trans {s = ⟦ g₄ V a b • Dg₄ Q ⟧} {t = ⟦ g₄ V a b ⟧ ∙ ⟦ Dg₄ Q ⟧} {u = Πp ((V , a , b) ∷ Q)}
      (hom (g₄ V a b) (Dg₄ Q))
      (∙-cong {s = ⟦ g₄ V a b ⟧} {s' = tl (blkOf V) a b} {t = ⟦ Dg₄ Q ⟧} {t' = Πp Q}
        (g₄-sem V a b ne) (sem4 Q ds))

  Π-pts₄ : ∀ Gs → D0.Π Gs ≡ Πp (pts₄ Gs)
  Π-pts₄ []       = Eq.refl
  Π-pts₄ (G ∷ Gs) = Eq.cong (tl (blkOf (D0.kind G)) (E4.cod (D0.i G)) (E4.cod (D0.j G)) ∙_) (Π-pts₄ Gs)

-- The four-wire product of a word's gadgets has the word's reading.
W₄ : Word (GenP 16) → Circuit 4
W₄ u = Dg₄ (pts₄ (D0.GL u))

W₄-sem : ∀ u → ⟦ W₄ u ⟧ ~ ⟦ u ⟧P4
W₄-sem u =
  ~-trans {s = ⟦ W₄ u ⟧} {t = Πp (pts₄ (D0.GL u))} {u = ⟦ u ⟧P4}
    (sem4 (pts₄ (D0.GL u)) (dist₄ (D0.GL u) (D0.valid-GL u)))
    (Eq.subst (_~ ⟦ u ⟧P4) (Π-pts₄ (D0.GL u)) (~-sym {s = ⟦ u ⟧P4} {t = D0.Π (D0.GL u)} (D0.sem-w u)))

------------------------------------------------------------------------
-- Points of the two halves

private
  low-++ : (v : Bits 4) (b : Bool) → low (v ++ᵥ (b ∷ᵥ []ᵥ)) ≡ v
  low-++ (x₀ ∷ᵥ x₁ ∷ᵥ x₂ ∷ᵥ x₃ ∷ᵥ []ᵥ) b = Eq.refl

  top-++ : (v : Bits 4) (b : Bool) → top (v ++ᵥ (b ∷ᵥ []ᵥ)) ≡ b
  top-++ (x₀ ∷ᵥ x₁ ∷ᵥ x₂ ∷ᵥ x₃ ∷ᵥ []ᵥ) b = Eq.refl

  -- A list of gadgets whose points β sends to the lower half, onto the
  -- four-wire codes.
  module Onto (β : B.Circuit 5) (ρ : Fin 16 → Fin 32)
              (on : ∀ a → bm β (E5.cod (ρ a)) ≡ E4.cod a ++ᵥ F⁰) where

    renG : D0.Gd → D1.Gd
    renG (D0.gd V a b) = D1.gd V (ρ a) (ρ b)

    low-on : ∀ a → low (bm β (E5.cod (ρ a))) ≡ E4.cod a
    low-on a = Eq.trans (Eq.cong low (on a)) (low-++ (E4.cod a) false)

    top-on : ∀ a → top (bm β (E5.cod (ρ a))) ≡ false
    top-on a = Eq.trans (Eq.cong top (on a)) (top-++ (E4.cod a) false)

    goods : ∀ Gs → All D0.Valid Gs → All (Good β) (pts (map renG Gs))
    goods []                 []       = []
    goods (D0.gd V a b ∷ Gs) (v ∷ vs) = (pq , lpq , top-on a , top-on b) ∷ goods Gs vs
      where
      lpq : low (bm β (E5.cod (ρ a))) ≢ low (bm β (E5.cod (ρ b)))
      lpq e = vne (D0.gd V a b) v (E4.cod-inj (Eq.trans (Eq.sym (low-on a)) (Eq.trans e (low-on b))))

      pq : E5.cod (ρ a) ≢ E5.cod (ρ b)
      pq e = lpq (Eq.cong (λ x → low (bm β x)) e)

    lows-on : ∀ Gs → lowsβ β (pts (map renG Gs)) ≡ pts₄ Gs
    lows-on []                 = Eq.refl
    lows-on (D0.gd V a b ∷ Gs) =
      Eq.cong₂ _∷_ (Eq.cong₂ (λ x y → V , x , y) (low-on a) (low-on b)) (lows-on Gs)

  -- The lower half: the identity.
  module OL = Onto ε lo cod-lo

  -- The upper half: X on wires 3 and 4.
  x₃ : B.Circuit 4
  x₃ = [ B.gate₁ B.X-gate B.↥ B.↥ B.↥ ]ʷ

  x₄ : B.Circuit 5
  x₄ = [ B.gate₁ B.X-gate B.↥ B.↥ B.↥ B.↥ ]ʷ

  β : B.Circuit 5
  β = bot x₃ • x₄

  xr : ∀ b → b xor false ≡ b
  xr false = Eq.refl
  xr true  = Eq.refl

  xn : ∀ b → not (b xor true) ≡ b
  xn false = Eq.refl
  xn true  = Eq.refl

  x₃-e₃ : (v : Bits 4) → bm x₃ (v ⊕ᵥ e₃) ≡ v
  x₃-e₃ (a ∷ᵥ b ∷ᵥ c ∷ᵥ e ∷ᵥ []ᵥ) =
    Eq.cong₂ _∷ᵥ_ (xr a) (Eq.cong₂ _∷ᵥ_ (xr b) (Eq.cong₂ _∷ᵥ_ (xr c) (Eq.cong (_∷ᵥ []ᵥ) (xn e))))

  x₄-T : (v : Bits 4) → bm x₄ (v ++ᵥ T⁰) ≡ v ++ᵥ F⁰
  x₄-T (a ∷ᵥ b ∷ᵥ c ∷ᵥ e ∷ᵥ []ᵥ) = Eq.refl

  β-hi : ∀ a → bm β (E5.cod (hi a)) ≡ E4.cod a ++ᵥ F⁰
  β-hi a =
    Eq.trans (Eq.cong (bm β) (cod-hi a))
      (Eq.trans (Eq.cong (bm (bot x₃)) (x₄-T (E4.cod a ⊕ᵥ e₃)))
        (Eq.trans (bm-bot x₃ (E4.cod a ⊕ᵥ e₃) false) (Eq.cong (_++ᵥ F⁰) (x₃-e₃ (E4.cod a)))))

  module OH = Onto β hi β-hi

  -- The renamings' gadgets are Onto's.
  renG-lo : ∀ Gs → map L.renG Gs ≡ map OL.renG Gs
  renG-lo []                 = Eq.refl
  renG-lo (D0.gd V a b ∷ Gs) = Eq.cong (D1.gd V (lo a) (lo b) ∷_) (renG-lo Gs)

  renG-hi : ∀ Gs → map H.renG Gs ≡ map OH.renG Gs
  renG-hi []                 = Eq.refl
  renG-hi (D0.gd V a b ∷ Gs) = Eq.cong (D1.gd V (hi a) (hi b) ∷_) (renG-hi Gs)

------------------------------------------------------------------------
-- The lower half

lower : (h : Circuit 4) (u : Word (GenP 16)) → ⟦ u ⟧P4 ~ ⟦ h ⟧ → (d ʷ) (L.renʷ u) ≈ Λ⁰ h
lower h u e = begin
  (d ʷ) (L.renʷ u)                     ≈⟨ dʷ-D (L.renʷ u) ⟩
  Dg (pts (D1.GL (L.renʷ u)))          ≈⟨ ≡→ (Eq.cong (Dg ∘ pts) (Eq.trans (L.GL-ren u) (renG-lo (D0.GL u)))) ⟩
  Dg K                                 ≈⟨ sym (trans left-unit right-unit) ⟩
  τ ε • Dg K • τ (ε ⁻¹)                ≈⟨ red-D ε K (OL.goods (D0.GL u) (D0.valid-GL u)) ⟩
  Λ⁰ (Dg₄ (lowsβ ε K))                 ≈⟨ ≡→ (Eq.cong (Λ⁰ ∘ Dg₄) (OL.lows-on (D0.GL u))) ⟩
  Λ⁰ (W₄ u)                            ≈⟨ transport⁰ ok {W₄ u} {h} (c4 {W₄ u} {h} sem) ⟩
  Λ⁰ h ∎
  where
  K : List (Pt 5)
  K = pts (map OL.renG (D0.GL u))

  sem : ⟦ W₄ u ⟧ ~ ⟦ h ⟧
  sem = ~-trans {s = ⟦ W₄ u ⟧} {t = ⟦ u ⟧P4} {u = ⟦ h ⟧} (W₄-sem u) e

------------------------------------------------------------------------
-- The upper half

private
  a a′ : Circuit 4
  a  = τ x₃
  a′ = τ (x₃ ⁻¹)

  -- The X on wire 3 cancels on four wires.
  cancel : (h : Circuit 4) → 4 ⊢ a′ • (a • h • a′) • a ≈ h
  cancel h =
    T4.trans (T4.by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl)
      (T4.trans (T4.cong il (T4.back h il)) (T4.trans T4.left-unit T4.right-unit))
    where
    il : 4 ⊢ a′ • a ≈ ε
    il = aff⇒ (Inv.inverseˡ 4 {x₃})

  -- X on wire 4, both ways.
  il₄ : τ (x₄ ⁻¹) • X4w ≈ ε
  il₄ = embed (aff⇒ (Inv.inverseˡ 5 {x₄}))

  x₄⁻ : τ (x₄ ⁻¹) ≈ X4w
  x₄⁻ = begin
    τ (x₄ ⁻¹)                      ≈⟨ sym right-unit ⟩
    τ (x₄ ⁻¹) • ε                  ≈⟨ back _ (sym x4x4) ⟩
    τ (x₄ ⁻¹) • X4w • X4w          ≈⟨ sym assoc ⟩
    (τ (x₄ ⁻¹) • X4w) • X4w        ≈⟨ front _ il₄ ⟩
    ε • X4w                        ≈⟨ left-unit ⟩
    X4w ∎

  -- Conjugating λ⁰ by X on wires 3 and 4.
  conjX : (h : Circuit 4) → τ (β ⁻¹) • Λ⁰ (a • h • a′) • τ β ≈ Λ¹ h
  conjX h = begin
    τ (β ⁻¹) • Λ⁰ (a • h • a′) • τ β
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    τ (x₄ ⁻¹) • (τ (bot x₃ ⁻¹) • Λ⁰ (a • h • a′) • τ (bot x₃)) • X4w
      ≈⟨ back _ (front _ (cong (bot-inv x₃) (back _ (≡→ (τ-bot x₃))))) ⟩
    τ (x₄ ⁻¹) • ((a′ ↓ᵏ 1) • Λ⁰ (a • h • a′) • (a ↓ᵏ 1)) • X4w
      ≈⟨ back _ (front _ (conj⁰ a′ a (a • h • a′) (aff⇒ (Inv.inverseˡ 4 {x₃})))) ⟩
    τ (x₄ ⁻¹) • Λ⁰ (a′ • (a • h • a′) • a) • X4w
      ≈⟨ back _ (front _ (transport⁰ ok {a′ • (a • h • a′) • a} {h} (cancel h))) ⟩
    τ (x₄ ⁻¹) • Λ⁰ h • X4w
      ≈⟨ front _ x₄⁻ ⟩
    X4w • Λ⁰ h • X4w
      ≈⟨ back _ (front _ (Λ⁰-X h)) ⟩
    X4w • (X4w • Λ¹ h • X4w) • X4w
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (X4w • X4w) • Λ¹ h • (X4w • X4w)
      ≈⟨ cong x4x4 (back _ x4x4) ⟩
    ε • Λ¹ h • ε
      ≈⟨ trans left-unit right-unit ⟩
    Λ¹ h ∎

upper : (h : Circuit 4) (u : Word (GenP 16)) → ⟦ u ⟧P4 ~ ⟦ a • h • a′ ⟧ → (d ʷ) (H.renʷ u) ≈ Λ¹ h
upper h u e = begin
  (d ʷ) (H.renʷ u)                         ≈⟨ dʷ-D (H.renʷ u) ⟩
  Dg (pts (D1.GL (H.renʷ u)))              ≈⟨ ≡→ (Eq.cong (Dg ∘ pts) (Eq.trans (H.GL-ren u) (renG-hi (D0.GL u)))) ⟩
  Dg K                                     ≈⟨ uncj (Dg K) ⟩
  τ (β ⁻¹) • (τ β • Dg K • τ (β ⁻¹)) • τ β ≈⟨ back _ (front _ (red-D β K (OH.goods (D0.GL u) (D0.valid-GL u)))) ⟩
  τ (β ⁻¹) • Λ⁰ (Dg₄ (lowsβ β K)) • τ β    ≈⟨ back _ (front _ (≡→ (Eq.cong (Λ⁰ ∘ Dg₄) (OH.lows-on (D0.GL u))))) ⟩
  τ (β ⁻¹) • Λ⁰ (W₄ u) • τ β               ≈⟨ back _ (front _ (transport⁰ ok {W₄ u} {a • h • a′} (c4 {W₄ u} {a • h • a′} sem))) ⟩
  τ (β ⁻¹) • Λ⁰ (a • h • a′) • τ β         ≈⟨ conjX h ⟩
  Λ¹ h ∎
  where
  K : List (Pt 5)
  K = pts (map OH.renG (D0.GL u))

  sem : ⟦ W₄ u ⟧ ~ ⟦ a • h • a′ ⟧
  sem = ~-trans {s = ⟦ W₄ u ⟧} {t = ⟦ u ⟧P4} {u = ⟦ a • h • a′ ⟧} (W₄-sem u) e

  il : τ (β ⁻¹) • τ β ≈ ε
  il = embed (aff⇒ (Inv.inverseˡ 5 {β}))

  uncj : ∀ x → x ≈ τ (β ⁻¹) • (τ β • x • τ (β ⁻¹)) • τ β
  uncj x = begin
    x                                             ≈⟨ sym left-unit ⟩
    ε • x                                         ≈⟨ front x (sym il) ⟩
    (τ (β ⁻¹) • τ β) • x                          ≈⟨ back _ (sym right-unit) ⟩
    (τ (β ⁻¹) • τ β) • (x • ε)                    ≈⟨ back _ (back x (sym il)) ⟩
    (τ (β ⁻¹) • τ β) • (x • (τ (β ⁻¹) • τ β))
      ≈⟨ by-passoc ((□ • □) • (□ • (□ • □))) (□ • (□ • □ • □) • □) Eq.refl ⟩
    τ (β ⁻¹) • (τ β • x • τ (β ⁻¹)) • τ β ∎

------------------------------------------------------------------------
-- A gate on the wires 0 … 3

-- The four-wire encoding preserves the semantics.
private
  eʷ-sem : (w : Circuit 4) → ⟦ (E4.e ʷ) w ⟧P4 ~ ⟦ w ⟧
  eʷ-sem [ g ]ʷ  = S8.e-sem g
  eʷ-sem ε       = ~-sym {s = ⟦_⟧ {4} ε} {t = ε∙} (~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {4} ε} {Idₒ} Eq.refl ⟦⟧ₒ-ε)
  eʷ-sem (u • v) =
    ~-trans {s = ⟦ (E4.e ʷ) u ⟧P4 ∙ ⟦ (E4.e ʷ) v ⟧P4} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} {u = ⟦ u • v ⟧}
      (∙-cong {s = ⟦ (E4.e ʷ) u ⟧P4} {s' = ⟦ u ⟧} {t = ⟦ (E4.e ʷ) v ⟧P4} {t' = ⟦ v ⟧} (eʷ-sem u) (eʷ-sem v))
      (~-sym {s = ⟦ u • v ⟧} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} (hom u v))

-- The encoding, kept opaque: a conversion that unfolded the encoding of
-- the closed word for X on wire 3 would compute its matrix.
opaque
  enc : Circuit 4 → Word (GenP 16)
  enc = E4.e ʷ

  enc-sem : (w : Circuit 4) → ⟦ enc w ⟧P4 ~ ⟦ w ⟧
  enc-sem = eʷ-sem

-- The word: h's encoding on the lower half, and the encoding of h
-- conjugated by X on wire 3 on the upper.
upw : Circuit 4 → Word (GenP 32)
upw h = H.renʷ (enc (a • h • a′))

wd : Circuit 4 → Word (GenP 32)
wd h = L.renʷ (enc h) • upw h

-- The upper half alone: λ¹ h.
above : (h : Circuit 4) → (d ʷ) (upw h) ≈ Λ¹ h
above h = upper h (enc (a • h • a′)) (enc-sem (a • h • a′))

below : (h : Circuit 4) → (d ʷ) (wd h) ≈ h ↓ᵏ 1
below h = begin
  (d ʷ) (L.renʷ (enc h)) • (d ʷ) (upw h)
    ≈⟨ cong (lower h (enc h) (enc-sem h)) (above h) ⟩
  Λ⁰ h • Λ¹ h                ≈⟨ sym (F5ʷ h) ⟩
  D h                        ≈⟨ D-sp h ⟩
  h ↓ᵏ 1 ∎
