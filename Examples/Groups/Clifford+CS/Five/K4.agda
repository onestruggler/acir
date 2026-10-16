------------------------------------------------------------------------
-- Presentations of groups
--
-- K on wire 4 as the decoding of a word over P′
--
-- K on wire 4 is K on wire 3 conjugated by the swap of the wires 3 and
-- 4, an affine circuit; K on wire 3 is the decoding of a word (Five.
-- Halves.below), and conjugating a gadget by an affine circuit moves it
-- to the images of its two points (`move`, by the gadgets' independence
-- `cind`).  The moved gadgets are again gadgets of letters of P′ — the
-- hybrid's on (p , q) with p before q in the numbering, which no letter
-- has, being iZ on (q , p) times the hybrid's on (q , p) (`respell`, by
-- one identity of two-level operators on four wires decided on tries).
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

module Examples.Groups.Clifford+CS.Five.K4
  (I : Inputs)
  (F : Facts4)
  (c4 : Complete 4)
  (cind : (V : Kind) (α β : B.Circuit 5) → fn α 0ᵛ ≡ fn β 0ᵛ → fn α e₀ ≡ fn β e₀ →
          5 ⊢ₓ τ α • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (α ⁻¹)
             ≈ τ β • Calc.Λ⁰ (Inputs.F4ᵍ I) (Inputs.F5ᵍ I) (Inputs.x4x4 I) (Facts4.G F V) • τ (β ⁻¹))
  where

open import Data.Bool using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; _<_)
open import Data.Fin.Properties using (_≟_ ; <-cmp)
open import Data.List using (List ; [] ; _∷_ ; map ; _++_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using () renaming (_∷_ to _∷ᵥ_)
open import Function using (_∘_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _ʷ)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; _≟_)
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Clifford+CS.Syntactics
  using (Circuit ; Gen ; gate₁ ; _↥ ; K-gate ; _VRel,_===_ ; _⊢_≈_ ; _↑ ; _↓ᵏ_ ; K ; Swap ; lemma-cong↑)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Swaps using (Swap² ; swap-K)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Five.Rules using (embed)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Affine using (aff⇒)
open import Examples.Groups.Clifford+CS.Five.Sem.TL using (tl ; tlOp ; perm ; module Bij)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm ; bm-inv ; bm-inv′ ; aff4 ; Lv)
open import Examples.Groups.Clifford+CS.Five.Sem.Build using (α ; α-o ; α-e ; ze ; fn-bm)
open import Examples.Groups.Clifford+CS.Five.Sem.Core using (Pt)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (blkOf ; kpp ; krot ; kki ; o₄ ; e₄)
open import Examples.Groups.Clifford+CS.Five.Bot using (bot ; τ-bot)
open import Examples.Groups.Clifford+CS.Five.Conj I using (conj⁰ ; bot-inv)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp)
import Examples.Groups.Clifford+CS.Encoding 1 as E5
open import Examples.Groups.Clifford+CS.Five.Decode 1
  using (Gd ; gd ; kind ; i ; j ; gl ; GL ; ppL ; pxL ; kiL ; kd ; xd-lt ; xd-gt ; kd-lt ; valid-GL ; Valid)
open import Examples.Groups.Clifford+CS.Auxiliary.Template E5.N′ using (xd)
open import Examples.Groups.Clifford+CS.Five.Dec5 I F cind
  using (d ; Dg ; gad₅ ; pts ; dʷ-D ; Dg-++ ; pts-++)
open import Examples.Groups.Clifford+CS.Five.Halves I F c4 cind using (wd ; below)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn-•)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (module Inv)

open Inputs I using (F4ᵍ ; F5ᵍ ; x4x4 ; ok)
open Facts4 F using (G)
open Calc F4ᵍ F5ᵍ x4x4 using (Λ⁰ ; hom⁰ ; transport⁰)

private
  module T4 = Tools (_VRel,_===_ 4)
  module T5 = Tools (_VRel,_===_ 5)

  ≡→ : ∀ {u v : Circuit 5} → u ≡ v → u ≈ v
  ≡→ Eq.refl = refl

------------------------------------------------------------------------
-- Moving gadgets by an affine circuit

private
  bm-ne : (β : B.Circuit 5) {p q : Bits 5} → p ≢ q → bm β p ≢ bm β q
  bm-ne β {p} {q} ne e = ne (Eq.trans (Eq.sym (bm-inv β p)) (Eq.trans (Eq.cong (bm (β ⁻¹)) e) (bm-inv β q)))

  -- Where α p q sends 0 and e₀.
  at-o : (β : B.Circuit 5) (p q : Bits 5) → fn (β • α p q) 0ᵛ ≡ Lv (bm β p)
  at-o β p q =
    Eq.trans (fn-• β (α p q) 0ᵛ)
      (Eq.trans (Eq.cong (fn β) (Eq.trans (fn-bm (α p q) ze) (Eq.cong Lv (α-o p q)))) (fn-bm β p))

  at-e : (β : B.Circuit 5) (p q : Bits 5) → p ≢ q → fn (β • α p q) e₀ ≡ Lv (bm β q)
  at-e β p q ne =
    Eq.trans (fn-• β (α p q) e₀)
      (Eq.trans (Eq.cong (fn β) (Eq.trans (fn-bm (α p q) (true ∷ᵥ ze)) (Eq.cong Lv (α-e p q ne)))) (fn-bm β q))

  at-o′ : (p q : Bits 5) → fn (α p q) 0ᵛ ≡ Lv p
  at-o′ p q = Eq.trans (fn-bm (α p q) ze) (Eq.cong Lv (α-o p q))

  at-e′ : (p q : Bits 5) → p ≢ q → fn (α p q) e₀ ≡ Lv q
  at-e′ p q ne = Eq.trans (fn-bm (α p q) (true ∷ᵥ ze)) (Eq.cong Lv (α-e p q ne))

move : (β : B.Circuit 5) (V : Kind) (p q : Bits 5) → p ≢ q →
       τ β • gad₅ V p q • τ (β ⁻¹) ≈ gad₅ V (bm β p) (bm β q)
move β V p q ne = begin
  τ β • gad₅ V p q • τ (β ⁻¹)
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  τ (β • α p q) • Λ⁰ (G V) • τ ((β • α p q) ⁻¹)
    ≈⟨ cind V (β • α p q) (α p′ q′)
         (Eq.trans (at-o β p q) (Eq.sym (at-o′ p′ q′)))
         (Eq.trans (at-e β p q ne) (Eq.sym (at-e′ p′ q′ (bm-ne β ne)))) ⟩
  gad₅ V p′ q′ ∎
  where
  p′ q′ : Bits 5
  p′ = bm β p
  q′ = bm β q

Dist : Pt 5 → Set
Dist (V , p , q) = p ≢ q

mapβ : B.Circuit 5 → List (Pt 5) → List (Pt 5)
mapβ β = map (λ { (V , p , q) → V , bm β p , bm β q })

conjD : (β : B.Circuit 5) (L : List (Pt 5)) → All Dist L →
        τ β • Dg L • τ (β ⁻¹) ≈ Dg (mapβ β L)
conjD β [] [] = begin
  τ β • ε • τ (β ⁻¹)   ≈⟨ back (τ β) left-unit ⟩
  τ β • τ (β ⁻¹)       ≈⟨ embed (aff⇒ (Inv.inverseʳ 5 {β})) ⟩
  ε ∎
conjD β ((V , p , q) ∷ L) (ne ∷ ds) = begin
  τ β • (gad₅ V p q • Dg L) • τ (β ⁻¹)
    ≈⟨ back (τ β) assoc ⟩
  τ β • gad₅ V p q • (Dg L • τ (β ⁻¹))
    ≈⟨ back (τ β) (back (gad₅ V p q) (sym left-unit)) ⟩
  τ β • gad₅ V p q • (ε • (Dg L • τ (β ⁻¹)))
    ≈⟨ back (τ β) (back (gad₅ V p q) (front _ (sym (embed (aff⇒ (Inv.inverseˡ 5 {β})))))) ⟩
  τ β • gad₅ V p q • ((τ (β ⁻¹) • τ β) • (Dg L • τ (β ⁻¹)))
    ≈⟨ by-passoc (□ • □ • ((□ • □) • (□ • □))) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (τ β • gad₅ V p q • τ (β ⁻¹)) • (τ β • Dg L • τ (β ⁻¹))
    ≈⟨ cong (move β V p q ne) (conjD β L ds) ⟩
  gad₅ V (bm β p) (bm β q) • Dg (mapβ β L) ∎

------------------------------------------------------------------------
-- The respelling of a hybrid gadget

private
  -- The block identity on four wires, decided on tries.
  by-tries : (k l : ℕ) (M N : Op 4) →
             eqM (scaleM (γ^ l) (matOf M)) (scaleM (γ^ k) (matOf N)) ≡ true → (k , M) ~ (l , N)
  by-tries k l M N e =
    ≐-trans (·-cong Eq.refl (≐-sym (ix-matOf M)))
      (≐-trans (≐-sym (ix-scaleM (γ^ l) (matOf M)))
        (≐-trans (ix-≡ (eqM-sound _ _ e))
          (≐-trans (ix-scaleM (γ^ k) (matOf N)) (·-cong Eq.refl (ix-matOf N)))))

  respell₄ : tl (blkOf kki) o₄ e₄ ~ (tl (blkOf kpp) e₄ o₄ ∙ tl (blkOf kki) e₄ o₄)
  respell₄ = by-tries 1 1 (tlOp (blkOf kki) o₄ e₄) (tlOp (blkOf kpp) e₄ o₄ ⊙ tlOp (blkOf kki) e₄ o₄) Eq.refl

  -- X on wire 0 exchanges 0 and e₀.
  x₀₄ : B.Circuit 4
  x₀₄ = [ B.gate₁ B.X-gate ]ʷ

  x₀ : B.Circuit 5
  x₀ = bot x₀₄

  -- Conjugated by X on wire 0, the product iZ · hybrid on (0 , e₀) is
  -- the hybrid on (e₀ , 0), on four wires.
  sem-x : ⟦ τ x₀₄ • (G kpp • G kki) • τ (x₀₄ ⁻¹) ⟧ ~ ⟦ G kki ⟧
  sem-x =
    ~-trans {s = ⟦ a • (gp • gk) • a′ ⟧} {t = ⟦ a ⟧ ∙ ((⟦ gp ⟧ ∙ ⟦ gk ⟧) ∙ ⟦ a′ ⟧)} {u = ⟦ gk ⟧}
      (~-trans {s = ⟦ a • (gp • gk) • a′ ⟧} {t = ⟦ a ⟧ ∙ ⟦ (gp • gk) • a′ ⟧}
               {u = ⟦ a ⟧ ∙ ((⟦ gp ⟧ ∙ ⟦ gk ⟧) ∙ ⟦ a′ ⟧)}
        (hom a ((gp • gk) • a′))
        (∙-cong {s = ⟦ a ⟧} {s' = ⟦ a ⟧} {t = ⟦ (gp • gk) • a′ ⟧} {t' = (⟦ gp ⟧ ∙ ⟦ gk ⟧) ∙ ⟦ a′ ⟧}
          (~-refl ⟦ a ⟧)
          (~-trans {s = ⟦ (gp • gk) • a′ ⟧} {t = ⟦ gp • gk ⟧ ∙ ⟦ a′ ⟧} {u = (⟦ gp ⟧ ∙ ⟦ gk ⟧) ∙ ⟦ a′ ⟧}
            (hom (gp • gk) a′)
            (∙-cong {s = ⟦ gp • gk ⟧} {s' = ⟦ gp ⟧ ∙ ⟦ gk ⟧} {t = ⟦ a′ ⟧} {t' = ⟦ a′ ⟧}
              (hom gp gk) (~-refl ⟦ a′ ⟧)))))
      (~-trans {s = ⟦ a ⟧ ∙ ((⟦ gp ⟧ ∙ ⟦ gk ⟧) ∙ ⟦ a′ ⟧)} {t = Pf ∙ ((Bp ∙ Bk) ∙ Pg)} {u = ⟦ gk ⟧}
        (∙-cong {s = ⟦ a ⟧} {s' = Pf} {t = (⟦ gp ⟧ ∙ ⟦ gk ⟧) ∙ ⟦ a′ ⟧} {t' = (Bp ∙ Bk) ∙ Pg}
          (aff4 x₀₄)
          (∙-cong {s = ⟦ gp ⟧ ∙ ⟦ gk ⟧} {s' = Bp ∙ Bk} {t = ⟦ a′ ⟧} {t' = Pg}
            (∙-cong {s = ⟦ gp ⟧} {s' = Bp} {t = ⟦ gk ⟧} {t' = Bk} (Facts4.sem F kpp) (Facts4.sem F kki))
            (aff4 (x₀₄ ⁻¹))))
        (~-trans {s = Pf ∙ ((Bp ∙ Bk) ∙ Pg)} {t = (Pf ∙ (Bp ∙ Bk)) ∙ Pg} {u = ⟦ gk ⟧}
          (~-sym {s = (Pf ∙ (Bp ∙ Bk)) ∙ Pg} {t = Pf ∙ ((Bp ∙ Bk) ∙ Pg)} (∙-assoc Pf (Bp ∙ Bk) Pg))
          (~-trans {s = (Pf ∙ (Bp ∙ Bk)) ∙ Pg} {t = Cp ∙ Ck} {u = ⟦ gk ⟧}
            (X.conj-∙ Bp Bk)
            (~-trans {s = Cp ∙ Ck} {t = tl (blkOf kpp) e₄ o₄ ∙ tl (blkOf kki) e₄ o₄} {u = ⟦ gk ⟧}
              (∙-cong {s = Cp} {s' = tl (blkOf kpp) e₄ o₄} {t = Ck} {t' = tl (blkOf kki) e₄ o₄}
                (X.conj-tl (blkOf kpp) o₄ e₄) (X.conj-tl (blkOf kki) o₄ e₄))
              (~-trans {s = tl (blkOf kpp) e₄ o₄ ∙ tl (blkOf kki) e₄ o₄} {t = Bk} {u = ⟦ gk ⟧}
                (~-sym {s = Bk} {t = tl (blkOf kpp) e₄ o₄ ∙ tl (blkOf kki) e₄ o₄} respell₄)
                (~-sym {s = ⟦ gk ⟧} {t = Bk} (Facts4.sem F kki)))))))
    where
    a a′ gp gk : Circuit 4
    a  = τ x₀₄
    a′ = τ (x₀₄ ⁻¹)
    gp = G kpp
    gk = G kki

    f f′ : Bits 4 → Bits 4
    f  = bm x₀₄
    f′ = bm (x₀₄ ⁻¹)

    module X = Bij f f′ (bm-inv′ x₀₄) (bm-inv x₀₄)

    Pf Pg Bp Bk Cp Ck : Scaled 4
    Pf = 0 , perm f
    Pg = 0 , perm f′
    Bp = tl (blkOf kpp) o₄ e₄
    Bk = tl (blkOf kki) o₄ e₄
    Cp = X.conjS Bp
    Ck = X.conjS Bk

respell : (p q : Bits 5) → p ≢ q → gad₅ kpp q p • gad₅ kki q p ≈ gad₅ kki p q
respell p q ne = begin
  gad₅ kpp q p • gad₅ kki q p
    ≈⟨ cong (to kpp) (to kki) ⟩
  (c • Λ⁰ (G kpp) • c′) • (c • Λ⁰ (G kki) • c′)
    ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  c • Λ⁰ (G kpp) • (c′ • c) • Λ⁰ (G kki) • c′
    ≈⟨ back c (back _ (front _ il)) ⟩
  c • Λ⁰ (G kpp) • ε • Λ⁰ (G kki) • c′
    ≈⟨ back c (back _ left-unit) ⟩
  c • Λ⁰ (G kpp) • Λ⁰ (G kki) • c′
    ≈⟨ back c (sym assoc) ⟩
  c • (Λ⁰ (G kpp) • Λ⁰ (G kki)) • c′
    ≈⟨ back c (front c′ (sym (hom⁰ (G kpp) (G kki)))) ⟩
  c • Λ⁰ (G kpp • G kki) • c′
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  τ A • (τ x₀ • Λ⁰ (G kpp • G kki) • τ (x₀ ⁻¹)) • τ (A ⁻¹)
    ≈⟨ back _ (front _ (cong (≡→ (τ-bot x₀₄)) (back _ (bot-inv x₀₄)))) ⟩
  τ A • ((τ x₀₄ ↓ᵏ 1) • Λ⁰ (G kpp • G kki) • (τ (x₀₄ ⁻¹) ↓ᵏ 1)) • τ (A ⁻¹)
    ≈⟨ back _ (front _ (conj⁰ (τ x₀₄) (τ (x₀₄ ⁻¹)) (G kpp • G kki) (aff⇒ (Inv.inverseʳ 4 {x₀₄})))) ⟩
  τ A • Λ⁰ (τ x₀₄ • (G kpp • G kki) • τ (x₀₄ ⁻¹)) • τ (A ⁻¹)
    ≈⟨ back _ (front _ (transport⁰ ok {τ x₀₄ • (G kpp • G kki) • τ (x₀₄ ⁻¹)} {G kki}
                         (c4 {τ x₀₄ • (G kpp • G kki) • τ (x₀₄ ⁻¹)} {G kki} sem-x))) ⟩
  τ A • Λ⁰ (G kki) • τ (A ⁻¹) ∎
  where
  A : B.Circuit 5
  A = α p q

  c c′ : Circuit 5
  c  = τ (A • x₀)
  c′ = τ ((A • x₀) ⁻¹)

  il : c′ • c ≈ ε
  il = embed (aff⇒ (Inv.inverseˡ 5 {A • x₀}))

  -- A x₀ sends 0 and e₀ to q and p.
  h0 : fn (α q p) 0ᵛ ≡ fn (A • x₀) 0ᵛ
  h0 = Eq.trans (at-o′ q p)
         (Eq.sym (Eq.trans (fn-• A x₀ 0ᵛ)
           (Eq.trans (Eq.cong (fn A) (fn-bm x₀ ze)) (at-e′ p q ne))))

  h1 : fn (α q p) e₀ ≡ fn (A • x₀) e₀
  h1 = Eq.trans (at-e′ q p (λ e → ne (Eq.sym e)))
         (Eq.sym (Eq.trans (fn-• A x₀ e₀)
           (Eq.trans (Eq.cong (fn A) (fn-bm x₀ (true ∷ᵥ ze))) (at-o′ p q))))

  to : (V : Kind) → gad₅ V q p ≈ c • Λ⁰ (G V) • c′
  to V = cind V (α q p) (A • x₀) h0 h1

------------------------------------------------------------------------
-- Gadgets as words over P′

private
  cd : Fin 32 → Bits 5
  cd = E5.cod

  -- The hybrid's block on (a , b): its letter when b comes first, and
  -- otherwise iZ on (b , a) times the block on (b , a).
  kw : (a b : Fin 32) → Tri (b < a) (b ≡ a) (a < b) → Word (GenP 32)
  kw a b (tri< _ _ _) = kd a b
  kw a b (tri≈ _ _ _) = ε
  kw a b (tri> _ _ _) = [ pp b a ]ʷ • kd b a

gw′ : Gd → Word (GenP 32)
gw′ (gd kpp a b)  = [ pp a b ]ʷ
gw′ (gd krot a b) = xd a a b
gw′ (gd kki a b)  = kw a b (<-cmp b a)

∏′ : List Gd → Word (GenP 32)
∏′ []      = ε
∏′ (g ∷ L) = gw′ g • ∏′ L

private
  one-pp : ∀ a b (e : Dec (a ≡ b)) → a ≢ b → Dg (pts (ppL a b e)) ≈ gad₅ kpp (cd a) (cd b)
  one-pp a b (yes ab) ne = ⊥-elim (ne ab)
  one-pp a b (no _)   ne = right-unit

  one-rot< : ∀ a b (e₁ : Dec (a ≡ a)) (e₂ : Dec (a ≡ b)) →
             Dg (pts (pxL a a b e₁ e₂)) ≈ gad₅ krot (cd a) (cd b)
  one-rot< a b (yes _) _ = right-unit
  one-rot< a b (no ne) _ = ⊥-elim (ne Eq.refl)

  one-rot> : ∀ a b (e₁ : Dec (a ≡ b)) (e₂ : Dec (a ≡ a)) → a ≢ b →
             Dg (pts (pxL a b a e₁ e₂)) ≈ gad₅ krot (cd a) (cd b)
  one-rot> a b (yes ab) _       ne = ⊥-elim (ne ab)
  one-rot> a b (no _)   (yes _) ne = right-unit
  one-rot> a b (no _)   (no aa) ne = ⊥-elim (aa Eq.refl)

  one-rot : ∀ a b (t : Tri (a < b) (a ≡ b) (b < a)) → a ≢ b →
            Dg (pts (GL (xd a a b))) ≈ gad₅ krot (cd a) (cd b)
  one-rot a b (tri< lt _ _) ne =
    trans (≡→ (Eq.cong (Dg ∘ pts ∘ GL) (xd-lt a a b lt))) (one-rot< a b (a ≟ a) (a ≟ b))
  one-rot a b (tri≈ _ e _)  ne = ⊥-elim (ne e)
  one-rot a b (tri> _ _ gt) ne =
    trans (≡→ (Eq.cong (Dg ∘ pts ∘ GL) (xd-gt a b a gt))) (one-rot> a b (a ≟ b) (a ≟ a) ne)

  one-kiL : ∀ a b (e : Dec (b ≡ b)) → Dg (pts (kiL b a b e)) ≈ gad₅ kki (cd a) (cd b)
  one-kiL a b (yes _) = right-unit
  one-kiL a b (no ne) = ⊥-elim (ne Eq.refl)

  one-resp : ∀ a b (e₁ : Dec (b ≡ a)) (e₂ : Dec (a ≡ a)) → a ≢ b →
             Dg (pts (ppL b a e₁ ++ kiL a b a e₂)) ≈ gad₅ kki (cd a) (cd b)
  one-resp a b (yes ba) _       ne = ⊥-elim (ne (Eq.sym ba))
  one-resp a b (no _)   (no aa) ne = ⊥-elim (aa Eq.refl)
  one-resp a b (no _)   (yes _) ne =
    trans (back _ right-unit) (respell (cd a) (cd b) (λ e → ne (E5.cod-inj e)))

  one-ki : ∀ a b (t : Tri (b < a) (b ≡ a) (a < b)) → a ≢ b →
           Dg (pts (GL (kw a b t))) ≈ gad₅ kki (cd a) (cd b)
  one-ki a b (tri< lt _ _) ne =
    trans (≡→ (Eq.cong (Dg ∘ pts ∘ GL) (kd-lt a b lt))) (one-kiL a b (b ≟ b))
  one-ki a b (tri≈ _ e _)  ne = ⊥-elim (ne (Eq.sym e))
  one-ki a b (tri> _ _ gt) ne =
    trans (≡→ (Eq.cong (λ w → Dg (pts (GL ([ pp b a ]ʷ • w)))) (kd-lt b a gt)))
      (one-resp a b (b ≟ a) (a ≟ a) ne)

  Ne : Gd → Set
  Ne g = i g ≢ j g

one : (g : Gd) → i g ≢ j g → Dg (pts (GL (gw′ g))) ≈ gad₅ (kind g) (cd (i g)) (cd (j g))
one (gd kpp a b)  ne = one-pp a b (a ≟ b) ne
one (gd krot a b) ne = one-rot a b (<-cmp a b) ne
one (gd kki a b)  ne = one-ki a b (<-cmp b a) ne

prod : (Gs : List Gd) → All Ne Gs → Dg (pts (GL (∏′ Gs))) ≈ Dg (pts Gs)
prod []       []         = refl
prod (g ∷ Gs) (ne ∷ nes) = begin
  Dg (pts (GL (gw′ g) ++ GL (∏′ Gs)))
    ≈⟨ ≡→ (Eq.cong Dg (pts-++ (GL (gw′ g)) (GL (∏′ Gs)))) ⟩
  Dg (pts (GL (gw′ g)) ++ pts (GL (∏′ Gs)))
    ≈⟨ Dg-++ (pts (GL (gw′ g))) (pts (GL (∏′ Gs))) ⟩
  Dg (pts (GL (gw′ g))) • Dg (pts (GL (∏′ Gs)))
    ≈⟨ cong (one g ne) (prod Gs nes) ⟩
  gad₅ (kind g) (cd (i g)) (cd (j g)) • Dg (pts Gs) ∎

------------------------------------------------------------------------
-- K on wire 4

-- The swap of the wires 3 and 4, as an affine circuit, and the renaming
-- of the indices it makes.
π : B.Circuit 5
π = [ B.gate₂ B.SWAP-gate B.↥ B.↥ B.↥ ]ʷ

K₃ : Circuit 4
K₃ = [ gate₁ K-gate ↥ ↥ ↥ ]ʷ

σ : Fin 32 → Fin 32
σ a = E5.idx (bm π (cd a))

renσ : Gd → Gd
renσ (gd V a b) = gd V (σ a) (σ b)

private
  pts-σ : ∀ Gs → pts (map renσ Gs) ≡ mapβ π (pts Gs)
  pts-σ []                = Eq.refl
  pts-σ (gd V a b ∷ Gs) =
    Eq.cong₂ _∷_ (Eq.cong₂ (λ x y → V , x , y) (E5.cod-idx (bm π (cd a))) (E5.cod-idx (bm π (cd b))))
      (pts-σ Gs)

  vne : ∀ g → Valid g → Ne g
  vne (gd kpp a b)  ne = ne
  vne (gd krot a b) ne = ne
  vne (gd kki a b)  lt = λ e → Data.Fin.Properties.<⇒≢ lt (Eq.sym e)

  valid-ne : ∀ Gs → All Valid Gs → All Ne Gs
  valid-ne []       []        = []
  valid-ne (g ∷ Gs) (vg ∷ vs) = vne g vg ∷ valid-ne Gs vs

  dist-pts : ∀ Gs → All Ne Gs → All Dist (pts Gs)
  dist-pts []       []         = []
  dist-pts (g ∷ Gs) (ne ∷ nes) = (λ e → ne (E5.cod-inj e)) ∷ dist-pts Gs nes

  σ-inj : ∀ {a b} → σ a ≡ σ b → a ≡ b
  σ-inj {a} {b} e = E5.cod-inj
    (Eq.trans (Eq.sym (bm-inv π (cd a))) (Eq.trans (Eq.cong (bm (π ⁻¹)) (E5.idx-inj {bm π (cd a)} {bm π (cd b)} e)) (bm-inv π (cd b))))

  ne-σ : ∀ Gs → All Ne Gs → All Ne (map renσ Gs)
  ne-σ []                []         = []
  ne-σ (gd V a b ∷ Gs) (ne ∷ nes) = (λ e → ne (σ-inj e)) ∷ ne-σ Gs nes

  -- On the old theory: K on wire 4 is K on wire 3 between two swaps.
  K₄-swap : 5 ⊢ [ gate₁ K-gate ↥ ↥ ↥ ↥ ]ʷ ≈ τ π • (K₃ ↓ᵏ 1) • τ (π ⁻¹)
  K₄-swap =
    T5.trans (T5.sym T5.right-unit)
      (T5.trans (T5.back _ (T5.sym sw²))
        (T5.trans (T5.sym T5.assoc)
          (T5.trans (T5.front _ L3)
            (T5.trans T5.assoc (T5.back _ (T5.back _ (T5.sym inv-π)))))))
    where
    L3 : 5 ⊢ K ↑ ↑ ↑ ↑ • Swap ↑ ↑ ↑ ≈ Swap ↑ ↑ ↑ • K ↑ ↑ ↑
    L3 = lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ (swap-K {0})))

    sw² : 5 ⊢ Swap ↑ ↑ ↑ • Swap ↑ ↑ ↑ ≈ ε
    sw² = lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ (Swap² {0})))

    inv-π : 5 ⊢ τ (π ⁻¹) ≈ τ π
    inv-π =
      T5.trans (T5.sym T5.right-unit)
        (T5.trans (T5.back _ (T5.sym sw²))
          (T5.trans (T5.sym T5.assoc)
            (T5.trans (T5.front _ (aff⇒ (Inv.inverseˡ 5 {π}))) T5.left-unit)))

wK : Word (GenP 32)
wK = ∏′ (map renσ (GL (wd K₃)))

K₄-dec : [ gate₁ K-gate ↥ ↥ ↥ ↥ ]ʷ ≈ (d ʷ) wK
K₄-dec = begin
  [ gate₁ K-gate ↥ ↥ ↥ ↥ ]ʷ               ≈⟨ embed K₄-swap ⟩
  τ π • (K₃ ↓ᵏ 1) • τ (π ⁻¹)               ≈⟨ back _ (front _ (sym (below K₃))) ⟩
  τ π • (d ʷ) (wd K₃) • τ (π ⁻¹)           ≈⟨ back _ (front _ (dʷ-D (wd K₃))) ⟩
  τ π • Dg (pts Gs) • τ (π ⁻¹)             ≈⟨ conjD π (pts Gs) (dist-pts Gs nes) ⟩
  Dg (mapβ π (pts Gs))                     ≈⟨ ≡→ (Eq.cong Dg (Eq.sym (pts-σ Gs))) ⟩
  Dg (pts (map renσ Gs))                   ≈⟨ sym (prod (map renσ Gs) (ne-σ Gs nes)) ⟩
  Dg (pts (GL wK))                         ≈⟨ sym (dʷ-D wK) ⟩
  (d ʷ) wK ∎
  where
  Gs : List Gd
  Gs = GL (wd K₃)

  nes : All Ne Gs
  nes = valid-ne Gs (valid-GL (wd K₃))
