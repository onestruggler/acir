------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.7 at every width from five wires on
--
-- On 5 + m wires every gate is the decoding of a word over P′, given
-- completeness on 4 + m, so by CompleteStep.by-decodes it is the
-- decoding of its encoding (`d∘e`), and the induction step on the width
-- holds (`step`).  A gate either leaves the top wire idle, and is then
-- Halves.below, or reaches it (Transport.Shape): the scalar shifted all
-- the way up is the scalar (ω↑=ω, `topS≈`); S on the top wire is λ¹ of
-- the scalar and the CS on the top two wires λ¹ of S (Insert4's
-- λ¹-topS, λ¹-top1), both Halves.above; and K on the top wire is K on
-- the wire below between two swaps of the top two wires (`Ktop`, from
-- Swaps.swap-K), the swap an affine word (TopSwap.sw-aff), so
-- conjugating the decoding of K on the wire below by it moves each
-- gadget to the images of its two states (Hyper.D-eqv), which are again
-- the gadgets of letters of P′ (`one`, `prod`, after Five.K4) — the
-- hybrid's on (p , q) with p before q in the numbering, which no letter
-- has, being iZ on (q , p) times the hybrid's on (q , p) (`respell-D`,
-- by HyperCanon.lemma-sem from Respell.respell).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.Lemma87
  (c4 : Complete 4) (c₅ : Completeᵧ 5)
  (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; _<_) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (_≟_ ; <-cmp)
open import Data.List using (List ; [] ; _∷_ ; map ; _++_)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat using (zero ; z≤n ; s≤s)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₂₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; _∙_ ; ε∙ ; ~-trans ; ~-sym ; ~-refl ; ∙-cong ; ∙-assoc)
open import Examples.Groups.Clifford+CS.Syntactics
  using (Gen ; gate₀ ; gate₁ ; gate₂ ; _↥ ; _↑ ; I-gate ; S-gate ; K-gate ; CS-gate ; K ; Swap ;
         _VRel,_===_ ; _⊢_≈_ ; lemma-cong↑ ; ω↑=ω)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; _↧)
open import Examples.Groups.Clifford+CS.Swaps using (Swap² ; swap-K)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ ; Swᵗ ; Sᵗ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_ ; embed)
open import Examples.Groups.Clifford+CS.Stable.Transport using (View ; low ; high ; view ; Shape ; sS ; s1 ; s2 ; high-shape)
open import Examples.Groups.Clifford+CS.Stable.Insert4 using (topS ; top1 ; top2 ; λ¹-topS ; λ¹-top1 ; Zᵗ)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; kpp ; krot ; kki)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp)
open import Examples.Groups.Clifford+CS.Stable.GadgetFacts c4 c₅ f4 f5 tr F
  using (D ; Ne ; D-sem ; lemma-sem ; IW ; ind₄ ; f6) renaming (sym to gsym)
open import Examples.Groups.Clifford+CS.Stable.Hyper c4 f4 f5 tr Kind (Facts4.G F) ind₄ f6 gsym
  using (D-eqv ; ren)
import Examples.Groups.Clifford+CS.Stable.DWDGen c4 c₅ f4 f5 tr F as W
import Examples.Groups.Clifford+CS.Stable.Halves c4 c₅ f4 f5 tr F as H
import Examples.Groups.Clifford+CS.Stable.CompleteStep c4 c₅ f4 f5 tr F as CSt
import Examples.Groups.Clifford+CS.Stable.Respell c4 f4 f5 tr F as Rs
import Examples.Groups.Clifford+CS.Stable.TopSwap as TopSwap
import Examples.Groups.Clifford+CS.Stable.DecSem as DecSem
import Examples.Groups.Clifford+CS.Five.Decode as Decode
import Examples.Groups.Clifford+CS.Encoding as Encoding
import Examples.Groups.Clifford+CS.Auxiliary.Template as Template
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Affine.Circuits as Circuits

------------------------------------------------------------------------
-- The gates on the top wire, in the old theory

-- The scalar shifted all the way up is the scalar.
topS≈ : ∀ k → (suc k) ⊢ [ topS k ]ʷ ≈ [ gate₀ I-gate ]ʷ
topS≈ zero    = PB.axiom (ω↑=ω I-gate)
topS≈ (suc k) = PB.trans (lemma-cong↑ [ topS k ]ʷ [ gate₀ I-gate ]ʷ (topS≈ k)) (PB.axiom (ω↑=ω I-gate))

-- S on the top wire.
top1S≡ : ∀ k → [ top1 k S-gate ]ʷ ≡ Sᵗ k
top1S≡ zero    = Eq.refl
top1S≡ (suc k) = Eq.cong _↑ (top1S≡ k)

-- The CS on the top two wires.
top2≡ : ∀ k → [ top2 k CS-gate ]ʷ ≡ Zᵗ k S-gate
top2≡ zero    = Eq.refl
top2≡ (suc k) = Eq.cong _↑ (top2≡ k)

-- K on the top wire is K on the wire below between two swaps.
Ktop : ∀ k → (₂₊ k) ⊢ [ top1 (suc k) K-gate ]ʷ ≈ Swᵗ k • [ top1 k K-gate ↧ ]ʷ • Swᵗ k
Ktop zero    = begin
  K ↑                    ≈⟨ sym right-unit ⟩
  K ↑ • ε                ≈⟨ back _ (sym Swap²) ⟩
  K ↑ • (Swap • Swap)    ≈⟨ sym assoc ⟩
  (K ↑ • Swap) • Swap    ≈⟨ front _ swap-K ⟩
  (Swap • K) • Swap      ≈⟨ assoc ⟩
  Swap • K • Swap ∎
  where open Tools (2 VRel,_===_)
Ktop (suc k) = lemma-cong↑ _ _ (Ktop k)

------------------------------------------------------------------------
-- Lemma 8.7 on 5 + m wires

module _ (m : ℕ) (c : Completeᵧ (₄₊ m)) where
  private
    n : ℕ
    n = suc (₄₊ m)

    module D1 = Decode (suc m)
    module E1 = Encoding (suc m)
    module L1 = W.Lits (suc m)
    module A₁ = Theory (₄₊ m)
    module Al₁ = Alpha (₄₊ m)
    module C₁ = Circuits (suc m) c4
    module TS = TopSwap m c4
    module DS = DecSem (suc m) c4
    open Template E1.N′ using (xd)
    open Tools (n YVRel,_===_)

    ≡→≈ : ∀ {a b : Circuit n} → a ≡ b → n ⊢ᵧ a ≈ b
    ≡→≈ Eq.refl = refl

    cd : Fin E1.N → _
    cd = E1.cod

    toLit = L1.toLit

  ------------------------------------------------------------------------
  -- Gadgets as words over P′

  private
    -- A decoded word with its letters cut at a concatenation.
    D-++ : ∀ (ℓ₁ ℓ₂ : List _) → n ⊢ᵧ D (suc m) (ℓ₁ ++ ℓ₂) ≈ D (suc m) ℓ₁ • D (suc m) ℓ₂
    D-++ []                ℓ₂ = sym left-unit
    D-++ ((κ , p , q) ∷ ℓ₁) ℓ₂ = trans (cong refl (D-++ ℓ₁ ℓ₂)) (sym assoc)

    -- The hybrid's gadget on (p , q) is iZ on (q , p) times the hybrid's
    -- on (q , p).
    respell-D : ∀ (p q : Vec Bool n) → p ≢ q →
                n ⊢ᵧ D (suc m) ((kpp , q , p) ∷ (kki , q , p) ∷ []) ≈ D (suc m) ((kki , p , q) ∷ [])
    respell-D p q ne =
      lemma-sem m c w₁ w₂ (p ∷ q ∷ []) (s≤s z≤n) ((λ e → ne (Eq.sym e)) ∷ (λ e → ne (Eq.sym e)) ∷ []) (ne ∷ [])
        (~-trans {s = ⟦ D (suc m) ℓ₁ ⟧} {Rs.Pp q p ∙ (Rs.Ki q p ∙ ε∙)} {⟦ D (suc m) ℓ₂ ⟧}
          (D-sem (suc m) ℓ₁ ((λ e → ne (Eq.sym e)) ∷ (λ e → ne (Eq.sym e)) ∷ []))
          (~-trans {s = Rs.Pp q p ∙ (Rs.Ki q p ∙ ε∙)} {(Rs.Pp q p ∙ Rs.Ki q p) ∙ ε∙} {⟦ D (suc m) ℓ₂ ⟧}
            (~-sym {s = (Rs.Pp q p ∙ Rs.Ki q p) ∙ ε∙} {Rs.Pp q p ∙ (Rs.Ki q p ∙ ε∙)} (∙-assoc (Rs.Pp q p) (Rs.Ki q p) ε∙))
            (~-trans {s = (Rs.Pp q p ∙ Rs.Ki q p) ∙ ε∙} {Rs.Ki p q ∙ ε∙} {⟦ D (suc m) ℓ₂ ⟧}
              (∙-cong {s = Rs.Pp q p ∙ Rs.Ki q p} {s' = Rs.Ki p q} {t = ε∙} {t' = ε∙}
                (~-sym {s = Rs.Ki p q} {Rs.Pp q p ∙ Rs.Ki q p} (Rs.respell (suc m) p q ne)) (~-refl ε∙))
              (~-sym {s = ⟦ D (suc m) ℓ₂ ⟧} {Rs.Ki p q ∙ ε∙} (D-sem (suc m) ℓ₂ (ne ∷ []))))))
      where
      w₁ w₂ : IW 2
      w₁ = (kpp , sF 0F , 0F) ∷ (kki , sF 0F , 0F) ∷ []
      w₂ = (kki , 0F , sF 0F) ∷ []
      ℓ₁ ℓ₂ : List _
      ℓ₁ = (kpp , q , p) ∷ (kki , q , p) ∷ []
      ℓ₂ = (kki , p , q) ∷ []

    -- The hybrid's block on (a , b): its letter when b comes first, and
    -- otherwise iZ on (b , a) times the block on (b , a).
    kw : (a b : Fin E1.N) → Tri (b < a) (b ≡ a) (a < b) → Word (GenP E1.N)
    kw a b (tri< _ _ _) = D1.kd a b
    kw a b (tri≈ _ _ _) = ε
    kw a b (tri> _ _ _) = [ pp b a ]ʷ • D1.kd b a

    gw′ : D1.Gd → Word (GenP E1.N)
    gw′ (D1.gd kpp a b)  = [ pp a b ]ʷ
    gw′ (D1.gd krot a b) = xd a a b
    gw′ (D1.gd kki a b)  = kw a b (<-cmp b a)

    ∏′ : List D1.Gd → Word (GenP E1.N)
    ∏′ []      = ε
    ∏′ (g ∷ L) = gw′ g • ∏′ L

    Dw : Word (GenP E1.N) → Circuit n
    Dw w = D (suc m) (map toLit (D1.GL w))

    one-pp : ∀ a b (e : Dec (a ≡ b)) → a ≢ b →
             D (suc m) (map toLit (D1.ppL a b e)) ≈ D (suc m) (toLit (D1.gd kpp a b) ∷ [])
    one-pp a b (yes ab) ne = ⊥-elim (ne ab)
    one-pp a b (no _)   ne = refl

    one-rot< : ∀ a b (e₁ : Dec (a ≡ a)) (e₂ : Dec (a ≡ b)) →
               D (suc m) (map toLit (D1.pxL a a b e₁ e₂)) ≈ D (suc m) (toLit (D1.gd krot a b) ∷ [])
    one-rot< a b (yes _) _ = refl
    one-rot< a b (no ne) _ = ⊥-elim (ne Eq.refl)

    one-rot> : ∀ a b (e₁ : Dec (a ≡ b)) (e₂ : Dec (a ≡ a)) → a ≢ b →
               D (suc m) (map toLit (D1.pxL a b a e₁ e₂)) ≈ D (suc m) (toLit (D1.gd krot a b) ∷ [])
    one-rot> a b (yes ab) _       ne = ⊥-elim (ne ab)
    one-rot> a b (no _)   (yes _) ne = refl
    one-rot> a b (no _)   (no aa) ne = ⊥-elim (aa Eq.refl)

    one-rot : ∀ a b (t : Tri (a < b) (a ≡ b) (b < a)) → a ≢ b →
              Dw (xd a a b) ≈ D (suc m) (toLit (D1.gd krot a b) ∷ [])
    one-rot a b (tri< lt _ _) ne =
      trans (≡→≈ (Eq.cong Dw (D1.xd-lt a a b lt))) (one-rot< a b (a ≟ a) (a ≟ b))
    one-rot a b (tri≈ _ e _)  ne = ⊥-elim (ne e)
    one-rot a b (tri> _ _ gt) ne =
      trans (≡→≈ (Eq.cong Dw (D1.xd-gt a b a gt))) (one-rot> a b (a ≟ b) (a ≟ a) ne)

    one-kiL : ∀ a b (e : Dec (b ≡ b)) →
              D (suc m) (map toLit (D1.kiL b a b e)) ≈ D (suc m) (toLit (D1.gd kki a b) ∷ [])
    one-kiL a b (yes _) = refl
    one-kiL a b (no ne) = ⊥-elim (ne Eq.refl)

    one-resp : ∀ a b (e₁ : Dec (b ≡ a)) (e₂ : Dec (a ≡ a)) → a ≢ b →
               D (suc m) (map toLit (D1.ppL b a e₁ ++ D1.kiL a b a e₂)) ≈ D (suc m) (toLit (D1.gd kki a b) ∷ [])
    one-resp a b (yes ba) _       ne = ⊥-elim (ne (Eq.sym ba))
    one-resp a b (no _)   (no aa) ne = ⊥-elim (aa Eq.refl)
    one-resp a b (no _)   (yes _) ne = respell-D (cd a) (cd b) (λ e → ne (E1.cod-inj e))

    one-ki : ∀ a b (t : Tri (b < a) (b ≡ a) (a < b)) → a ≢ b →
             Dw (kw a b t) ≈ D (suc m) (toLit (D1.gd kki a b) ∷ [])
    one-ki a b (tri< lt _ _) ne =
      trans (≡→≈ (Eq.cong Dw (D1.kd-lt a b lt))) (one-kiL a b (b ≟ b))
    one-ki a b (tri≈ _ e _)  ne = ⊥-elim (ne (Eq.sym e))
    one-ki a b (tri> _ _ gt) ne =
      trans (≡→≈ (Eq.cong (λ w → Dw ([ pp b a ]ʷ • w)) (D1.kd-lt b a gt)))
        (one-resp a b (b ≟ a) (a ≟ a) ne)

    Ne₀ : D1.Gd → Set
    Ne₀ g = D1.i g ≢ D1.j g

    one : (g : D1.Gd) → Ne₀ g → Dw (gw′ g) ≈ D (suc m) (toLit g ∷ [])
    one (D1.gd kpp a b)  ne = one-pp a b (a ≟ b) ne
    one (D1.gd krot a b) ne = one-rot a b (<-cmp a b) ne
    one (D1.gd kki a b)  ne = one-ki a b (<-cmp b a) ne

    prod : (Gs : List D1.Gd) → All Ne₀ Gs → Dw (∏′ Gs) ≈ D (suc m) (map toLit Gs)
    prod []       []         = refl
    prod (g ∷ Gs) (ne ∷ nes) = begin
      D (suc m) (map toLit (D1.GL (gw′ g) ++ D1.GL (∏′ Gs)))
        ≈⟨ ≡→≈ (Eq.cong (D (suc m)) (map-++ toLit (D1.GL (gw′ g)) (D1.GL (∏′ Gs)))) ⟩
      D (suc m) (map toLit (D1.GL (gw′ g)) ++ map toLit (D1.GL (∏′ Gs)))
        ≈⟨ D-++ (map toLit (D1.GL (gw′ g))) (map toLit (D1.GL (∏′ Gs))) ⟩
      Dw (gw′ g) • Dw (∏′ Gs)
        ≈⟨ cong (one g ne) (prod Gs nes) ⟩
      D (suc m) (toLit g ∷ []) • D (suc m) (map toLit Gs)
        ≈⟨ front _ right-unit ⟩
      D (suc m) (toLit g ∷ map toLit Gs) ∎

  ------------------------------------------------------------------------
  -- K on the top wire

  private
    K₃ : Circuit (₄₊ m)
    K₃ = [ top1 (₃₊ m) K-gate ]ʷ

    w₃ : Word (GenP E1.N)
    w₃ = H.wd m c K₃

    Gs : List D1.Gd
    Gs = D1.GL w₃

    -- The renaming of the indices the swap of the top two wires makes.
    σ : Fin E1.N → Fin E1.N
    σ a = E1.idx (Al₁.amapʷ TS.τsw (cd a))

    renσ : D1.Gd → D1.Gd
    renσ (D1.gd V a b) = D1.gd V (σ a) (σ b)

    σ-inj : ∀ {a b} → σ a ≡ σ b → a ≡ b
    σ-inj {a} {b} e = E1.cod-inj
      (Eq.trans (Eq.sym (DS.amapʷ-rev TS.τsw (cd a)))
        (Eq.trans (Eq.cong (Al₁.amapʷ (A₁.rev TS.τsw)) (E1.idx-inj {Al₁.amapʷ TS.τsw (cd a)} {Al₁.amapʷ TS.τsw (cd b)} e)) (DS.amapʷ-rev TS.τsw (cd b))))

    lits-σ : ∀ (L : List D1.Gd) → ren m TS.τsw (map toLit L) ≡ map toLit (map renσ L)
    lits-σ []                 = Eq.refl
    lits-σ (D1.gd V a b ∷ L) =
      Eq.cong₂ _∷_
        (Eq.cong₂ (λ x y → V , x , y)
          (Eq.sym (E1.cod-idx (Al₁.amapʷ TS.τsw (cd a)))) (Eq.sym (E1.cod-idx (Al₁.amapʷ TS.τsw (cd b)))))
        (lits-σ L)

    valid-ne : ∀ (L : List D1.Gd) → All D1.Valid L → All Ne₀ L
    valid-ne []      []       = []
    valid-ne (g ∷ L) (v ∷ vs) = L1.valid≢ g v ∷ valid-ne L vs

    ne-σ : ∀ (L : List D1.Gd) → All Ne₀ L → All Ne₀ (map renσ L)
    ne-σ []                 []         = []
    ne-σ (D1.gd V a b ∷ L) (ne ∷ nes) = (λ e → ne (σ-inj e)) ∷ ne-σ L nes

    wK : Word (GenP E1.N)
    wK = ∏′ (map renσ Gs)

    k-dec : n ⊢ᵧ [ top1 (₄₊ m) K-gate ]ʷ ≈ (W.dl m ʷ) wK
    k-dec = begin
      [ top1 (₄₊ m) K-gate ]ʷ
        ≈⟨ embed (Ktop (₃₊ m)) ⟩
      Swᵗ (₃₊ m) • top K₃ • Swᵗ (₃₊ m)
        ≈⟨ cong (embed TS.sw-aff) (cong (H.below m c K₃) (embed TS.sw-aff′)) ⟩
      C₁.⟪ TS.τsw ⟫ʷ • (W.dl m ʷ) w₃ • C₁.⟪ A₁.rev TS.τsw ⟫ʷ
        ≈⟨ back _ (front _ (W.dec-ʷ m w₃)) ⟩
      C₁.⟪ TS.τsw ⟫ʷ • D (suc m) (map toLit Gs) • C₁.⟪ A₁.rev TS.τsw ⟫ʷ
        ≈⟨ D-eqv m TS.τsw (map toLit Gs) (L1.ne-lit Gs (D1.valid-GL w₃)) ⟩
      D (suc m) (ren m TS.τsw (map toLit Gs))
        ≈⟨ ≡→≈ (Eq.cong (D (suc m)) (lits-σ Gs)) ⟩
      D (suc m) (map toLit (map renσ Gs))
        ≈⟨ sym (prod (map renσ Gs) (ne-σ Gs (valid-ne Gs (D1.valid-GL w₃)))) ⟩
      Dw wK
        ≈⟨ sym (W.dec-ʷ m wK) ⟩
      (W.dl m ʷ) wK ∎

  ------------------------------------------------------------------------
  -- Every gate

  private
    Goal : Gen n → Set
    Goal g = n ⊢ᵧ [ g ]ʷ ≈ (W.dl m ʷ) (E1.e g)

    shape : ∀ (g : Gen n) → Shape g → Goal g
    shape .(topS (₄₊ m)) sS =
      CSt.by-decodes m c (topS (₄₊ m)) (H.wd m c [ gate₀ I-gate ]ʷ)
        (trans (embed (topS≈ (₄₊ m))) (H.below m c [ gate₀ I-gate ]ʷ))
    shape .(top1 (₄₊ m) S-gate) (s1 S-gate) =
      CSt.by-decodes m c (top1 (₄₊ m) S-gate) (H.upw m c [ topS (₃₊ m) ]ʷ)
        (trans (≡→≈ (Eq.trans (top1S≡ (₄₊ m)) (Eq.sym (λ¹-topS m))))
               (sym (H.above m c [ topS (₃₊ m) ]ʷ)))
    shape .(top1 (₄₊ m) K-gate) (s1 K-gate) = CSt.by-decodes m c (top1 (₄₊ m) K-gate) wK k-dec
    shape .(top2 (₃₊ m) CS-gate) (s2 CS-gate) =
      CSt.by-decodes m c (top2 (₃₊ m) CS-gate) (H.upw m c [ top1 (₃₊ m) S-gate ]ʷ)
        (trans (≡→≈ (Eq.trans (top2≡ (₃₊ m)) (Eq.sym (λ¹-top1 m S-gate))))
               (sym (H.above m c [ top1 (₃₊ m) S-gate ]ʷ)))

    cases : ∀ (g : Gen n) (v : View g) → view g ≡ v → Goal g
    cases .(g′ ↧) (low g′) _ = CSt.by-decodes m c (g′ ↧) (H.wd m c [ g′ ]ʷ) (H.below m c [ g′ ]ʷ)
    cases g       (high .g) e = shape g (high-shape g e)

  -- Lemma 8.7 on 5 + m wires.
  d∘e : CSt.D∘E m
  d∘e g = cases g (view g) Eq.refl

-- The induction step on the width: completeness on 4 + m wires gives it
-- on 5 + m.
step : ∀ m → Completeᵧ (₄₊ m) → Completeᵧ (₄₊ (suc m))
step m c = CSt.complete-step m c (d∘e m c)
