------------------------------------------------------------------------
-- Presentations of groups
--
-- The two halves of 5 + m wires: words over P′ on 4 + m wires, renamed
--
-- Five.Halves at every width.  A word u over P′ on 4 + m wires, renamed
-- into the lower half of the numbering (Stable.GrayHalves.lo, whose
-- codes have the top bit 0), decodes to λ⁰ h for every h with u's
-- reading (`lower`): its gadgets lie on the hyperplane where the top
-- bit is 0, so it is λ⁰ of their decoding one width down (Hyper.D-top),
-- which is h by completeness on 4 + m.  Renamed into the upper half
-- (`hi`: the code with its top bit flipped and a 1 on top) it decodes to
-- λ¹ h when u reads as h conjugated by X on the wire 3 + m (`upper`):
-- X on the top two wires moves its gadgets into the hyperplane
-- (Hyper.D-eqv), the X below the top goes into λ⁰ (CalcW.conj⁰) and the
-- one on top turns λ⁰ into λ¹ (CalcW.λ⁰-X).  So a gate h on the wires
-- below the top is the decoding of a word: λ⁰ h λ¹ h is h with an idle
-- top wire, by (F5) (`below`); and λ¹ h alone is one (`above`).
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

module Examples.Groups.Clifford+CS.Stable.Halves
  (c4 : Complete 4) (c₅ : Completeᵧ 5)
  (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; fromℕ ; inject₁) renaming (zero to 0F ; suc to sF)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_ ; _∙_ ; ε∙ ; ~-trans ; ~-sym ; ~-reflexive ; ∙-cong ; Idₒ)
open import Examples.Groups.Clifford+CS.Syntactics using (Gen ; X)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ₒ ; ⟦⟧ₒ-ε)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ ; Xᵗ)
open import Examples.Groups.Clifford+CS.Networks using (bring₁)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_ ; embed)
open import Examples.Groups.Clifford+CS.Stable.Mixed using (Xᵗ²)
open import Examples.Groups.Clifford+CS.Stable.XPlace using (Xᵗ-placed)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (hom)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Stable.GadgetFacts c4 c₅ f4 f5 tr F using (D ; ind₄ ; f6) renaming (sym to gsym)
open import Examples.Groups.Clifford+CS.Stable.Hyper c4 f4 f5 tr Kind (Facts4.G F) ind₄ f6 gsym
  using (D-top ; D-eqv ; up ; ren)
import Examples.Groups.Clifford+CS.Stable.DWDGen c4 c₅ f4 f5 tr F as W
import Examples.Groups.Clifford+CS.Stable.GrayHalves as GrayHalves
import Examples.Groups.Clifford+CS.Stable.Ren as Ren
import Examples.Groups.Clifford+CS.Stable.CalcW as CalcW
import Examples.Groups.Clifford+CS.Five.Decode as Decode
import Examples.Groups.Clifford+CS.Encoding as Encoding
import Examples.Groups.Clifford+CS.Section8 as Section8
import Examples.Groups.Clifford+CS.BridgeGray as BridgeGray
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Affine.Circuits as Circuits
import Examples.Groups.Clifford+CS.Affine.Widen as Widen

module _ (m : ℕ) (c : Completeᵧ (₄₊ m)) where
  private
    module D0 = Decode m
    module D1 = Decode (suc m)
    module E0 = Encoding m
    module E1 = Encoding (suc m)
    module L0 = W.Lits m
    module L1 = W.Lits (suc m)
    module GH = GrayHalves m
    module RL = Ren m GH.lo GH.lo-inj GH.lo-mono
    module RH = Ren m GH.hi GH.hi-inj GH.hi-mono
    module CW = CalcW m (f4 m) (f5 m) (tr m)
    module BG0 = BridgeGray (₄₊ m)
    module S8 = Section8 m
    module A₀ = Theory (₃₊ m)
    module A₁ = Theory (₄₊ m)
    module Al₁ = Alpha (₄₊ m)
    module C₀ = Circuits m c4
    module C₁ = Circuits (suc m) c4
    module Wd = Widen m c4
    open Tools ((suc (₄₊ m)) YVRel,_===_)
    module T0 = Tools ((₄₊ m) YVRel,_===_)

    ≡→≈ : ∀ {a b : Circuit (suc (₄₊ m))} → a ≡ b → (suc (₄₊ m)) ⊢ᵧ a ≈ b
    ≡→≈ Eq.refl = refl

  ------------------------------------------------------------------------
  -- The encoding on 4 + m wires, kept opaque

  private
    eʷ-sem : (w : Circuit (₄₊ m)) → BG0.⟦ (E0.e ʷ) w ⟧PY ~ ⟦ w ⟧
    eʷ-sem [ g ]ʷ  = S8.e-sem g
    eʷ-sem ε       = ~-sym {s = ⟦_⟧ {₄₊ m} ε} {t = ε∙} (~-reflexive {l = 0} {0} {M = ⟦_⟧ₒ {₄₊ m} ε} {Idₒ} Eq.refl ⟦⟧ₒ-ε)
    eʷ-sem (u • v) =
      ~-trans {s = BG0.⟦ (E0.e ʷ) u ⟧PY ∙ BG0.⟦ (E0.e ʷ) v ⟧PY} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} {u = ⟦ u • v ⟧}
        (∙-cong {s = BG0.⟦ (E0.e ʷ) u ⟧PY} {s' = ⟦ u ⟧} {t = BG0.⟦ (E0.e ʷ) v ⟧PY} {t' = ⟦ v ⟧} (eʷ-sem u) (eʷ-sem v))
        (~-sym {s = ⟦ u • v ⟧} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} (hom u v))

  opaque
    enc : Circuit (₄₊ m) → Word (GenP E0.N)
    enc = E0.e ʷ

    enc-sem : (w : Circuit (₄₊ m)) → BG0.⟦ enc w ⟧PY ~ ⟦ w ⟧
    enc-sem = eʷ-sem

  ------------------------------------------------------------------------
  -- The lower half

  private
    lits-lo : ∀ (L : List D0.Gd) → map L1.toLit (map RL.renG L) ≡ up m (map L0.toLit L)
    lits-lo []                 = Eq.refl
    lits-lo (D0.gd V a b ∷ L) =
      Eq.cong₂ _∷_ (Eq.cong₂ (λ x y → V , x , y) (GH.cod-lo a) (GH.cod-lo b)) (lits-lo L)

  lower : ∀ (h : Circuit (₄₊ m)) (u : Word (GenP E0.N)) → BG0.⟦ u ⟧PY ~ ⟦ h ⟧ →
          (suc (₄₊ m)) ⊢ᵧ L1.decL (RL.renʷ u) ≈ λ⁰ʷ h
  lower h u e = begin
    D (suc m) (map L1.toLit (D1.GL (RL.renʷ u)))
      ≈⟨ ≡→≈ (Eq.cong (λ L → D (suc m) (map L1.toLit L)) (RL.GL-ren u)) ⟩
    D (suc m) (map L1.toLit (map RL.renG (D0.GL u)))
      ≈⟨ ≡→≈ (Eq.cong (D (suc m)) (lits-lo (D0.GL u))) ⟩
    D (suc m) (up m (map L0.toLit (D0.GL u)))
      ≈⟨ D-top m (map L0.toLit (D0.GL u)) ⟩
    λ⁰ʷ (L0.decL u)
      ≈⟨ CW.transport⁰ (c {L0.decL u} {h} (~-trans {s = ⟦ L0.decL u ⟧} {BG0.⟦ u ⟧PY} {⟦ h ⟧} (L0.decL-sem u) e)) ⟩
    λ⁰ʷ h ∎

  ------------------------------------------------------------------------
  -- The upper half

  private
    tp tq : A₁.Wire
    tp = fromℕ (₄₊ m)
    tq = inject₁ (fromℕ (₃₊ m))

    -- X on the wire 3 + m, on 4 + m wires.
    a : Circuit (₄₊ m)
    a = C₀.⟪ A₀.xL (fromℕ (₃₊ m)) ⟫

    aa : (₄₊ m) ⊢ᵧ a • a ≈ ε
    aa = embed (C₀.⟪⟫-sound A₀.x-sq)

    -- X on the top two wires, on 5 + m wires.
    β : Word A₁.Lt
    β = A₁.X tq • A₁.X tp

    x : Circuit (suc (₄₊ m))
    x = Xᵗ (₄₊ m)

    xx : x • x ≈ ε
    xx = embed (Xᵗ² (₄₊ m))

    Xtp : C₁.⟪ A₁.xL tp ⟫ ≈ x
    Xtp = embed (PB.sym (Xᵗ-placed (₄₊ m) (proj₁ (bring₁ tp)) (proj₂ (bring₁ tp))))

    Xtq : C₁.⟪ A₁.xL tq ⟫ ≈ top a
    Xtq = embed (Wd.ι*-top [ A₀.xL (fromℕ (₃₊ m)) ]ʷ)

    -- The bit maps.
    tg-top : ∀ {k} (v : Vec Bool k) (b : Bool) → A₁.toggle (v ∷ʳ b) (fromℕ k) ≡ v ∷ʳ not b
    tg-top []       b = Eq.refl
    tg-top (y ∷ v) b = Eq.cong (y ∷_) (tg-top v b)

    tg-inj : ∀ {k} (v : Vec Bool k) (b : Bool) (i : Fin k) → A₁.toggle (v ∷ʳ b) (inject₁ i) ≡ A₁.toggle v i ∷ʳ b
    tg-inj (y ∷ v) b 0F     = Eq.refl
    tg-inj (y ∷ v) b (sF i) = Eq.cong (y ∷_) (tg-inj v b i)

    tg-flp : ∀ {k} (v : Vec Bool (suc k)) → A₁.toggle v (fromℕ k) ≡ GH.flp v
    tg-flp {Data.Nat.zero}  (y ∷ []) = Eq.refl
    tg-flp {suc k}          (y ∷ v)  = Eq.cong (y ∷_) (tg-flp v)

    β-hi : ∀ (p : Vec Bool (₄₊ m)) → Al₁.amapʷ β (GH.flp p ∷ʳ true) ≡ p ∷ʳ false
    β-hi p =
      Eq.trans (Eq.cong (λ y → A₁.toggle y tq) (tg-top (GH.flp p) true))
        (Eq.trans (tg-inj (GH.flp p) false (fromℕ (₃₊ m)))
          (Eq.cong (_∷ʳ false) (Eq.trans (tg-flp (GH.flp p)) (GH.flp-flp p))))

    lits-hi : ∀ (L : List D0.Gd) → ren m β (map L1.toLit (map RH.renG L)) ≡ up m (map L0.toLit L)
    lits-hi []                 = Eq.refl
    lits-hi (D0.gd V a′ b′ ∷ L) =
      Eq.cong₂ _∷_
        (Eq.cong₂ (λ y z → V , y , z)
          (Eq.trans (Eq.cong (Al₁.amapʷ β) (GH.cod-hi a′)) (β-hi (E0.cod a′)))
          (Eq.trans (Eq.cong (Al₁.amapʷ β) (GH.cod-hi b′)) (β-hi (E0.cod b′))))
        (lits-hi L)

    il : C₁.⟪ A₁.rev β ⟫ʷ • C₁.⟪ β ⟫ʷ ≈ ε
    il = embed (C₁.⟪⟫-cong (A₁.rev-inv′ β))

    uncjβ : ∀ y → y ≈ C₁.⟪ A₁.rev β ⟫ʷ • (C₁.⟪ β ⟫ʷ • y • C₁.⟪ A₁.rev β ⟫ʷ) • C₁.⟪ β ⟫ʷ
    uncjβ y = begin
      y                                     ≈⟨ sym (trans (front _ il) left-unit) ⟩
      (r • t) • y                           ≈⟨ back _ (sym right-unit) ⟩
      (r • t) • (y • ε)                     ≈⟨ back _ (back y (sym il)) ⟩
      (r • t) • (y • (r • t))               ≈⟨ by-passoc ((□ • □) • (□ • (□ • □))) (□ • (□ • □ • □) • □) Eq.refl ⟩
      r • (t • y • r) • t ∎
      where
      t = C₁.⟪ β ⟫ʷ
      r = C₁.⟪ A₁.rev β ⟫ʷ

  upper : ∀ (h : Circuit (₄₊ m)) (u : Word (GenP E0.N)) → BG0.⟦ u ⟧PY ~ ⟦ a • h • a ⟧ →
          (suc (₄₊ m)) ⊢ᵧ L1.decL (RH.renʷ u) ≈ λ¹ʷ h
  upper h u e = begin
    D (suc m) (map L1.toLit (D1.GL (RH.renʷ u)))
      ≈⟨ ≡→≈ (Eq.cong (λ L → D (suc m) (map L1.toLit L)) (RH.GL-ren u)) ⟩
    D (suc m) K
      ≈⟨ uncjβ (D (suc m) K) ⟩
    C₁.⟪ A₁.rev β ⟫ʷ • (C₁.⟪ β ⟫ʷ • D (suc m) K • C₁.⟪ A₁.rev β ⟫ʷ) • C₁.⟪ β ⟫ʷ
      ≈⟨ back _ (front _ (D-eqv m β K ne)) ⟩
    C₁.⟪ A₁.rev β ⟫ʷ • D (suc m) (ren m β K) • C₁.⟪ β ⟫ʷ
      ≈⟨ ≡→≈ (Eq.cong (λ L → C₁.⟪ A₁.rev β ⟫ʷ • D (suc m) L • C₁.⟪ β ⟫ʷ) (lits-hi (D0.GL u))) ⟩
    C₁.⟪ A₁.rev β ⟫ʷ • D (suc m) (up m (map L0.toLit (D0.GL u))) • C₁.⟪ β ⟫ʷ
      ≈⟨ back _ (front _ (D-top m (map L0.toLit (D0.GL u)))) ⟩
    (C₁.⟪ A₁.xL tp ⟫ • C₁.⟪ A₁.xL tq ⟫) • λ⁰ʷ G • (C₁.⟪ A₁.xL tq ⟫ • C₁.⟪ A₁.xL tp ⟫)
      ≈⟨ cong (cong Xtp Xtq) (back _ (cong Xtq Xtp)) ⟩
    (x • top a) • λ⁰ʷ G • (top a • x)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    x • (top a • λ⁰ʷ G • top a) • x
      ≈⟨ back x (front x (CW.conj⁰ a a G aa)) ⟩
    x • λ⁰ʷ (a • G • a) • x
      ≈⟨ back x (front x (CW.λ⁰-X (a • G • a))) ⟩
    x • (x • λ¹ʷ (a • G • a) • x) • x
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (x • x) • λ¹ʷ (a • G • a) • (x • x)
      ≈⟨ cong xx (back _ xx) ⟩
    ε • λ¹ʷ (a • G • a) • ε
      ≈⟨ trans left-unit right-unit ⟩
    λ¹ʷ (a • G • a)
      ≈⟨ tr m aGa ⟩
    λ¹ʷ h ∎
    where
    K : List _
    K = map L1.toLit (map RH.renG (D0.GL u))

    ne = L1.ne-lit (map RH.renG (D0.GL u))
           (Eq.subst (All D1.Valid) (RH.GL-ren u) (D1.valid-GL (RH.renʷ u)))

    G : Circuit (₄₊ m)
    G = L0.decL u

    G≈ : (₄₊ m) ⊢ᵧ G ≈ a • h • a
    G≈ = c {G} {a • h • a} (~-trans {s = ⟦ G ⟧} {BG0.⟦ u ⟧PY} {⟦ a • h • a ⟧} (L0.decL-sem u) e)

    aGa : (₄₊ m) ⊢ᵧ a • G • a ≈ h
    aGa = T0.trans (T0.back a (T0.front a G≈))
            (T0.trans (T0.by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl)
              (T0.trans (T0.cong aa (T0.back h aa)) (T0.trans T0.left-unit T0.right-unit)))

  ------------------------------------------------------------------------
  -- A gate below the top wire

  -- The words: h's encoding on the lower half, and the encoding of h
  -- conjugated by X on the wire 3 + m on the upper.
  upw : Circuit (₄₊ m) → Word (GenP E1.N)
  upw h = RH.renʷ (enc (a • h • a))

  wd : Circuit (₄₊ m) → Word (GenP E1.N)
  wd h = RL.renʷ (enc h) • upw h

  above : ∀ (h : Circuit (₄₊ m)) → (suc (₄₊ m)) ⊢ᵧ (W.dl m ʷ) (upw h) ≈ λ¹ʷ h
  above h = trans (W.dec-ʷ m (upw h)) (upper h (enc (a • h • a)) (enc-sem (a • h • a)))

  below : ∀ (h : Circuit (₄₊ m)) → (suc (₄₊ m)) ⊢ᵧ top h ≈ (W.dl m ʷ) (wd h)
  below h = begin
    top h                                ≈⟨ CW.F5ʷ h ⟩
    λ⁰ʷ h • λ¹ʷ h                        ≈⟨ sym (cong (lower h (enc h) (enc-sem h)) (above h)) ⟩
    L1.decL (RL.renʷ (enc h)) • (W.dl m ʷ) (upw h)
                                         ≈⟨ sym (front _ (W.dec-ʷ m (RL.renʷ (enc h)))) ⟩
    (W.dl m ʷ) (RL.renʷ (enc h)) • (W.dl m ʷ) (upw h) ∎
