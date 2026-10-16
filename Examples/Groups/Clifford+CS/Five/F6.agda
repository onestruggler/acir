------------------------------------------------------------------------
-- Presentations of groups
--
-- (F6): the gadget of the affine decoding commutes with CX from wire 1
-- onto wire 4
--
-- The gadget on five wires is λ⁰₄ of a four-wire circuit.  For the
-- twisted commutator g⁻¹ S⁻¹ g S, with G₄(g^±1) four-wire circuits for
-- the controlled g^±1 (`Gm`, `Gp`), the joint paper's proof (Lemma F6)
-- goes through with the control wire 4 alone, where the paper also uses
-- the controlled functor at wire 1 with wire 4 borrowed:
--
--  (i)   λ⁰(Gm S⁻¹ Gp S) = Gm · λ⁰(S⁻¹) · Gp · λ⁰(S): split Gm, Gp by
--        (F5), move their λ¹ parts right by (F4), and cancel them by
--        transport of Gm Gp = ε;
--  (ii)  A = CX(1→4) is K₄ λ¹(Z₁) K₄ i, and λ¹(Z₁) passes a four-wire W
--        that commutes with Z₁ ((F5), (F4), transport), K₄ and i pass
--        anything on wires 0..3; so A passes Gm and Gp;
--  (iii) A λ⁰(S) A = E λ⁰(S) and A λ⁰(S³) A = λ⁰(S³) E′ (windows), with
--        E = CS01⁻¹ CCZ014, E′ = CS01 CCZ014 and E′ E = ε; E and E′ pass
--        Gp, the CCZ being λ¹(CZ01) (the joint paper's SB2);
--  (iv)  hence A (Gm λ⁰(S³) Gp λ⁰(S)) A = Gm λ⁰(S³) Gp λ⁰(S).
--
-- The hypotheses on Gm, Gp are four-wire facts, each one evaluation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Word.Base using (ε)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁ ; λᵈ)
open import Examples.Groups.Clifford+CS.Five.Transport using (AxOk)

module Examples.Groups.Clifford+CS.Five.F6
  -- The λ-calculus at control wire 4 for generators (Five.Calc).
  (F4ᵍ : ∀ g h → ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ h ∷ [] ⟫ʷ ≈ ⟪ λ₁ h ∷ X4 ∷ λ₁ g ∷ X4 ∷ [] ⟫ʷ)
  (F5ᵍ : ∀ g → ⟪ λᵈ g ∷ [] ⟫ʷ ≈ ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ g ∷ [] ⟫ʷ)
  (x4x4 : ⟪ X4 ∷ X4 ∷ [] ⟫ʷ ≈ ε)
  -- Transport.
  (ok : AxOk)
  -- The window lemmas of Five.F6Ax and the joint paper's SB2.
  (cx14ˡ : ⟪ CX14 ∷ [] ⟫ʷ ≈ ⟪ K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ [] ⟫ʷ)
  (w1ˡ : ⟪ CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ [] ⟫ʷ ≈ ⟪ CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ [] ⟫ʷ)
  (w2ˡ : ⟪ CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ [] ⟫ʷ ≈
         ⟪ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ [] ⟫ʷ)
  (aaˡ : ⟪ CX14 ∷ CX14 ∷ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ)
  (eeˡ : ⟪ CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ)
  (sb2ˡ : ⟪ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [] ⟫ʷ ≈ ⟪ CCZ014 ∷ [] ⟫ʷ)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
  using (Circuit ; S ; K ; CS ; iI ; _↑ ; _↓ᵏ_ ; _↑ᵏ_ ; _⊢_≈_)
open import Examples.Groups.Clifford+CS.Weakening using (weaken)
open import Examples.Groups.Clifford+CS.Five.Rules using (embed)
open import Examples.Groups.Clifford+CS.Five.Transport using (λʷ ; transport)
open import Examples.Groups.Clifford+CS.Five.Calc F4ᵍ F5ᵍ x4x4

Z₁ CZ₀₁ CSd₀₁ Sd : Circuit 4
Z₁    = (S • S) ↑
CZ₀₁  = CS • CS
CSd₀₁ = CS • CS • CS
Sd    = S • S • S

A Cs Cd E E′ K4w ιw : Circuit 5
A   = ⟪ CX14 ∷ [] ⟫ʷ
Cs  = Λ⁰ S
Cd  = Λ⁰ Sd
E   = ⟪ CS01⁻ ∷ CCZ014 ∷ [] ⟫ʷ
E′  = ⟪ CS01 ∷ CCZ014 ∷ [] ⟫ʷ
K4w = ⟪ K4 ∷ [] ⟫ʷ
ιw  = ⟪ ι ∷ [] ⟫ʷ

private
  sp : ∀ xs ys → ⟪ xs ++ ys ⟫ʷ ≈ ⟪ xs ⟫ʷ • ⟪ ys ⟫ʷ
  sp = ⟪⟫-++

  -- a • w ≈ w • a and b • w ≈ w • b give (a • b) • w ≈ w • (a • b).
  slide : ∀ {a b w : Circuit 5} → a • w ≈ w • a → b • w ≈ w • b → (a • b) • w ≈ w • (a • b)
  slide {a} {b} {w} ea eb = begin
    (a • b) • w   ≈⟨ assoc ⟩
    a • (b • w)   ≈⟨ back a eb ⟩
    a • (w • b)   ≈⟨ sym assoc ⟩
    (a • w) • b   ≈⟨ front b ea ⟩
    (w • a) • b   ≈⟨ assoc ⟩
    w • (a • b)   ∎

  -- From a • w ≈ w • a and a • a ≈ ε: a • w • a ≈ w.
  conj-out : ∀ {a w : Circuit 5} → a • w ≈ w • a → a • a ≈ ε → a • w • a ≈ w
  conj-out {a} {w} e aa = begin
    a • w • a     ≈⟨ sym assoc ⟩
    (a • w) • a   ≈⟨ front a e ⟩
    (w • a) • a   ≈⟨ assoc ⟩
    w • (a • a)   ≈⟨ back w aa ⟩
    w • ε         ≈⟨ right-unit ⟩
    w             ∎

------------------------------------------------------------------------
-- The window lemmas as circuits

aa : A • A ≈ ε
aa = aaˡ

w1 : A • Cs • A ≈ E • Cs
w1 = trans (sym (back A (sp (λ⁰ʷ S) (CX14 ∷ []))))
           (trans (w1ˡ) (sp (CS01⁻ ∷ CCZ014 ∷ []) (λ⁰ʷ S)))

w2 : A • Cd • A ≈ Cd • E′
w2 = trans (sym (back A (sp (λ⁰ʷ Sd) (CX14 ∷ []))))
           (trans (w2ˡ) (sp (λ⁰ʷ Sd) (CS01 ∷ CCZ014 ∷ [])))

ee : E′ • E ≈ ε
ee = trans (sym (sp (CS01 ∷ CCZ014 ∷ []) (CS01⁻ ∷ CCZ014 ∷ []))) (eeˡ)

-- A = K₄ λ¹(Z₁) K₄ i.
A-form : A ≈ K4w • Λ¹ Z₁ • K4w • ιw
A-form = trans (cx14ˡ)
               (trans (sp (K4 ∷ []) (λʷ Z₁ ++ (K4 ∷ ι ∷ [])))
                      (back K4w (trans (sp (λʷ Z₁) (K4 ∷ ι ∷ [])) (back (Λ¹ Z₁) (sp (K4 ∷ []) (ι ∷ []))))))

------------------------------------------------------------------------
-- Passing a circuit on wires 0..3

-- λ¹(Y) passes W when Y and W commute on four wires.
passΛ¹ : (Y W : Circuit 4) → 4 ⊢ Y • W ≈ W • Y → Λ¹ Y • (W ↓ᵏ 1) ≈ (W ↓ᵏ 1) • Λ¹ Y
passΛ¹ Y W h = begin
  Λ¹ Y • (W ↓ᵏ 1)                       ≈⟨ back _ (trans (sym (D-sp W)) (F5ʷ W)) ⟩
  Λ¹ Y • (Λ⁰ W • Λ¹ W)                ≈⟨ sym assoc ⟩
  (Λ¹ Y • Λ⁰ W) • Λ¹ W                ≈⟨ front _ (sym (F4ʷ W Y)) ⟩
  (Λ⁰ W • Λ¹ Y) • Λ¹ W                ≈⟨ assoc ⟩
  Λ⁰ W • (Λ¹ Y • Λ¹ W)                ≈⟨ back _ (sym (hom¹ Y W)) ⟩
  Λ⁰ W • Λ¹ (Y • W)                   ≈⟨ back _ (transport ok h) ⟩
  Λ⁰ W • Λ¹ (W • Y)                   ≈⟨ back _ (hom¹ W Y) ⟩
  Λ⁰ W • (Λ¹ W • Λ¹ Y)                ≈⟨ sym assoc ⟩
  (Λ⁰ W • Λ¹ W) • Λ¹ Y                ≈⟨ front _ (trans (sym (F5ʷ W)) (D-sp W)) ⟩
  (W ↓ᵏ 1) • Λ¹ Y                       ∎

passK4 : (W : Circuit 4) → K4w • (W ↓ᵏ 1) ≈ (W ↓ᵏ 1) • K4w
passK4 W = sym (embed (lowᵏ 4 W K))

passι : (W : Circuit 4) → ιw • (W ↓ᵏ 1) ≈ (W ↓ᵏ 1) • ιw
passι W = sym zc

-- A passes W when W commutes with Z₁.
passA : (W : Circuit 4) → 4 ⊢ Z₁ • W ≈ W • Z₁ → A • (W ↓ᵏ 1) ≈ (W ↓ᵏ 1) • A
passA W h = begin
  A • (W ↓ᵏ 1)                                ≈⟨ front _ A-form ⟩
  (K4w • Λ¹ Z₁ • K4w • ιw) • (W ↓ᵏ 1)         ≈⟨ slide (passK4 W) (slide (passΛ¹ Z₁ W h) (slide (passK4 W) (passι W))) ⟩
  (W ↓ᵏ 1) • (K4w • Λ¹ Z₁ • K4w • ιw)         ≈⟨ back _ (sym A-form) ⟩
  (W ↓ᵏ 1) • A                                ∎

-- CS01^±1 and CCZ014 pass W when CS01^±1 and CZ01 commute with it.
passCCZ : (W : Circuit 4) → 4 ⊢ CZ₀₁ • W ≈ W • CZ₀₁ → ⟪ CCZ014 ∷ [] ⟫ʷ • (W ↓ᵏ 1) ≈ (W ↓ᵏ 1) • ⟪ CCZ014 ∷ [] ⟫ʷ
passCCZ W h = begin
  ⟪ CCZ014 ∷ [] ⟫ʷ • (W ↓ᵏ 1)             ≈⟨ front _ (sym (sb2ˡ)) ⟩
  Λ¹ CZ₀₁ • (W ↓ᵏ 1)                     ≈⟨ passΛ¹ CZ₀₁ W h ⟩
  (W ↓ᵏ 1) • Λ¹ CZ₀₁                     ≈⟨ back _ (sb2ˡ) ⟩
  (W ↓ᵏ 1) • ⟪ CCZ014 ∷ [] ⟫ʷ             ∎

passE : (W : Circuit 4) → 4 ⊢ CSd₀₁ • W ≈ W • CSd₀₁ → 4 ⊢ CZ₀₁ • W ≈ W • CZ₀₁ →
        E • (W ↓ᵏ 1) ≈ (W ↓ᵏ 1) • E
passE W hs hz = slide (embed (weaken 1 hs)) (passCCZ W hz)

passE′ : (W : Circuit 4) → 4 ⊢ CS • W ≈ W • CS → 4 ⊢ CZ₀₁ • W ≈ W • CZ₀₁ →
         E′ • (W ↓ᵏ 1) ≈ (W ↓ᵏ 1) • E′
passE′ W hs hz = slide (embed (weaken 1 hs)) (passCCZ W hz)

------------------------------------------------------------------------
-- The twisted commutator

module Comm (Gm Gp : Circuit 4)
  (h-inv : 4 ⊢ Gm • Gp ≈ ε)
  (zm : 4 ⊢ Z₁ • Gm ≈ Gm • Z₁) (zp : 4 ⊢ Z₁ • Gp ≈ Gp • Z₁)
  (cs⁻p : 4 ⊢ CSd₀₁ • Gp ≈ Gp • CSd₀₁) (csp : 4 ⊢ CS • Gp ≈ Gp • CS)
  (czp : 4 ⊢ CZ₀₁ • Gp ≈ Gp • CZ₀₁)
  where

  Λ : Circuit 5
  Λ = Λ⁰ (Gm • Sd • Gp • S)

  -- (i)
  split : Λ ≈ (Gm ↓ᵏ 1) • Cd • (Gp ↓ᵏ 1) • Cs
  split = sym (begin
    (Gm ↓ᵏ 1) • Cd • (Gp ↓ᵏ 1) • Cs
      ≈⟨ cong (trans (sym (D-sp Gm)) (F5ʷ Gm)) (back Cd (front Cs (trans (sym (D-sp Gp)) (F5ʷ Gp)))) ⟩
    (a • b) • c • (d • e) • f
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
    a • (b • c) • d • e • f
      ≈⟨ back a (front _ (sym (F4ʷ Sd Gm))) ⟩
    a • (c • b) • d • e • f
      ≈⟨ back a (by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □) • □ • □) Eq.refl) ⟩
    a • c • (b • d) • e • f
      ≈⟨ back a (back c (front _ (sym (F4ʷ Gp Gm)))) ⟩
    a • c • (d • b) • e • f
      ≈⟨ back a (back c (by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl)) ⟩
    a • c • d • (b • e) • f
      ≈⟨ back a (back c (back d (front f (trans (sym (hom¹ Gm Gp)) (transport ok h-inv))))) ⟩
    a • c • d • ε • f
      ≈⟨ back a (back c (back d left-unit)) ⟩
    a • c • d • f
      ≈⟨ back a (back c (sym (hom⁰ Gp S))) ⟩
    a • c • Λ⁰ (Gp • S)
      ≈⟨ back a (sym (hom⁰ Sd (Gp • S))) ⟩
    a • Λ⁰ (Sd • Gp • S)
      ≈⟨ sym (hom⁰ Gm (Sd • Gp • S)) ⟩
    Λ ∎)
    where
    a = Λ⁰ Gm ; b = Λ¹ Gm ; c = Cd ; d = Λ⁰ Gp ; e = Λ¹ Gp ; f = Cs

  -- (ii)–(iv)
  conj : A • ((Gm ↓ᵏ 1) • Cd • (Gp ↓ᵏ 1) • Cs) • A ≈ (Gm ↓ᵏ 1) • Cd • (Gp ↓ᵏ 1) • Cs
  conj = begin
    A • (m • Cd • p • Cs) • A
      ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) ((□ • □) • □ • □ • □ • □) Eq.refl ⟩
    (A • m) • Cd • p • Cs • A
      ≈⟨ front _ (passA Gm zm) ⟩
    (m • A) • Cd • p • Cs • A
      ≈⟨ back _ (back Cd (sym left-unit)) ⟩
    (m • A) • Cd • ε • p • Cs • A
      ≈⟨ back _ (back Cd (front _ (sym aa))) ⟩
    (m • A) • Cd • (A • A) • p • Cs • A
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □ • □ • □) (□ • (□ • □ • □) • □ • □ • □ • □) Eq.refl ⟩
    m • (A • Cd • A) • A • p • Cs • A
      ≈⟨ back m (front _ w2) ⟩
    m • (Cd • E′) • A • p • Cs • A
      ≈⟨ back m (back _ (by-passoc (□ • □ • □ • □) ((□ • □) • □ • □) Eq.refl)) ⟩
    m • (Cd • E′) • (A • p) • Cs • A
      ≈⟨ back m (back _ (front _ (passA Gp zp))) ⟩
    m • (Cd • E′) • (p • A) • Cs • A
      ≈⟨ back m (back _ (by-passoc ((□ • □) • □ • □) (□ • □ • □ • □) Eq.refl)) ⟩
    m • (Cd • E′) • p • A • Cs • A
      ≈⟨ back m (back _ (back p w1)) ⟩
    m • (Cd • E′) • p • (E • Cs)
      ≈⟨ back m (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □) • □ • □) Eq.refl) ⟩
    m • Cd • (E′ • p) • E • Cs
      ≈⟨ back m (back Cd (front _ (passE′ Gp csp czp))) ⟩
    m • Cd • (p • E′) • E • Cs
      ≈⟨ back m (back Cd (by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl)) ⟩
    m • Cd • p • (E′ • E) • Cs
      ≈⟨ back m (back Cd (back p (front Cs ee))) ⟩
    m • Cd • p • ε • Cs
      ≈⟨ back m (back Cd (back p left-unit)) ⟩
    m • Cd • p • Cs ∎
    where
    m = Gm ↓ᵏ 1 ; p = Gp ↓ᵏ 1

  f6 : A • Λ ≈ Λ • A
  f6 = begin
    A • Λ                    ≈⟨ back A split ⟩
    A • X                    ≈⟨ sym right-unit ⟩
    (A • X) • ε              ≈⟨ back _ (sym aa) ⟩
    (A • X) • (A • A)        ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (A • X • A) • A          ≈⟨ front A conj ⟩
    X • A                    ≈⟨ front A (sym split) ⟩
    Λ • A                    ∎
    where X = (Gm ↓ᵏ 1) • Cd • (Gp ↓ᵏ 1) • Cs
