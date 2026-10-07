------------------------------------------------------------------------
-- Presentations of groups
--
-- One qubit: H, S and words over them
--
-- Conjugation by H and by S on Pauli codes (actᴳ, gate-act), the
-- operator opW of a word over {H, S} and its action actW on codes
-- (word-act), and the 24 words.  Part of PathSum.Hierarchy.OneQubit.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.OneQubit.Words (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _∨_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; -[1+_]; _+_; _-_; _*_; _%_; _/_)
open import Data.Integer.DivMod using (a≡a%n+[a/n]*n; n%d<d)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using
  (_≟_; *-zeroʳ; *-identityʳ; +-identityˡ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero; _<_; z≤n; s≤s)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; lookup)
  renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Nullary.Decidable using
  (⌊_⌋; yes; no; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using
  ([_]ᶻ; _=ᵇ_; =ᵇ-refl; =ᵇ-true; same; same-≗; ≔-here)
open import PathSum.Compose.Matrix M₀ using (if-⊛; ⊛-if)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong; zpow-≡; scale-exp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; -ᴬ_; _≐_; Σᴮ-cong; zpow; rot; rot-exp; rot-0; rot-anti;
   scale-injective; N)
  renaming (H to Hᶻ)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy M₀
open import PathSum.Hierarchy.Gates M₀
open import PathSum.Hierarchy.Levels M₀
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ--; ≡ᴺ-N)
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong)
open import PathSum.Ring.Laws M₀ using (⊛-comm)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

open import PathSum.Hierarchy.OneQubit.Code M₀

private
  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Conjugation, for every n

-- Every lemma here is stated for every n and applied at n = 1 with its
-- operators given explicitly.  At n = 1 a chain of congruences through
-- products of operators is expensive for Agda (Images.conj-act, written
-- as such a chain, took 141 s; as one application of conj-decomp below,
-- 8 s): its sums over assignments compute, and unsolved operators in
-- the chain are found by unfolding the products.

-- Chains with their operators named.

chain₂ : {n : ℕ} (A B C : Op n) → A ≈ B → B ≈ C → A ≈ C
chain₂ A B C e f = e ⟨≈⟩ f

chain₃ : {n : ℕ} (A B C D : Op n) → A ≈ B → B ≈ C → C ≈ D → A ≈ D
chain₃ A B C D e f g = e ⟨≈⟩ f ⟨≈⟩ g

chain₄ : {n : ℕ} (A B C D E : Op n) →
         A ≈ B → B ≈ C → C ≈ D → D ≈ E → A ≈ E
chain₄ A B C D E e f g h = e ⟨≈⟩ f ⟨≈⟩ g ⟨≈⟩ h

chain₅ : {n : ℕ} (A B C D E F : Op n) →
         A ≈ B → B ≈ C → C ≈ D → D ≈ E → E ≈ F → A ≈ F
chain₅ A B C D E F e f g h k = e ⟨≈⟩ f ⟨≈⟩ g ⟨≈⟩ h ⟨≈⟩ k

-- Conjugating back, by a unitary.

peel : {n : ℕ} (U P : Op n) → Unitary U → U † · (U · P · U †) · U ≈ P
peel U P u =
  ·-congˡ U (·-congʳ (U †) (·-assoc U P (U †)) ⟨≈⟩ cancelˡ U (P · U †) u)
  ⟨≈⟩ cancelʳ′ U P u

unconj : {n : ℕ} (U P Q : Op n) → Unitary U →
         U · P · U † ≈ U · Q · U † → P ≈ Q
unconj U P Q u e =
  ≈-sym (peel U P u) ⟨≈⟩ ·-congˡ U (·-congʳ (U †) e) ⟨≈⟩ peel U Q u

-- If the conjugates of P and Q by a unitary are e apart, so are P and Q.

back-gen : {n : ℕ} (U P Q P′ Q′ : Op n) (e : ℤ) → Unitary U →
           U · P · U † ≈ P′ → U · Q · U † ≈ Q′ → Q′ ≈ e ◃ P′ → Q ≈ e ◃ P
back-gen U P Q P′ Q′ e u hP hQ k =
  unconj U Q (e ◃ P) u
    (hQ ⟨≈⟩ k ⟨≈⟩ ◃-cong e (≈-sym hP) ⟨≈⟩ ≈-sym (conj-◃ e U P))

-- The conjugate of a Hermitian operator is Hermitian.

conj-† : {n : ℕ} (U P : Op n) → P † ≈ P → (U · P · U †) † ≈ U · P · U †
conj-† U P e =
  †-· (U · P) (U †)
  ⟨≈⟩ ·-cong (†-involutive U) (†-· U P ⟨≈⟩ ·-congˡ (U †) e)
  ⟨≈⟩ ≈-sym (·-assoc U P (U †))

herm-gen : {n : ℕ} (U P R : Op n) → P † ≈ P → U · P · U † ≈ R → R † ≈ R
herm-gen U P R e h = †-cong (≈-sym h) ⟨≈⟩ conj-† U P e ⟨≈⟩ h

-- A unitary fixes the identity.

conj-id : {n : ℕ} (U P : Op n) → Unitary U → P ≈ I → U · P · U † ≈ P
conj-id U P u e =
  conj-congᴾ U e ⟨≈⟩ ·-congˡ (U †) (·-identityʳ U) ⟨≈⟩ proj₂ u ⟨≈⟩ ≈-sym e

conj-I : {n : ℕ} (P : Op n) → I · P · I † ≈ P
conj-I P = ·-congʳ (I · P) †-I ⟨≈⟩ ·-identityʳ (I · P) ⟨≈⟩ ·-identityˡ P

-- Conjugates through equalities of the conjugating operator, of the
-- conjugated one and of the result.

conj-via : {n : ℕ} (G P Q R S : Op n) →
           P ≈ Q → G · Q · G † ≈ R → R ≈ S → G · P · G † ≈ S
conj-via G P Q R S e h k = conj-congᴾ G e ⟨≈⟩ h ⟨≈⟩ k

conj-gate : {n : ℕ} (G G′ P P′ Q Q′ : Op n) → G ≈ G′ → P ≈ P′ →
            G′ · P′ · G′ † ≈ Q → Q ≈ Q′ → G · P · G † ≈ Q′
conj-gate G G′ P P′ Q Q′ eG eP h k =
  conj-cong eG P ⟨≈⟩ conj-congᴾ G′ eP ⟨≈⟩ h ⟨≈⟩ k

conj-intw : {n : ℕ} (G G′ P P′ Q′ Q : Op n) → G ≈ G′ → P ≈ P′ →
            Unitary G′ → G′ · P′ ≈ Q′ · G′ → Q′ ≈ Q → G · P · G † ≈ Q
conj-intw G G′ P P′ Q′ Q eG eP u i k =
  conj-cong eG P ⟨≈⟩ conj-congᴾ G′ eP ⟨≈⟩ intertwine⇒conj G′ P′ Q′ u i
  ⟨≈⟩ k

-- A phase times a product, factor by factor.

◃-prod : {n : ℕ} (e : ℤ) (A A′ B B′ R : Op n) →
         A ≈ A′ → B ≈ B′ → A′ · B′ ≈ R → e ◃ (A · B) ≈ e ◃ R
◃-prod e A A′ B B′ R eA eB h = ◃-cong e (·-cong eA eB ⟨≈⟩ h)

-- Conjugating a phase times a product.

conj-decomp : {n : ℕ} (G P A B A′ B′ R S : Op n) (e : ℤ) → Unitary G →
              P ≈ e ◃ (A · B) → G · A · G † ≈ A′ → G · B · G † ≈ B′ →
              A′ · B′ ≈ R → e ◃ R ≈ S → G · P · G † ≈ S
conj-decomp G P A B A′ B′ R S e uG d hA hB hR k =
  conj-congᴾ G d ⟨≈⟩ conj-◃ e G (A · B)
  ⟨≈⟩ ◃-cong e (conj-split G A B uG ⟨≈⟩ ·-cong hA hB ⟨≈⟩ hR) ⟨≈⟩ k

-- Conjugating by a product, one factor at a time.

conj-step : {n : ℕ} (W G V P Q R S : Op n) → W ≈ G · V →
            V · P · V † ≈ Q → G · Q · G † ≈ R → R ≈ S → W · P · W † ≈ S
conj-step W G V P Q R S e hQ hR k =
  conj-cong e P ⟨≈⟩ conj-· G V P ⟨≈⟩ conj-congᴾ G hQ ⟨≈⟩ hR ⟨≈⟩ k

-- U agrees with W on P: then W† U fixes P.

fixes : {n : ℕ} (U W P : Op n) → Unitary W → U · P · U † ≈ W · P · W † →
        (W † · U) · P · (W † · U) † ≈ P
fixes U W P uW e =
  conj-· (W †) U P
  ⟨≈⟩ conj-congᴾ (W †) e
  ⟨≈⟩ ·-congʳ (W † · (W · P · W †)) (†-involutive W)
  ⟨≈⟩ peel W P uW

-- One qubit: a unitary fixes the identity.

conj-c1 : (U : Op 1) → Unitary U → U · pauli ⟦ c1 ⟧ᶜ · U † ≈ pauli ⟦ c1 ⟧ᶜ
conj-c1 U u = conj-id U (pauli ⟦ c1 ⟧ᶜ) u c1≈I


------------------------------------------------------------------------
-- Images of X and Z determine the images of all Paulis

pick : Bool → Code → Code
pick false _ = c1
pick true  c = c

actᴳ : Code → Code → Code → Code
actᴳ gx gz c = shiftᶜ (cph c) (pick (cx c) gx ·ᶜ pick (cz c) gz)

module Images (G : Op 1) (uG : Unitary G) (gx gz : Code)
  (hx : G · pauli ⟦ cX ⟧ᶜ · G † ≈ pauli ⟦ gx ⟧ᶜ)
  (hz : G · pauli ⟦ cZ ⟧ᶜ · G † ≈ pauli ⟦ gz ⟧ᶜ) where

  conj-x : (b : Bool) →
           G · pauli ⟦ code 0ℤ b false ⟧ᶜ · G † ≈ pauli ⟦ pick b gx ⟧ᶜ
  conj-x false =
    conj-via G (pauli ⟦ code 0ℤ false false ⟧ᶜ) (pauli ⟦ c1 ⟧ᶜ)
             (pauli ⟦ c1 ⟧ᶜ) (pauli ⟦ pick false gx ⟧ᶜ)
             (code≡ (code 0ℤ false false) c1 refl) (conj-c1 G uG)
             (code≡ c1 (pick false gx) refl)
  conj-x true =
    conj-via G (pauli ⟦ code 0ℤ true false ⟧ᶜ) (pauli ⟦ cX ⟧ᶜ)
             (pauli ⟦ gx ⟧ᶜ) (pauli ⟦ pick true gx ⟧ᶜ)
             (code≡ (code 0ℤ true false) cX refl) hx
             (code≡ gx (pick true gx) refl)

  conj-z : (b : Bool) →
           G · pauli ⟦ code 0ℤ false b ⟧ᶜ · G † ≈ pauli ⟦ pick b gz ⟧ᶜ
  conj-z false =
    conj-via G (pauli ⟦ code 0ℤ false false ⟧ᶜ) (pauli ⟦ c1 ⟧ᶜ)
             (pauli ⟦ c1 ⟧ᶜ) (pauli ⟦ pick false gz ⟧ᶜ)
             (code≡ (code 0ℤ false false) c1 refl) (conj-c1 G uG)
             (code≡ c1 (pick false gz) refl)
  conj-z true =
    conj-via G (pauli ⟦ code 0ℤ false true ⟧ᶜ) (pauli ⟦ cZ ⟧ᶜ)
             (pauli ⟦ gz ⟧ᶜ) (pauli ⟦ pick true gz ⟧ᶜ)
             (code≡ (code 0ℤ false true) cZ refl) hz
             (code≡ gz (pick true gz) refl)

  conj-act : (c : Code) → G · pauli ⟦ c ⟧ᶜ · G † ≈ pauli ⟦ actᴳ gx gz c ⟧ᶜ
  conj-act c =
    conj-decomp G (pauli ⟦ c ⟧ᶜ)
      (pauli ⟦ code 0ℤ (cx c) false ⟧ᶜ) (pauli ⟦ code 0ℤ false (cz c) ⟧ᶜ)
      (pauli ⟦ pick (cx c) gx ⟧ᶜ) (pauli ⟦ pick (cz c) gz ⟧ᶜ)
      (pauli ⟦ pick (cx c) gx ·ᶜ pick (cz c) gz ⟧ᶜ)
      (pauli ⟦ actᴳ gx gz c ⟧ᶜ) (¼ * cph c) uG
      (decomp c) (conj-x (cx c)) (conj-z (cz c))
      (·ᶜ-ok (pick (cx c) gx) (pick (cz c) gz))
      (◃-code (cph c) (pick (cx c) gx ·ᶜ pick (cz c) gz)
       ⟨≈⟩ code≡ (shiftᶜ (cph c) (pick (cx c) gx ·ᶜ pick (cz c) gz))
                 (actᴳ gx gz c) refl)


------------------------------------------------------------------------
-- H and S

-- The two gates, on any wire of any width: their facts are proved for
-- every n and used at n = 1, wire w₀.  (Proved at n = 1 directly, with
-- the lemmas of PathSum.Hierarchy.Gates and .Levels, the three facts
-- below took 140-200 s each: those lemmas' types name the operators
-- through other modules' copies of the definitions, and at one qubit
-- Agda compares the two spellings by computing the products.)

data Gate₁ : Set where
  gH gS : Gate₁

gateOp : {n : ℕ} → Gate₁ → Fin n → Op n
gateOp gH w = hadOp w
gateOp gS w = Rs (ρ false 2) w

-- The images of X and Z: H swaps them, S sends X to Y = i X Z.

imgX imgZ : {n : ℕ} → Gate₁ → Fin n → PauliData n
imgX gH w = Z^ w
imgX gS w = Y^ w
imgZ gH w = X^ w
imgZ gS w = Z^ w

private
  two-s : (+ 2) * ρ false 2 ≡ ½
  two-s = trans (ρ-double false 0 (s≤s (s≤s z≤n))) (ρ-def false 1)

  neg-s : - ρ false 2 ≡ ¼ * -1ℤ
  neg-s = trans (cong -_ (ρ-def false 2))
             (solve 1 (λ q → :- q := q :* con -1ℤ) refl ¼)

gate-unitaryₙ : {n : ℕ} (g : Gate₁) (w : Fin n) → Unitary (gateOp g w)
gate-unitaryₙ gH w =
  Unitary-cong {U = hadOp w} {V = gateOp gH w} ≈-refl (had-unitary w)
gate-unitaryₙ gS w =
  Unitary-cong {U = diagOp (wireFn (ρ false 2) w)} {V = gateOp gS w} ≈-refl
    (diag-unitary (wireFn (ρ false 2) w))

gate-xₙ : {n : ℕ} (g : Gate₁) (w : Fin n) →
          gateOp g w · pauli (X^ w) · gateOp g w † ≈ pauli (imgX g w)
gate-xₙ gH w =
  conj-cong {U = gateOp gH w} {V = hadOp w} ≈-refl (pauli (X^ w))
  ⟨≈⟩ intertwine⇒conj (hadOp w) (pauli (X^ w)) (pauli (Z^ w))
                      (had-unitary w) (had-X w)
gate-xₙ gS w =
  conj-cong {U = gateOp gS w} {V = Rs (ρ false 2) w} ≈-refl (pauli (X^ w))
  ⟨≈⟩ Rs-conj-1 (ρ false 2) w (X^ w) (≔-here 0ᵛ w true)
  ⟨≈⟩ ◃-prod (- ρ false 2) (Rs ((+ 2) * ρ false 2) w) (pauli (Z^ w))
             (pauli (X^ w)) (pauli (X^ w)) (pauli (Z^ w ∙ᴾ X^ w))
             (Rs-exp {a = (+ 2) * ρ false 2} {b = ½} w two-s ⟨≈⟩ Rs-½ w)
             ≈-refl (pauli-· (Z^ w) (X^ w))
  ⟨≈⟩ ◃-exp {e = - ρ false 2} {e′ = ¼ * -1ℤ} (pauli (Z^ w ∙ᴾ X^ w)) neg-s
  ⟨≈⟩ ◃-pauli -1ℤ (Z^ w ∙ᴾ X^ w)
  ⟨≈⟩ pauli-≈ (pd (ph (Z^ w ∙ᴾ X^ w) + -1ℤ) (xs (Z^ w ∙ᴾ X^ w))
                  (zs (Z^ w ∙ᴾ X^ w)))
              (Y^ w)
              (≡ᴺ-≡ (cong (λ b → ¼ * (0ℤ + 0ℤ + (+ 2) * [ b ]ᶻ + -1ℤ))
                          (trans (dot-e (eᵛ w) w) (≔-here 0ᵛ w true))))
              (λ _ → refl) (λ j → xor-false (eᵛ w j))

gate-zₙ : {n : ℕ} (g : Gate₁) (w : Fin n) →
          gateOp g w · pauli (Z^ w) · gateOp g w † ≈ pauli (imgZ g w)
gate-zₙ gH w =
  conj-cong {U = gateOp gH w} {V = hadOp w} ≈-refl (pauli (Z^ w))
  ⟨≈⟩ intertwine⇒conj (hadOp w) (pauli (Z^ w)) (pauli (X^ w))
                      (had-unitary w) (had-Z w)
gate-zₙ gS w =
  conj-cong {U = gateOp gS w} {V = Rs (ρ false 2) w} ≈-refl (pauli (Z^ w))
  ⟨≈⟩ Rs-conj-0 (ρ false 2) w (Z^ w) refl

gate-𝒞₂ₙ : {n : ℕ} (g : Gate₁) (w : Fin n) → 𝒞 2 (gateOp g w)
gate-𝒞₂ₙ gH w = 𝒞-resp 2 {hadOp w} {gateOp gH w} ≈-refl (had-𝒞₂ w)
gate-𝒞₂ₙ gS w =
  𝒞-resp 2 {Rs (ρ false 2) w} {gateOp gS w} ≈-refl (R∈𝒞 2 w (s≤s z≤n))

-- At one qubit, on codes.

gateX gateZ : Gate₁ → Code
gateX gH = cZ
gateX gS = shiftᶜ -1ℤ (cZ ·ᶜ cX)
gateZ gH = cX
gateZ gS = cZ

private
  e₀-true : ∀ j → eᵛ w₀ j ≡ true
  e₀-true zero = ≔-here 0ᵛ w₀ true
  e₀-true (suc ())

imgX≈ : (g : Gate₁) → pauli (imgX g w₀) ≈ pauli ⟦ gateX g ⟧ᶜ
imgX≈ gH = pauli-≈ (imgX gH w₀) ⟦ gateX gH ⟧ᶜ ≡ᴺ-refl (λ _ → refl) e₀-true
imgX≈ gS = pauli-≈ (imgX gS w₀) ⟦ gateX gS ⟧ᶜ ≡ᴺ-refl e₀-true e₀-true

imgZ≈ : (g : Gate₁) → pauli (imgZ g w₀) ≈ pauli ⟦ gateZ g ⟧ᶜ
imgZ≈ gH = pauli-≈ (imgZ gH w₀) ⟦ gateZ gH ⟧ᶜ ≡ᴺ-refl e₀-true (λ _ → refl)
imgZ≈ gS = pauli-≈ (imgZ gS w₀) ⟦ gateZ gS ⟧ᶜ ≡ᴺ-refl (λ _ → refl) e₀-true

gate-x : (g : Gate₁) →
         gateOp g w₀ · pauli ⟦ cX ⟧ᶜ · gateOp g w₀ † ≈ pauli ⟦ gateX g ⟧ᶜ
gate-x g =
  conj-via (gateOp g w₀) (pauli ⟦ cX ⟧ᶜ) (pauli (X^ w₀)) (pauli (imgX g w₀))
           (pauli ⟦ gateX g ⟧ᶜ) (≈-sym X≈) (gate-xₙ g w₀) (imgX≈ g)

gate-z : (g : Gate₁) →
         gateOp g w₀ · pauli ⟦ cZ ⟧ᶜ · gateOp g w₀ † ≈ pauli ⟦ gateZ g ⟧ᶜ
gate-z g =
  conj-via (gateOp g w₀) (pauli ⟦ cZ ⟧ᶜ) (pauli (Z^ w₀)) (pauli (imgZ g w₀))
           (pauli ⟦ gateZ g ⟧ᶜ) (≈-sym Z≈) (gate-zₙ g w₀) (imgZ≈ g)

gate-act : (g : Gate₁) (c : Code) →
           gateOp g w₀ · pauli ⟦ c ⟧ᶜ · gateOp g w₀ † ≈
           pauli ⟦ actᴳ (gateX g) (gateZ g) c ⟧ᶜ
gate-act g = Images.conj-act (gateOp g w₀) (gate-unitaryₙ g w₀)
                             (gateX g) (gateZ g) (gate-x g) (gate-z g)


------------------------------------------------------------------------
-- Words

-- A word g₁ g₂ … is the product g₁ · g₂ · …: its last letter is
-- applied first.

Word : Set
Word = List Gate₁

opW : Word → Op 1
opW []       = I
opW (g ∷ ws) = gateOp g w₀ · opW ws

actW : Word → Code → Code
actW []       c = c
actW (g ∷ ws) c = actᴳ (gateX g) (gateZ g) (actW ws c)

opW-unitary : (ws : Word) → Unitary (opW ws)
opW-unitary [] = Unitary-cong {U = I} {V = opW []} ≈-refl Unitary-I
opW-unitary (g ∷ ws) =
  Unitary-cong {U = gateOp g w₀ · opW ws} {V = opW (g ∷ ws)} ≈-refl
    (Unitary-· (gateOp g w₀) (opW ws) (gate-unitaryₙ g w₀) (opW-unitary ws))

opW-𝒞₂ : (ws : Word) → 𝒞 2 (opW ws)
opW-𝒞₂ [] = 𝒞-resp 2 {I} {opW []} ≈-refl (𝒞-I 1)
opW-𝒞₂ (g ∷ ws) =
  𝒞-resp 2 {gateOp g w₀ · opW ws} {opW (g ∷ ws)} ≈-refl
    (𝒞₂-· {U = gateOp g w₀} {V = opW ws} (gate-𝒞₂ₙ g w₀) (opW-𝒞₂ ws))

-- A word conjugates the Pauli of c to the Pauli of actW ws c.

word-act : (ws : Word) (c : Code) →
           opW ws · pauli ⟦ c ⟧ᶜ · opW ws † ≈ pauli ⟦ actW ws c ⟧ᶜ
word-act [] c =
  conj-gate (opW []) I (pauli ⟦ c ⟧ᶜ) (pauli ⟦ c ⟧ᶜ) (pauli ⟦ c ⟧ᶜ)
            (pauli ⟦ actW [] c ⟧ᶜ) ≈-refl ≈-refl (conj-I (pauli ⟦ c ⟧ᶜ))
            (code≡ c (actW [] c) refl)
word-act (g ∷ ws) c =
  conj-step (opW (g ∷ ws)) (gateOp g w₀) (opW ws) (pauli ⟦ c ⟧ᶜ)
            (pauli ⟦ actW ws c ⟧ᶜ)
            (pauli ⟦ actᴳ (gateX g) (gateZ g) (actW ws c) ⟧ᶜ)
            (pauli ⟦ actW (g ∷ ws) c ⟧ᶜ)
            ≈-refl (word-act ws c) (gate-act g (actW ws c))
            (code≡ (actᴳ (gateX g) (gateZ g) (actW ws c)) (actW (g ∷ ws) c)
                   refl)

-- The 24 words.

words : Vec Word 24
words =
  [] ∷ᵛ
  (gH ∷ []) ∷ᵛ
  (gS ∷ []) ∷ᵛ
  (gH ∷ gS ∷ []) ∷ᵛ
  (gS ∷ gH ∷ []) ∷ᵛ
  (gS ∷ gS ∷ []) ∷ᵛ
  (gH ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gH ∷ gS ∷ gS ∷ []) ∷ᵛ
  (gS ∷ gH ∷ gS ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gS ∷ []) ∷ᵛ
  (gH ∷ gS ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gS ∷ gH ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gS ∷ gH ∷ gS ∷ gS ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gH ∷ gS ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gH ∷ gS ∷ gS ∷ gH ∷ gS ∷ []) ∷ᵛ
  (gS ∷ gH ∷ gS ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gH ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gH ∷ gS ∷ gS ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gS ∷ gH ∷ gS ∷ []) ∷ᵛ
  (gH ∷ gS ∷ gS ∷ gH ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gH ∷ gS ∷ gS ∷ gH ∷ []) ∷ᵛ
  (gS ∷ gS ∷ gS ∷ gH ∷ gS ∷ gH ∷ []) ∷ᵛ
  []ᵛ

word-𝒞₂ : (i : Fin 24) → 𝒞 2 (opW (lookup words i))
word-𝒞₂ i = opW-𝒞₂ (lookup words i)
