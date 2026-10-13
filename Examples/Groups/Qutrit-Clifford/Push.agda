------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing dirty gates into the ladders of a Z-normal circuit (part of
-- the proof of Lemma 4.2)
--
-- A gate in front of a ladder is pushed through it by the rewriting
-- tables: it meets the bottom B box, and what comes out is either done
-- (on wire 0, where it goes on to the X-normal circuit), an input of
-- the ladder one wire up, or CZ straddling wires 0 and 1, which meets
-- that ladder's bottom box in turn (straddle).  The sizes of the
-- ladders are explicit arguments, the measure of the recursion: the
-- dirty gates are pushed into ladders one size down.  The box
-- relations come as an argument too (Rels), those on at most as many
-- qutrits as the ladder's wires.  This is Qubit-Clifford's Push with the
-- qutrit tables.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Push where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.List.Properties using (map-++ ; ++-assoc)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine using (⟪_⟫ ; ⟪++⟫ ; ⟪≈⟫ ; ⟪map↥⟫)
open import Examples.Groups.Qutrit-Clifford.Axioms
  using (𝕟 ; h₀ ; h₁ ; h₂ ; s₀ ; s₁ ; s₂ ; c₀ ; c₁)
open import Examples.Groups.Qutrit-Clifford.Reasoning
open import Examples.Groups.Qutrit-Clifford.NormalForm
open import Examples.Groups.Qutrit-Clifford.Tables
open import Examples.Groups.Qutrit-Clifford.Rels

open BoxRelations₁
open BoxRelations₂
open BoxRelations₃

private
  variable
    n m k : ℕ

------------------------------------------------------------------------
-- The gates an X-normal circuit takes

-- S or Z on the only wire (label 3), H and S on wire 0, CZ on wires 0
-- and 1, a gate one wire up, and the scalar.
data MIn : ℕ → Set where
  mSt mZt  : MIn 1
  mH mS mC : MIn (₂₊ m)
  mup      : MIn (₁₊ m) → MIn (₂₊ m)
  mν       : MIn n

Ml : MIn n → List (Gen n)
Ml mSt     = s₀ ∷ []
Ml mZt     = Zˡ
Ml mH      = h₀ ∷ []
Ml mS      = s₀ ∷ []
Ml mC      = c₀ ∷ []
Ml (mup g) = map _↥ (Ml g)
Ml mν      = 𝕟 ∷ []

Mls : List (MIn n) → List (Gen n)
Mls = concatMap Ml

Mls-++ : (xs ys : List (MIn n)) → Mls (xs ++ ys) ≡ Mls xs ++ Mls ys
Mls-++ []       ys = Eq.refl
Mls-++ (x ∷ xs) ys = Eq.trans (Eq.cong (Ml x ++_) (Mls-++ xs ys)) (Eq.sym (++-assoc (Ml x) (Mls xs) (Mls ys)))

Mls-up : (ds : List (MIn (₁₊ m))) → Mls (map mup ds) ≡ map _↥ (Mls ds)
Mls-up []       = Eq.refl
Mls-up (d ∷ ds) = Eq.trans (Eq.cong (map _↥ (Ml d) ++_) (Mls-up ds)) (Eq.sym (map-++ _↥ (Ml d) (Mls ds)))

-- Propositional equality of words gives the congruence.
≡⇒≈ : {a b : Circuit n} → a ≡ b → n ⊢ a ≈ b
≡⇒≈ Eq.refl = PB.refl

-- The word of a list of dirty gates moved up a wire.
Mls-up-≈ : (ds : List (MIn (₁₊ m))) → (₂₊ m) ⊢ ⟪ Mls (map mup ds) ⟫ ≈ ⟪ Mls ds ⟫ ↑
Mls-up-≈ ds = PB.trans (⟪≈⟫ (Mls-up ds)) (≡⇒≈ (⟪map↥⟫ (Mls ds)))

------------------------------------------------------------------------
-- Results of a push

record Out {X : Set} (n : ℕ) (⟦_⟧ : X → Circuit n) (lhs : Circuit n) : Set where
  constructor out
  field
    ds  : List (MIn n)
    new : X
    ok  : n ⊢ lhs ≈ ⟪ Mls ds ⟫ • ⟦ new ⟧

open Out

-- Inputs of a ladder: a gate on its input wire, or a letter above it.
data LIn : ℕ → Set where
  lw0 : W0 → LIn (₁₊ m)
  lup : Gen (₁₊ m) → LIn (₂₊ m)

LInl : LIn n → List (Gen n)
LInl (lw0 w) = W0l w
LInl (lup g) = g ↥ ∷ []

⟦_⟧ᴸ↑ : Lad m → Circuit (₁₊ m)
⟦ l ⟧ᴸ↑ = ⟦ l ⟧ᴸ ↑

⟦_⟧ᴸ↑↑ : Lad m → Circuit (₂₊ m)
⟦ l ⟧ᴸ↑↑ = ⟦ l ⟧ᴸ ↑ ↑

------------------------------------------------------------------------
-- Glue

module Glue {n : ℕ} where

  open Width n

  -- Two pushes in a row.
  seq : ∀ {l a b o₁ l₁ o₂ l₂} → l • a ≈ o₁ • l₁ → l₁ • b ≈ o₂ • l₂ →
        l • (a • b) ≈ (o₁ • o₂) • l₂
  seq {l} {a} {b} {o₁} {l₁} {o₂} {l₂} e₁ e₂ = begin
    l • (a • b)        ≈⟨ sym assoc ⟩
    (l • a) • b        ≈⟨ front b e₁ ⟩
    (o₁ • l₁) • b      ≈⟨ assoc ⟩
    o₁ • (l₁ • b)      ≈⟨ back o₁ e₂ ⟩
    o₁ • (o₂ • l₂)     ≈⟨ sym assoc ⟩
    (o₁ • o₂) • l₂     ∎

  -- A clean box x meeting g becomes y x'; y is then pushed into l.
  glue : ∀ {l x g y x' o l'} → x • g ≈ y • x' → l • y ≈ o • l' →
         (l • x) • g ≈ o • (l' • x')
  glue {l} {x} {g} {y} {x'} {o} {l'} e₁ e₂ = begin
    (l • x) • g        ≈⟨ assoc ⟩
    l • (x • g)        ≈⟨ back l e₁ ⟩
    l • (y • x')       ≈⟨ sym assoc ⟩
    (l • y) • x'       ≈⟨ front x' e₂ ⟩
    (o • l') • x'      ≈⟨ assoc ⟩
    o • (l' • x')      ∎

  -- The same with two clean boxes.
  glue₂ : ∀ {l x₁ x₀ g y x₁' x₀' o l'} → x₁ • x₀ • g ≈ y • x₁' • x₀' → l • y ≈ o • l' →
          ((l • x₁) • x₀) • g ≈ o • ((l' • x₁') • x₀')
  glue₂ {l} {x₁} {x₀} {g} {y} {x₁'} {x₀'} {o} {l'} e₁ e₂ = begin
    ((l • x₁) • x₀) • g      ≈⟨ trans assoc assoc ⟩
    l • (x₁ • (x₀ • g))      ≈⟨ back l e₁ ⟩
    l • (y • (x₁' • x₀'))    ≈⟨ sym assoc ⟩
    (l • y) • (x₁' • x₀')    ≈⟨ front (x₁' • x₀') e₂ ⟩
    (o • l') • (x₁' • x₀')   ≈⟨ assoc ⟩
    o • (l' • (x₁' • x₀'))   ≈⟨ back o (sym assoc) ⟩
    o • ((l' • x₁') • x₀')   ∎

  -- A list of dirty gates made of two.
  join : (xs ys : List (MIn n)) → ⟪ Mls xs ⟫ • ⟪ Mls ys ⟫ ≈ ⟪ Mls (xs ++ ys) ⟫
  join xs ys = trans (sym (⟪++⟫ (Mls xs) (Mls ys))) (⟪≈⟫ (Eq.sym (Mls-++ xs ys)))

------------------------------------------------------------------------
-- The letters of the clean boxes are on the bottom wires

W0l-low1 : (w : W0) → all low1 (W0l {n = m} w) ≡ true
W0l-low1 iS = Eq.refl
W0l-low1 iX = Eq.refl
W0l-low1 iZ = Eq.refl
W0l-low1 iν = Eq.refl

Al-low1 : (a : AT) → all low1 (Al {n = m} a) ≡ true
Al-low1 A₀₁ = Eq.refl
Al-low1 A₀₂ = Eq.refl
Al-low1 A₁₀ = Eq.refl
Al-low1 A₁₁ = Eq.refl
Al-low1 A₁₂ = Eq.refl
Al-low1 A₂₀ = Eq.refl
Al-low1 A₂₁ = Eq.refl
Al-low1 A₂₂ = Eq.refl

Bl-low2 : (b : BT) → all low2 (Bl {n = m} b) ≡ true
Bl-low2 B₀₀ = Eq.refl
Bl-low2 B₀₁ = Eq.refl
Bl-low2 B₀₂ = Eq.refl
Bl-low2 B₁₀ = Eq.refl
Bl-low2 B₁₁ = Eq.refl
Bl-low2 B₁₂ = Eq.refl
Bl-low2 B₂₀ = Eq.refl
Bl-low2 B₂₁ = Eq.refl
Bl-low2 B₂₂ = Eq.refl

Dl-low2 : (d : DT) → all low2 (Dl {n = m} d) ≡ true
Dl-low2 D₀₀ = Eq.refl
Dl-low2 D₀₁ = Eq.refl
Dl-low2 D₀₂ = Eq.refl
Dl-low2 D₁₀ = Eq.refl
Dl-low2 D₁₁ = Eq.refl
Dl-low2 D₁₂ = Eq.refl
Dl-low2 D₂₀ = Eq.refl
Dl-low2 D₂₁ = Eq.refl
Dl-low2 D₂₂ = Eq.refl

El-low1 : (e : ET) → all low1 (El {n = m} e) ≡ true
El-low1 E₀ = Eq.refl
El-low1 E₁ = Eq.refl
El-low1 E₂ = Eq.refl

Fl-low1 : (f : FT) → all low1 (Fl {n = m} f) ≡ true
Fl-low1 F₀ = Eq.refl
Fl-low1 F₁ = Eq.refl
Fl-low1 F₂ = Eq.refl

------------------------------------------------------------------------
-- Conversions of the outputs of the tables

co→M : CO → MIn 1
co→M coS = mSt
co→M coZ = mZt
co→M coν = mν

co→M-l : (cs : List CO) → Mls (map co→M cs) ≡ COls {n = 0} cs
co→M-l []         = Eq.refl
co→M-l (coS ∷ cs) = Eq.cong (s₀ ∷_) (co→M-l cs)
co→M-l (coZ ∷ cs) = Eq.cong (Zˡ ++_) (co→M-l cs)
co→M-l (coν ∷ cs) = Eq.cong (𝕟 ∷_) (co→M-l cs)

sc→M : SCO → MIn 2
sc→M scC = mC
sc→M scH = mH
sc→M scS = mS
sc→M scν = mν

sc→M-l : (cs : List SCO) → Mls (map sc→M cs) ≡ SCOls {n = 0} cs
sc→M-l []         = Eq.refl
sc→M-l (scC ∷ cs) = Eq.cong (c₀ ∷_) (sc→M-l cs)
sc→M-l (scH ∷ cs) = Eq.cong (h₀ ∷_) (sc→M-l cs)
sc→M-l (scS ∷ cs) = Eq.cong (s₀ ∷_) (sc→M-l cs)
sc→M-l (scν ∷ cs) = Eq.cong (𝕟 ∷_) (sc→M-l cs)

q→M : Q01 → MIn (₃₊ m)
q→M qh₀ = mH
q→M qs₀ = mS
q→M qh₁ = mup mH
q→M qs₁ = mup mS
q→M qc₀ = mC

q→M-l : (q : Q01) → Ml (q→M {m = m} q) ≡ Ql q ∷ []
q→M-l qh₀ = Eq.refl
q→M-l qs₀ = Eq.refl
q→M-l qh₁ = Eq.refl
q→M-l qs₁ = Eq.refl
q→M-l qc₀ = Eq.refl

q-low2 : (q : Q01) → all low2 (Ql {n = m} q ∷ []) ≡ true
q-low2 qh₀ = Eq.refl
q-low2 qs₀ = Eq.refl
q-low2 qh₁ = Eq.refl
q-low2 qs₁ = Eq.refl
q-low2 qc₀ = Eq.refl

------------------------------------------------------------------------
-- Lifting a push one wire up

liftOut : {X : Set} {F : X → Circuit (₁₊ k)} {lhs : Circuit (₁₊ k)} →
          Out (₁₊ k) F lhs → Out (₂₊ k) (λ x → F x ↑) (lhs ↑)
liftOut {k} {F = F} (out ds x e) = out (map mup ds) x
  (PB.trans (lift e) (PB.cong (PB.sym (Mls-up-≈ ds)) PB.refl))

-- An equation between lists, read as one between words.
module _ {n : ℕ} where

  open Width n

  rule→ : {xs gs ys xs' : List (Gen n)} → ⟪ xs ++ gs ⟫ ≈ ⟪ ys ++ xs' ⟫ →
          ⟪ xs ⟫ • ⟪ gs ⟫ ≈ ⟪ ys ⟫ • ⟪ xs' ⟫
  rule→ {xs} {gs} {ys} {xs'} e = trans (sym (⟪++⟫ xs gs)) (trans e (⟪++⟫ ys xs'))

  -- The same with three lists on each side.
  rule3→ : {x₁ x₀ g y x₁' x₀' : List (Gen n)} → ⟪ x₁ ++ x₀ ++ g ⟫ ≈ ⟪ y ++ x₁' ++ x₀' ⟫ →
           ⟪ x₁ ⟫ • ⟪ x₀ ⟫ • ⟪ g ⟫ ≈ ⟪ y ⟫ • ⟪ x₁' ⟫ • ⟪ x₀' ⟫
  rule3→ {x₁} {x₀} {g} {y} {x₁'} {x₀'} e =
    trans (back ⟪ x₁ ⟫ (sym (⟪++⟫ x₀ g))) (trans (sym (⟪++⟫ x₁ (x₀ ++ g)))
    (trans e (trans (⟪++⟫ y (x₁' ++ x₀')) (back ⟪ y ⟫ (⟪++⟫ x₁' x₀')))))

-- The words of the two lists ⟪ map _↥ xs ⟫ and ⟪ xs ⟫ ↑.
⟪↑⟫ : (xs : List (Gen n)) → (₁₊ n) ⊢ ⟪ map _↥ xs ⟫ ≈ ⟪ xs ⟫ ↑
⟪↑⟫ xs = ≡⇒≈ (⟪map↥⟫ xs)

------------------------------------------------------------------------
-- The steps of a push into a ladder, given the pushes they recurse to

-- Two pushes in a row.
seqOut : {X : Set} {F : X → Circuit n} {L : Circuit n} (A B : List (Gen n)) →
         (a : Out n F (L • ⟪ A ⟫)) → Out n F (F (new a) • ⟪ B ⟫) → Out n F (L • ⟪ A ++ B ⟫)
seqOut {n} A B (out d₁ x₁ e₁) (out d₂ x₂ e₂) =
  out (d₁ ++ d₂) x₂ (trans (back _ (⟪++⟫ A B)) (trans (seq e₁ e₂) (front _ (join d₁ d₂))))
  where
  open Width n
  open Glue

-- Nothing to push.
nilOut : {X : Set} {F : X → Circuit n} (x : X) → Out n F (F x • ⟪ [] ⟫)
nilOut {n} x = out [] x (trans right-unit (sym left-unit))
  where open Width n

-- Changing the left-hand side.
convOut : {X : Set} {F : X → Circuit n} {l l' : Circuit n} → n ⊢ l' ≈ l → Out n F l → Out n F l'
convOut e (out d x e') = out d x (PB.trans e e')

-- A word that passes the structure, read as dirty gates.
passOut : {X : Set} {F : X → Circuit n} (x : X) (g : List (Gen n)) (d : List (MIn n)) →
          n ⊢ F x • ⟪ g ⟫ ≈ ⟪ g ⟫ • F x → ⟪ g ⟫ ≡ ⟪ Mls d ⟫ → Out n F (F x • ⟪ g ⟫)
passOut {n} x g d e e' = out d x (trans e (front _ (≡⇒≈ e')))
  where open Width n

-- The scalar passes anything.
scalarOut : {X : Set} {F : X → Circuit n} (x : X) (g : Gen n) → n ⊢ [ g ]ʷ ≈ ν →
            Out n F (F x • ⟪ g ∷ [] ⟫)
scalarOut {n} x g e = out (mν ∷ []) x
  (trans (back _ (trans right-unit e)) (trans (sym (ν-comm _)) (front _ (sym right-unit))))
  where open Width n

-- The bottom B box meets an input.
stepB : BoxRelations₂ → (b : BT) (g : In1) (lad : Lad (₁₊ m)) →
        Out (₂₊ m) ⟦_⟧ᴸ↑ (⟦ lad ⟧ᴸ ↑ • ⟪ Pls (proj₂ (ruleB b g)) ⟫) →
        Out (₂₊ m) ⟦_⟧ᴸ ((⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫) • ⟪ In1l g ⟫)
stepB r b g lad (out d lad' e) = out d (proj₁ (ruleB b g) ∷ᴮ lad') (Glue.glue (rule→ (ruleB-ok r b g)) e)

-- The bottom two B boxes meet CZ on wires 1 and 2.
stepBB : BoxRelations₃ → (b b₁ : BT) (lad : Lad (₁₊ m)) →
         Out (₃₊ m) ⟦_⟧ᴸ↑↑ (⟦ lad ⟧ᴸ ↑ ↑ • ⟪ P2ls (proj₂ (proj₂ (ruleBB b b₁))) ⟫) →
         Out (₃₊ m) ⟦_⟧ᴸ (((⟦ lad ⟧ᴸ ↑ ↑ • ⟪ Bl b₁ ⟫ ↑) • ⟪ Bl b ⟫) • ⟪ c₁ ∷ [] ⟫)
stepBB {m = m} r b b₁ lad (out d lad' e) =
  out d (proj₁ q ∷ᴮ proj₁ (proj₂ q) ∷ᴮ lad') (Glue.glue₂ e₁ e)
  where
  open Width (₃₊ m)
  q = ruleBB b b₁
  e₁ = trans (front _ (sym (⟪↑⟫ (Bl b₁))))
       (trans (rule3→ (ruleBB-ok r b b₁)) (back _ (front _ (⟪↑⟫ (Bl (proj₁ (proj₂ q)))))))

-- A letter higher up passes the bottom B box.
stepUp : (b : BT) (lad : Lad (₂₊ m)) (g : Gen (₁₊ m)) →
         Out (₂₊ m) ⟦_⟧ᴸ (⟦ lad ⟧ᴸ • ⟪ g ↥ ∷ [] ⟫) →
         Out (₃₊ m) ⟦_⟧ᴸ ((⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫) • ⟪ g ↥ ↥ ∷ [] ⟫)
stepUp {m = m} b lad g (out d lad' e₀) = out (map mup d) (b ∷ᴮ lad') e
  where
  open Width (₃₊ m)
  e = begin
    (⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫) • ⟪ g ↥ ↥ ∷ [] ⟫   ≈⟨ trans assoc (back _ (back _ right-unit)) ⟩
    ⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫ • [ g ↥ ↥ ]ʷ        ≈⟨ back _ (low2s-comm (Bl b) (Bl-low2 b) [ g ]ʷ) ⟩
    ⟦ lad ⟧ᴸ ↑ • [ g ↥ ↥ ]ʷ • ⟪ Bl b ⟫        ≈⟨ sym assoc ⟩
    (⟦ lad ⟧ᴸ • [ g ↥ ]ʷ) ↑ • ⟪ Bl b ⟫        ≈⟨ front _ (lift (PB.trans (PB.cong PB.refl (PB.sym PB.right-unit)) e₀)) ⟩
    (⟪ Mls d ⟫ • ⟦ lad' ⟧ᴸ) ↑ • ⟪ Bl b ⟫      ≈⟨ trans (front _ (front _ (sym (Mls-up-≈ d)))) assoc ⟩
    ⟪ Mls (map mup d) ⟫ • (⟦ lad' ⟧ᴸ ↑ • ⟪ Bl b ⟫) ∎

-- A gate on the bottom wire passes a ladder shifted up.
pass1 : (lad : Lad (₁₊ m)) (x : Gen (₂₊ m)) (d : MIn (₂₊ m)) → all low1 (x ∷ []) ≡ true → Ml d ≡ x ∷ [] →
        Out (₂₊ m) ⟦_⟧ᴸ↑ (⟦ lad ⟧ᴸ ↑ • ⟪ x ∷ [] ⟫)
pass1 lad x d e e' = passOut lad (x ∷ []) (d ∷ [])
  (PB.sym (low1s-comm (x ∷ []) e ⟦ lad ⟧ᴸ)) (Eq.cong ⟪_⟫ (Eq.cong (_++ []) (Eq.sym e')))

-- CZ straddling wires 0 and 1 meets the bottom B box of the ladder
-- above.
stepS : BoxRelations₃ → (b : BT) (lad : Lad (₁₊ m)) →
        Out (₃₊ m) ⟦_⟧ᴸ↑↑ (⟦ lad ⟧ᴸ ↑ ↑ • ⟪ P2ls (proj₂ (ruleS b)) ⟫) →
        Out (₃₊ m) ⟦_⟧ᴸ↑ ((⟦ lad ⟧ᴸ ↑ ↑ • ⟪ Bl b ⟫ ↑) • ⟪ c₀ ∷ [] ⟫)
stepS {m = m} r b lad (out d lad' e) = out d (proj₁ (ruleS b) ∷ᴮ lad') (Glue.glue e₁ e)
  where
  open Width (₃₊ m)
  e₁ = trans (front _ (sym (⟪↑⟫ (Bl b))))
       (trans (rule→ (ruleS-ok r b)) (back _ (⟪↑⟫ (Bl (proj₁ (ruleS b))))))

------------------------------------------------------------------------
-- Pushing into ladders
--
-- The first argument is the size of the ladder minus one; it decreases
-- along every recursive path that comes back to the same function.

ladPush   : (m : ℕ) → Rels (₁₊ m) → (lad : Lad (₁₊ m)) (g : LIn (₁₊ m)) →
            Out (₁₊ m) ⟦_⟧ᴸ (⟦ lad ⟧ᴸ • ⟪ LInl g ⟫)
ladPushW  : (m : ℕ) → Rels (₁₊ m) → (lad : Lad (₁₊ m)) (ws : List W0) →
            Out (₁₊ m) ⟦_⟧ᴸ (⟦ lad ⟧ᴸ • ⟪ W0ls ws ⟫)
pushPost  : (m : ℕ) → Rels (₂₊ m) → (lad : Lad (₁₊ m)) (ps : List Post) →
            Out (₂₊ m) ⟦_⟧ᴸ↑ (⟦ lad ⟧ᴸ ↑ • ⟪ Pls ps ⟫)
pushPost1 : (m : ℕ) → Rels (₂₊ m) → (lad : Lad (₁₊ m)) (p : Post) →
            Out (₂₊ m) ⟦_⟧ᴸ↑ (⟦ lad ⟧ᴸ ↑ • ⟪ Pl p ⟫)
straddle  : (m : ℕ) → Rels (₂₊ m) → (lad : Lad (₁₊ m)) →
            Out (₂₊ m) ⟦_⟧ᴸ↑ (⟦ lad ⟧ᴸ ↑ • ⟪ c₀ ∷ [] ⟫)
pushPost2 : (m : ℕ) → Rels (₂₊ m) → (lad : Lad (₁₊ m)) (qs : List Post2) →
            Out (₃₊ m) ⟦_⟧ᴸ↑↑ (⟦ lad ⟧ᴸ ↑ ↑ • ⟪ P2ls qs ⟫)
pushPost21 : (m : ℕ) → Rels (₂₊ m) → (lad : Lad (₁₊ m)) (q : Post2) →
            Out (₃₊ m) ⟦_⟧ᴸ↑↑ (⟦ lad ⟧ᴸ ↑ ↑ • ⟪ P2l q ⟫)

-- The C box at the top.
ladPush zero rs (top c) (lw0 w) = out (map co→M (proj₂ (ruleC c w))) (top (proj₁ (ruleC c w)))
  (PB.trans (rule→ (ruleC-ok (rel₁ {0} rs) c w))
    (PB.cong (≡⇒≈ (Eq.sym (Eq.cong ⟪_⟫ (co→M-l (proj₂ (ruleC c w)))))) PB.refl))
ladPush (suc m) rs (b ∷ᴮ lad) (lw0 w) =
  stepB (rel₂ {m} rs) b (w0 w) lad (pushPost m rs lad (proj₂ (ruleB b (w0 w))))
ladPush (suc m) rs (b ∷ᴮ lad) (lup (gate₁ H-gate)) =
  stepB (rel₂ {m} rs) b (w1 gH) lad (pushPost m rs lad (proj₂ (ruleB b (w1 gH))))
ladPush (suc m) rs (b ∷ᴮ lad) (lup (gate₁ S-gate)) =
  stepB (rel₂ {m} rs) b (w1 gS) lad (pushPost m rs lad (proj₂ (ruleB b (w1 gS))))
ladPush (suc (suc m)) rs (b ∷ᴮ b₁ ∷ᴮ lad) (lup (gate₂ CZ-gate)) =
  stepBB (rel₃ {m} rs) b b₁ lad (pushPost2 m (down {₂₊ m} rs) lad (proj₂ (proj₂ (ruleBB b b₁))))
ladPush (suc (suc m)) rs (b ∷ᴮ lad) (lup (g ↥)) =
  stepUp b lad g (ladPush (suc m) (down {₂₊ m} rs) lad (lup g))
ladPush (suc m) rs lad (lup (gate₀ ν-gate)) =
  scalarOut lad (gate₀ ν-gate ↥) ν↑
ladPush (suc zero) rs lad (lup (gate₀ ν-gate ↥)) =
  scalarOut lad (gate₀ ν-gate ↥ ↥) (PB.trans (lift ν↑) ν↑)

ladPushW m rs lad []       = nilOut lad
ladPushW m rs lad (w ∷ ws) =
  seqOut (W0l w) (W0ls ws) (ladPush m rs lad (lw0 w)) (ladPushW m rs (new (ladPush m rs lad (lw0 w))) ws)

pushPost m rs lad []       = nilOut lad
pushPost m rs lad (p ∷ ps) =
  seqOut (Pl p) (Pls ps) (pushPost1 m rs lad p) (pushPost m rs (new (pushPost1 m rs lad p)) ps)

pushPost1 m rs lad pH   = pass1 lad h₀ mH Eq.refl Eq.refl
pushPost1 m rs lad pS   = pass1 lad s₀ mS Eq.refl Eq.refl
pushPost1 m rs lad pν   = pass1 lad 𝕟 mν Eq.refl Eq.refl
pushPost1 m rs lad (pin w) =
  convOut (PB.cong PB.refl (⟪↑⟫ (W0l w))) (liftOut (ladPush m (down {₁₊ m} rs) lad (lw0 w)))
pushPost1 m rs lad pstr = straddle m rs lad

straddle zero rs (top c) = out (map sc→M (proj₂ (ruleSC c))) (top (proj₁ (ruleSC c)))
  (PB.trans (PB.cong (PB.sym (⟪↑⟫ (Cl c))) PB.refl)
  (PB.trans (rule→ (ruleSC-ok (rel₂ {0} rs) c))
    (PB.cong (≡⇒≈ (Eq.sym (Eq.cong ⟪_⟫ (sc→M-l (proj₂ (ruleSC c)))))) (⟪↑⟫ (Cl (proj₁ (ruleSC c)))))))
straddle (suc m) rs (b ∷ᴮ lad) = stepS (rel₃ {m} rs) b lad (pushPost2 m (down {₂₊ m} rs) lad (proj₂ (ruleS b)))

pushPost2 m rs lad []       = nilOut lad
pushPost2 m rs lad (q ∷ qs) =
  seqOut (P2l q) (P2ls qs) (pushPost21 m rs lad q) (pushPost2 m rs (new (pushPost21 m rs lad q)) qs)

pushPost21 m rs lad (qd q) = passOut lad (Ql q ∷ []) (q→M q ∷ [])
  (PB.sym (low2s-comm (Ql q ∷ []) (q-low2 q) ⟦ lad ⟧ᴸ)) (Eq.cong ⟪_⟫ (Eq.cong (_++ []) (Eq.sym (q→M-l q))))
pushPost21 m rs lad qν = passOut lad (𝕟 ∷ []) (mν ∷ [])
  (PB.sym (low2s-comm (𝕟 ∷ []) Eq.refl ⟦ lad ⟧ᴸ)) Eq.refl
pushPost21 m rs lad (qin w) =
  convOut (PB.cong PB.refl (PB.trans (⟪↑⟫ (map _↥ (W0l w))) (lift (⟪↑⟫ (W0l w)))))
    (liftOut (liftOut (ladPush m (down {₁₊ m} rs) lad (lw0 w))))
pushPost21 m rs lad qstr =
  convOut (PB.cong PB.refl (⟪↑⟫ (c₀ ∷ []))) (liftOut (straddle m rs lad))
