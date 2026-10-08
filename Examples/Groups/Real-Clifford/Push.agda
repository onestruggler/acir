------------------------------------------------------------------------
-- Presentations of groups
--
-- Normalisation of real Clifford circuits (Section 5.1)
--
-- A generator in front of a normal form is pushed through it by the
-- typed relations (Tables): through the Z-circuit, which turns it into
-- dirty gates at the positions the paper labels (MIn, the gates an
-- X-circuit can take); through the X-circuit, which leaves gates on the
-- top n − 1 wires and a sign; and those are pushed, one wire down, into
-- the normal form of the top wires.  Every circuit is then equal to a
-- normal form (normalise).
--
-- The pushes through a ladder follow its recursive structure: a gate
-- meets the bottom B gate, and what comes out is either done (on wire
-- 0), an input of the ladder one wire up, or a gate straddling wires 0
-- and 1, which meets that ladder's bottom gate in turn (straddle).  The
-- sizes of the ladders are explicit arguments, the measure of the
-- recursion: the dirty gates are pushed into ladders one size down.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Push where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.List.Properties using (map-++ ; ++-assoc)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine using (⟪_⟫ ; ⟪++⟫ ; ⟪≈⟫ ; ⟪map↥⟫)
open import Examples.Groups.Real-Clifford.Axioms
  using (𝕞 ; h₀ ; h₁ ; h₂ ; z₀ ; z₁ ; z₂ ; c₀ ; c₁)
open import Examples.Groups.Real-Clifford.Reasoning
open import Examples.Groups.Real-Clifford.NormalForm
open import Examples.Groups.Real-Clifford.Tables

private
  variable
    n m k : ℕ
    t u : Ty

------------------------------------------------------------------------
-- The gates an X-circuit takes

data MIn : ℕ → Set where
  mZt      : MIn 1
  mH mZ mC : MIn (₂₊ m)
  mup      : MIn (₁₊ m) → MIn (₂₊ m)
  mneg     : MIn n

Ml : MIn n → List (Gen n)
Ml mZt     = z₀ ∷ []
Ml mH      = h₀ ∷ []
Ml mZ      = z₀ ∷ []
Ml mC      = c₀ ∷ []
Ml (mup g) = map _↥ (Ml g)
Ml mneg    = 𝕞 ∷ []

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
data LIn (t : Ty) : ℕ → Set where
  lw0 : W0 t → LIn t (₁₊ m)
  lup : Gen (₁₊ m) → LIn t (₂₊ m)

LInl : LIn t n → List (Gen n)
LInl (lw0 w) = W0l w
LInl (lup g) = g ↥ ∷ []

⟦_⟧ᴸ↑ : Lad t m → Circuit (₁₊ m)
⟦ l ⟧ᴸ↑ = ⟦ l ⟧ᴸ ↑

⟦_⟧ᴸ↑↑ : Lad t m → Circuit (₂₊ m)
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

  -- A clean gate x meeting g becomes y x'; y is then pushed into l.
  glue : ∀ {l x g y x' o l'} → x • g ≈ y • x' → l • y ≈ o • l' →
         (l • x) • g ≈ o • (l' • x')
  glue {l} {x} {g} {y} {x'} {o} {l'} e₁ e₂ = begin
    (l • x) • g        ≈⟨ assoc ⟩
    l • (x • g)        ≈⟨ back l e₁ ⟩
    l • (y • x')       ≈⟨ sym assoc ⟩
    (l • y) • x'       ≈⟨ front x' e₂ ⟩
    (o • l') • x'      ≈⟨ assoc ⟩
    o • (l' • x')      ∎

  -- The same with two clean gates.
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

  -- Splitting a list.
  split : (xs ys : List (Gen n)) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
  split = ⟪++⟫

  -- A list of dirty gates made of two.
  join : (xs ys : List (MIn n)) → ⟪ Mls xs ⟫ • ⟪ Mls ys ⟫ ≈ ⟪ Mls (xs ++ ys) ⟫
  join xs ys = trans (sym (⟪++⟫ (Mls xs) (Mls ys))) (⟪≈⟫ (Eq.sym (Mls-++ xs ys)))

  -- ⟪ [x] ⟫ is [ x ].
  one : (x : Gen n) → ⟪ x ∷ [] ⟫ ≈ [ x ]ʷ
  one x = right-unit

------------------------------------------------------------------------
-- The letters of derived gates are on the bottom wires

W0l-low1 : (w : W0 t) → all low1 (W0l {n = m} w) ≡ true
W0l-low1 iZ = Eq.refl
W0l-low1 iX = Eq.refl
W0l-low1 iH = Eq.refl

Al-low1 : (a : AT t) → all low1 (Al {n = m} a) ≡ true
Al-low1 A₁ = Eq.refl
Al-low1 A₂ = Eq.refl
Al-low1 A₃ = Eq.refl

Bl-low2 : {u : Ty} (b : BT t u) → all low2 (Bl {n = m} b) ≡ true
Bl-low2 B₁ = Eq.refl
Bl-low2 B₂ = Eq.refl
Bl-low2 B₃ = Eq.refl
Bl-low2 B₄ = Eq.refl
Bl-low2 B₅ = Eq.refl
Bl-low2 B₆ = Eq.refl
Bl-low2 B₇ = Eq.refl
Bl-low2 B₈ = Eq.refl

Dl-low2 : (d : DT) → all low2 (Dl {n = m} d) ≡ true
Dl-low2 D₁ = Eq.refl
Dl-low2 D₂ = Eq.refl
Dl-low2 D₃ = Eq.refl
Dl-low2 D₄ = Eq.refl

El-low1 : (e : ET) → all low1 (El {n = m} e) ≡ true
El-low1 E₁ = Eq.refl
El-low1 E₂ = Eq.refl

------------------------------------------------------------------------
-- Conversions of the outputs of the tables

co→M : CO → MIn 1
co→M coZ   = mZt
co→M coneg = mneg

co→M-l : (cs : List CO) → Mls (map co→M cs) ≡ concatMap (COl {n = 0}) cs
co→M-l []          = Eq.refl
co→M-l (coZ ∷ cs)   = Eq.cong (z₀ ∷_) (co→M-l cs)
co→M-l (coneg ∷ cs) = Eq.cong (𝕞 ∷_) (co→M-l cs)

sc→M : SCO → MIn 2
sc→M scC   = mC
sc→M scZ   = mZ
sc→M scneg = mneg

sc→M-l : (cs : List SCO) → Mls (map sc→M cs) ≡ concatMap (SCOl {n = 0}) cs
sc→M-l []           = Eq.refl
sc→M-l (scC ∷ cs)   = Eq.cong (c₀ ∷_) (sc→M-l cs)
sc→M-l (scZ ∷ cs)   = Eq.cong (z₀ ∷_) (sc→M-l cs)
sc→M-l (scneg ∷ cs) = Eq.cong (𝕞 ∷_) (sc→M-l cs)

q→M : Q01 → MIn (₃₊ m)
q→M qh₀ = mH
q→M qz₀ = mZ
q→M qh₁ = mup mH
q→M qz₁ = mup mZ
q→M qc₀ = mC

q→M-l : (q : Q01) → Ml (q→M {m = m} q) ≡ Ql q ∷ []
q→M-l qh₀ = Eq.refl
q→M-l qz₀ = Eq.refl
q→M-l qh₁ = Eq.refl
q→M-l qz₁ = Eq.refl
q→M-l qc₀ = Eq.refl

q-low2 : (q : Q01) → all low2 (Ql {n = m} q ∷ []) ≡ true
q-low2 qh₀ = Eq.refl
q-low2 qz₀ = Eq.refl
q-low2 qh₁ = Eq.refl
q-low2 qz₁ = Eq.refl
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

  -- One letter as a word.
  [_]≈ : (x : Gen n) → ⟪ x ∷ [] ⟫ ≈ [ x ]ʷ
  [ x ]≈ = right-unit

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

-- The bottom B gate meets an input.
stepB : (b : BT t u) (g : In1 t) (lad : Lad u (₁₊ m)) →
        Out (₂₊ m) (⟦_⟧ᴸ↑ {t = u}) (⟦ lad ⟧ᴸ ↑ • ⟪ Pls (proj₂ (ruleB b g)) ⟫) →
        Out (₂₊ m) (⟦_⟧ᴸ {t = t}) ((⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫) • ⟪ In1l g ⟫)
stepB b g lad (out d lad' e) = out d (proj₁ (ruleB b g) ∷ᴮ lad') (Glue.glue (rule→ (ruleB-ok b g)) e)

-- The bottom two B gates meet CZ on wires 1 and 2.
stepBB : {v : Ty} (b : BT t v) (b₁ : BT v u) (lad : Lad u (₁₊ m)) →
         Out (₃₊ m) (⟦_⟧ᴸ↑↑ {t = u}) (⟦ lad ⟧ᴸ ↑ ↑ • ⟪ P2ls (proj₂ (proj₂ (proj₂ (ruleBB b b₁)))) ⟫) →
         Out (₃₊ m) (⟦_⟧ᴸ {t = t}) (((⟦ lad ⟧ᴸ ↑ ↑ • ⟪ Bl b₁ ⟫ ↑) • ⟪ Bl b ⟫) • ⟪ c₁ ∷ [] ⟫)
stepBB {m = m} b b₁ lad (out d lad' e) =
  out d (proj₁ (proj₂ r) ∷ᴮ proj₁ (proj₂ (proj₂ r)) ∷ᴮ lad') (Glue.glue₂ e₁ e)
  where
  open Width (₃₊ m)
  r = ruleBB b b₁
  e₁ = trans (front _ (sym (⟪↑⟫ (Bl b₁))))
       (trans (rule3→ (ruleBB-ok b b₁)) (back _ (front _ (⟪↑⟫ (Bl (proj₁ (proj₂ (proj₂ r))))))))

-- A letter higher up passes the bottom B gate.
stepUp : (b : BT t u) (lad : Lad u (₂₊ m)) (g : Gen (₁₊ m)) →
         Out (₂₊ m) (⟦_⟧ᴸ {t = u}) (⟦ lad ⟧ᴸ • ⟪ g ↥ ∷ [] ⟫) →
         Out (₃₊ m) (⟦_⟧ᴸ {t = t}) ((⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫) • ⟪ g ↥ ↥ ∷ [] ⟫)
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
pass1 : (lad : Lad u (₁₊ m)) (x : Gen (₂₊ m)) (d : MIn (₂₊ m)) → all low1 (x ∷ []) ≡ true → Ml d ≡ x ∷ [] →
        Out (₂₊ m) (⟦_⟧ᴸ↑ {t = u}) (⟦ lad ⟧ᴸ ↑ • ⟪ x ∷ [] ⟫)
pass1 lad x d e e' = passOut lad (x ∷ []) (d ∷ [])
  (PB.sym (low1s-comm (x ∷ []) e ⟦ lad ⟧ᴸ)) (Eq.cong ⟪_⟫ (Eq.cong (_++ []) (Eq.sym e')))

-- A straddling gate meets the bottom B gate of the ladder above.
stepS : (x : SIn t) (b : BT t u) (lad : Lad u (₁₊ m)) →
        Out (₃₊ m) (⟦_⟧ᴸ↑↑ {t = u}) (⟦ lad ⟧ᴸ ↑ ↑ • ⟪ P2ls (proj₂ (ruleS x b)) ⟫) →
        Out (₃₊ m) (⟦_⟧ᴸ↑ {t = t}) ((⟦ lad ⟧ᴸ ↑ ↑ • ⟪ Bl b ⟫ ↑) • ⟪ Sl x ⟫)
stepS {m = m} x b lad (out d lad' e) = out d (proj₁ (ruleS x b) ∷ᴮ lad') (Glue.glue e₁ e)
  where
  open Width (₃₊ m)
  e₁ = trans (front _ (sym (⟪↑⟫ (Bl b))))
       (trans (rule→ (ruleS-ok x b)) (back _ (⟪↑⟫ (Bl (proj₁ (ruleS x b))))))

-- The scalar passes a ladder.
scalarOut : (lad : Lad t (₁₊ m)) (x : Gen (₁₊ m)) → (₁₊ m) ⊢ [ x ]ʷ ≈ neg →
            Out (₁₊ m) (⟦_⟧ᴸ {t = t}) (⟦ lad ⟧ᴸ • ⟪ x ∷ [] ⟫)
scalarOut {m = m} lad x e = out (mneg ∷ []) lad
  (trans (back _ (trans right-unit e)) (trans (sym (neg-comm _)) (front _ (sym right-unit))))
  where open Width (₁₊ m)

------------------------------------------------------------------------
-- Pushing into ladders
--
-- The first argument is the size of the ladder minus one; it decreases
-- along every recursive path that comes back to the same function.

ladPush   : {t : Ty} (m : ℕ) (lad : Lad t (₁₊ m)) (g : LIn t (₁₊ m)) →
            Out (₁₊ m) (⟦_⟧ᴸ {t = t}) (⟦ lad ⟧ᴸ • ⟪ LInl g ⟫)
ladPushW  : {t : Ty} (m : ℕ) (lad : Lad t (₁₊ m)) (ws : List (W0 t)) →
            Out (₁₊ m) (⟦_⟧ᴸ {t = t}) (⟦ lad ⟧ᴸ • ⟪ W0ls ws ⟫)
pushPost  : {u : Ty} (m : ℕ) (lad : Lad u (₁₊ m)) (ps : List (Post u)) →
            Out (₂₊ m) (⟦_⟧ᴸ↑ {t = u}) (⟦ lad ⟧ᴸ ↑ • ⟪ Pls ps ⟫)
pushPost1 : {u : Ty} (m : ℕ) (lad : Lad u (₁₊ m)) (p : Post u) →
            Out (₂₊ m) (⟦_⟧ᴸ↑ {t = u}) (⟦ lad ⟧ᴸ ↑ • ⟪ Pl p ⟫)
straddle  : {t : Ty} (m : ℕ) (lad : Lad t (₁₊ m)) (x : SIn t) →
            Out (₂₊ m) (⟦_⟧ᴸ↑ {t = t}) (⟦ lad ⟧ᴸ ↑ • ⟪ Sl x ⟫)
pushPost2 : {u : Ty} (m : ℕ) (lad : Lad u (₁₊ m)) (qs : List (Post2 u)) →
            Out (₃₊ m) (⟦_⟧ᴸ↑↑ {t = u}) (⟦ lad ⟧ᴸ ↑ ↑ • ⟪ P2ls qs ⟫)
pushPost21 : {u : Ty} (m : ℕ) (lad : Lad u (₁₊ m)) (q : Post2 u) →
            Out (₃₊ m) (⟦_⟧ᴸ↑↑ {t = u}) (⟦ lad ⟧ᴸ ↑ ↑ • ⟪ P2l q ⟫)

-- The C gate at the top.
ladPush zero (top c) (lw0 w) = out (map co→M (proj₂ (ruleC c w))) (top (proj₁ (ruleC c w)))
  (PB.trans (rule→ (ruleC-ok c w))
    (PB.cong (≡⇒≈ (Eq.sym (Eq.cong ⟪_⟫ (co→M-l (proj₂ (ruleC c w)))))) PB.refl))
ladPush (suc m) (b ∷ᴮ lad) (lw0 w) =
  stepB b (w0 w) lad (pushPost m lad (proj₂ (ruleB b (w0 w))))
ladPush (suc m) (b ∷ᴮ lad) (lup (gate₁ H-gate)) =
  stepB b (w1 gH) lad (pushPost m lad (proj₂ (ruleB b (w1 gH))))
ladPush (suc m) (b ∷ᴮ lad) (lup (gate₁ Z-gate)) =
  stepB b (w1 gZ) lad (pushPost m lad (proj₂ (ruleB b (w1 gZ))))
ladPush (suc (suc m)) (b ∷ᴮ b₁ ∷ᴮ lad) (lup (gate₂ CZ-gate)) =
  stepBB b b₁ lad (pushPost2 m lad (proj₂ (proj₂ (proj₂ (ruleBB b b₁)))))
ladPush (suc (suc m)) (b ∷ᴮ lad) (lup (g ↥)) =
  stepUp b lad g (ladPush (suc m) lad (lup g))
ladPush (suc m) lad (lup (gate₀ neg-gate)) =
  scalarOut lad (gate₀ neg-gate ↥) neg↑
ladPush (suc zero) lad (lup (gate₀ neg-gate ↥)) =
  scalarOut lad (gate₀ neg-gate ↥ ↥) (PB.trans (lift neg↑) neg↑)

ladPushW m lad []       = nilOut lad
ladPushW m lad (w ∷ ws) =
  seqOut (W0l w) (W0ls ws) (ladPush m lad (lw0 w)) (ladPushW m (new (ladPush m lad (lw0 w))) ws)

pushPost m lad []       = nilOut lad
pushPost m lad (p ∷ ps) =
  seqOut (Pl p) (Pls ps) (pushPost1 m lad p) (pushPost m (new (pushPost1 m lad p)) ps)

pushPost1 m lad pH   = pass1 lad h₀ mH Eq.refl Eq.refl
pushPost1 m lad pZ   = pass1 lad z₀ mZ Eq.refl Eq.refl
pushPost1 m lad pneg = pass1 lad 𝕞 mneg Eq.refl Eq.refl
pushPost1 m lad (pin w) =
  convOut (PB.cong PB.refl (⟪↑⟫ (W0l w))) (liftOut (ladPush m lad (lw0 w)))
pushPost1 m lad (pstr x) = straddle m lad x

straddle zero (top c) sCZ = out (map sc→M (proj₂ (ruleSC c))) (top (proj₁ (ruleSC c)))
  (PB.trans (PB.cong (PB.sym (⟪↑⟫ (Cl c))) PB.refl)
  (PB.trans (rule→ (ruleSC-ok c))
    (PB.cong (≡⇒≈ (Eq.sym (Eq.cong ⟪_⟫ (sc→M-l (proj₂ (ruleSC c)))))) (⟪↑⟫ (Cl (proj₁ (ruleSC c)))))))
straddle (suc m) (b ∷ᴮ lad) x = stepS x b lad (pushPost2 m lad (proj₂ (ruleS x b)))

pushPost2 m lad []       = nilOut lad
pushPost2 m lad (q ∷ qs) =
  seqOut (P2l q) (P2ls qs) (pushPost21 m lad q) (pushPost2 m (new (pushPost21 m lad q)) qs)

pushPost21 m lad (qd q) = passOut lad (Ql q ∷ []) (q→M q ∷ [])
  (PB.sym (low2s-comm (Ql q ∷ []) (q-low2 q) ⟦ lad ⟧ᴸ)) (Eq.cong ⟪_⟫ (Eq.cong (_++ []) (Eq.sym (q→M-l q))))
pushPost21 m lad qneg = passOut lad (𝕞 ∷ []) (mneg ∷ [])
  (PB.sym (low2s-comm (𝕞 ∷ []) Eq.refl ⟦ lad ⟧ᴸ)) Eq.refl
pushPost21 m lad (qin w) =
  convOut (PB.cong PB.refl (PB.trans (⟪↑⟫ (map _↥ (W0l w))) (lift (⟪↑⟫ (W0l w)))))
    (liftOut (liftOut (ladPush m lad (lw0 w))))
pushPost21 m lad (qstr x) =
  convOut (PB.cong PB.refl (⟪↑⟫ (Sl x))) (liftOut (straddle m lad x))
