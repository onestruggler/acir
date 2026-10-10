------------------------------------------------------------------------
-- Presentations of groups
--
-- Routes on m local indices, and their check on linear forms.
--
-- A route is a list of letters on Fin m (H i j, X i j, Z i), applied
-- head first.  On numerators at a fixed scale, H i j replaces the
-- entries x, y at i and j by (x + y)/√2 and (x - y)/√2, which Step
-- states as a relation (√2 must divide both).  check runs a route on
-- forms (Forms): each step must divide, and every state must have a
-- known number of odd entries, at most three (below the level) or four
-- (at it); an edge with an end at the level must not be an H on two odd
-- entries of different classes there.
--
-- The lemmas say what a successful check gives for the values of the
-- forms (Route turns it into a path).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_ ; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does)

open import Examples.Groups.Clifford+CS-TwoLevel.Vector using (_!_ ; vec-ext)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (Z ; module ZR ; √2ᶻ ; oddᶻ ; rbit)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms

private
  variable
    m r : ℕ
    A B : Set

------------------------------------------------------------------------
-- Updates at any type (definitionally those of Local at ℤ[√2])

updA₁ : Fin m → A → Vec A m → Vec A m
updA₁ i a e = tabulate (λ l → if does (l FinP.≟ i) then a else e ! l)

updA₂ : Fin m → Fin m → A → A → Vec A m → Vec A m
updA₂ i j a b e = tabulate (λ l → if does (l FinP.≟ i) then a else if does (l FinP.≟ j) then b else e ! l)

private
  map-if : (f : A → B) (d : Bool) (x y : A) → f (if d then x else y) ≡ (if d then f x else f y)
  map-if f true x y = refl
  map-if f false x y = refl

map-upd₁ : (f : A → B) (i : Fin m) (a : A) (e : Vec A m) →
           Vec.map f (updA₁ i a e) ≡ updA₁ i (f a) (Vec.map f e)
map-upd₁ f i a e = vec-ext λ l →
  trans (VecP.lookup-map l f (updA₁ i a e))
    (trans (cong f (VecP.lookup∘tabulate _ l))
      (trans (map-if f (does (l FinP.≟ i)) a (e ! l))
        (trans (cong (if does (l FinP.≟ i) then f a else_) (sym (VecP.lookup-map l f e)))
          (sym (VecP.lookup∘tabulate _ l)))))

map-upd₂ : (f : A → B) (i j : Fin m) (a b : A) (e : Vec A m) →
           Vec.map f (updA₂ i j a b e) ≡ updA₂ i j (f a) (f b) (Vec.map f e)
map-upd₂ f i j a b e = vec-ext λ l →
  trans (VecP.lookup-map l f (updA₂ i j a b e))
    (trans (cong f (VecP.lookup∘tabulate _ l))
      (trans (map-if f (does (l FinP.≟ i)) a _)
        (trans (cong (if does (l FinP.≟ i) then f a else_)
                 (trans (map-if f (does (l FinP.≟ j)) b (e ! l))
                   (cong (if does (l FinP.≟ j) then f b else_) (sym (VecP.lookup-map l f e)))))
          (sym (VecP.lookup∘tabulate _ l)))))

------------------------------------------------------------------------
-- Letters and routes

data Let (m : ℕ) : Set where
  Hˡ : Fin m → Fin m → Let m
  Xˡ : Fin m → Fin m → Let m
  Zˡ : Fin m → Let m

Route : ℕ → Set
Route m = List (Let m)

-- The two indices of a letter differ.
Distinct : Let m → Set
Distinct (Hˡ i j) = i ≢ j
Distinct (Xˡ i j) = i ≢ j
Distinct (Zˡ i) = ⊤

distinctF : Let m → Bool
distinctF (Hˡ i j) = not (does (i FinP.≟ j))
distinctF (Xˡ i j) = not (does (i FinP.≟ j))
distinctF (Zˡ i) = true

distinctF-sound : (g : Let m) → distinctF g ≡ true → Distinct g
distinctF-sound (Hˡ i j) e = at (i FinP.≟ j) e
  where
  at : (d : Dec (i ≡ j)) → not (does d) ≡ true → i ≢ j
  at (yes _) ()
  at (no ne) _ = ne
distinctF-sound (Xˡ i j) e = at (i FinP.≟ j) e
  where
  at : (d : Dec (i ≡ j)) → not (does d) ≡ true → i ≢ j
  at (yes _) ()
  at (no ne) _ = ne
distinctF-sound (Zˡ i) _ = tt

------------------------------------------------------------------------
-- One step on numerators

data Step {m : ℕ} : Let m → Vec Z m → Vec Z m → Set where
  stepH : ∀ {i j : Fin m} {e : Vec Z m} (α β : Z) → e ! i ZR.+ e ! j ≡ √2ᶻ ZR.* α →
          e ! i ZR.- e ! j ≡ √2ᶻ ZR.* β → Step (Hˡ i j) e (updA₂ i j α β e)
  stepX : ∀ {i j : Fin m} {e : Vec Z m} → Step (Xˡ i j) e (updA₂ i j (e ! j) (e ! i) e)
  stepZ : ∀ {i : Fin m} {e : Vec Z m} → Step (Zˡ i) e (updA₁ i (ZR.- (e ! i)) e)

-- The values of forms.
⟦_⟧ᵛ : Vec (Form r) m → Vec Z r → Vec Z m
⟦ fs ⟧ᵛ ρ = Vec.map (λ f → ⟦ f ⟧ ρ) fs

⟦⟧ᵛ-! : (fs : Vec (Form r) m) (ρ : Vec Z r) (i : Fin m) → ⟦ fs ⟧ᵛ ρ ! i ≡ ⟦ fs ! i ⟧ ρ
⟦⟧ᵛ-! fs ρ i = VecP.lookup-map i (λ f → ⟦ f ⟧ ρ) fs

-- One step on forms.
stepF : Let m → Vec (Form r) m → Maybe (Vec (Form r) m)
stepF (Hˡ i j) fs with halfF (fs ! i ⊕ fs ! j) | halfF (fs ! i ⊖ fs ! j)
... | just a | just b = just (updA₂ i j a b fs)
... | _ | _ = nothing
stepF (Xˡ i j) fs = just (updA₂ i j (fs ! j) (fs ! i) fs)
stepF (Zˡ i) fs = just (updA₁ i (⊝ (fs ! i)) fs)

stepF-sound : (g : Let m) (fs : Vec (Form r) m) {fs′ : Vec (Form r) m} → stepF g fs ≡ just fs′ →
              ∀ ρ → Step g (⟦ fs ⟧ᵛ ρ) (⟦ fs′ ⟧ᵛ ρ)
stepF-sound (Hˡ i j) fs eq ρ with halfF (fs ! i ⊕ fs ! j) in ha | halfF (fs ! i ⊖ fs ! j) in hb
stepF-sound (Hˡ i j) fs refl ρ | just a | just b =
  subst (Step (Hˡ i j) (⟦ fs ⟧ᵛ ρ)) (sym (map-upd₂ (λ f → ⟦ f ⟧ ρ) i j a b fs))
    (stepH (⟦ a ⟧ ρ) (⟦ b ⟧ ρ)
      (trans (cong₂ ZR._+_ (⟦⟧ᵛ-! fs ρ i) (⟦⟧ᵛ-! fs ρ j)) (trans (sym (⟦⊕⟧ (fs ! i) (fs ! j) ρ)) (halfF-sound (fs ! i ⊕ fs ! j) ha ρ)))
      (trans (cong₂ ZR._-_ (⟦⟧ᵛ-! fs ρ i) (⟦⟧ᵛ-! fs ρ j)) (trans (sym (⟦⊖⟧ (fs ! i) (fs ! j) ρ)) (halfF-sound (fs ! i ⊖ fs ! j) hb ρ))))
stepF-sound (Hˡ i j) fs () ρ | just a | nothing
stepF-sound (Hˡ i j) fs () ρ | nothing | _
stepF-sound (Xˡ i j) fs refl ρ =
  subst (Step (Xˡ i j) (⟦ fs ⟧ᵛ ρ))
    (sym (trans (map-upd₂ (λ f → ⟦ f ⟧ ρ) i j (fs ! j) (fs ! i) fs)
               (cong₂ (λ a b → updA₂ i j a b (⟦ fs ⟧ᵛ ρ)) (sym (⟦⟧ᵛ-! fs ρ j)) (sym (⟦⟧ᵛ-! fs ρ i)))))
    stepX
stepF-sound (Zˡ i) fs refl ρ =
  subst (Step (Zˡ i) (⟦ fs ⟧ᵛ ρ))
    (sym (trans (map-upd₁ (λ f → ⟦ f ⟧ ρ) i (⊝ (fs ! i)) fs)
               (cong (λ a → updA₁ i a (⟦ fs ⟧ᵛ ρ)) (trans (⟦⊝⟧ (fs ! i) ρ) (cong ZR.-_ (sym (⟦⟧ᵛ-! fs ρ i)))))))
    stepZ

------------------------------------------------------------------------
-- Parities of states

-- The number of entries of a vector satisfying P.
countV : (Z → Bool) → Vec Z m → ℕ
countV P [] = 0
countV P (x ∷ e) = (if P x then 1 else 0) ℕ.+ countV P e

-- The number of odd entries of a vector.
noddV : Vec Z m → ℕ
noddV [] = 0
noddV (x ∷ xs) = (if oddᶻ x then 1 else 0) ℕ.+ noddV xs

-- The number of odd forms, when each is odd or even.
noddF : Vec (Form r) m → Maybe ℕ
noddF [] = just 0
noddF (f ∷ fs) with noddF fs
... | nothing = nothing
... | just c = if oddF f then just (suc c) else if evenF f then just c else nothing

private
  if-t : ∀ {d : Bool} {x y : A} → d ≡ true → (if d then x else y) ≡ x
  if-t refl = refl

  if-f : ∀ {d : Bool} {x y : A} → d ≡ false → (if d then x else y) ≡ y
  if-f refl = refl

noddF-sound : (fs : Vec (Form r) m) {c : ℕ} → noddF fs ≡ just c → ∀ ρ → noddV (⟦ fs ⟧ᵛ ρ) ≡ c
noddF-sound [] refl ρ = refl
noddF-sound (f ∷ fs) eq ρ with noddF fs in e
noddF-sound (f ∷ fs) () ρ | nothing
noddF-sound (f ∷ fs) eq ρ | just c with oddF f in o
noddF-sound (f ∷ fs) refl ρ | just c | true =
  cong₂ ℕ._+_ (if-t (oddF-sound f o ρ)) (noddF-sound fs e ρ)
noddF-sound (f ∷ fs) eq ρ | just c | false with evenF f in ev
noddF-sound (f ∷ fs) refl ρ | just c | false | true =
  cong₂ ℕ._+_ (if-f (evenF-sound f ev ρ)) (noddF-sound fs e ρ)
noddF-sound (f ∷ fs) () ρ | just c | false | false

data Kind : Set where
  low atL : Kind

kindN : ℕ → Maybe Kind
kindN 0 = just low
kindN 1 = just low
kindN 2 = just low
kindN 3 = just low
kindN 4 = just atL
kindN _ = nothing

kindF : Vec (Form r) m → Maybe Kind
kindF fs with noddF fs
... | just c = kindN c
... | nothing = nothing

-- What a kind says about the number of odd entries.
kindF-sound : (fs : Vec (Form r) m) {κ : Kind} → kindF fs ≡ just κ → ∀ ρ →
              (κ ≡ low → noddV (⟦ fs ⟧ᵛ ρ) ℕ.< 4) × (κ ≡ atL → noddV (⟦ fs ⟧ᵛ ρ) ≡ 4)
kindF-sound fs eq ρ with noddF fs in e
kindF-sound fs () ρ | nothing
kindF-sound fs eq ρ | just c = at c eq (noddF-sound fs e ρ)
  where
  at : ∀ c {κ} → kindN c ≡ just κ → noddV (⟦ fs ⟧ᵛ ρ) ≡ c →
       (κ ≡ low → noddV (⟦ fs ⟧ᵛ ρ) ℕ.< 4) × (κ ≡ atL → noddV (⟦ fs ⟧ᵛ ρ) ≡ 4)
  at 0 refl n≡ = (λ _ → subst (ℕ._< 4) (sym n≡) (ℕ.s≤s ℕ.z≤n)) , λ ()
  at 1 refl n≡ = (λ _ → subst (ℕ._< 4) (sym n≡) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))) , λ ()
  at 2 refl n≡ = (λ _ → subst (ℕ._< 4) (sym n≡) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))) , λ ()
  at 3 refl n≡ = (λ _ → subst (ℕ._< 4) (sym n≡) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))))) , λ ()
  at 4 refl n≡ = (λ ()) , λ _ → n≡
  at (suc (suc (suc (suc (suc c))))) () n≡

------------------------------------------------------------------------
-- Edges

private
  sameF : Maybe Bool → Maybe Bool → Bool
  sameF (just true) (just true) = true
  sameF (just false) (just false) = true
  sameF _ _ = false

-- H i j is not an H on two odd entries of different classes.
plainF : Let m → Vec (Form r) m → Bool
plainF (Hˡ i j) fs = evenF (fs ! i) ∨ evenF (fs ! j) ∨ sameF (clsF (fs ! i)) (clsF (fs ! j))
plainF (Xˡ i j) fs = true
plainF (Zˡ i) fs = true

-- Not hard, at the values.
Plain : Let m → Vec Z m → Set
Plain (Hˡ i j) e = oddᶻ (e ! i) ≡ true → oddᶻ (e ! j) ≡ true → rbit (e ! i) ≡ rbit (e ! j)
Plain (Xˡ i j) e = ⊤
Plain (Zˡ i) e = ⊤

plainF-sound : (g : Let m) (fs : Vec (Form r) m) → plainF g fs ≡ true → ∀ ρ → Plain g (⟦ fs ⟧ᵛ ρ)
plainF-sound (Hˡ i j) fs eq ρ oi oj = by (evenF (fs ! i)) (evenF (fs ! j)) refl refl eq
  where
  vi = ⟦⟧ᵛ-! fs ρ i
  vj = ⟦⟧ᵛ-! fs ρ j
  t≢f : true ≡ false → ⊥
  t≢f ()
  same : ∀ u v → sameF u v ≡ true → (clsF (fs ! i) ≡ u) → (clsF (fs ! j) ≡ v) →
         rbit (⟦ fs ⟧ᵛ ρ ! i) ≡ rbit (⟦ fs ⟧ᵛ ρ ! j)
  same (just true) (just true) _ ci cj =
    trans (cong rbit vi) (trans (clsF-sound (fs ! i) ci ρ) (sym (trans (cong rbit vj) (clsF-sound (fs ! j) cj ρ))))
  same (just false) (just false) _ ci cj =
    trans (cong rbit vi) (trans (clsF-sound (fs ! i) ci ρ) (sym (trans (cong rbit vj) (clsF-sound (fs ! j) cj ρ))))
  same (just true) (just false) () _ _
  same (just false) (just true) () _ _
  same (just true) nothing () _ _
  same (just false) nothing () _ _
  same nothing _ () _ _
  by : ∀ a b → evenF (fs ! i) ≡ a → evenF (fs ! j) ≡ b →
       a ∨ b ∨ sameF (clsF (fs ! i)) (clsF (fs ! j)) ≡ true → rbit (⟦ fs ⟧ᵛ ρ ! i) ≡ rbit (⟦ fs ⟧ᵛ ρ ! j)
  by true _ ea _ _ = ⊥-elim (t≢f (trans (sym oi) (trans (cong oddᶻ vi) (evenF-sound (fs ! i) ea ρ))))
  by false true _ eb _ = ⊥-elim (t≢f (trans (sym oj) (trans (cong oddᶻ vj) (evenF-sound (fs ! j) eb ρ))))
  by false false _ _ s = same (clsF (fs ! i)) (clsF (fs ! j)) s refl refl
plainF-sound (Xˡ i j) fs eq ρ = tt
plainF-sound (Zˡ i) fs eq ρ = tt

edgeF : Let m → Maybe Kind → Vec (Form r) m → Maybe Kind → Vec (Form r) m → Bool
edgeF g (just low) fs (just low) fs′ = true
edgeF g (just atL) fs (just _) fs′ = plainF g fs
edgeF g (just low) fs (just atL) fs′ = plainF g fs′
edgeF g _ fs _ fs′ = false

------------------------------------------------------------------------
-- The check

check : Route m → Vec (Form r) m → Bool
check [] fs = true
check (g ∷ gs) fs with stepF g fs
... | nothing = false
... | just fs′ = distinctF g ∧ edgeF g (kindF fs) fs (kindF fs′) fs′ ∧ check gs fs′
