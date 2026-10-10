------------------------------------------------------------------------
-- Presentations of groups
--
-- Decision trees for the hard edge, and their check.
--
-- A tree works on a window of m local indices of a state at L (of
-- which two, ic and id, are the hard pair) whose local entries are the
-- values of forms in r variables.  Its nodes:
--
-- * leaf: a decorated diagram (20) or (30) (Routes), which must pass
--   the route check (Check) and have the hard pair as its H;
-- * split: on the parity of a form g with coefficient 1 at v (Subst);
-- * extend: a new local index, outside the window, whose entry is
--   √2^δ times an odd element (of class κ if given): at the state after
--   the route R, all local entries are divisible by √2^δ, two disjoint
--   pairs of their quotients have odd sums (so at least two are odd),
--   and the quotients have an odd number of odd entries (of class κ);
--   for δ ≥ 2, the window holds for each depth below δ two tagged
--   entries of different classes there (minimality then puts every
--   entry outside the window at depth δ at least);
-- * conj: a letter g, apart from the pair (or Z at id), that is an
--   edge out of the state and out of the pair's H applied to it;
-- * relabel: a permutation of the window, possibly reversing the pair;
-- * useNF: a change of variables into a normal form, whose tree is
--   checked once.
--
-- Tags record the depths of the entries added by extend.  The flag
-- mini says that the state is minimal (no two entries of depth 1, or
-- of depth 2, of one class); extend needs it, and conj H drops it.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; _xor_ ; if_then_else_)
open import Data.Fin.Base using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; length)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _≤ᵇ_ ; _≡ᵇ_)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_ ; _[_]≔_)
open import Relation.Nullary.Decidable using (does)

open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ)
open import Examples.Groups.Clifford+CS-TwoLevel.Vector using (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (Z ; module ZR ; √2ᶻ ; _^ᶻ_ ; _≟ᶻ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Subst
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Routes using (diag20 ; diag30 ; decoRoute)

private
  variable
    m r : ℕ

------------------------------------------------------------------------
-- Booleans on indices and forms

infix 4 _==_

_==_ : Fin m → Fin m → Bool
i == j = does (i FinP.≟ j)

-- Every index of the list is not i.
avoid : Fin m → List (Fin m) → Bool
avoid i [] = true
avoid i (j ∷ js) = not (j == i) ∧ avoid i js

-- No entry of a vector is i.
notInV : ∀ {k} → Fin m → Vec (Fin m) k → Bool
notInV i [] = true
notInV i (j ∷ js) = not (j == i) ∧ notInV i js

-- The entries of a vector are distinct.
distinctV : ∀ {k} → Vec (Fin m) k → Bool
distinctV [] = true
distinctV (i ∷ is) = notInV i is ∧ distinctV is

-- Some entry of a vector is j.
anyV : ∀ {k} → Fin m → Vec (Fin m) k → Bool
anyV j [] = false
anyV j (i ∷ is) = (i == j) ∨ anyV j is

-- P holds at every index.
allFin : ∀ {k} → (Fin k → Bool) → Bool
allFin {zero} P = true
allFin {suc k} P = P zero ∧ allFin (λ j → P (suc j))

-- Every index is an entry: with distinctV, a permutation of the window.
ontoV : Vec (Fin m) m → Bool
ontoV π = allFin (λ j → anyV j π)

-- Equality of forms.
eqZ : Z → Z → Bool
eqZ x y = does (x ≟ᶻ y)

eqV : ∀ {k} → Vec Z k → Vec Z k → Bool
eqV [] [] = true
eqV (x ∷ xs) (y ∷ ys) = eqZ x y ∧ eqV xs ys

eqF : Form r → Form r → Bool
eqF (form k cs) (form l ds) = eqZ k l ∧ eqV cs ds

eqFs : ∀ {k} → Vec (Form r) k → Vec (Form r) k → Bool
eqFs [] [] = true
eqFs (f ∷ fs) (g ∷ gs) = eqF f g ∧ eqFs fs gs

eqMN : Maybe ℕ → Maybe ℕ → Bool
eqMN nothing nothing = true
eqMN (just a) (just b) = a ≡ᵇ b
eqMN _ _ = false

eqTags : ∀ {k} → Vec (Maybe ℕ) k → Vec (Maybe ℕ) k → Bool
eqTags [] [] = true
eqTags (x ∷ xs) (y ∷ ys) = eqMN x y ∧ eqTags xs ys

------------------------------------------------------------------------
-- Forms: zero, sums, composition, division by powers of √2

zeroF : Form r
zeroF = form ZR.0# (Vec.replicate _ ZR.0#)

sumF : Vec (Form r) m → Form r
sumF [] = zeroF
sumF (f ∷ fs) = f ⊕ sumF fs

-- The sum of the odd forms.
oddSumF : Vec (Form r) m → Form r
oddSumF [] = zeroF
oddSumF (f ∷ fs) = if oddF f then f ⊕ oddSumF fs else oddSumF fs

-- Σ cᵢ τᵢ.
combF : ∀ {k} → Vec Z k → Vec (Form r) k → Form r
combF [] [] = zeroF
combF (c ∷ cs) (t ∷ τ) = (c ⊛ t) ⊕ combF cs τ

-- f with its variables replaced by the forms τ.
compF : ∀ {r′} → Form r′ → Vec (Form r) r′ → Form r
compF (form k cs) τ = form k (Vec.replicate _ ZR.0#) ⊕ combF cs τ

halfFⁿ : ℕ → Form r → Maybe (Form r)
halfFⁿ zero f = just f
halfFⁿ (suc δ) f with halfF f
... | just g = halfFⁿ δ g
... | nothing = nothing

halfVⁿ : ℕ → Vec (Form r) m → Maybe (Vec (Form r) m)
halfVⁿ δ [] = just []
halfVⁿ δ (f ∷ fs) with halfFⁿ δ f | halfVⁿ δ fs
... | just g | just gs = just (g ∷ gs)
... | _ | _ = nothing

-- The forms after a route (with distinct indices).
runF : Route m → Vec (Form r) m → Maybe (Vec (Form r) m)
runF [] fs = just fs
runF (g ∷ gs) fs with distinctF g | stepF g fs
... | true | just fs′ = runF gs fs′
... | _ | _ = nothing

------------------------------------------------------------------------
-- Leaves

data LeafD (m : ℕ) : Set where
  l20 : Vec (Fin m) 4 → List (Fin m) → Bool → LeafD m
  l30 : Vec (Fin m) 6 → List (Fin m) → Bool → LeafD m

leafRoute : LeafD m → Route m
leafRoute (l20 lab Q fl) = decoRoute diag20 (Vec.lookup lab) Q fl
leafRoute (l30 lab Q fl) = decoRoute diag30 (Vec.lookup lab) Q fl

-- The two ends of the core H are the pair (reversed with flip).
endsOK : Fin m → Fin m → Fin m → Fin m → Bool → Bool
endsOK ic id a b false = (a == ic) ∧ (b == id)
endsOK ic id a b true = (a == id) ∧ (b == ic)

leafOK : Fin m → Fin m → LeafD m → Bool
leafOK ic id (l20 (a ∷ b ∷ lab) Q fl) = distinctV (a ∷ b ∷ lab) ∧ endsOK ic id a b fl ∧ avoid a Q
leafOK ic id (l30 (a ∷ b ∷ lab) Q fl) = distinctV (a ∷ b ∷ lab) ∧ endsOK ic id a b fl ∧ avoid a Q

------------------------------------------------------------------------
-- Extensions

-- At least two odd quotients: two disjoint pairs with odd sums.
certOK : Vec (Form r) m → Fin m → Fin m → Fin m → Fin m → Bool
certOK gs a b c d = distinctV (a ∷ b ∷ c ∷ d ∷ []) ∧ oddF (gs ! a ⊕ gs ! b) ∧ oddF (gs ! c ⊕ gs ! d)

-- An odd number of odd quotients (of class κ).
countOK : Maybe Bool → Vec (Form r) m → Bool
countOK nothing gs = oddF (sumF gs)
countOK (just b) gs with noddF gs | clsF (oddSumF gs)
... | just c | just c₁ = if b then c₁ else oddℕ c xor c₁
... | _ | _ = false

-- Two tagged entries of depth δ′ whose quotients differ in class.
pairOK : ℕ → Vec (Maybe ℕ) m → Vec (Form r) m → Fin m × Fin m → Bool
pairOK δ′ tags fs (a , b) with tags ! a | tags ! b | halfFⁿ δ′ (fs ! a) | halfFⁿ δ′ (fs ! b)
... | just δa | just δb | just qa | just qb = (δa ≡ᵇ δ′) ∧ (δb ≡ᵇ δ′) ∧ sameCls (clsF (qa ⊕ qb))
  where
  sameCls : Maybe Bool → Bool
  sameCls (just true) = true
  sameCls _ = false
... | _ | _ | _ | _ = false

pairsOK : ℕ → Vec (Maybe ℕ) m → Vec (Form r) m → List (Fin m × Fin m) → Bool
pairsOK δ′ tags fs [] = true
pairsOK δ′ tags fs (ab ∷ ps) = pairOK δ′ tags fs ab ∧ pairsOK (suc δ′) tags fs ps

extOK : ℕ → Maybe Bool → Route m → Fin m → Fin m → Fin m → Fin m → List (Fin m × Fin m) →
        Vec (Maybe ℕ) m → Vec (Form r) m → Bool
extOK δ κ R a b c d ps tags fs with runF R fs
... | nothing = false
... | just fs′ with halfVⁿ δ fs′
...   | nothing = false
...   | just gs = (δ ≤ᵇ 3) ∧ (suc (length ps) ≡ᵇ δ) ∧ pairsOK 1 tags fs ps ∧ certOK gs a b c d ∧ countOK κ gs

-- The form of the new entry: √2^δ (1 + √2 κ + 2 v), or √2^δ (1 + √2 v).
newF : ℕ → Maybe Bool → Form (suc r)
newF δ (just b) = (√2ᶻ ^ᶻ δ) ⊛ form (ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b) ((ZR.1# ZR.+ ZR.1#) ∷ Vec.replicate _ ZR.0#)
newF δ nothing = (√2ᶻ ^ᶻ δ) ⊛ form ZR.1# (√2ᶻ ∷ Vec.replicate _ ZR.0#)

------------------------------------------------------------------------
-- Conjugation

-- The letter out of H_pair s: g itself, or X on the pair for Z at id.
conjLetter : Fin m → Fin m → Let m → Let m
conjLetter ic id (Zˡ i) = if i == id then Xˡ ic id else Zˡ i
conjLetter ic id g = g

apart : Fin m → Fin m → Let m → Bool
apart ic id (Zˡ i) = not (i == ic)
apart ic id (Hˡ u v) = not (u == ic) ∧ not (u == id) ∧ not (v == ic) ∧ not (v == id)
apart ic id (Xˡ _ _) = false

atL? : Maybe (Vec (Form r) m) → Bool
atL? (just fs) with kindF fs
... | just atL = true
... | _ = false
atL? nothing = false

conjOK : Fin m → Fin m → Let m → Vec (Form r) m → Bool
conjOK ic id g fs with stepF (Hˡ ic id) fs
... | nothing = false
... | just fcd = apart ic id g ∧ check (g ∷ []) fs ∧ atL? (stepF g fs) ∧ check (conjLetter ic id g ∷ []) fcd

tagsAfter : Let m → Vec (Maybe ℕ) m → Vec (Maybe ℕ) m
tagsAfter (Hˡ u v) tags = (tags [ u ]≔ nothing) [ v ]≔ nothing
tagsAfter _ tags = tags

miniAfter : Let m → Bool → Bool
miniAfter (Hˡ _ _) _ = false
miniAfter _ b = b

------------------------------------------------------------------------
-- Reversing the pair: Hs c d = Xs d c • Z c • Hs d c

flipOK : Fin m → Fin m → Vec (Form r) m → Bool
flipOK ic id fs with stepF (Hˡ id ic) fs
... | just fN = check (Zˡ ic ∷ Xˡ id ic ∷ []) fN
... | nothing = false

------------------------------------------------------------------------
-- Normal forms

data NF : Set where
  nf38 nf341 : NF

nfRows nfVars : NF → ℕ
nfRows nf38 = 6
nfRows nf341 = 4
nfVars nf38 = 14
nfVars nf341 = 12

record NFData (nf : NF) : Set where
  field
    forms : Vec (Form (nfVars nf)) (nfRows nf)
    tags  : Vec (Maybe ℕ) (nfRows nf)
    ic id : Fin (nfRows nf)
    mini  : Bool

------------------------------------------------------------------------
-- Trees and their check

data Tree : ℕ → ℕ → Set where
  leaf    : ∀ {m r} → LeafD m → Tree m r
  split   : ∀ {m r} → Fin r → Form r → Tree m r → Tree m r → Tree m r
  extend  : ∀ {m r} (δ : ℕ) (κ : Maybe Bool) → Route m → (a b c d : Fin m) → List (Fin m × Fin m) →
            Tree (suc m) (suc r) → Tree m r
  conj    : ∀ {m r} → Let m → Tree m r → Tree m r
  relabel : ∀ {m r} → Vec (Fin m) m → Bool → (ic′ id′ : Fin m) → Tree m r → Tree m r
  useNF   : ∀ {r} (nf : NF) → Vec (Form r) (nfVars nf) → Tree (nfRows nf) r

module Checker (nfData : (nf : NF) → NFData nf) (allow : NF → Bool) where

  checkT : Tree m r → Vec (Maybe ℕ) m → Bool → Fin m → Fin m → Vec (Form r) m → Bool
  checkT (leaf ld) tags mini ic id fs = leafOK ic id ld ∧ check (leafRoute ld) fs
  checkT (split v g t₀ t₁) tags mini ic id fs =
    isOne (co g ! v) ∧ checkT t₀ tags mini ic id (Vec.map (substF v (splitH v g false)) fs)
                     ∧ checkT t₁ tags mini ic id (Vec.map (substF v (splitH v g true)) fs)
  checkT (extend δ κ R a b c d ps t) tags mini ic id fs =
    mini ∧ extOK δ κ R a b c d ps tags fs ∧ checkT t (just δ ∷ tags) true (suc ic) (suc id) (newF δ κ ∷ Vec.map liftF fs)
  checkT (conj g t) tags mini ic id fs with stepF g fs
  ... | nothing = false
  ... | just fs′ = conjOK ic id g fs ∧ checkT t (tagsAfter g tags) (miniAfter g mini) ic id fs′
  checkT (relabel π sw ic′ id′ t) tags mini ic id fs =
    distinctV π ∧ ontoV π ∧ (π ! ic′ == (if sw then id else ic)) ∧ (π ! id′ == (if sw then ic else id))
      ∧ (if sw then flipOK ic id fs else true)
      ∧ checkT t (Vec.map (tags !_) π) mini ic′ id′ (Vec.map (fs !_) π)
  checkT (useNF nf τ) tags mini ic id fs =
    allow nf ∧ (ic == NFData.ic (nfData nf)) ∧ (id == NFData.id (nfData nf)) ∧ eqTags tags (NFData.tags (nfData nf))
      ∧ (if NFData.mini (nfData nf) then mini else true)
      ∧ eqFs (Vec.map (λ f → compF f τ) (NFData.forms (nfData nf))) fs
