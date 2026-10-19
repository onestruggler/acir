------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix of a decoded word in the nine letters determines its
-- signed permutation.
--
-- A decoded word acts on the signed basis vectors ±e_k as its signed
-- permutation (`act-sp`), letter by letter: each letter is checked on
-- the sixteen signed basis vectors by one boolean (`letter-act`).  A
-- column of the matrix is the action on a basis vector
-- (GeneralN.ClassicalSemantics.quantum-column), and a signed basis
-- vector is read back to its index and sign (`read-sbasis`), so two
-- decoded words with one matrix have one signed permutation
-- (`sp-of-matrix`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Columns where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _xor_ ; T ; if_then_else_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)
import Data.Bool.Properties as BP
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; map ; lookup ; tabulate)
import Data.Vec.Properties as VP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; cong ; sym ; trans ; subst)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as A
import Examples.Groups.CCX+HH.Semantics as Q
open import Examples.Groups.CCX+HH.Decide using (eqD ; eqVec ; by-eqᵛ)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum ; quantum-column)

open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Kit using (Circuit ; ⟪_⟫)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Circuit.Letters using (dec)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Perm using (SP ; ID ; act ; mul ; lookup-mul ; vec-ext)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Gamma using (L ; x0 ; x1 ; x2 ; cx0 ; cx1 ; cxr0 ; cxr1 ; ccx0 ; z1 ; spL ; sp)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Invariants using (ιD)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fin8 using (allFin ; allFin-sound ; eqF ; eqF-sound)

------------------------------------------------------------------------
-- Signed basis vectors

sbasis : Fin 8 × Bool → Vec D 8
sbasis (k , false) = basis k
sbasis (k , true)  = map -ᴰ_ (basis k)

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = refl

  ∧-r : ∀ a {b} → a ∧ b ≡ true → b ≡ true
  ∧-r true h = h

  toT : ∀ {b} → b ≡ true → T b
  toT refl = tt

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  private
    same : Vec D 8 → Vec D 8 → Bool
    same = eqVec eqD

    chk : L → Fin 8 → Bool
    chk ℓ k = same (quantum ⟪ dec ℓ ⟫ (sbasis (k , false))) (sbasis (act (spL ℓ) (k , false)))
            ∧ same (quantum ⟪ dec ℓ ⟫ (sbasis (k , true))) (sbasis (act (spL ℓ) (k , true)))

    chk-ok : ∀ ℓ → allFin 8 (chk ℓ) ≡ true
    chk-ok x0   = refl
    chk-ok x1   = refl
    chk-ok x2   = refl
    chk-ok cx0  = refl
    chk-ok cx1  = refl
    chk-ok cxr0 = refl
    chk-ok cxr1 = refl
    chk-ok ccx0 = refl
    chk-ok z1   = refl

  letter-act : ∀ ℓ p → quantum ⟪ dec ℓ ⟫ (sbasis p) ≡ sbasis (act (spL ℓ) p)
  letter-act ℓ (k , false) = by-eqᵛ (toT (∧-l (allFin-sound 8 (chk ℓ) (chk-ok ℓ) k)))
  letter-act ℓ (k , true)  = by-eqᵛ (toT (∧-r (same (quantum ⟪ dec ℓ ⟫ (sbasis (k , false))) (sbasis (act (spL ℓ) (k , false))))
    (allFin-sound 8 (chk ℓ) (chk-ok ℓ) k)))

------------------------------------------------------------------------
-- Reading a signed basis vector back

eqB : Bool → Bool → Bool
eqB true  true  = true
eqB false false = true
eqB _     _     = false

eqP : Fin 8 × Bool → Fin 8 × Bool → Bool
eqP (a , s) (b , t) = eqF a b ∧ eqB s t

eqP-sound : ∀ p q → eqP p q ≡ true → p ≡ q
eqP-sound (a , s) (b , t) h = Eq.cong₂ _,_ (eqF-sound a b (∧-l h)) (eqB-sound s t (∧-r (eqF a b) h))
  where
  eqB-sound : ∀ x y → eqB x y ≡ true → x ≡ y
  eqB-sound true  true  _ = refl
  eqB-sound false false _ = refl

cands : List (Fin 8 × Bool)
cands = (₀ , false) ∷ (₀ , true) ∷ (₁ , false) ∷ (₁ , true) ∷ (₂ , false) ∷ (₂ , true) ∷
        (₃ , false) ∷ (₃ , true) ∷ (₄ , false) ∷ (₄ , true) ∷ (₅ , false) ∷ (₅ , true) ∷
        (₆ , false) ∷ (₆ , true) ∷ (₇ , false) ∷ (₇ , true) ∷ []

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  read : Vec D 8 → Fin 8 × Bool
  read v = find cands
    where
    find : List (Fin 8 × Bool) → Fin 8 × Bool
    find []       = ₀ , false
    find (p ∷ ps) = if eqVec eqD v (sbasis p) then p else find ps

  private
    rd : Fin 8 → Bool
    rd k = eqP (read (sbasis (k , false))) (k , false) ∧ eqP (read (sbasis (k , true))) (k , true)

    rd-ok : allFin 8 rd ≡ true
    rd-ok = refl

  read-sbasis : ∀ p → read (sbasis p) ≡ p
  read-sbasis (k , false) = eqP-sound _ _ (∧-l (allFin-sound 8 rd rd-ok k))
  read-sbasis (k , true)  = eqP-sound _ _ (∧-r (eqP (read (sbasis (k , false))) (k , false))
                                               (allFin-sound 8 rd rd-ok k))

------------------------------------------------------------------------
-- A decoded word acts as its signed permutation

E9 : Word (Fin 9) → Word L
E9 = (λ x → [ ιD x ]ʷ) ʷ

F9 : Word (Fin 9) → Circuit 3
F9 = (λ x → ⟪ dec (ιD x) ⟫) ʷ

private
  act-mul : ∀ a b p → act (mul a b) p ≡ act a (act b p)
  act-mul a b (j , s) rewrite lookup-mul a b j =
    cong (proj₁ (lookup a (proj₁ (lookup b j))) ,_)
      (sym (BP.xor-assoc s (proj₂ (lookup b j)) (proj₂ (lookup a (proj₁ (lookup b j))))))

  act-id : ∀ p → act ID p ≡ p
  act-id (j , s) rewrite VP.lookup∘tabulate (λ i → i , false) j =
    cong (j ,_) (BP.xor-identityʳ s)

act-sp : ∀ w p → quantum (F9 w) (sbasis p) ≡ sbasis (act (sp (E9 w)) p)
act-sp [ x ]ʷ  p = letter-act (ιD x) p
act-sp ε       p = cong sbasis (sym (act-id p))
act-sp (u • v) p = trans (cong (quantum (F9 u)) (act-sp v p))
  (trans (act-sp u (act (sp (E9 v)) p)) (cong sbasis (sym (act-mul (sp (E9 u)) (sp (E9 v)) p))))

-- One matrix, one signed permutation.
sp-of-matrix : ∀ (l m : Word (Fin 9)) → Q.interpret (F9 l) ≡ Q.interpret (F9 m) →
               sp (E9 l) ≡ sp (E9 m)
sp-of-matrix l m eq = vec-ext λ j → trans (sym (at l j)) (trans (cong read (column j)) (at m j))
  where
  at : ∀ w j → read (quantum (F9 w) (basis j)) ≡ lookup (sp (E9 w)) j
  at w j = trans (cong read (act-sp w (j , false))) (read-sbasis _)
  column : ∀ j → quantum (F9 l) (basis j) ≡ quantum (F9 m) (basis j)
  column j = trans (sym (quantum-column (F9 l) j))
    (trans (cong (λ M → A.col M j) eq) (quantum-column (F9 m) j))
