------------------------------------------------------------------------
-- Presentations of groups
--
-- The decisions behind DecodingChecks: a decoded letter against the
-- letter, by stored matrices
--
-- A Hadamard-free letter decodes to a word in 21 atoms on three wires
-- (DecodingChecks.Atoms), so its decoding is decided on products of the
-- atoms' matrices: the atoms are the factors of a ProdEval family, read
-- once for every letter that a boolean decides (`okD`, `okD-sound`), and
-- the letter is read by Checks8's row operations, the two compared at
-- the difference of their powers of √2 (Checks8.Base.cmpR).  Read gate by gate, as
-- a Hadamard pair still is (`decideD`), the 512 signed exchanges took
-- about 100 s.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.Base where

open import Data.Bool using (Bool ; true ; false ; _∧_)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧ ; ⟦_⟧M ; ⟦⟧-ix ; len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R ; ⟦⟧R-ix ; rix)
open import Examples.Groups.Real-Clifford+CH.ProdEval
  using (at ; expand ; prodM ; lenW ; prod-reads ; lenW-lens)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Decoding using () renaming (d to D)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Checks8.Base
  using (module BF ; runP ; I₃ ; PR-ix ; cmpR ; cmpR-sound)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.Atoms
  using (Atom ; zA ; loA ; hiA ; atomR ; hf ; skW ; sk-word)

open BF public using (⟦_⟧Y)

private
  ∧-l : ∀ {x y : Bool} → x ∧ y ≡ true → x ≡ true
  ∧-l {true} _ = Eq.refl

  ∧-r : ∀ {x y : Bool} → x ∧ y ≡ true → y ≡ true
  ∧-r {true} h = h

------------------------------------------------------------------------
-- A circuit against a word over P, read gate by gate

decideD : Circuit 3 → Word (GenP 3) → Bool
decideD w u = cmpR (proj₁ ⟦ u ⟧Y) (entries ⟦ w ⟧R) (len w) (runP u I₃)

decideD-sound : (w : Circuit 3) (u : Word (GenP 3)) → decideD w u ≡ true → ⟦ w ⟧ ~ ⟦ u ⟧Y
decideD-sound w u h x y =
  Eq.trans (Eq.cong (λ z → √2^ proj₁ ⟦ u ⟧Y * z) (⟦⟧R-ix w x y))
    (Eq.trans (cmpR-sound (proj₁ ⟦ u ⟧Y) (entries ⟦ w ⟧R) (len w) (runP u I₃) h x y)
              (Eq.cong (λ z → √2^ len w * z) (Eq.sym (PR-ix u x y))))

-- A letter of P against its decoding.
check : Word (GenP 3) → Bool
check u = decideD ((D ʷ) u) u

------------------------------------------------------------------------
-- The atoms on three wires, as the factors of a family

-- The names, in the order of the factors.
private
  ok : ℕ → Bool
  ok (suc (suc (suc (suc (suc (suc (suc _))))))) = false
  ok _                                           = true

okA : Atom → Bool
okA (zA a)  = ok a
okA (loA a) = ok a
okA (hiA a) = ok a

atomIx : Atom → ℕ
atomIx (zA a)  = a
atomIx (loA a) = 7 +ℕ a
atomIx (hiA a) = 14 +ℕ a

atoms : List (Circuit 3)
atoms = map atomR
  (zA 0 ∷ zA 1 ∷ zA 2 ∷ zA 3 ∷ zA 4 ∷ zA 5 ∷ zA 6 ∷
   loA 0 ∷ loA 1 ∷ loA 2 ∷ loA 3 ∷ loA 4 ∷ loA 5 ∷ loA 6 ∷
   hiA 0 ∷ hiA 1 ∷ hiA 2 ∷ hiA 3 ∷ hiA 4 ∷ hiA 5 ∷ hiA 6 ∷ [])

private
  at-ix : ∀ x → okA x ≡ true → at atoms (atomIx x) ≡ atomR x
  at-ix (zA 0)  _ = Eq.refl
  at-ix (zA 1)  _ = Eq.refl
  at-ix (zA 2)  _ = Eq.refl
  at-ix (zA 3)  _ = Eq.refl
  at-ix (zA 4)  _ = Eq.refl
  at-ix (zA 5)  _ = Eq.refl
  at-ix (zA 6)  _ = Eq.refl
  at-ix (zA (suc (suc (suc (suc (suc (suc (suc _)))))))) ()
  at-ix (loA 0) _ = Eq.refl
  at-ix (loA 1) _ = Eq.refl
  at-ix (loA 2) _ = Eq.refl
  at-ix (loA 3) _ = Eq.refl
  at-ix (loA 4) _ = Eq.refl
  at-ix (loA 5) _ = Eq.refl
  at-ix (loA 6) _ = Eq.refl
  at-ix (loA (suc (suc (suc (suc (suc (suc (suc _)))))))) ()
  at-ix (hiA 0) _ = Eq.refl
  at-ix (hiA 1) _ = Eq.refl
  at-ix (hiA 2) _ = Eq.refl
  at-ix (hiA 3) _ = Eq.refl
  at-ix (hiA 4) _ = Eq.refl
  at-ix (hiA 5) _ = Eq.refl
  at-ix (hiA 6) _ = Eq.refl
  at-ix (hiA (suc (suc (suc (suc (suc (suc (suc _)))))))) ()

-- Every name of a skeleton is among the factors.
okW : Word Atom → Bool
okW [ x ]ʷ  = okA x
okW ε       = true
okW (s • t) = okW s ∧ okW t

private
  expand-ix : ∀ s → okW s ≡ true → expand atoms (wmap atomIx s) ≡ (atomR ʷ) s
  expand-ix [ x ]ʷ  h = at-ix x h
  expand-ix ε       h = Eq.refl
  expand-ix (s • t) h =
    Eq.cong₂ _•_ (expand-ix s (∧-l {okW s} h)) (expand-ix t (∧-r {okW s} h))

------------------------------------------------------------------------
-- A Hadamard-free word over P against its decoding, decided on the
-- atoms' matrices
--
-- The matrices and lengths of the factors are arguments, so that a
-- boolean over many letters reads each atom once: pass
-- `map ⟦_⟧R atoms` and `map len atoms`.

cmp : List (Mat 3) → List ℕ → Word (GenP 3) → Word ℕ → Bool
cmp ms ls u e = cmpR (proj₁ ⟦ u ⟧Y) (entries (prodM ms e)) (lenW ls e) (runP u I₃)

okS : List (Mat 3) → List ℕ → Word (GenP 3) → Word Atom → Bool
okS ms ls u s = okW s ∧ cmp ms ls u (wmap atomIx s)

okD : List (Mat 3) → List ℕ → Word (GenP 3) → Bool
okD ms ls u = hf u ∧ okS ms ls u (skW u)

private
  cmp-sound : ∀ u e → cmp (map ⟦_⟧R atoms) (map len atoms) u e ≡ true →
              ⟦ expand atoms e ⟧ ~ ⟦ u ⟧Y
  cmp-sound u e h x y =
    Eq.trans (Eq.cong (λ z → √2^ ℓ * z)
                      (Eq.trans (⟦⟧-ix w x y) (Eq.cong (λ M → ix M x y) (Eq.sym (prod-reads atoms e)))))
      (Eq.trans (cmpR-sound ℓ (entries P) L (runP u I₃) h x y)
        (Eq.trans (Eq.cong (λ j → √2^ j * rix (runP u I₃) x y) (lenW-lens atoms e))
                  (Eq.cong (λ z → √2^ len w * z) (Eq.sym (PR-ix u x y)))))
    where
    w : Circuit 3
    w = expand atoms e

    P : Mat 3
    P = prodM (map ⟦_⟧R atoms) e

    ℓ L : ℕ
    ℓ = proj₁ ⟦ u ⟧Y
    L = lenW (map len atoms) e

okD-sound : ∀ u → okD (map ⟦_⟧R atoms) (map len atoms) u ≡ true → ⟦ (D ʷ) u ⟧ ~ ⟦ u ⟧Y
okD-sound u h =
  Eq.subst (λ w → ⟦ w ⟧ ~ ⟦ u ⟧Y) (Eq.sym word)
    (cmp-sound u (wmap atomIx (skW u)) (∧-r {okW (skW u)} h₂))
  where
  h₂ : okS (map ⟦_⟧R atoms) (map len atoms) u (skW u) ≡ true
  h₂ = ∧-r {hf u} h

  word : (D ʷ) u ≡ expand atoms (wmap atomIx (skW u))
  word = Eq.trans (sk-word u (∧-l {hf u} h))
                  (Eq.sym (expand-ix (skW u) (∧-l {okW (skW u)} h₂)))
