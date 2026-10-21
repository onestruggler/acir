------------------------------------------------------------------------
-- Presentations of groups
--
-- A family of equations between products of shared factors, decided
-- by one boolean
--
-- `evaluated Eq.refl : Evaluated u v` reads both words gate by gate, so
-- a factor that occurs in several equations of a module — the box
-- Λ□ 3, say — is replayed in each, as often as it occurs.  Here the
-- factors are listed once, each equation is a pair of words over their
-- indices (bracketed as the words are, so that `expand` gives them back
-- on the nose), and one boolean decides the whole family on the
-- factors' stored matrices: they are arguments of the boolean, so the
-- evaluator reads each factor once, and an equation is a comparison of
-- products of them (Semantics.Sparse.mulS, which skips zero entries).
-- `fam-eval F E all i` is the i-th equation.  CommEval is the special
-- case of commutations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.ProdEval where

open import Data.Bool using (Bool ; true ; false ; _∧_)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Semantics.Decide
  using (eqM ; eqM-sound ; eqM-refl)
open import Examples.Groups.Real-Clifford+CH.Semantics.Sparse using (mulS ; mulS-ok)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧M ; len)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R ; ⟦⟧R≡⟦⟧M)
open import Examples.Groups.Real-Clifford+CH.Soundness.Relators using (≡-same)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Factors, and words over their indices

-- The i-th factor (ε past the end).
at : List (Circuit k) → ℕ → Circuit k
at []       _       = ε
at (w ∷ ws) zero    = w
at (w ∷ ws) (suc i) = at ws i

-- A word over factor indices, as the circuit it spells.
expand : List (Circuit k) → Word ℕ → Circuit k
expand ws = (at ws) ʷ

-- The same on the factors' matrices and lengths.
atM : List (Mat k) → ℕ → Mat k
atM []       _       = idM
atM (m ∷ ms) zero    = m
atM (m ∷ ms) (suc i) = atM ms i

atL : List ℕ → ℕ → ℕ
atL []       _       = 0
atL (l ∷ ls) zero    = l
atL (l ∷ ls) (suc i) = atL ls i

prodM : List (Mat k) → Word ℕ → Mat k
prodM ms [ i ]ʷ   = atM ms i
prodM ms ε        = idM
prodM ms (a • b)  = mulS (prodM ms a) (prodM ms b)

lenW : List ℕ → Word ℕ → ℕ
lenW ls [ i ]ʷ  = atL ls i
lenW ls ε       = 0
lenW ls (a • b) = lenW ls a +ℕ lenW ls b

------------------------------------------------------------------------
-- The family, decided by one boolean

-- One equation: the two products, each scaled by the other's length,
-- as `Same` compares two words.
OK : List (Mat k) → List ℕ → Word ℕ → Word ℕ → Bool
OK ms ls e f = eqM (scaleM (√2^ lenW ls f) (prodM ms e))
                   (scaleM (√2^ lenW ls e) (prodM ms f))

allOK : List (Mat k) → List ℕ → List (Word ℕ × Word ℕ) → Bool
allOK ms ls []             = true
allOK ms ls ((e , f) ∷ es) = OK ms ls e f ∧ allOK ms ls es

-- The i-th equation (ε = ε past the end).
nth : List (Word ℕ × Word ℕ) → ℕ → Word ℕ × Word ℕ
nth []       _       = ε , ε
nth (p ∷ ps) zero    = p
nth (p ∷ ps) (suc i) = nth ps i

private
  ∧-l : ∀ {x y : Bool} → x ∧ y ≡ true → x ≡ true
  ∧-l {true} _ = Eq.refl

  ∧-r : ∀ {x y : Bool} → x ∧ y ≡ true → y ≡ true
  ∧-r {true}  h = h
  ∧-r {false} ()

  OK-nth : ∀ (ms : List (Mat k)) ls es i → allOK ms ls es ≡ true →
           OK ms ls (proj₁ (nth es i)) (proj₂ (nth es i)) ≡ true
  OK-nth {k} ms ls []         i       h = eqM-refl {k} (scaleM (√2^ 0) idM)
  OK-nth ms ls ((e , f) ∷ es) zero    h = ∧-l h
  OK-nth ms ls ((e , f) ∷ es) (suc i) h = OK-nth ms ls es i (∧-r {OK ms ls e f} h)

  atM-reads : ∀ (ws : List (Circuit k)) i → atM (map ⟦_⟧R ws) i ≡ ⟦ at ws i ⟧M
  atM-reads []       i       = Eq.refl
  atM-reads (w ∷ ws) zero    = ⟦⟧R≡⟦⟧M w
  atM-reads (w ∷ ws) (suc i) = atM-reads ws i

  atL-lens : ∀ (ws : List (Circuit k)) i → atL (map len ws) i ≡ len (at ws i)
  atL-lens []       i       = Eq.refl
  atL-lens (w ∷ ws) zero    = Eq.refl
  atL-lens (w ∷ ws) (suc i) = atL-lens ws i

-- A product of the factors' matrices is the matrix of the word it
-- spells, and likewise the lengths.
prod-reads : ∀ (ws : List (Circuit k)) e → prodM (map ⟦_⟧R ws) e ≡ ⟦ expand ws e ⟧M
prod-reads ws [ i ]ʷ  = atM-reads ws i
prod-reads ws ε       = Eq.refl
prod-reads ws (a • b) =
  Eq.trans (mulS-ok _ _) (Eq.cong₂ mulM (prod-reads ws a) (prod-reads ws b))

lenW-lens : ∀ (ws : List (Circuit k)) e → lenW (map len ws) e ≡ len (expand ws e)
lenW-lens ws [ i ]ʷ  = atL-lens ws i
lenW-lens ws ε       = Eq.refl
lenW-lens ws (a • b) = Eq.cong₂ _+ℕ_ (lenW-lens ws a) (lenW-lens ws b)

-- The i-th equation of a family whose boolean holds.
fam-eval : (ws : List (Circuit k)) (es : List (Word ℕ × Word ℕ)) →
           allOK (map ⟦_⟧R ws) (map len ws) es ≡ true → (i : ℕ) →
           Evaluated (expand ws (proj₁ (nth es i))) (expand ws (proj₂ (nth es i)))
fam-eval ws es h i = evaluated (≡-same (expand ws e) (expand ws f) q)
  where
  e f : Word ℕ
  e = proj₁ (nth es i)
  f = proj₂ (nth es i)

  sc : ℕ → Mat _ → Mat _
  sc n M = scaleM (√2^ n) M

  p : sc (lenW (map len ws) f) (prodM (map ⟦_⟧R ws) e) ≡
      sc (lenW (map len ws) e) (prodM (map ⟦_⟧R ws) f)
  p = eqM-sound _ _ (OK-nth (map ⟦_⟧R ws) (map len ws) es i h)

  q : sc (len (expand ws f)) ⟦ expand ws e ⟧M ≡ sc (len (expand ws e)) ⟦ expand ws f ⟧M
  q = Eq.trans (Eq.sym (Eq.cong₂ sc (lenW-lens ws f) (prod-reads ws e)))
               (Eq.trans p (Eq.cong₂ sc (lenW-lens ws e) (prod-reads ws f)))
