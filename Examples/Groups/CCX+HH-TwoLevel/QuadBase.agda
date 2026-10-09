------------------------------------------------------------------------
-- Presentations of groups
--
-- The setting of the edges at a level with a positive exponent
-- (Lemma A.20, the cases k > 0).
--
-- There the pivot column of s is W / 2ᴷ with K > 0, its first four odd
-- entries are a < b < c < d (Step.Quad), and the normal syllable is
-- N = K_[a,b,c,d] (-1)_[a]^t.  After N the level drops, and words of
-- X's and (-1)'s on indices ≤ p keep a state below the level
-- (States.mono-word-below), so a square whose bottom is such a word
-- closes (square).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth ; ColOrth-actMʷ ; actM ; actMʷ ; actV ; col-actM ; _!_)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadBase {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s)) where

import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Bool.Base using (Bool)
open import Data.Integer.Base using (ℤ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Nullary.Decidable using (recompute)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Minimal)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (distinct₄ ; Distinct₄ ; <⇒≢)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot-just ; pivot-char ; Beyond ; _<ₗ_)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (syl ; step ; top ; Beyond-actM)
open import Examples.Groups.CCX+HH-TwoLevel.Step using (Quad ; quad⟨_,_,_,_⟩)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (Bℓ)
open R {n} using (Path ; Low)
open import Examples.Groups.CCX+HH-TwoLevel.PathTools {n} using (module Below)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (path-normal ; lt-step ; bℓ-below ; MonoWord ; mono-word-below ; ne-𝕀 ; syl-of)
import Examples.Groups.CCX+HH-TwoLevel.PivotColumn as PC

open PB (_===_ {n}) using (_≈_)
open PC s o ps public using (v ; W ; v≡ ; min ; syl≡ ; lvl ; zero> ; norm ; odd≤)

------------------------------------------------------------------------
-- The pivot column and the normal syllable

K′ : ℕ
K′ = suc k′

be : Beyond p s
be = proj₂ (pivot-just s ps)

colK : col s p ≡ scV K′ W
colK = ≡.trans v≡ (≡.cong (λ k → scV k W) ks)

minK : Minimal K′ W
minK = ≡.subst (λ k → Minimal k W) ks min

private
  Q : Quad W
  Q = PC.quad s o ps ks

a b c d : Fin n
a = Quad.a Q
b = Quad.b Q
c = Quad.c Q
d = Quad.d Q

fo : firstOdd W ≡ just a
fo = Quad.fo Q
na : nextOdd a W ≡ just b
na = Quad.na Q
nb : nextOdd b W ≡ just c
nb = Quad.nb Q
nc : nextOdd c W ≡ just d
nc = Quad.nc Q

a<b : a < b
a<b = proj₁ (nextOdd-spec W na)
b<c : b < c
b<c = proj₁ (nextOdd-spec W nb)
c<d : c < d
c<d = proj₁ (nextOdd-spec W nc)

D₄ : Distinct₄ a b c d
D₄ = distinct₄ a<b b<c c<d

d≤p : d ≤ p
d≤p = odd≤ (proj₁ (proj₂ (nextOdd-spec W nc)))

t : Bool
t = σ₄ W a b c d

-- The normal syllable N = K_[a,b,c,d] (-1)_[a]^t.
N≡ : syl s ≡ K a b c d a<b b<c c<d • Mτ a t
N≡ = ≡.trans syl≡ (≡.trans (≡.cong (λ k → sylData p k W) ks) (sylData-quad {p = p} k′ W fo na nb nc a<b b<c c<d))

pN : Path (syl s) s o
pN = path-normal s o ps

------------------------------------------------------------------------
-- Words of X's and (-1)'s after N stay below the level

Ns : Matrix n n D
Ns = actMʷ (syl s) s

lNs : level Ns <ₗ level s
lNs = lt-step s o ps

lB : Bℓ p <ₗ level s
lB = ≡.subst (Bℓ p <ₗ_) (≡.sym lvl) (bℓ-below {p = p} (nodd W) (≡.subst (0 ℕ.<_) (≡.sym ks) (ℕ.s≤s ℕ.z≤n)) ℕP.≤-refl)

low-mono : (V : Word (Gen n)) → MonoWord p V → Low (level s) V Ns
low-mono V mV = mono-word-below V mV Ns lNs lB

open Below {L = level s} ih

-- The square N′ g ≈ V N with V a word of X's and (-1)'s below p, N′ a
-- path out of g·s.
square : (g : Gen n) (N′ V : Word (Gen n)) → Path N′ (actM g s) (ColOrth-actMʷ [ g ]ʷ o) →
         MonoWord p V → V • syl s ≈ N′ • [ g ]ʷ → Path [ g ]ʷ s o
square g N′ V pN′ mV rel = bridge g s o (syl s) N′ V pN pN′ (low-mono V mV) rel

------------------------------------------------------------------------
-- The syllable of g·s, when its pivot column is W′ / 2ᴷ at the same
-- pivot

module _ (g : Gen n) (tg : top g ≤ p) (W′ : Vec ℤ n) (eq : col (actM g s) p ≡ scV K′ W′) (mn : Minimal K′ W′) where

  pivot-g : pivot (actM g s) ≡ just p
  pivot-g = pivot-char (actM g s) (ne-𝕀 (actM g s) p k′ W′ eq mn) (Beyond-actM g {M = s} tg be)

  syl-g : syl (actM g s) ≡ sylData p K′ W′
  syl-g = syl-of (actM g s) pivot-g K′ W′ eq mn

  path-g : Path (sylData p K′ W′) (actM g s) (ColOrth-actMʷ [ g ]ʷ o)
  path-g = ≡.subst (λ w → Path w (actM g s) (ColOrth-actMʷ [ g ]ʷ o)) syl-g
             (path-normal (actM g s) (ColOrth-actMʷ [ g ]ʷ o) pivot-g)

-- With the same parities as W, the syllable is on a, b, c, d.
syl-same-odd : (W′ : Vec ℤ n) → (∀ x → oddℤ (W′ ! x) ≡ oddℤ (W ! x)) →
               sylData p K′ W′ ≡ K a b c d a<b b<c c<d • Mτ a (σ₄ W′ a b c d)
syl-same-odd W′ par = sylData-quad {p = p} k′ W′
  (≡.trans (firstOdd-cong W′ W par) fo) (≡.trans (nextOdd-cong a W′ W par) na)
  (≡.trans (nextOdd-cong b W′ W par) nb) (≡.trans (nextOdd-cong c W′ W par) nc) a<b b<c c<d

-- The column of g·s.
colg : (g : Gen n) → col (actM g s) p ≡ actV g (scV K′ W)
colg g = ≡.trans (col-actM g s p) (≡.cong (actV g) colK)
