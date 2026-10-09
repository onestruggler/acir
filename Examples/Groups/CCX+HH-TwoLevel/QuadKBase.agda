------------------------------------------------------------------------
-- Presentations of groups
--
-- The setting of the edge K_[0,1,2,3] at a level with a positive
-- exponent (Lemma A.20, Subcase 3.2).
--
-- K = K_[0,1,2,3] acts on the entries 0..3 of the pivot column W / 2ᴷ;
-- 2K·W is KW at exponent K + 1.  If an entry of KW is odd the exponent
-- rises and the edge goes up, against the hypothesis (up-odd).  If the
-- column after K is W′ / 2ᴷ, its normal syllable N′ is a path out of
-- K·s that drops below the level of s (After).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth ; actM)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadKBase {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s))
  {P0 P1 P2 P3 : Fin n} .(p01 : P0 < P1) .(p12 : P1 < P2) .(p23 : P2 < P3)
  (z0 : toℕ P0 ≡ 0) (z1 : toℕ P1 ≡ 1) (z2 : toℕ P2 ≡ 2) (z3 : toℕ P3 ≡ 3)
  (le : R._≤ₗ_ {n} (level (actM (K-gen P0 P1 P2 P3 p01 p12 p23) s)) (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂ ; [_,_]′)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)

open import Word.Base
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Minimal ; Odd ; Even)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction using (Kᶻ ; actV-K ; rowAᶻ ; rowBᶻ ; rowCᶻ ; rowDᶻ ; odd-rowA)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
  using (ColOrth-actMʷ ; actMʷ ; _!_ ; distinct₄ ; Distinct₄ ; set₄-a)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot-char ; _<ₗ_ ; <ₗ-irrefl)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (syl ; step ; Beyond-actM)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (<ₗ-trans)
open R {n} using (Path)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (lt-step ; level-of ; ne-𝕀)

open import Examples.Groups.CCX+HH-TwoLevel.QuadBase s o ps ks ih public

------------------------------------------------------------------------
-- K and its column

gK : Gen n
gK = K-gen P0 P1 P2 P3 p01 p12 p23

gs : Matrix n n D
gs = actM gK s

KW : Vec ℤ n
KW = Kᶻ P0 P1 P2 P3 W

colKP : col gs p ≡ scV (suc K′) KW
colKP = ≡.trans (colg gK) (actV-K P0 P1 P2 P3 p01 p12 p23 K′ W)

-- 3 ≤ d ≤ p.
P3≤p : P3 ≤ p
P3≤p = ≡.subst (ℕ._≤ toℕ p) (≡.sym z3) (ℕP.≤-trans three≤d d≤p)
  where
  three≤d : 3 ℕ.≤ toℕ d
  three≤d = ℕP.≤-trans (ℕ.s≤s (ℕP.≤-trans (ℕ.s≤s (ℕP.≤-trans (ℕ.s≤s ℕ.z≤n) a<b)) b<c)) c<d

------------------------------------------------------------------------
-- Going up is excluded

not-up : level s <ₗ level gs → ⊥
not-up lt = [ (λ x → <ₗ-irrefl (<ₗ-trans lt x)) , (λ e → <ₗ-irrefl (≡.subst (level s <ₗ_) e lt)) ]′ le

lvs : level s ≡ (suc (toℕ p) , K′ , nodd W)
lvs = ≡.trans lvl (≡.cong (λ k → suc (toℕ p) , k , nodd W) ks)

-- An odd entry of KW raises the exponent.
up-odd : ∀ x → Odd (KW ! x) → ⊥
up-odd x ox = not-up (≡.subst₂ _<ₗ_ (≡.sym lvs) (≡.sym lv′) (inj₂ (≡.refl , inj₁ (ℕP.n<1+n K′))))
  where
  mn : Minimal (suc K′) KW
  mn = inj₂ (x , ox)
  pv′ : pivot gs ≡ just p
  pv′ = pivot-char gs (ne-𝕀 gs p K′ KW colKP mn) (Beyond-actM gK {M = s} P3≤p be)
  lv′ : level gs ≡ (suc (toℕ p) , suc K′ , nodd KW)
  lv′ = level-of gs pv′ (suc K′) KW colKP mn

-- The first entry of KW is the sum of the four.
KW-P0 : oddℤ (KW ! P0) ≡ ((oddℤ (W ! P0) xor oddℤ (W ! P1)) xor oddℤ (W ! P2)) xor oddℤ (W ! P3)
KW-P0 = ≡.trans (≡.cong oddℤ (set₄-a (distinct₄ p01 p12 p23) (rowAᶻ w₀ w₁ w₂ w₃) (rowBᶻ w₀ w₁ w₂ w₃)
                   (rowCᶻ w₀ w₁ w₂ w₃) (rowDᶻ w₀ w₁ w₂ w₃) (Vec.map (+ 2 ℤ.*_) W)))
          (odd-rowA w₀ w₁ w₂ w₃)
  where
  w₀ = W ! P0
  w₁ = W ! P1
  w₂ = W ! P2
  w₃ = W ! P3

-- Four parities of W with an odd sum send the edge up.
up-par : ∀ {e₀ e₁ e₂ e₃ : Bool} → oddℤ (W ! P0) ≡ e₀ → oddℤ (W ! P1) ≡ e₁ → oddℤ (W ! P2) ≡ e₂ →
         oddℤ (W ! P3) ≡ e₃ → ((e₀ xor e₁) xor e₂) xor e₃ ≡ true → ⊥
up-par {e₀} {e₁} h₀ h₁ h₂ h₃ odd = up-odd P0 (≡.trans KW-P0
  (≡.trans (≡.cong₂ (λ u v → ((u xor v) xor oddℤ (W ! P2)) xor oddℤ (W ! P3)) h₀ h₁)
    (≡.trans (≡.cong₂ (λ u v → ((e₀ xor e₁) xor u) xor v) h₂ h₃) odd)))

------------------------------------------------------------------------
-- After K, at the same exponent

module After (W′ : Vec ℤ n) (eq : col gs p ≡ scV K′ W′) (mn : Minimal K′ W′) where

  pN′ : Path (sylData p K′ W′) gs (ColOrth-actMʷ [ gK ]ʷ o)
  pN′ = path-g gK P3≤p W′ eq mn

  -- N′ drops below the level of K·s, which is at most that of s.
  lN′ : level (actMʷ (sylData p K′ W′) gs) <ₗ level s
  lN′ = [ (λ x → <ₗ-trans lt x) , (λ e → ≡.subst (level (actMʷ (sylData p K′ W′) gs) <ₗ_) e lt) ]′ le
    where
    lt : level (actMʷ (sylData p K′ W′) gs) <ₗ level gs
    lt = ≡.subst (λ w → level (actMʷ w gs) <ₗ level gs) (syl-g gK P3≤p W′ eq mn)
           (lt-step gs (ColOrth-actMʷ [ gK ]ʷ o) (pivot-g gK P3≤p W′ eq mn))
