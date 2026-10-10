------------------------------------------------------------------------
-- Presentations of groups
--
-- States below the level of s, and the end of the paper's path for the
-- edge X_[d,e] when e is odd (Lemma A.20, Subcase 1.2.2.3).
--
-- A state at the pivot of s whose column is V / 2ᴷ, with fewer odd
-- entries than W (or a smaller exponent), lies below s (level-under).
-- After the signed swap the entries a..h are 2α and 2β with an even
-- number of odd α's and of odd β's; then K_[a,b,c,d] and K_[e,f,g,h]
-- keep them even (XEStep.EvenK), and both states lie below s (tail).
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
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadXETail {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Nullary using (Dec ; yes ; no)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde
  using (scV ; Minimal ; Odd ; Even ; lde-≤ ; lde-char ; all-even? ; halveV ; scV-halve ; ¬Even⇒Odd ; Odd⇒¬Even ; num ; even-2*)
open import Examples.Groups.CCX+HH-TwoLevel.Column using (nodd)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_ ; actV ; col-actM)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (_<ₗ_ ; Beyond ; pivot-just ; level-just ; lvlAt)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (Beyond-actM)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count-lt)
import Examples.Groups.CCX+HH-TwoLevel.XEStep as XS

open import Examples.Groups.CCX+HH-TwoLevel.QuadBase s o ps ks ih public

private
  lvs′ : level s ≡ (suc (toℕ p) , K′ , nodd W)
  lvs′ = ≡.trans lvl (≡.cong (λ k → suc (toℕ p) , k , nodd W) ks)

------------------------------------------------------------------------
-- States below the level of s

-- A state whose pivot column is U′ / 2ᴷ, with fewer odd entries than W.
level-under : (M : Matrix n n D) → Beyond p M → (U′ : Vec ℤ n) → col M p ≡ scV K′ U′ →
              nodd U′ ℕ.< nodd W → level M <ₗ level s
level-under M be U′ eq lt = ≡.subst (level M <ₗ_) (≡.sym lvs′) (go (pivot M) ≡.refl)
  where
  L₀ = (suc (toℕ p) , K′ , nodd W)
  go : (r : Maybe (Fin n)) → pivot M ≡ r → level M <ₗ L₀
  go nothing e = ≡.subst (_<ₗ L₀) (≡.sym (≡.cong (λ x → lvlAt x M) e)) (inj₁ (ℕ.s≤s ℕ.z≤n))
  go (just q) e = by (FinP.<-cmp q p)
    where
    lv : level M ≡ (suc (toℕ q) , lde (col M q) , nodd (num (col M q)))
    lv = level-just M e
    by : Tri (q < p) (q ≡ p) (p < q) → level M <ₗ L₀
    by (tri< q<p _ _) = ≡.subst (_<ₗ L₀) (≡.sym lv) (inj₁ (ℕ.s≤s q<p))
    by (tri> _ _ p<q) = ⊥-elim (proj₁ (pivot-just M e) (be q p<q))
    by (tri≈ _ ≡.refl _) = ≡.subst (_<ₗ L₀) (≡.sym lv) (inj₂ (≡.refl , pair (all-even? U′)))
      where
      pair : Dec (∀ x → Even (U′ ! x)) → (lde (col M q) ℕ.< K′) ⊎ (lde (col M q) ≡ K′ × nodd (num (col M q)) ℕ.< nodd W)
      pair (yes ev) = inj₁ (ℕ.s≤s (lde-≤ k′ (halveV U′ ev) (≡.trans eq (scV-halve k′ U′ ev))))
      pair (no ¬ev) = inj₂ (proj₁ ch , ≡.subst (λ v → nodd v ℕ.< nodd W) (≡.sym (proj₂ ch)) lt)
        where
        mn : Minimal K′ U′
        mn = inj₂ (proj₁ ex , ¬Even⇒Odd {U′ ! proj₁ ex} (proj₂ ex))
          where
          ex = FinP.¬∀⇒∃¬ _ (λ x → Even (U′ ! x)) (λ x → oddℤ (U′ ! x) BoolP.≟ false) ¬ev
        ch = lde-char K′ U′ eq mn

-- Fewer odd entries: those of V are odd in U, and V is even at some odd
-- entry of U.
fewer : (U V : Vec ℤ n) (z : Fin n) → (∀ x → Odd (V ! x) → Odd (U ! x)) → Odd (U ! z) → Even (V ! z) →
        nodd V ℕ.< nodd U
fewer U V z sub oz ez = count-lt (λ x → oddℤ (U ! x)) (λ x → oddℤ (V ! x)) z sub oz ez

-- With fewer odd entries than U, which has as many as W.
under : (U : Vec ℤ n) → nodd U ≡ nodd W → Odd (U ! a) →
        ∀ (M : Matrix n n D) (V : Vec ℤ n) → Beyond p M → col M p ≡ scV K′ V →
        (∀ x → Odd (V ! x) → Odd (U ! x)) → Even (V ! a) → level M <ₗ level s
under U cnt oaU M V be eq sub ea = level-under M be V eq (≡.subst (nodd V ℕ.<_) cnt (fewer U V a sub oaU ea))

------------------------------------------------------------------------
-- Odd entries, after changes at even places

private
  bad : ∀ (V V′ : Vec ℤ n) {x y : Fin n} → Odd (V ! x) → x ≡ y → Even (V ! y) → Odd (V′ ! x)
  bad V V′ {x} ox ≡.refl ey = ⊥-elim (Odd⇒¬Even {V ! x} ox ey)

-- The odd entries of a vector that agrees with V′ off some entries,
-- where it is even, are odd in V′.
sub4 : ∀ (V V′ : Vec ℤ n) {i j k l : Fin n} → (∀ {x} → x ≢ i → x ≢ j → x ≢ k → x ≢ l → V ! x ≡ V′ ! x) →
       Even (V ! i) → Even (V ! j) → Even (V ! k) → Even (V ! l) → ∀ x → Odd (V ! x) → Odd (V′ ! x)
sub4 V V′ {i} {j} {k} {l} off ei ej ek el x ox = by (x FinP.≟ i) (x FinP.≟ j) (x FinP.≟ k) (x FinP.≟ l)
  where
  by : Dec (x ≡ i) → Dec (x ≡ j) → Dec (x ≡ k) → Dec (x ≡ l) → Odd (V′ ! x)
  by (yes e) _ _ _ = bad V V′ ox e ei
  by (no _) (yes e) _ _ = bad V V′ ox e ej
  by (no _) (no _) (yes e) _ = bad V V′ ox e ek
  by (no _) (no _) (no _) (yes e) = bad V V′ ox e el
  by (no xi) (no xj) (no xk) (no xl) = ≡.trans (≡.cong oddℤ (≡.sym (off xi xj xk xl))) ox

sub2 : ∀ (V V′ : Vec ℤ n) {i j : Fin n} → (∀ {x} → x ≢ i → x ≢ j → V ! x ≡ V′ ! x) →
       Even (V ! i) → Even (V ! j) → ∀ x → Odd (V ! x) → Odd (V′ ! x)
sub2 V V′ {i} {j} off ei ej x ox = by (x FinP.≟ i) (x FinP.≟ j)
  where
  by : Dec (x ≡ i) → Dec (x ≡ j) → Odd (V′ ! x)
  by (yes e) _ = bad V V′ ox e ei
  by (no _) (yes e) = bad V V′ ox e ej
  by (no xi) (no xj) = ≡.trans (≡.cong oddℤ (≡.sym (off xi xj))) ox

ev2 : ∀ {v} x → v ≡ + 2 ℤ.* x → Even v
ev2 x eq = ≡.trans (≡.cong oddℤ eq) (even-2* x)

------------------------------------------------------------------------
-- K and K′ on even entries

module _ (U : Vec ℤ n) (cnt : nodd U ≡ nodd W) (oaU : Odd (U ! a))
         {e f g h : Fin n} (d<e : d < e) (e<f : e < f) (f<g : f < g) (g<h : g < h) (h≤p : h ≤ p) where

  private
    ne< : ∀ {u v : Fin n} → u < v → u ≢ v
    ne< lt e = ℕP.<-irrefl (≡.cong toℕ e) lt
    gt : ∀ {u v : Fin n} → u < v → v ≢ u
    gt lt e = ne< lt (≡.sym e)
    _⟨<⟩_ = FinP.<-trans
    infixr 5 _⟨<⟩_
    d≤p′ : d ≤ p
    d≤p′ = ℕP.≤-trans (ℕP.<⇒≤ d<e) (ℕP.≤-trans (ℕP.<⇒≤ e<f) (ℕP.≤-trans (ℕP.<⇒≤ f<g) (ℕP.≤-trans (ℕP.<⇒≤ g<h) h≤p)))
    ae = a<b ⟨<⟩ b<c ⟨<⟩ c<d ⟨<⟩ d<e

    K₁g K₂g : Gen n
    K₁g = K-gen a b c d a<b b<c c<d
    K₂g = K-gen e f g h e<f f<g g<h

    module Tail (M₃ : Matrix n n D) (U₃ : Vec ℤ n) (be₃ : Beyond p M₃) (col₃ : col M₃ p ≡ scV K′ U₃)
                (sub₃ : ∀ x → Odd (U₃ ! x) → Odd (U ! x))
                (α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄ : ℤ)
                (wa : U₃ ! a ≡ + 2 ℤ.* α₁) (wb : U₃ ! b ≡ + 2 ℤ.* α₂) (wc : U₃ ! c ≡ + 2 ℤ.* α₃) (wd : U₃ ! d ≡ + 2 ℤ.* α₄)
                (we : U₃ ! e ≡ + 2 ℤ.* β₁) (wf : U₃ ! f ≡ + 2 ℤ.* β₂) (wg : U₃ ! g ≡ + 2 ℤ.* β₃) (wh : U₃ ! h ≡ + 2 ℤ.* β₄)
                (Σα : ((oddℤ α₁ xor oddℤ α₂) xor oddℤ α₃) xor oddℤ α₄ ≡ false)
                (Σβ : ((oddℤ β₁ xor oddℤ β₂) xor oddℤ β₃) xor oddℤ β₄ ≡ false) where

      ek₁ : XS.EvenKR U₃ a b c d a<b b<c c<d
      ek₁ = XS.evenK U₃ a<b b<c c<d α₁ α₂ α₃ α₄ wa wb wc wd Σα

      module E₁ = XS.EvenKR ek₁

      col₄ : col (actM K₁g M₃) p ≡ scV K′ E₁.Wh
      col₄ = ≡.trans (col-actM K₁g M₃ p) (≡.trans (≡.cong (actV K₁g) col₃) (E₁.col-K K′))

      be₄ : Beyond p (actM K₁g M₃)
      be₄ = Beyond-actM K₁g {M = M₃} d≤p′ be₃

      -- K leaves e, f, g, h.
      hi₄ : ∀ {z} → d < z → E₁.Wh ! z ≡ U₃ ! z
      hi₄ dz = E₁.Wh-≢ (gt (a<b ⟨<⟩ b<c ⟨<⟩ c<d ⟨<⟩ dz)) (gt (b<c ⟨<⟩ c<d ⟨<⟩ dz)) (gt (c<d ⟨<⟩ dz)) (gt dz)

      sub₄ : ∀ x → Odd (E₁.Wh ! x) → Odd (U ! x)
      sub₄ x ox = sub₃ x (sub4 E₁.Wh U₃ E₁.Wh-≢ E₁.ev-i E₁.ev-j E₁.ev-k E₁.ev-l x ox)

      l₄ : level (actM K₁g M₃) <ₗ level s
      l₄ = under U cnt oaU (actM K₁g M₃) E₁.Wh be₄ col₄ sub₄ E₁.ev-i

      ek₂ : XS.EvenKR E₁.Wh e f g h e<f f<g g<h
      ek₂ = XS.evenK E₁.Wh e<f f<g g<h β₁ β₂ β₃ β₄ (≡.trans (hi₄ d<e) we) (≡.trans (hi₄ (d<e ⟨<⟩ e<f)) wf)
                    (≡.trans (hi₄ (d<e ⟨<⟩ e<f ⟨<⟩ f<g)) wg) (≡.trans (hi₄ (d<e ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h)) wh) Σβ

      module E₂ = XS.EvenKR ek₂

      col₅ : col (actM K₂g (actM K₁g M₃)) p ≡ scV K′ E₂.Wh
      col₅ = ≡.trans (col-actM K₂g (actM K₁g M₃) p) (≡.trans (≡.cong (actV K₂g) col₄) (E₂.col-K K′))

      be₅ : Beyond p (actM K₂g (actM K₁g M₃))
      be₅ = Beyond-actM K₂g {M = actM K₁g M₃} h≤p be₄

      sub₅ : ∀ x → Odd (E₂.Wh ! x) → Odd (U ! x)
      sub₅ x ox = sub₄ x (sub4 E₂.Wh E₁.Wh E₂.Wh-≢ E₂.ev-i E₂.ev-j E₂.ev-k E₂.ev-l x ox)

      -- K′ leaves a even.
      ev₅a : Even (E₂.Wh ! a)
      ev₅a = ≡.trans (≡.cong oddℤ (E₂.Wh-≢ (ne< ae) (ne< (ae ⟨<⟩ e<f)) (ne< (ae ⟨<⟩ e<f ⟨<⟩ f<g)) (ne< (ae ⟨<⟩ e<f ⟨<⟩ f<g ⟨<⟩ g<h)))) E₁.ev-i

      l₅ : level (actM K₂g (actM K₁g M₃)) <ₗ level s
      l₅ = under U cnt oaU (actM K₂g (actM K₁g M₃)) E₂.Wh be₅ col₅ sub₅ ev₅a

  tail : (M₃ : Matrix n n D) (U₃ : Vec ℤ n) → Beyond p M₃ → col M₃ p ≡ scV K′ U₃ →
         (∀ x → Odd (U₃ ! x) → Odd (U ! x)) → (α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄ : ℤ) →
         U₃ ! a ≡ + 2 ℤ.* α₁ → U₃ ! b ≡ + 2 ℤ.* α₂ → U₃ ! c ≡ + 2 ℤ.* α₃ → U₃ ! d ≡ + 2 ℤ.* α₄ →
         U₃ ! e ≡ + 2 ℤ.* β₁ → U₃ ! f ≡ + 2 ℤ.* β₂ → U₃ ! g ≡ + 2 ℤ.* β₃ → U₃ ! h ≡ + 2 ℤ.* β₄ →
         ((oddℤ α₁ xor oddℤ α₂) xor oddℤ α₃) xor oddℤ α₄ ≡ false →
         ((oddℤ β₁ xor oddℤ β₂) xor oddℤ β₃) xor oddℤ β₄ ≡ false →
         level (actM (K-gen a b c d a<b b<c c<d) M₃) <ₗ level s ×
         level (actM (K-gen e f g h e<f f<g g<h) (actM (K-gen a b c d a<b b<c c<d) M₃)) <ₗ level s
  tail M₃ U₃ be₃ col₃ sub₃ α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄ wa wb wc wd we wf wg wh Σα Σβ = T.l₄ , T.l₅
    where module T = Tail M₃ U₃ be₃ col₃ sub₃ α₁ α₂ α₃ α₄ β₁ β₂ β₃ β₄ wa wb wc wd we wf wg wh Σα Σβ
