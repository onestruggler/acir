------------------------------------------------------------------------
-- Presentations of groups
--
-- Idle controls are every colouring, and colours are conjugations.
--
-- A circuit under k idle positions is the product, over every
-- colouring of those positions, of the circuit under that colouring
-- (`merge₁`): an idle wire is its two controls (CtrlColour.split-w),
-- and control passes into products.  A circuit under a colouring is the
-- circuit under white controls conjugated by X on the black ones
-- (`colour-conj`, from LambdaLaws.Λ-flip-top and `under`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S

module Examples.Groups.CCX+HH.NaturalP.Merge
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Maybe.Base using (just ; nothing)
open import Data.Nat.Base using (zero ; suc ; _+_)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.PropositionalEquality as Eq using (refl ; sym ; trans ; cong ; cong₂ ; subst₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)
open import Notations using (₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl ; ctrl⁻)
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (Pos ; Λ ; Λw ; whites ; ctrlᵖ ; flip)
open import Examples.Groups.CCX+HH.NaturalP.LambdaLaws complete≤
  using (ctrlᵖ-cong ; ctrlᵖ-• ; ctrlᵖ-ε ; Λ-cong ; Λ-• ; Λ-ε ; under ; Λ-flip-top)
open import Examples.Groups.CCX+HH.NaturalP.CtrlColour complete≤ using (split-w)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; ax ; ⌈_⌉ ; inv ; inv-l ; inv-r)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (_↑ₐ)
open import Examples.Groups.CCX+HH.NaturalP.Transport using (idles ; top ; placed)
open import Examples.Groups.CCX+HH.NaturalP.WinGate complete≤ using (_↑ᵃ_ ; conj-Λw ; inv-↑ᵃ ; inv-inv)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)

private
  variable
    k c m : ℕ

------------------------------------------------------------------------
-- Words of controls

-- Every colouring of k positions.
cols : ∀ k → Word (Vec Bool k)
cols zero    = [ [] ]ʷ
cols (suc k) = wmap (true ∷_) (cols k) • wmap (false ∷_) (cols k)

colour : Vec Bool k → Vec Pos k
colour = map just

private
  ʷ-wmap : ∀ {A B C : Set} (f : B → Word C) (g : A → B) (w : Word A) →
    (f ʷ) (wmap g w) ≡ ((λ a → f (g a)) ʷ) w
  ʷ-wmap f g [ a ]ʷ  = refl
  ʷ-wmap f g ε       = refl
  ʷ-wmap f g (u • v) = cong₂ _•_ (ʷ-wmap f g u) (ʷ-wmap f g v)

-- Control passes into a product.
ctrlᵖ-ʷ : ∀ {A : Set} p (f : A → Circuit (₄₊ m)) (w : Word A) →
  suc (₄₊ m) ⊢ ctrlᵖ p ((f ʷ) w) ≈ ((λ a → ctrlᵖ p (f a)) ʷ) w
ctrlᵖ-ʷ p f [ a ]ʷ  = PB.refl
ctrlᵖ-ʷ p f ε       = ctrlᵖ-ε p
ctrlᵖ-ʷ p f (u • v) = PB.trans (ctrlᵖ-• p ((f ʷ) u) ((f ʷ) v)) (PB.cong (ctrlᵖ-ʷ p f u) (ctrlᵖ-ʷ p f v))

Λ-ʷ : ∀ {A : Set} (s : Vec Pos k) (f : A → Circuit (₄₊ c)) (w : Word A) →
  (₄₊ (k + c)) ⊢ Λ s ((f ʷ) w) ≈ ((λ a → Λ s (f a)) ʷ) w
Λ-ʷ s f [ a ]ʷ  = PB.refl
Λ-ʷ s f ε       = Λ-ε s
Λ-ʷ s f (u • v) = PB.trans (Λ-• s ((f ʷ) u) ((f ʷ) v)) (PB.cong (Λ-ʷ s f u) (Λ-ʷ s f v))

------------------------------------------------------------------------
-- Idle positions are every colouring

merge₁ : ∀ k (w : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ Λ (idles k) w ≈ ((λ s → Λ (colour s) w) ʷ) (cols k)
merge₁ zero    w = PB.refl
merge₁ {c = c} (suc k) w =
  PB.trans (split-w (Λ (idles k) w))
  (PB.trans (PB.cong (ctrlᵖ-cong (just true) (merge₁ k w)) (ctrlᵖ-cong (just false) (merge₁ k w)))
  (PB.trans (PB.cong (ctrlᵖ-ʷ (just true) f (cols k)) (ctrlᵖ-ʷ (just false) f (cols k)))
    (Eq.subst (λ z → (₄₊ (suc k + c)) ⊢ ((λ s → ctrlᵖ (just true) (f s)) ʷ) (cols k) • ((λ s → ctrlᵖ (just false) (f s)) ʷ) (cols k) ≈ z) (sym (cong₂ _•_ (ʷ-wmap g (true ∷_) (cols k)) (ʷ-wmap g (false ∷_) (cols k))))
      PB.refl)))
  where
  f = λ s → Λ (colour s) w
  g = λ s → Λ (colour s) w

------------------------------------------------------------------------
-- Colours are conjugations by X

-- X on the black positions of a colouring.
trC : Vec Bool k → Word (AGen (₄₊ (k + c)))
trC []          = ε
trC (true ∷ s)  = [ ax ]ʷ • (trC s ↑ₐ)
trC (false ∷ s) = trC s ↑ₐ

private
  inv-↑ : (w : Word (AGen m)) → inv (w ↑ₐ) ≡ inv w ↑ₐ
  inv-↑ [ g ]ʷ  = refl
  inv-↑ ε       = refl
  inv-↑ (u • v) = cong₂ _•_ (inv-↑ v) (inv-↑ u)

  ⌈⌉-↑ : (w : Word (AGen m)) → ⌈ w ↑ₐ ⌉ ≡ ⌈ w ⌉ ↑
  ⌈⌉-↑ [ g ]ʷ  = refl
  ⌈⌉-↑ ε       = refl
  ⌈⌉-↑ (u • v) = cong₂ _•_ (⌈⌉-↑ u) (⌈⌉-↑ v)

  ⌈inv-↑⌉ : (w : Word (AGen m)) → ⌈ inv (w ↑ₐ) ⌉ ≡ ⌈ inv w ⌉ ↑
  ⌈inv-↑⌉ w = trans (cong ⌈_⌉ (inv-↑ w)) (⌈⌉-↑ (inv w))

  -- A conjugation passes under a control.
  conj↑ : ∀ p (T : Word (AGen (₄₊ m))) (Z : Circuit (₄₊ m)) →
    suc (₄₊ m) ⊢ ctrlᵖ p (⌈ inv T ⌉ • (Z • ⌈ T ⌉)) ≈ ⌈ inv (T ↑ₐ) ⌉ • (ctrlᵖ p Z • ⌈ T ↑ₐ ⌉)
  conj↑ p T Z =
    subst₂ (λ L R → _ ⊢ ctrlᵖ p (⌈ inv T ⌉ • (Z • ⌈ T ⌉)) ≈ L • (ctrlᵖ p Z • R))
      (sym (⌈inv-↑⌉ T)) (sym (⌈⌉-↑ T))
      (PB.sym (under p {x = ⌈ inv T ⌉} {x⁻ = ⌈ T ⌉} (inv-l T) PB.refl))

colour-conj : ∀ k (s : Vec Bool k) (Y : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ Λ (colour s) Y ≈ ⌈ inv (trC s) ⌉ • (Λw k Y • ⌈ trC s ⌉)
colour-conj zero    []          Y = PB.sym (PB.trans PB.left-unit PB.right-unit)
colour-conj (suc k) (false ∷ s) Y =
  PB.trans (ctrlᵖ-cong (just false) (colour-conj k s Y)) (conj↑ (just false) (trC s) (Λw k Y))
colour-conj (suc k) (true ∷ s)  Y =
  PB.trans (ctrlᵖ-cong (just true) (colour-conj k s Y))
  (PB.trans (conj↑ (just true) (trC s) (Λw k Y))
  (PB.trans (PB.cong PB.refl (PB.cong (PB.sym (Λ-flip-top (just false) (Λw k Y))) PB.refl))
  (PB.trans (PB.cong PB.refl PB.assoc)
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.assoc))
    (PB.sym PB.assoc)))))

------------------------------------------------------------------------
-- Window gates

-- A circuit on four wires in the window, moved back by an affine word.
gate′ : ∀ k c → Word (AGen (₄₊ (k + (c + 0)))) → Circuit 4 → Circuit (₄₊ (k + (c + 0)))
gate′ k c A Y = ⌈ inv A ⌉ • (Λw k (Λw c Y) • ⌈ A ⌉)

private
  ʷ-cong : ∀ {A : Set} {f g : A → Circuit m} → (∀ a → m ⊢ f a ≈ g a) → (w : Word A) →
    m ⊢ (f ʷ) w ≈ (g ʷ) w
  ʷ-cong e [ a ]ʷ  = e a
  ʷ-cong e ε       = PB.refl
  ʷ-cong e (u • v) = PB.cong (ʷ-cong e u) (ʷ-cong e v)

  reassoc : ∀ {a b L b′ a′ : Circuit m} → m ⊢ a • ((b • (L • b′)) • a′) ≈ (a • b) • (L • (b′ • a′))
  reassoc = PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.sym PB.assoc) (PB.cong PB.refl PB.assoc))

-- The colouring of both levels of the window, as X.
trW : ∀ k c → Vec Bool k → Vec Bool c → Word (AGen (₄₊ (k + (c + 0))))
trW k c s₁ s₂ = (trC {c = 0} s₂ ↑ᵃ k) • trC s₁

nested : ∀ k c (s₁ : Vec Bool k) (s₂ : Vec Bool c) (Y : Circuit 4) →
  (₄₊ (k + (c + 0))) ⊢ Λ (colour s₁) (Λ (colour s₂) Y) ≈ gate′ k c (trW k c s₁ s₂) Y
nested k c s₁ s₂ Y =
  PB.trans (colour-conj k s₁ (Λ (colour s₂) Y))
  (PB.trans (PB.cong PB.refl (PB.cong (Λ-cong (whites k) (colour-conj c s₂ Y)) PB.refl))
  (PB.trans (PB.cong PB.refl (PB.cong (PB.sym inner) PB.refl))
    reassoc))
  where
  T₂ = trC {c = 0} s₂
  inner : (₄₊ (k + (c + 0))) ⊢ ⌈ inv (T₂ ↑ᵃ k) ⌉ • (Λw k (Λw c Y) • ⌈ T₂ ↑ᵃ k ⌉) ≈
    Λw k (⌈ inv T₂ ⌉ • (Λw c Y • ⌈ T₂ ⌉))
  inner = subst₂ (λ L R → _ ⊢ ⌈ L ⌉ • (Λw k (Λw c Y) • ⌈ R ⌉) ≈ Λw k (⌈ inv T₂ ⌉ • (Λw c Y • ⌈ T₂ ⌉)))
    (sym (inv-↑ᵃ k T₂))
    (trans (inv-↑ᵃ k (inv T₂)) (cong (_↑ᵃ k) (inv-inv T₂)))
    (Eq.subst (λ R → _ ⊢ ⌈ inv T₂ ↑ᵃ k ⌉ • (Λw k (Λw c Y) • ⌈ inv (inv T₂ ↑ᵃ k) ⌉) ≈
                       Λw k (⌈ inv T₂ ⌉ • (Λw c Y • ⌈ R ⌉)))
      (inv-inv T₂) (conj-Λw k (inv T₂) (Λw c Y)))

-- Every colouring of the window's controls, outer then inner.
pairs : ∀ k c → Word (Vec Bool k × Vec Bool c)
pairs k c = ((λ s₂ → wmap (λ s₁ → s₁ , s₂) (cols k)) ʷ) (cols c)

-- A circuit on the top four wires is the product of its window gates.
top-gates : ∀ k c (Y : Circuit 4) →
  (₄₊ (k + (c + 0))) ⊢ top k c Y ≈ ((λ p → gate′ k c (trW k c (proj₁ p) (proj₂ p)) Y) ʷ) (pairs k c)
top-gates k c Y =
  PB.trans (Λ-cong (idles k) (merge₁ c Y))
  (PB.trans (Λ-ʷ (idles k) (λ s₂ → Λ (colour s₂) Y) (cols c))
  (PB.trans (ʷ-cong (λ s₂ → merge₁ k (Λ (colour s₂) Y)) (cols c))
  (PB.trans (ʷ-cong (λ s₂ → ʷ-cong (λ s₁ → nested k c s₁ s₂ Y) (cols k)) (cols c))
    (Eq.subst (λ z → (₄₊ (k + (c + 0))) ⊢ ((λ s₂ → ((λ s₁ → g (s₁ , s₂)) ʷ) (cols k)) ʷ) (cols c) ≈ z)
      (sym (flat (cols c))) PB.refl))))
  where
  g : Vec Bool k × Vec Bool c → Circuit _
  g p = gate′ k c (trW k c (proj₁ p) (proj₂ p)) Y
  h : Vec Bool c → Word (Vec Bool k × Vec Bool c)
  h s₂ = wmap (λ s₁ → s₁ , s₂) (cols k)
  flat : ∀ w → (g ʷ) ((h ʷ) w) ≡ ((λ s₂ → ((λ s₁ → g (s₁ , s₂)) ʷ) (cols k)) ʷ) w
  flat [ s₂ ]ʷ = ʷ-wmap g (λ s₁ → s₁ , s₂) (cols k)
  flat ε       = refl
  flat (u • v) = cong₂ _•_ (flat u) (flat v)

-- Conjugation by an affine word distributes over a product of gates.
conj-ʷ : ∀ {A : Set} (N : Word (AGen m)) (f : A → Circuit m) (w : Word A) →
  m ⊢ ⌈ inv N ⌉ • ((f ʷ) w • ⌈ N ⌉) ≈ ((λ a → ⌈ inv N ⌉ • (f a • ⌈ N ⌉)) ʷ) w
conj-ʷ N f [ a ]ʷ  = PB.refl
conj-ʷ N f ε       = PB.trans (PB.cong PB.refl PB.left-unit) (inv-l N)
conj-ʷ N f (u • v) =
  PB.trans (PB.cong PB.refl (PB.trans PB.assoc
             (PB.cong PB.refl (PB.trans (PB.sym PB.left-unit)
               (PB.cong (PB.sym (inv-r N)) PB.refl)))))
  (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.assoc))
  (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
  (PB.trans (PB.sym PB.assoc)
    (PB.cong (conj-ʷ N f u) (conj-ʷ N f v)))))

-- Every gate is a product of window gates, one for each colouring of
-- the controls, all moved back by the same swaps N.
recover-win : ∀ k c (x : Gen (₄₊ (k + (c + 0)))) →
  Σ (Word (AGen (₄₊ (k + (c + 0))))) λ N → Σ (Circuit 4) λ x₄ →
    (₄₊ (k + (c + 0))) ⊢ [ x ]ʷ ≈
      ((λ p → gate′ k c (trW k c (proj₁ p) (proj₂ p) • N) x₄) ʷ) (pairs k c)
recover-win k c x = N , x₄ ,
  PB.trans e
  (PB.trans (PB.cong PB.refl (PB.cong (top-gates k c x₄) PB.refl))
  (PB.trans (conj-ʷ N (λ p → gate′ k c (trW k c (proj₁ p) (proj₂ p)) x₄) (pairs k c))
    (ʷ-cong (λ p → reassoc) (pairs k c))))
  where
  pl = placed k c x
  N = proj₁ pl
  x₄ = proj₁ (proj₂ pl)
  e = proj₂ (proj₂ pl)
