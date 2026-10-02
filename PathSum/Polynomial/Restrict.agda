------------------------------------------------------------------------
-- Presentations of groups
--
-- Restricting a polynomial to some of its input variables
--
-- A polynomial P in N input variables, restricted along an injection
-- ι : Fin K → Fin N, is the polynomial in K variables whose coefficient
-- on a monomial α is P's coefficient on its image img ι α (restrict).
-- Its value at an assignment v of the K variables is the value of P at
-- the assignment ext ι v that reads v through ι and sets every other
-- variable to 0 (eval-restrict): every monomial of P containing a
-- variable outside the image of ι vanishes there, and the others are
-- the images of the monomials in K variables.  The proof inducts on K,
-- splitting the restriction at its head variable and P at the image of
-- that variable (PathSum.Polynomial.Properties.eval-split), wherever
-- in P it lies.
--
-- This is how a statement about the coefficients of a polynomial in a
-- few of a path-sum's wires -- the input registers of an adder, say --
-- is read off a polynomial in all of them: Möbius inversion applies to
-- the restriction, whose values are those of P on the inputs that are
-- 0 off the registers.  img ι is injective with ι (img-injective), so
-- distinct monomials of the restriction are distinct monomials of P.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Restrict where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using
  (Subset; inside; outside; ⊥; ⁅_⁆; _∪_; _∈_; _⊆_)
open import Data.Fin.Subset.Properties using
  (_∈?_; ∉⊥; x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x∈p∪q⁻; x∈p∪q⁺; ∪-comm; ∪-identityʳ;
   ⊆-antisym)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-comm; *-identityˡ; *-zeroˡ)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using ([]; _∷_; here; there)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Fin.Properties as Fin

open import PathSum.Polynomial using
  (Poly; Mon; x[_]; _∈ᵐ?_; ⟪_⟫; _∪ᵐ_; Σsub; sat; satᵐ; eval)
open import PathSum.Polynomial.Properties using
  (_∖ᵛ_; _/ᵛ_; eval-split; eval-ext; Σsub-0; Σsub-cong; Σmon-cong;
   sat-cong-⊆)

private
  variable
    K N m : ℕ


------------------------------------------------------------------------
-- Images and extensions along a map of variables

Injective′ : (Fin K → Fin N) → Set
Injective′ ι = ∀ i j → ι i ≡ ι j → i ≡ j

-- The image of a monomial: the variables ι i, for i in it.

img : (Fin K → Fin N) → Subset K → Subset N
img {K = zero}  ι []            = ⊥
img {K = suc K} ι (inside  ∷ α) = ⁅ ι zero ⁆ ∪ img (λ j → ι (suc j)) α
img {K = suc K} ι (outside ∷ α) = img (λ j → ι (suc j)) α

-- An assignment read through ι, and 0 off its image.

ext : (Fin K → Fin N) → (Fin K → Bool) → Fin N → Bool
ext {K = zero}  ι v w = false
ext {K = suc K} ι v w = if ⌊ ι zero Fin.≟ w ⌋ then v zero
                    else ext (λ j → ι (suc j)) (λ j → v (suc j)) w

-- The restriction of P: its coefficients on the images.

restrict : (Fin K → Fin N) → Poly N m → Poly K m
restrict ι P γ = P (img ι (proj₁ γ) , proj₂ γ)


------------------------------------------------------------------------
-- Membership in an image

img-∈⁺ : (ι : Fin K → Fin N) (α : Subset K) (j : Fin K) → j ∈ α →
         ι j ∈ img ι α
img-∈⁺ ι (inside  ∷ α) zero    here      = x∈p∪q⁺ (inj₁ (x∈⁅x⁆ (ι zero)))
img-∈⁺ ι (inside  ∷ α) (suc j) (there p) =
  x∈p∪q⁺ (inj₂ (img-∈⁺ (λ i → ι (suc i)) α j p))
img-∈⁺ ι (outside ∷ α) (suc j) (there p) = img-∈⁺ (λ i → ι (suc i)) α j p
img-∈⁺ ι (outside ∷ α) zero    ()
img-∈⁺ ι []            ()      _

img-∈⁻ : (ι : Fin K → Fin N) (α : Subset K) {u : Fin N} → u ∈ img ι α →
         ∃ λ j → (j ∈ α) × (ι j ≡ u)
img-∈⁻ {K = zero}  ι []            p = contradiction p ∉⊥
img-∈⁻ {K = suc K} ι (inside  ∷ α) p
  with x∈p∪q⁻ ⁅ ι zero ⁆ (img (λ j → ι (suc j)) α) p
... | inj₁ q = zero , here , sym (x∈⁅y⁆⇒x≡y (ι zero) q)
... | inj₂ q with img-∈⁻ (λ j → ι (suc j)) α q
...   | j , j∈ , e = suc j , there j∈ , e
img-∈⁻ {K = suc K} ι (outside ∷ α) p with img-∈⁻ (λ j → ι (suc j)) α p
... | j , j∈ , e = suc j , there j∈ , e

-- ι zero is not in the image of the rest, ι being injective.

private
  head∉ : (ι : Fin (suc K) → Fin N) → Injective′ ι → (α : Subset K) →
          ¬ (ι zero ∈ img (λ j → ι (suc j)) α)
  head∉ ι inj α p with img-∈⁻ (λ j → ι (suc j)) α p
  ... | j , _ , e with inj (suc j) zero e
  ...   | ()

-- img ι is injective.

img-injective : (ι : Fin K → Fin N) → Injective′ ι →
                (α α′ : Subset K) → img ι α ≡ img ι α′ → α ≡ α′
img-injective ι inj α α′ e = ⊆-antisym (sub α α′ e) (sub α′ α (sym e))
  where
  sub : ∀ a b → img ι a ≡ img ι b → a ⊆ b
  sub a b e {j} j∈a with img-∈⁻ ι b (subst (ι j ∈_) e (img-∈⁺ ι a j j∈a))
  ... | j′ , j′∈b , e′ = subst (_∈ b) (inj j′ j e′) j′∈b


------------------------------------------------------------------------
-- The extended assignment

ext-at : (ι : Fin (suc K) → Fin N) (v : Fin (suc K) → Bool) (w : Fin N) →
         ι zero ≡ w → ext ι v w ≡ v zero
ext-at ι v w e with ι zero Fin.≟ w
... | yes _  = refl
... | no  ¬e = contradiction e ¬e

ext-there : (ι : Fin (suc K) → Fin N) (v : Fin (suc K) → Bool) (w : Fin N) →
            ¬ (ι zero ≡ w) →
            ext ι v w ≡ ext (λ j → ι (suc j)) (λ j → v (suc j)) w
ext-there ι v w ¬e with ι zero Fin.≟ w
... | yes e = contradiction e ¬e
... | no  _ = refl

ext-off : (ι : Fin K → Fin N) (v : Fin K → Bool) (w : Fin N) →
          (∀ j → ¬ (ι j ≡ w)) → ext ι v w ≡ false
ext-off {K = zero}  ι v w h = refl
ext-off {K = suc K} ι v w h =
  trans (ext-there ι v w (h zero))
        (ext-off (λ j → ι (suc j)) (λ j → v (suc j)) w (λ j → h (suc j)))

-- On the image of ι it reads v.

ext-ι : (ι : Fin K → Fin N) → Injective′ ι → (v : Fin K → Bool) →
        ∀ j → ext ι v (ι j) ≡ v j
ext-ι ι inj v zero    = ext-at ι v (ι zero) refl
ext-ι ι inj v (suc j) =
  trans (ext-there ι v (ι (suc j)) (λ e → contra (inj zero (suc j) e)))
        (ext-ι (λ i → ι (suc i))
               (λ a b e → Fin.suc-injective (inj (suc a) (suc b) e))
               (λ i → v (suc i)) j)
  where
  contra : ¬ (zero ≡ suc j)
  contra ()


------------------------------------------------------------------------
-- Evaluation

private
  -- An assignment to no variables satisfies only the empty monomial.

  eval-zeros : (P : Poly N m) (y : Fin m → Bool) →
               eval P (λ _ → false) y ≡
               Σsub (λ β → if sat β y then P (⊥ , β) else 0ℤ)
  eval-zeros {N = zero}  P y = refl
  eval-zeros {N = suc N} {m = m} P y = trans
    (cong (_+ℤ eval (λ γ → P (outside ∷ proj₁ γ , proj₂ γ))
                    (λ _ → false) y)
          (trans (Σsub-cong {k = N} (λ α → Σsub-0 {m})) (Σsub-0 {N})))
    (trans (+-identityˡ _)
           (eval-zeros (λ γ → P (outside ∷ proj₁ γ , proj₂ γ)) y))

  -- The head variable of the restriction, split off.

  head-part : (Q : Poly (suc K) m) (w : Fin K → Bool) (y : Fin m → Bool) →
              ∀ b →
              Σsub (λ α → Σsub (λ β →
                if (b ∧ sat α w) ∧ sat β y then Q (inside ∷ α , β) else 0ℤ))
              ≡ (if b then eval (λ γ → Q (inside ∷ proj₁ γ , proj₂ γ)) w y
                 else 0ℤ)
  head-part Q w y true  = refl
  head-part {K = K} {m = m} Q w y false =
    trans (Σsub-cong {k = K} (λ α → Σsub-0 {m})) (Σsub-0 {K})

  eval-head : (Q : Poly (suc K) m) (v : Fin (suc K) → Bool)
              (y : Fin m → Bool) →
              eval Q v y ≡
              (if v zero
               then eval (λ γ → Q (inside ∷ proj₁ γ , proj₂ γ))
                         (λ j → v (suc j)) y
               else 0ℤ) +ℤ
              eval (λ γ → Q (outside ∷ proj₁ γ , proj₂ γ)) (λ j → v (suc j)) y
  eval-head Q v y =
    cong (_+ℤ eval (λ γ → Q (outside ∷ proj₁ γ , proj₂ γ))
                   (λ j → v (suc j)) y)
         (head-part Q (λ j → v (suc j)) y (v zero))

  -- A polynomial with no monomial containing x_w does not read the
  -- assignment at w.

  if-zero : ∀ (b b′ : Bool) {q : ℤ} → q ≡ 0ℤ →
            (if b then q else 0ℤ) ≡ (if b′ then q else 0ℤ)
  if-zero true  true  e = refl
  if-zero true  false e = e
  if-zero false true  e = sym e
  if-zero false false e = refl

  eval-off : (Q : Poly N m) (w : Fin N) →
             (∀ γ → w ∈ proj₁ γ → Q γ ≡ 0ℤ) →
             (x x′ : Fin N → Bool) (y : Fin m → Bool) →
             (∀ u → ¬ (u ≡ w) → x u ≡ x′ u) →
             eval Q x y ≡ eval Q x′ y
  eval-off Q w hQ x x′ y agree = Σmon-cong term
    where
    term : ∀ γ → (if satᵐ γ x y then Q γ else 0ℤ) ≡
                 (if satᵐ γ x′ y then Q γ else 0ℤ)
    term (α , β) with w ∈? α
    ... | yes w∈ = if-zero (satᵐ (α , β) x y) (satᵐ (α , β) x′ y)
                           (hQ (α , β) w∈)
    ... | no  w∉ = cong (λ b → if b ∧ sat β y then Q (α , β) else 0ℤ)
      (sat-cong-⊆ α (λ j j∈ → agree j (λ j≡w → w∉ (subst (_∈ α) j≡w j∈))))

  -- The two parts of P at x_w do not contain x_w.

  if-∈ : ∀ {w : Fin N} (α : Subset N) {z : ℤ} → w ∈ α →
         (if ⌊ w ∈? α ⌋ then 0ℤ else z) ≡ 0ℤ
  if-∈ {w = w} α w∈ with w ∈? α
  ... | yes _  = refl
  ... | no  w∉ = contradiction w∈ w∉

  if-∉ : ∀ {w : Fin N} (α : Subset N) {z : ℤ} → ¬ (w ∈ α) →
         (if ⌊ w ∈? α ⌋ then 0ℤ else z) ≡ z
  if-∉ {w = w} α w∉ with w ∈? α
  ... | yes w∈ = contradiction w∈ w∉
  ... | no  _  = refl

  -- if b then a else 0 is the bit b times a.

  if-bit : ∀ b a → (if b then a else 0ℤ) ≡ (if b then 1ℤ else 0ℤ) *ℤ a
  if-bit true  a = sym (*-identityˡ a)
  if-bit false a = sym (*-zeroˡ a)

-- The value of the restriction is the value of P at the extended
-- assignment.

eval-restrict : (ι : Fin K → Fin N) → Injective′ ι → (P : Poly N m)
                (v : Fin K → Bool) (y : Fin m → Bool) →
                eval (restrict ι P) v y ≡ eval P (ext ι v) y
eval-restrict {K = zero}  ι inj P v y = sym (eval-zeros P y)
eval-restrict {K = suc K} {N = N} {m = m} ι inj P v y = begin
  eval (restrict ι P) v y
    ≡⟨ eval-head (restrict ι P) v y ⟩
  (if v zero then eval Q₁ v′ y else 0ℤ) +ℤ eval (restrict ι′ P) v′ y
    ≡⟨ cong₂ _+ℤ_ (cong (λ z → if v zero then z else 0ℤ) part₁) part₀ ⟩
  (if v zero then eval (P /ᵛ x[ w ]) x y else 0ℤ) +ℤ
  eval (P ∖ᵛ x[ w ]) x y
    ≡⟨ +-comm _ (eval (P ∖ᵛ x[ w ]) x y) ⟩
  eval (P ∖ᵛ x[ w ]) x y +ℤ (if v zero then eval (P /ᵛ x[ w ]) x y else 0ℤ)
    ≡⟨ cong (eval (P ∖ᵛ x[ w ]) x y +ℤ_)
            (trans (if-bit (v zero) (eval (P /ᵛ x[ w ]) x y))
                   (cong (λ b → (if b then 1ℤ else 0ℤ) *ℤ
                                eval (P /ᵛ x[ w ]) x y)
                         (sym (ext-at ι v w refl)))) ⟩
  eval (P ∖ᵛ x[ w ]) x y +ℤ
  ((if x w then 1ℤ else 0ℤ) *ℤ eval (P /ᵛ x[ w ]) x y)
    ≡⟨ sym (eval-split P x[ w ] x y) ⟩
  eval P x y
    ∎
  where
  open ≡-Reasoning

  w : Fin N
  w = ι zero

  ι′ : Fin K → Fin N
  ι′ j = ι (suc j)

  inj′ : Injective′ ι′
  inj′ a b e = Fin.suc-injective (inj (suc a) (suc b) e)

  v′ : Fin K → Bool
  v′ j = v (suc j)

  x x′ : Fin N → Bool
  x  = ext ι v
  x′ = ext ι′ v′

  Q₁ : Poly K m
  Q₁ γ = restrict ι P (inside ∷ proj₁ γ , proj₂ γ)

  -- x and x′ differ at most at w, where x′ is 0.

  agree : ∀ u → ¬ (u ≡ w) → x u ≡ x′ u
  agree u u≢w = ext-there ι v u (λ e → u≢w (sym e))

  x′w : x′ w ≡ false
  x′w = ext-off ι′ v′ w (λ j e → contradiction (inj (suc j) zero e) λ ())

  off∖ : ∀ γ → w ∈ proj₁ γ → (P ∖ᵛ x[ w ]) γ ≡ 0ℤ
  off∖ (α , β) w∈ = if-∈ α w∈

  off/ : ∀ γ → w ∈ proj₁ γ → (P /ᵛ x[ w ]) γ ≡ 0ℤ
  off/ (α , β) w∈ = if-∈ α w∈

  -- The monomials without the head variable: P less its x_w part.

  part₀ : eval (restrict ι′ P) v′ y ≡ eval (P ∖ᵛ x[ w ]) x y
  part₀ = begin
    eval (restrict ι′ P) v′ y
      ≡⟨ eval-restrict ι′ inj′ P v′ y ⟩
    eval P x′ y
      ≡⟨ eval-split P x[ w ] x′ y ⟩
    eval (P ∖ᵛ x[ w ]) x′ y +ℤ
    ((if x′ w then 1ℤ else 0ℤ) *ℤ eval (P /ᵛ x[ w ]) x′ y)
      ≡⟨ cong (λ b → eval (P ∖ᵛ x[ w ]) x′ y +ℤ
                     ((if b then 1ℤ else 0ℤ) *ℤ eval (P /ᵛ x[ w ]) x′ y))
              x′w ⟩
    eval (P ∖ᵛ x[ w ]) x′ y +ℤ (0ℤ *ℤ eval (P /ᵛ x[ w ]) x′ y)
      ≡⟨ cong (eval (P ∖ᵛ x[ w ]) x′ y +ℤ_)
              (*-zeroˡ (eval (P /ᵛ x[ w ]) x′ y)) ⟩
    eval (P ∖ᵛ x[ w ]) x′ y +ℤ 0ℤ
      ≡⟨ +-identityʳ _ ⟩
    eval (P ∖ᵛ x[ w ]) x′ y
      ≡⟨ sym (eval-off (P ∖ᵛ x[ w ]) w off∖ x x′ y agree) ⟩
    eval (P ∖ᵛ x[ w ]) x y
      ∎

  -- The monomials with it: the quotient of P by x_w.

  coeff₁ : ∀ γ → Q₁ γ ≡ restrict ι′ (P /ᵛ x[ w ]) γ
  coeff₁ (α , β) = sym (trans
    (if-∉ (img ι′ α) (head∉ ι inj α))
    (cong₂ (λ a b → P (a , b)) (∪-comm (img ι′ α) ⁅ w ⁆) (∪-identityʳ β)))

  part₁ : eval Q₁ v′ y ≡ eval (P /ᵛ x[ w ]) x y
  part₁ = begin
    eval Q₁ v′ y
      ≡⟨ eval-ext Q₁ (restrict ι′ (P /ᵛ x[ w ])) coeff₁ v′ y ⟩
    eval (restrict ι′ (P /ᵛ x[ w ])) v′ y
      ≡⟨ eval-restrict ι′ inj′ (P /ᵛ x[ w ]) v′ y ⟩
    eval (P /ᵛ x[ w ]) x′ y
      ≡⟨ sym (eval-off (P /ᵛ x[ w ]) w off/ x x′ y agree) ⟩
    eval (P /ᵛ x[ w ]) x y
      ∎
