------------------------------------------------------------------------
-- Presentations of groups
--
-- Scaled dyadic matrices (Definition 5.1): M = N / √2ʲ for an integer
-- matrix N, that is, every entry is z (1/√2)ʲ for an integer z, with
-- one j for the whole matrix.
--
-- They contain I and are closed under products and adjoints; the
-- images of matrices over ℤ[1/2] are scaled dyadic (every dyadic
-- fraction is z / 2ᵗ = z (1/√2)²ᵗ, and exponents can be raised by 2 to
-- a common one), and so is I ⊗ H (exponent 1).  So the matrix of every
-- word over ℱₙ is scaled dyadic.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Dyadic where

open import Data.Fin.Base using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _∸_ ; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics using (Genᴸ ; ⌊_⌋ ; IH ; ⌊_⌋ʷ)
import Examples.Groups.CCX+HH-TwoLevel.Ring as R1
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
import Examples.Groups.CCX+HH-TwoLevel.Scale as Sc

private
  module DS = R2.DS
  open DS using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)
  variable
    n : ℕ

------------------------------------------------------------------------
-- Integers and powers of 1/√2

ιᴰ : ℤ → D
ιᴰ z = e (R1.ι z)

ιᴰ-+ : ∀ a b → ιᴰ (a ℤ.+ b) ≡ ιᴰ a DR.+ ιᴰ b
ιᴰ-+ a b = trans (cong e (R1.ι-+ a b)) (e-+ (R1.ι a) (R1.ι b))

ιᴰ-* : ∀ a b → ιᴰ (a ℤ.* b) ≡ ιᴰ a DR.* ιᴰ b
ιᴰ-* a b = trans (cong e (R1.ι-* a b)) (e-* (R1.ι a) (R1.ι b))

ιᴰ-neg : ∀ a → ιᴰ (ℤ.- a) ≡ DR.- ιᴰ a
ιᴰ-neg a = trans (cong e (R1.ι-neg a)) (e-neg (R1.ι a))

ιᴰ-0 : ιᴰ (+ 0) ≡ DR.0#
ιᴰ-0 = refl

ιᴰ-1 : ιᴰ (+ 1) ≡ DR.1#
ιᴰ-1 = refl

opaque
  unfolding R2._+ᴰ_

  ιᴰ-2 : ιᴰ (+ 2) ≡ DR.1# DR.+ DR.1#
  ιᴰ-2 = refl

-- (1/√2)ʲ.
sp : ℕ → D
sp zero = DR.1#
sp (suc j) = √½ DR.* sp j

-- 2t, with suc's on top.
dbl : ℕ → ℕ
dbl zero = zero
dbl (suc t) = suc (suc (dbl t))

private
  dbl-+ : ∀ a b → dbl a ℕ.+ dbl b ≡ dbl (a ℕ.+ b)
  dbl-+ zero b = refl
  dbl-+ (suc a) b = cong (λ m → suc (suc m)) (dbl-+ a b)

-- e (1/2)ᵗ = (1/√2)²ᵗ.
e-½^ : ∀ t → e (R1.½ᴰ Sc.^ᴰ t) ≡ sp (dbl t)
e-½^ zero = e-1
e-½^ (suc t) = trans (e-* R1.½ᴰ (R1.½ᴰ Sc.^ᴰ t))
  (trans (cong₂ DR._*_ (sym √½-sq) (e-½^ t)) (DR.*-assoc √½ √½ (sp (dbl t))))

------------------------------------------------------------------------
-- Entries z (1/√2)ʲ

infix 4 _∈ₛ_

-- (A record, so that the exponent can be inferred.)
record _∈ₛ_ (x : D) (j : ℕ) : Set where
  constructor mk∈
  field
    num : ℤ
    is  : x ≡ ιᴰ num DR.* sp j

∈-0 : ∀ {j} → DR.0# ∈ₛ j
∈-0 {j} = mk∈ (+ 0) (sym (DR.zeroˡ (sp j)))

∈-+ : ∀ {j x y} → x ∈ₛ j → y ∈ₛ j → x DR.+ y ∈ₛ j
∈-+ {j} (mk∈ z ex) (mk∈ z′ ey) =
  mk∈ (z ℤ.+ z′) (trans (cong₂ DR._+_ ex ey) (sym (trans (cong (DR._* sp j) (ιᴰ-+ z z′)) (DR.distribʳ (sp j) (ιᴰ z) (ιᴰ z′)))))

∈-neg : ∀ {j x} → x ∈ₛ j → DR.- x ∈ₛ j
∈-neg {j} (mk∈ z ex) =
  mk∈ (ℤ.- z) (trans (cong DR.-_ ex) (sym (trans (cong (DR._* sp j) (ιᴰ-neg z))
                                             (DS.solve 2 (λ a p → (:- a) :* p := :- (a :* p)) refl (ιᴰ z) (sp j)))))

private
  sp-+ : ∀ j j′ → sp (j ℕ.+ j′) ≡ sp j DR.* sp j′
  sp-+ zero j′ = sym (DR.*-identityˡ (sp j′))
  sp-+ (suc j) j′ = trans (cong (√½ DR.*_) (sp-+ j j′)) (sym (DR.*-assoc √½ (sp j) (sp j′)))

∈-* : ∀ {j j′ x y} → x ∈ₛ j → y ∈ₛ j′ → x DR.* y ∈ₛ (j ℕ.+ j′)
∈-* {j} {j′} (mk∈ z ex) (mk∈ z′ ey) =
  mk∈ (z ℤ.* z′) (trans (cong₂ DR._*_ ex ey)
    (sym (trans (cong₂ DR._*_ (ιᴰ-* z z′) (sp-+ j j′))
           (DS.solve 4 (λ a b p q → (a :* b) :* (p :* q) := (a :* p) :* (b :* q)) refl (ιᴰ z) (ιᴰ z′) (sp j) (sp j′)))))

∈-sum : ∀ {j m} (f : Fin m → D) → (∀ i → f i ∈ₛ j) → sum f ∈ₛ j
∈-sum {m = zero} f h = ∈-0
∈-sum {m = suc m} f h = ∈-+ (h zero) (∈-sum (λ i → f (suc i)) (λ i → h (suc i)))

-- The exponent can be raised by 2.
∈-raise₂ : ∀ {j x} → x ∈ₛ j → x ∈ₛ suc (suc j)
∈-raise₂ {j} (mk∈ z ex) =
  mk∈ (+ 2 ℤ.* z) (trans ex (sym (begin
    ιᴰ (+ 2 ℤ.* z) DR.* (√½ DR.* (√½ DR.* sp j))                    ≡⟨ cong (DR._* (√½ DR.* (√½ DR.* sp j)))
                                                                          (trans (ιᴰ-* (+ 2) z) (cong (DR._* ιᴰ z) ιᴰ-2)) ⟩
    ((DR.1# DR.+ DR.1#) DR.* ιᴰ z) DR.* (√½ DR.* (√½ DR.* sp j))    ≡⟨ DS.solve 3 (λ s a p → ((con (+ 1) :+ con (+ 1)) :* a) :* (s :* (s :* p))
                                                                          := (s :* s :+ s :* s) :* (a :* p)) refl √½ (ιᴰ z) (sp j) ⟩
    (√½ DR.* √½ DR.+ √½ DR.* √½) DR.* (ιᴰ z DR.* sp j)              ≡⟨ cong (DR._* (ιᴰ z DR.* sp j)) √½-half ⟩
    DR.1# DR.* (ιᴰ z DR.* sp j)                                     ≡⟨ DR.*-identityˡ _ ⟩
    ιᴰ z DR.* sp j                                                  ∎)))
  where open ≡-Reasoning

∈-raise : ∀ t {j x} → x ∈ₛ j → x ∈ₛ dbl t ℕ.+ j
∈-raise zero h = h
∈-raise (suc t) h = ∈-raise₂ (∈-raise t h)

-- An embedded dyadic fraction.
∈-e : ∀ (d : R1.D) → Σ ℕ λ t → e d ∈ₛ dbl t
∈-e d with Sc.rep d
... | K , a , d≡ = K , mk∈ a (trans (cong e (trans d≡ (Sc.sc-def K a)))
                              (trans (e-* (R1.ι a) (R1.½ᴰ Sc.^ᴰ K)) (cong (ιᴰ a DR.*_) (e-½^ K))))

------------------------------------------------------------------------
-- Scaled dyadic matrices

ScaledDyadic : Matrix n n D → Set
ScaledDyadic {n} M = Σ ℕ λ j → ∀ (r c : Fin n) → ent M r c ∈ₛ j

private
  δ∈ : ∀ (x y : Fin n) → δ x y ∈ₛ 0
  δ∈ x y with x FinP.≟ y
  ... | yes _ = mk∈ (+ 1) (sym (DR.*-identityˡ DR.1#))
  ... | no _ = ∈-0

SD-𝕀 : ScaledDyadic (𝕀 {n})
SD-𝕀 = 0 , λ r c → subst (_∈ₛ 0) (sym (ent-𝕀 r c)) (δ∈ r c)

SD-·*· : {M N : Matrix n n D} → ScaledDyadic M → ScaledDyadic N → ScaledDyadic (M ·*· N)
SD-·*· {M = M} {N} (j , fM) (j′ , fN) =
  j ℕ.+ j′ , λ r c → subst (_∈ₛ j ℕ.+ j′) (sym (ent-·*· M N r c)) (∈-sum _ (λ x → ∈-* (fM r x) (fN x c)))

SD-adjoint : {M : Matrix n n D} → ScaledDyadic M → ScaledDyadic (adjoint M)
SD-adjoint {M = M} (j , f) = j , λ r c → subst (_∈ₛ j) (sym (trans (ent-adjoint M r c) (R2.adjᴰ-id _))) (f c r)

-- Images of dyadic matrices: the exponents are raised to their sum.
private
  sumℕ : ∀ {m} → (Fin m → ℕ) → ℕ
  sumℕ {zero} f = 0
  sumℕ {suc m} f = f zero ℕ.+ sumℕ (λ i → f (suc i))

  ≤-sumℕ : ∀ {m} (f : Fin m → ℕ) i → f i ≤ sumℕ f
  ≤-sumℕ {suc m} f zero = ℕP.m≤m+n (f zero) _
  ≤-sumℕ {suc m} f (suc i) = ℕP.≤-trans (≤-sumℕ (λ i → f (suc i)) i) (ℕP.m≤n+m _ (f zero))

  -- From exponent dbl t to dbl T, t ≤ T.
  lift : ∀ {t T x} → t ≤ T → x ∈ₛ dbl t → x ∈ₛ dbl T
  lift {t} {T} t≤T h =
    subst (_ ∈ₛ_) (trans (dbl-+ (T ∸ t) t) (cong dbl (ℕP.m∸n+n≡m t≤T))) (∈-raise (T ∸ t) h)

SD-mapM : (N : Matrix n n R1.D) → ScaledDyadic (mapM N)
SD-mapM {n} N = dbl T , λ r c →
  subst (_∈ₛ dbl T) (sym (ent-mapM N r c))
    (lift (ℕP.≤-trans (≤-sumℕ (t r) c) (≤-sumℕ (λ r → sumℕ (t r)) r)) (proj₂ (∈-e (S1.ent N r c))))
  where
  t : Fin n → Fin n → ℕ
  t r c = proj₁ (∈-e (S1.ent N r c))
  T = sumℕ (λ r → sumℕ (t r))

-- I ⊗ H: exponent 1.
private
  s∈ : √½ ∈ₛ 1
  s∈ = mk∈ (+ 1) (trans (sym (DR.*-identityʳ √½)) (sym (DR.*-identityˡ (√½ DR.* DR.1#))))

  coef∈ : ∀ k (r c : Fin (k ℕ.* 2)) → coefIH k r c ∈ₛ 1
  coef∈ (suc k) zero x = ∈-* s∈ (∈-+ (δ∈ zero x) (δ∈ (suc zero) x))
  coef∈ (suc k) (suc zero) x = ∈-* s∈ (∈-+ (δ∈ zero x) (∈-neg (δ∈ (suc zero) x)))
  coef∈ (suc k) (suc (suc r)) zero = ∈-0
  coef∈ (suc k) (suc (suc r)) (suc zero) = ∈-0
  coef∈ (suc k) (suc (suc r)) (suc (suc x)) = coef∈ k r x

SD-gmatIH : ∀ k → ScaledDyadic (Dim.gmatIH k)
SD-gmatIH k = 1 , λ r c → subst (_∈ₛ 1) (sym (ent-mk (coefIH k) r c)) (coef∈ k r c)

-- The matrix of every word over ℱ₂ₖ.
SD-⟦⟧ : ∀ k (w : Word (Genᴸ (k ℕ.* 2))) → ScaledDyadic (Dim.⟦_⟧ᴸ k w)
SD-⟦⟧ k [ ⌊ g ⌋ ]ʷ = subst ScaledDyadic (sym (⟦⌊⌋⟧ k [ g ]ʷ)) (SD-mapM S1.⟦ [ g ]ʷ ⟧ᵐ)
SD-⟦⟧ k [ IH ]ʷ = subst ScaledDyadic (sym (Dim.⟦g⟧ᴸ≡ k IH)) (SD-gmatIH k)
SD-⟦⟧ k ε = SD-𝕀
SD-⟦⟧ k (u • w) =
  subst ScaledDyadic (sym (Dim.⟦•⟧ᴸ k u w)) (SD-·*· {M = Dim.⟦_⟧ᴸ k u} {N = Dim.⟦_⟧ᴸ k w} (SD-⟦⟧ k u) (SD-⟦⟧ k w))
