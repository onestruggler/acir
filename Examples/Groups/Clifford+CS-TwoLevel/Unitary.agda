------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators preserve inner products, their matrices are symmetric
-- and unitary, and so the matrix of every word is unitary.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; _-_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.Clifford+CS-TwoLevel.Unitary
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (ci cg : A)
  (ci-unit : adj ci * ci ≡ 1#)
  (cg-half : adj cg * cg + adj cg * cg ≡ 1#)
  where

open import Data.Fin.Base as Fin using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Negation using (contradiction)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)
import Quantum.Synthesis.Ring.Properties.Common as Common

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
import Examples.Groups.Clifford+CS-TwoLevel.Action as Action

open Action isCR adjI ci cg ci-unit cg-half public

private
  module S = Common.ZSolver R
  variable
    n m : ℕ

------------------------------------------------------------------------
-- Generators preserve inner products

private
  -- The identity behind K's unitarity: with h = c̄ c and h + h = 1,
  -- (c̄(P+Q))(c(P'+Q')) + (c̄(P-Q))(c(P'-Q')) = PP' + QQ'.
  K-identity : ∀ c̄ c P Q P' Q' → c̄ * c + c̄ * c ≡ 1# →
               (c̄ * (P + Q)) * (c * (P' + Q')) + (c̄ * (P + - Q)) * (c * (P' + - Q'))
               ≡ P * P' + Q * Q'
  K-identity c̄ c P Q P' Q' half = begin
    (c̄ * (P + Q)) * (c * (P' + Q')) + (c̄ * (P + - Q)) * (c * (P' + - Q'))
      ≡⟨ S.solve 6 (λ c̄ c P Q P' Q' →
            (c̄ S.:* (P S.:+ Q)) S.:* (c S.:* (P' S.:+ Q')) S.:+ (c̄ S.:* (P S.:+ S.:- Q)) S.:* (c S.:* (P' S.:+ S.:- Q'))
            S.:= (c̄ S.:* c S.:+ c̄ S.:* c) S.:* (P S.:* P' S.:+ Q S.:* Q')) AR.refl c̄ c P Q P' Q' ⟩
    (c̄ * c + c̄ * c) * (P * P' + Q * Q')
      ≡⟨ cong (_* (P * P' + Q * Q')) half ⟩
    1# * (P * P' + Q * Q')
      ≡⟨ AR.*-identityˡ _ ⟩
    P * P' + Q * Q' ∎
    where open ≡-Reasoning

  i-identity : ∀ c̄ c P P' → c̄ * c ≡ 1# → (c̄ * P) * (c * P') ≡ P * P'
  i-identity c̄ c P P' unit = begin
    (c̄ * P) * (c * P')    ≡⟨ S.solve 4 (λ c̄ c P P' → (c̄ S.:* P) S.:* (c S.:* P') S.:= (c̄ S.:* c) S.:* (P S.:* P'))
                               AR.refl c̄ c P P' ⟩
    (c̄ * c) * (P * P')    ≡⟨ cong (_* (P * P')) unit ⟩
    1# * (P * P')         ≡⟨ AR.*-identityˡ _ ⟩
    P * P'                ∎
    where open ≡-Reasoning

  adj-- : ∀ x y → adj (x - y) ≡ adj x + - adj y
  adj-- x y = trans (adj-+ x (- y)) (cong (adj x +_) (adj-neg y))

ip-actV : (g : Gen n) (u u' : Vec A n) → ⟨ actV g u , actV g u' ⟩ ≡ ⟨ u , u' ⟩
ip-actV (X-gen a b p) u u' =
  sum-update F G a b (<⇒≢ p) off
    (begin
      G a + G b
        ≡⟨ cong₂ _+_ (cong₂ (λ y z → adj y * z) (actV-Xa p u) (actV-Xa p u'))
                     (cong₂ (λ y z → adj y * z) (actV-Xb p u) (actV-Xb p u')) ⟩
      F b + F a
        ≡⟨ AR.+-comm (F b) (F a) ⟩
      F a + F b ∎)
  where
  open ≡-Reasoning
  F G : Fin _ → A
  F x = adj (u ! x) * u' ! x
  G x = adj (actV (X-gen a b p) u ! x) * actV (X-gen a b p) u' ! x
  off : ∀ x → x ≢ a → x ≢ b → G x ≡ F x
  off x x≢a x≢b = cong₂ (λ y z → adj y * z) (actV-X≢ p u x≢a x≢b)
                                           (actV-X≢ p u' x≢a x≢b)
ip-actV (K-gen a b p) u u' =
  sum-update F G a b (<⇒≢ p) off
    (begin
      G a + G b
        ≡⟨ cong₂ _+_ (cong₂ (λ y z → adj y * z) (actV-Ka p u) (actV-Ka p u'))
                     (cong₂ (λ y z → adj y * z) (actV-Kb p u) (actV-Kb p u')) ⟩
      adj α * α' + adj β * β'
        ≡⟨ cong₂ _+_ (cong (_* α') (trans (adj-* cg (u ! a + u ! b)) (cong (adj cg *_) (adj-+ (u ! a) (u ! b)))))
                     (cong (_* β') (trans (adj-* cg (u ! a - u ! b)) (cong (adj cg *_) (adj-- (u ! a) (u ! b))))) ⟩
      (adj cg * (adj (u ! a) + adj (u ! b))) * α' + (adj cg * (adj (u ! a) + - adj (u ! b))) * β'
        ≡⟨ K-identity (adj cg) cg (adj (u ! a)) (adj (u ! b)) (u' ! a) (u' ! b) cg-half ⟩
      F a + F b ∎)
  where
  open ≡-Reasoning
  α β α' β' : A
  α = cg * (u ! a + u ! b)
  β = cg * (u ! a - u ! b)
  α' = cg * (u' ! a + u' ! b)
  β' = cg * (u' ! a - u' ! b)
  F G : Fin _ → A
  F x = adj (u ! x) * u' ! x
  G x = adj (actV (K-gen a b p) u ! x) * actV (K-gen a b p) u' ! x
  off : ∀ x → x ≢ a → x ≢ b → G x ≡ F x
  off x x≢a x≢b = cong₂ (λ y z → adj y * z) (actV-K≢ p u x≢a x≢b) (actV-K≢ p u' x≢a x≢b)
ip-actV (i-gen a) u u' =
  sum-update₁ F G a off
    (begin
      G a
        ≡⟨ cong₂ (λ y z → adj y * z) (actV-ia a u) (actV-ia a u') ⟩
      adj (ci * u ! a) * (ci * u' ! a)
        ≡⟨ cong (_* (ci * u' ! a)) (adj-* ci (u ! a)) ⟩
      (adj ci * adj (u ! a)) * (ci * u' ! a)
        ≡⟨ i-identity (adj ci) ci (adj (u ! a)) (u' ! a) ci-unit ⟩
      F a ∎)
  where
  open ≡-Reasoning
  F G : Fin _ → A
  F x = adj (u ! x) * u' ! x
  G x = adj (actV (i-gen a) u ! x) * actV (i-gen a) u' ! x
  off : ∀ x → x ≢ a → G x ≡ F x
  off x x≢a = cong₂ (λ y z → adj y * z) (actV-i≢ a u x≢a) (actV-i≢ a u' x≢a)

ip-actVʷ : (w : Word (Gen n)) (u u' : Vec A n) → ⟨ actVʷ w u , actVʷ w u' ⟩ ≡ ⟨ u , u' ⟩
ip-actVʷ [ g ]ʷ u u' = ip-actV g u u'
ip-actVʷ ε u u' = refl
ip-actVʷ (v • w) u u' = trans (ip-actVʷ v (actVʷ w u) (actVʷ w u')) (ip-actVʷ w u u')

------------------------------------------------------------------------
-- Column-orthonormal matrices: M† M = I

ColOrth : Matrix n m A → Set
ColOrth M = adjoint M ·*· M ≡ 𝕀

-- The columns of a column-orthonormal matrix are orthonormal.
ColOrth-ip : {M : Matrix n m A} → ColOrth M → ∀ r c → ⟨ col M r , col M c ⟩ ≡ δ r c
ColOrth-ip {M = M} o r c = trans (sym (ent-†·*· M M r c)) (trans (cong (λ N → ent N r c) o) (ent-𝕀 r c))

ip⇒ColOrth : {M : Matrix n m A} → (∀ r c → ⟨ col M r , col M c ⟩ ≡ δ r c) → ColOrth M
ip⇒ColOrth {M = M} ip = mat-ext λ r c → trans (ent-†·*· M M r c) (trans (ip r c) (sym (ent-𝕀 r c)))

ColOrth-actMʷ : (w : Word (Gen n)) {M : Matrix n m A} → ColOrth M → ColOrth (actMʷ w M)
ColOrth-actMʷ w {M} o = ip⇒ColOrth λ r c → begin
  ⟨ col (actMʷ w M) r , col (actMʷ w M) c ⟩     ≡⟨ cong₂ ⟨_,_⟩ (col-actMʷ w M r) (col-actMʷ w M c) ⟩
  ⟨ actVʷ w (col M r) , actVʷ w (col M c) ⟩     ≡⟨ ip-actVʷ w (col M r) (col M c) ⟩
  ⟨ col M r , col M c ⟩                         ≡⟨ ColOrth-ip o r c ⟩
  δ r c                                         ∎
  where open ≡-Reasoning

ColOrth-𝕀 : ColOrth (𝕀 {n})
ColOrth-𝕀 = trans (cong (_·*· 𝕀) adjoint-𝕀) (·*·-identityˡ 𝕀)

------------------------------------------------------------------------
-- The matrices of the generators are symmetric

private
  0δ : ∀ {x y : Fin n} → x ≢ y → 0# ≡ δ x y
  0δ x≢y = sym (δ-≢ x≢y)

  -- cg (δ a x + δ b x) and cg (δ a x - δ b x) at the relevant points.
  k+01 : cg * (0# + 1#) ≡ cg
  k+01 = S.solve 1 (λ c → c S.:* (S.con (Data.Integer.Base.+ 0) S.:+ S.con (Data.Integer.Base.+ 1)) S.:= c) AR.refl cg
    where import Data.Integer.Base
  k-10 : cg * (1# + - 0#) ≡ cg
  k-10 = S.solve 1 (λ c → c S.:* (S.con (Data.Integer.Base.+ 1) S.:+ S.:- S.con (Data.Integer.Base.+ 0)) S.:= c) AR.refl cg
    where import Data.Integer.Base
  k+00 : cg * (0# + 0#) ≡ 0#
  k+00 = S.solve 1 (λ c → c S.:* (S.con (Data.Integer.Base.+ 0) S.:+ S.con (Data.Integer.Base.+ 0)) S.:= S.con (Data.Integer.Base.+ 0)) AR.refl cg
    where import Data.Integer.Base
  k-00 : cg * (0# + - 0#) ≡ 0#
  k-00 = S.solve 1 (λ c → c S.:* (S.con (Data.Integer.Base.+ 0) S.:+ S.:- S.con (Data.Integer.Base.+ 0)) S.:= S.con (Data.Integer.Base.+ 0)) AR.refl cg
    where import Data.Integer.Base

coef-sym : (g : Gen n) (r x : Fin n) → coef g r x ≡ coef g x r
coef-sym g r x = byDec (r FinP.≟ x) (λ r≡x → cong (λ y → coef g r y) (sym r≡x) ∙ cong (λ y → coef g y r) r≡x) (cases g)
  where
  _∙_ = trans
  cases : (g : Gen _) → r ≢ x → coef g r x ≡ coef g x r
  cases (X-gen a b p) r≢x =
    byDec (r FinP.≟ a)
      (λ { refl → byDec (x FinP.≟ b)
             (λ { refl → coef-X-a p x ∙ (δ-refl x ∙ (sym (δ-refl r) ∙ sym (coef-X-b p r))) })
             (λ x≢b → coef-X-a p x ∙ (δ-≢ (≢-sym x≢b) ∙ (0δ (≢-sym r≢x) ∙ sym (coef-X-≢ p (≢-sym r≢x) x≢b r)))) })
      (λ r≢a → byDec (r FinP.≟ b)
        (λ { refl → byDec (x FinP.≟ a)
               (λ { refl → coef-X-b p x ∙ (δ-refl x ∙ (sym (δ-refl r) ∙ sym (coef-X-a p r))) })
               (λ x≢a → coef-X-b p x ∙ (δ-≢ (≢-sym x≢a) ∙ (0δ (≢-sym r≢x) ∙ sym (coef-X-≢ p x≢a (≢-sym r≢x) r)))) })
        (λ r≢b → byDec (x FinP.≟ a)
          (λ { refl → coef-X-≢ p r≢a r≢b x ∙ (δ-≢ r≢x ∙ (0δ (≢-sym r≢b) ∙ sym (coef-X-a p r))) })
          (λ x≢a → byDec (x FinP.≟ b)
            (λ { refl → coef-X-≢ p r≢a r≢b x ∙ (δ-≢ r≢x ∙ (0δ (≢-sym r≢a) ∙ sym (coef-X-b p r))) })
            (λ x≢b → coef-X-≢ p r≢a r≢b x ∙ (δ-sym r x ∙ sym (coef-X-≢ p x≢a x≢b r))))))
  cases (K-gen a b p) r≢x =
    byDec (r FinP.≟ a)
      (λ { refl → byDec (x FinP.≟ b)
             (λ { refl → coef-K-a p x ∙ (cong₂ (λ y z → cg * (y + z)) (δ-≢ r≢x) (δ-refl x) ∙ (k+01 ∙ (sym k-10 ∙
                          (sym (cong₂ (λ y z → cg * (y + - z)) (δ-refl r) (δ-≢ (≢-sym r≢x))) ∙ sym (coef-K-b p r))))) })
             (λ x≢b → coef-K-a p x ∙ (cong₂ (λ y z → cg * (y + z)) (δ-≢ r≢x) (δ-≢ (≢-sym x≢b)) ∙ (k+00 ∙
                          (0δ (≢-sym r≢x) ∙ sym (coef-K-≢ p (≢-sym r≢x) x≢b r))))) })
      (λ r≢a → byDec (r FinP.≟ b)
        (λ { refl → byDec (x FinP.≟ a)
               (λ { refl → coef-K-b p x ∙ (cong₂ (λ y z → cg * (y + - z)) (δ-refl x) (δ-≢ r≢x) ∙ (k-10 ∙ (sym k+01 ∙
                            (sym (cong₂ (λ y z → cg * (y + z)) (δ-≢ (≢-sym r≢x)) (δ-refl r)) ∙ sym (coef-K-a p r))))) })
               (λ x≢a → coef-K-b p x ∙ (cong₂ (λ y z → cg * (y + - z)) (δ-≢ (≢-sym x≢a)) (δ-≢ r≢x) ∙ (k-00 ∙
                            (0δ (≢-sym r≢x) ∙ sym (coef-K-≢ p x≢a (≢-sym r≢x) r))))) })
        (λ r≢b → byDec (x FinP.≟ a)
          (λ { refl → coef-K-≢ p r≢a r≢b x ∙ (δ-≢ r≢x ∙ (sym k+00 ∙
                        (sym (cong₂ (λ y z → cg * (y + z)) (δ-≢ (≢-sym r≢x)) (δ-≢ (≢-sym r≢b))) ∙ sym (coef-K-a p r)))) })
          (λ x≢a → byDec (x FinP.≟ b)
            (λ { refl → coef-K-≢ p r≢a r≢b x ∙ (δ-≢ r≢x ∙ (sym k-00 ∙
                          (sym (cong₂ (λ y z → cg * (y + - z)) (δ-≢ (≢-sym r≢a)) (δ-≢ (≢-sym r≢x))) ∙ sym (coef-K-b p r)))) })
            (λ x≢b → coef-K-≢ p r≢a r≢b x ∙ (δ-sym r x ∙ sym (coef-K-≢ p x≢a x≢b r))))))
  cases (i-gen a) r≢x =
    byDec (r FinP.≟ a)
      (λ { refl → coef-i-a r x ∙ (cong (_* ci) (δ-≢ r≢x) ∙ (AR.zeroˡ ci ∙ (0δ (≢-sym r≢x) ∙ sym (coef-i-≢ r (≢-sym r≢x) r)))) })
      (λ r≢a → byDec (x FinP.≟ a)
        (λ { refl → coef-i-≢ x r≢a x ∙ (δ-≢ r≢x ∙ (sym (AR.zeroˡ ci) ∙ (cong (_* ci) (0δ (≢-sym r≢x)) ∙ sym (coef-i-a x r)))) })
        (λ x≢a → coef-i-≢ a r≢a x ∙ (δ-sym r x ∙ sym (coef-i-≢ a x≢a r))))

------------------------------------------------------------------------
-- Unitary matrices: U† U = U U† = I

Unitary : Matrix n n A → Set
Unitary M = (adjoint M ·*· M ≡ 𝕀) × (M ·*· adjoint M ≡ 𝕀)

Unitary-𝕀 : Unitary (𝕀 {n})
Unitary-𝕀 = ColOrth-𝕀 , trans (cong (𝕀 ·*·_) adjoint-𝕀) (·*·-identityˡ 𝕀)

Unitary-·*· : {M N : Matrix n n A} → Unitary M → Unitary N → Unitary (M ·*· N)
Unitary-·*· {M = M} {N} (m₁ , m₂) (n₁ , n₂) = u₁ , u₂
  where
  open ≡-Reasoning
  u₁ : adjoint (M ·*· N) ·*· (M ·*· N) ≡ 𝕀
  u₁ = begin
    adjoint (M ·*· N) ·*· (M ·*· N)               ≡⟨ cong (_·*· (M ·*· N)) (adjoint-·*· M N) ⟩
    (adjoint N ·*· adjoint M) ·*· (M ·*· N)       ≡⟨ ·*·-assoc (adjoint N) (adjoint M) (M ·*· N) ⟩
    adjoint N ·*· (adjoint M ·*· (M ·*· N))       ≡⟨ cong (adjoint N ·*·_) (sym (·*·-assoc (adjoint M) M N)) ⟩
    adjoint N ·*· ((adjoint M ·*· M) ·*· N)       ≡⟨ cong (λ z → adjoint N ·*· (z ·*· N)) m₁ ⟩
    adjoint N ·*· (𝕀 ·*· N)                       ≡⟨ cong (adjoint N ·*·_) (·*·-identityˡ N) ⟩
    adjoint N ·*· N                               ≡⟨ n₁ ⟩
    𝕀                                             ∎
  u₂ : (M ·*· N) ·*· adjoint (M ·*· N) ≡ 𝕀
  u₂ = begin
    (M ·*· N) ·*· adjoint (M ·*· N)               ≡⟨ cong ((M ·*· N) ·*·_) (adjoint-·*· M N) ⟩
    (M ·*· N) ·*· (adjoint N ·*· adjoint M)       ≡⟨ ·*·-assoc M N (adjoint N ·*· adjoint M) ⟩
    M ·*· (N ·*· (adjoint N ·*· adjoint M))       ≡⟨ cong (M ·*·_) (sym (·*·-assoc N (adjoint N) (adjoint M))) ⟩
    M ·*· ((N ·*· adjoint N) ·*· adjoint M)       ≡⟨ cong (λ z → M ·*· (z ·*· adjoint M)) n₂ ⟩
    M ·*· (𝕀 ·*· adjoint M)                       ≡⟨ cong (M ·*·_) (·*·-identityˡ (adjoint M)) ⟩
    M ·*· adjoint M                               ≡⟨ m₂ ⟩
    𝕀                                             ∎

Unitary-adjoint : {M : Matrix n n A} → Unitary M → Unitary (adjoint M)
Unitary-adjoint {M = M} (m₁ , m₂) =
  trans (cong (_·*· adjoint M) (adjoint-involutive M)) m₂ ,
  trans (cong (adjoint M ·*·_) (adjoint-involutive M)) m₁

-- A symmetric matrix with orthonormal columns is unitary.
private
  sym-ColOrth⇒Unitary : {M : Matrix n n A} → (∀ r c → ent M r c ≡ ent M c r) → ColOrth M → Unitary M
  sym-ColOrth⇒Unitary {M = M} s o = o , mat-ext λ r c → begin
    ent (M ·*· adjoint M) r c                         ≡⟨ ent-·*· M (adjoint M) r c ⟩
    sum (λ x → ent M r x * ent (adjoint M) x c)       ≡⟨ sum-cong-≗ (λ x → cong₂ _*_ (s r x) (ent-adjoint M x c)) ⟩
    sum (λ x → ent M x r * adj (ent M c x))           ≡⟨ sum-cong-≗ (λ x → cong (λ z → ent M x r * adj z) (s c x)) ⟩
    sum (λ x → ent M x r * adj (ent M x c))           ≡⟨ sum-cong-≗ (λ x → sym (adj-term r c x)) ⟩
    sum (λ x → adj (adj (ent M x r) * ent M x c))     ≡⟨ sym (adj-sum (λ x → adj (ent M x r) * ent M x c)) ⟩
    adj ⟨ col M r , col M c ⟩                         ≡⟨ cong adj (ColOrth-ip o r c) ⟩
    adj (δ r c)                                       ≡⟨ adj-δ r c ⟩
    δ r c                                             ≡⟨ sym (ent-𝕀 r c) ⟩
    ent 𝕀 r c                                         ∎
    where
    open ≡-Reasoning
    adj-term : ∀ r c x → adj (adj (ent M x r) * ent M x c) ≡ ent M x r * adj (ent M x c)
    adj-term r c x = trans (adj-* (adj (ent M x r)) (ent M x c)) (cong (_* adj (ent M x c)) (adj-adj (ent M x r)))
    adj-δ : (x y : Fin _) → adj (δ x y) ≡ δ x y
    adj-δ x y with x FinP.≟ y
    ... | yes _ = adj-1
    ... | no  _ = adj-0

Unitary-gmat : (g : Gen n) → Unitary (gmat g)
Unitary-gmat g = sym-ColOrth⇒Unitary
  (λ r c → trans (ent-gmat g r c) (trans (coef-sym g r c) (sym (ent-gmat g c r))))
  (subst ColOrth (⟦g⟧ᵐ≡ g) (ColOrth-actMʷ [ g ]ʷ ColOrth-𝕀))

-- The matrix of every word is unitary.
Unitary-⟦⟧ᵐ : (w : Word (Gen n)) → Unitary ⟦ w ⟧ᵐ
Unitary-⟦⟧ᵐ [ g ]ʷ = subst Unitary (sym (⟦g⟧ᵐ≡ g)) (Unitary-gmat g)
Unitary-⟦⟧ᵐ ε = Unitary-𝕀
Unitary-⟦⟧ᵐ (u • w) = subst Unitary (sym (⟦•⟧ᵐ u w)) (Unitary-·*· (Unitary-⟦⟧ᵐ u) (Unitary-⟦⟧ᵐ w))

------------------------------------------------------------------------
-- Columns of column-orthonormal matrices

private
  adj-δ′ : (x y : Fin n) → adj (δ x y) ≡ δ x y
  adj-δ′ x y with x FinP.≟ y
  ... | yes _ = adj-1
  ... | no  _ = adj-0

-- The inner product with a standard basis vector picks out an entry.
ip-e : (x : Fin n) (v : Vec A n) → ⟨ col 𝕀 x , v ⟩ ≡ v ! x
ip-e x v = begin
  sum (λ y → adj (col 𝕀 x ! y) * (v ! y))     ≡⟨ sum-cong-≗ (λ y → cong (λ a → adj a * (v ! y))
                                                                 (trans (ent-𝕀 y x) (δ-sym y x))) ⟩
  sum (λ y → adj (δ x y) * (v ! y))            ≡⟨ sum-cong-≗ (λ y → cong (_* (v ! y)) (adj-δ′ x y)) ⟩
  sum (λ y → δ x y * (v ! y))                  ≡⟨ sum-δˡ (v !_) x ⟩
  v ! x                                        ∎
  where open ≡-Reasoning

-- A column orthogonal to e_x has entry 0 in row x.
col-vanish : {M : Matrix n n A} → ColOrth M → ∀ {x p} → col M x ≡ col 𝕀 x → x ≢ p → col M p ! x ≡ 0#
col-vanish {M = M} o {x} {p} Mx x≢p = begin
  col M p ! x                    ≡⟨ sym (ip-e x (col M p)) ⟩
  ⟨ col 𝕀 x , col M p ⟩          ≡⟨ cong (λ u → ⟨ u , col M p ⟩) (sym Mx) ⟩
  ⟨ col M x , col M p ⟩          ≡⟨ ColOrth-ip o x p ⟩
  δ x p                          ≡⟨ δ-≢ x≢p ⟩
  0#                             ∎
  where open ≡-Reasoning

-- Columns are unit vectors.
col-unit : {M : Matrix n n A} → ColOrth M → ∀ p → ⟨ col M p , col M p ⟩ ≡ 1#
col-unit o p = trans (ColOrth-ip o p p) (δ-refl p)
