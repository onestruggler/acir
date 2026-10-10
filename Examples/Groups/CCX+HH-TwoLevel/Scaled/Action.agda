------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators of ℱₙ (Definition 5.2) acting on vectors and matrices,
-- for n = 2k, over any commutative ring with an involution, a
-- self-adjoint h with 4h² = 1 (the scalar of K) and a self-adjoint s
-- with s² = h and 2s² = 1 (that of H; in ℤ[1/√2], h = 1/2 and
-- s = 1/√2).
--
-- I ⊗ H acts on each block {2i, 2i+1} by (a, b) ↦ (s(a + b), s(a - b)).
-- It is an involution that keeps inner products, so its matrix, like
-- those of the generators of 𝒢ₙ, is self-adjoint and unitary, and ⟦_⟧ᴸ
-- is a homomorphism.  The relations of Table 2 hold as identities of
-- actions, by induction on the block of their indices (r7a-act, …).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Action
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A) (h-self : adj h ≡ h) (h-quarter : h * h + h * h + h * h + h * h ≡ 1#)
  (s : A) (s-self : adj s ≡ s) (s-sq : s * s ≡ h) (s-half : s * s + s * s ≡ 1#)
  where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; _<_)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _%_)
import Data.Integer.Base as ℤ
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_ ; id)
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; unMatrix ; _·*·_ ; adjoint)
import Quantum.Synthesis.Ring.Properties.Common as Common

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen ; M-gen ; X-gen ; K-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics using (Genᴸ ; ⌊_⌋ ; IH)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; gen)
import Examples.Groups.CCX+HH-TwoLevel.Orthogonal as Orthogonal
import Examples.Groups.CCX+HH-TwoLevel.EmbedAction as EmbedAction

open Orthogonal isCR adjI h h-self h-quarter public
open EmbedAction isCR adjI h using (restrict ; restrict-! ; emb-restrict ; emb-actV-out)

private
  module S = Common.ZSolver R
  variable
    k m : ℕ

  -- (s s + s s) x = x.
  half : ∀ x → (s * s + s * s) * x ≡ x
  half x = trans (cong (_* x) s-half) (AR.*-identityˡ x)

------------------------------------------------------------------------
-- I ⊗ H on vectors

actIH : ∀ k → Vec A (k ℕ.* 2) → Vec A (k ℕ.* 2)
actIH zero [] = []
actIH (suc k) (a ∷ b ∷ v) = s * (a + b) ∷ s * (a + - b) ∷ actIH k v

-- Its rows.
coefIH : ∀ k → Fin (k ℕ.* 2) → Fin (k ℕ.* 2) → A
coefIH (suc k) zero x = s * (δ zero x + δ (suc zero) x)
coefIH (suc k) (suc zero) x = s * (δ zero x + - δ (suc zero) x)
coefIH (suc k) (suc (suc r)) zero = 0#
coefIH (suc k) (suc (suc r)) (suc zero) = 0#
coefIH (suc k) (suc (suc r)) (suc (suc x)) = coefIH k r x

private
  open S using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)

actIH-row : ∀ k (v : Vec A (k ℕ.* 2)) (r : Fin (k ℕ.* 2)) → actIH k v ! r ≡ sum (λ x → coefIH k r x * v ! x)
actIH-row (suc k) (a ∷ b ∷ v) zero =
  trans (S.solve 3 (λ s a b → s :* (a :+ b) := s :* (con (ℤ.+ 1) :+ con (ℤ.+ 0)) :* a :+ (s :* (con (ℤ.+ 0) :+ con (ℤ.+ 1)) :* b :+ con (ℤ.+ 0)))
                    AR.refl s a b)
        (cong (λ t → s * (1# + 0#) * a + (s * (0# + 1#) * b + t))
              (sym (sum-zero (λ x → s * (0# + 0#) * v ! x) (λ x → z0′ (v ! x)))))
  where
  z0′ : ∀ y → s * (0# + 0#) * y ≡ 0#
  z0′ = S.solve 2 (λ s y → s :* (con (ℤ.+ 0) :+ con (ℤ.+ 0)) :* y := con (ℤ.+ 0)) AR.refl s
actIH-row (suc k) (a ∷ b ∷ v) (suc zero) =
  trans (S.solve 3 (λ s a b → s :* (a :+ :- b) := s :* (con (ℤ.+ 1) :+ :- con (ℤ.+ 0)) :* a :+ (s :* (con (ℤ.+ 0) :+ :- con (ℤ.+ 1)) :* b :+ con (ℤ.+ 0)))
                    AR.refl s a b)
        (cong (λ t → s * (1# + - 0#) * a + (s * (0# + - 1#) * b + t))
              (sym (sum-zero (λ x → s * (0# + - 0#) * v ! x) (λ x → z0′ (v ! x)))))
  where
  z0′ : ∀ y → s * (0# + - 0#) * y ≡ 0#
  z0′ = S.solve 2 (λ s y → s :* (con (ℤ.+ 0) :+ :- con (ℤ.+ 0)) :* y := con (ℤ.+ 0)) AR.refl s
actIH-row (suc k) (a ∷ b ∷ v) (suc (suc r)) =
  trans (actIH-row k v r)
        (S.solve 3 (λ a b t → t := con (ℤ.+ 0) :* a :+ (con (ℤ.+ 0) :* b :+ t)) AR.refl a b (sum (λ x → coefIH k r x * v ! x)))

------------------------------------------------------------------------
-- I ⊗ H is an involution and keeps inner products

private
  inv₁ : ∀ a b → s * (s * (a + b) + s * (a + - b)) ≡ a
  inv₁ a b = trans (S.solve 3 (λ s a b → s :* (s :* (a :+ b) :+ s :* (a :+ :- b)) := (s :* s :+ s :* s) :* a) AR.refl s a b) (half a)

  inv₂ : ∀ a b → s * (s * (a + b) + - (s * (a + - b))) ≡ b
  inv₂ a b = trans (S.solve 3 (λ s a b → s :* (s :* (a :+ b) :+ :- (s :* (a :+ :- b))) := (s :* s :+ s :* s) :* b) AR.refl s a b) (half b)

actIH-invol : ∀ k (v : Vec A (k ℕ.* 2)) → actIH k (actIH k v) ≡ v
actIH-invol zero [] = refl
actIH-invol (suc k) (a ∷ b ∷ v) = cong₂ _∷_ (inv₁ a b) (cong₂ _∷_ (inv₂ a b) (actIH-invol k v))

private
  adj-s+ : ∀ a b → adj (s * (a + b)) ≡ s * (adj a + adj b)
  adj-s+ a b = trans (adj-* s (a + b)) (cong₂ _*_ s-self (adj-+ a b))

  adj-s- : ∀ a b → adj (s * (a + - b)) ≡ s * (adj a + - adj b)
  adj-s- a b = trans (adj-* s (a + - b)) (cong₂ _*_ s-self (trans (adj-+ a (- b)) (cong (adj a +_) (adj-neg b))))

  ip₂ : ∀ a b c d t → s * (a + b) * (s * (c + d)) + (s * (a + - b) * (s * (c + - d)) + t) ≡ a * c + (b * d + t)
  ip₂ a b c d t =
    trans (S.solve 6 (λ s a b c d t → s :* (a :+ b) :* (s :* (c :+ d)) :+ (s :* (a :+ :- b) :* (s :* (c :+ :- d)) :+ t)
                                        := (s :* s :+ s :* s) :* (a :* c :+ b :* d) :+ t) AR.refl s a b c d t)
          (trans (cong (_+ t) (half (a * c + b * d))) (AR.+-assoc (a * c) (b * d) t))

ip-actIH : ∀ k (u u′ : Vec A (k ℕ.* 2)) → ⟨ actIH k u , actIH k u′ ⟩ ≡ ⟨ u , u′ ⟩
ip-actIH zero [] [] = refl
ip-actIH (suc k) (a ∷ b ∷ u) (c ∷ d ∷ u′) =
  trans (cong₂ (λ x y → x * (s * (c + d)) + (y * (s * (c + - d)) + ⟨ actIH k u , actIH k u′ ⟩)) (adj-s+ a b) (adj-s- a b))
    (trans (ip₂ (adj a) (adj b) c d ⟨ actIH k u , actIH k u′ ⟩)
      (cong (λ t → adj a * c + (adj b * d + t)) (ip-actIH k u u′)))

------------------------------------------------------------------------
-- The generators of ℱ₂ₖ on vectors and matrices, and the matrices of
-- words

module Dim (k : ℕ) where

  private
    n = k ℕ.* 2

  gmatIH : Matrix n n A
  gmatIH = mk (coefIH k)

  actVᴸ : Genᴸ n → Vec A n → Vec A n
  actVᴸ ⌊ g ⌋ = actV g
  actVᴸ IH = actIH k

  actVᴸʷ : Word (Genᴸ n) → Vec A n → Vec A n
  actVᴸʷ [ g ]ʷ  = actVᴸ g
  actVᴸʷ ε       = id
  actVᴸʷ (u • w) = actVᴸʷ u ∘ actVᴸʷ w

  actMᴸ : Genᴸ n → Matrix n m A → Matrix n m A
  actMᴸ g M = Matrix' (Vec.map (actVᴸ g) (unMatrix M))

  actMᴸʷ : Word (Genᴸ n) → Matrix n m A → Matrix n m A
  actMᴸʷ [ g ]ʷ  = actMᴸ g
  actMᴸʷ ε       = id
  actMᴸʷ (u • w) = actMᴸʷ u ∘ actMᴸʷ w

  col-actMᴸ : (g : Genᴸ n) (M : Matrix n m A) (c : Fin m) → col (actMᴸ g M) c ≡ actVᴸ g (col M c)
  col-actMᴸ g M c = VecP.lookup-map c (actVᴸ g) (unMatrix M)

  col-actMᴸʷ : (w : Word (Genᴸ n)) (M : Matrix n m A) (c : Fin m) → col (actMᴸʷ w M) c ≡ actVᴸʷ w (col M c)
  col-actMᴸʷ [ g ]ʷ M c = col-actMᴸ g M c
  col-actMᴸʷ ε M c = refl
  col-actMᴸʷ (u • w) M c = trans (col-actMᴸʷ u (actMᴸʷ w M) c) (cong (actVᴸʷ u) (col-actMᴸʷ w M c))

  gmatᴸ : Genᴸ n → Matrix n n A
  gmatᴸ ⌊ g ⌋ = gmat g
  gmatᴸ IH = gmatIH

  private
    coefᴸ : Genᴸ n → Fin n → Fin n → A
    coefᴸ ⌊ g ⌋ = coef g
    coefᴸ IH = coefIH k

    actVᴸ-row : (g : Genᴸ n) (v : Vec A n) (r : Fin n) → actVᴸ g v ! r ≡ sum (λ x → coefᴸ g r x * v ! x)
    actVᴸ-row ⌊ g ⌋ = actV-row g
    actVᴸ-row IH = actIH-row k

    ent-gmatᴸ : (g : Genᴸ n) (r c : Fin n) → ent (gmatᴸ g) r c ≡ coefᴸ g r c
    ent-gmatᴸ ⌊ g ⌋ = ent-gmat g
    ent-gmatᴸ IH = ent-mk (coefIH k)

  actMᴸ≡ : (g : Genᴸ n) (M : Matrix n m A) → actMᴸ g M ≡ gmatᴸ g ·*· M
  actMᴸ≡ g M = mat-ext λ r c → begin
    ent (actMᴸ g M) r c                           ≡⟨ cong (_! r) (col-actMᴸ g M c) ⟩
    actVᴸ g (col M c) ! r                         ≡⟨ actVᴸ-row g (col M c) r ⟩
    sum (λ x → coefᴸ g r x * ent M x c)           ≡⟨ sum-cong-≗ (λ x → cong (_* ent M x c) (sym (ent-gmatᴸ g r x))) ⟩
    sum (λ x → ent (gmatᴸ g) r x * ent M x c)     ≡⟨ sym (ent-·*· (gmatᴸ g) M r c) ⟩
    ent (gmatᴸ g ·*· M) r c                       ∎
    where open ≡-Reasoning

  ⟦_⟧ᴸ : Word (Genᴸ n) → Matrix n n A
  ⟦ w ⟧ᴸ = actMᴸʷ w 𝕀

  ⟦g⟧ᴸ≡ : (g : Genᴸ n) → ⟦ [ g ]ʷ ⟧ᴸ ≡ gmatᴸ g
  ⟦g⟧ᴸ≡ g = trans (actMᴸ≡ g 𝕀) (·*·-identityʳ (gmatᴸ g))

  actMᴸʷ≡ : (w : Word (Genᴸ n)) (M : Matrix n m A) → actMᴸʷ w M ≡ ⟦ w ⟧ᴸ ·*· M
  actMᴸʷ≡ [ g ]ʷ M = trans (actMᴸ≡ g M) (cong (_·*· M) (sym (⟦g⟧ᴸ≡ g)))
  actMᴸʷ≡ ε M = sym (·*·-identityˡ M)
  actMᴸʷ≡ (u • w) M = begin
    actMᴸʷ u (actMᴸʷ w M)            ≡⟨ actMᴸʷ≡ u (actMᴸʷ w M) ⟩
    ⟦ u ⟧ᴸ ·*· actMᴸʷ w M            ≡⟨ cong (⟦ u ⟧ᴸ ·*·_) (actMᴸʷ≡ w M) ⟩
    ⟦ u ⟧ᴸ ·*· (⟦ w ⟧ᴸ ·*· M)        ≡⟨ sym (·*·-assoc ⟦ u ⟧ᴸ ⟦ w ⟧ᴸ M) ⟩
    (⟦ u ⟧ᴸ ·*· ⟦ w ⟧ᴸ) ·*· M        ≡⟨ cong (_·*· M) (sym (actMᴸʷ≡ u ⟦ w ⟧ᴸ)) ⟩
    ⟦ u • w ⟧ᴸ ·*· M                 ∎
    where open ≡-Reasoning

  ⟦•⟧ᴸ : (u w : Word (Genᴸ n)) → ⟦ u • w ⟧ᴸ ≡ ⟦ u ⟧ᴸ ·*· ⟦ w ⟧ᴸ
  ⟦•⟧ᴸ u w = actMᴸʷ≡ u ⟦ w ⟧ᴸ

  -- Words that act alike have the same matrix.
  same-matrixᴸ : (w v : Word (Genᴸ n)) → (∀ u → actVᴸʷ w u ≡ actVᴸʷ v u) → ⟦ w ⟧ᴸ ≡ ⟦ v ⟧ᴸ
  same-matrixᴸ w v eq = col-ext λ c →
    trans (col-actMᴸʷ w 𝕀 c) (trans (eq (col 𝕀 c)) (sym (col-actMᴸʷ v 𝕀 c)))

  ----------------------------------------------------------------------
  -- Unitarity

  gmatIH≡ : actMᴸ IH 𝕀 ≡ gmatIH
  gmatIH≡ = trans (actMᴸ≡ IH 𝕀) (·*·-identityʳ gmatIH)

  gmatIH-invol : gmatIH ·*· gmatIH ≡ 𝕀
  gmatIH-invol = begin
    gmatIH ·*· gmatIH                 ≡⟨ sym (actMᴸ≡ IH gmatIH) ⟩
    actMᴸ IH gmatIH                   ≡⟨ cong (actMᴸ IH) (sym gmatIH≡) ⟩
    actMᴸ IH (actMᴸ IH 𝕀)             ≡⟨ col-ext (λ c → trans (col-actMᴸ IH (actMᴸ IH 𝕀) c)
                                                        (trans (cong (actIH k) (col-actMᴸ IH 𝕀 c)) (actIH-invol k (col 𝕀 c)))) ⟩
    𝕀                                 ∎
    where open ≡-Reasoning

  Unitary-gmatIH : Unitary gmatIH
  Unitary-gmatIH = o , trans (cong (G ·*·_) self) gmatIH-invol
    where
    G = gmatIH
    o : adjoint G ·*· G ≡ 𝕀
    o = ColOrth→ (subst ColOrth gmatIH≡ (ip⇒ColOrth λ r c → begin
          ⟨ col (actMᴸ IH 𝕀) r , col (actMᴸ IH 𝕀) c ⟩     ≡⟨ cong₂ ⟨_,_⟩ (col-actMᴸ IH 𝕀 r) (col-actMᴸ IH 𝕀 c) ⟩
          ⟨ actIH k (col 𝕀 r) , actIH k (col 𝕀 c) ⟩       ≡⟨ ip-actIH k (col 𝕀 r) (col 𝕀 c) ⟩
          ⟨ col 𝕀 r , col 𝕀 c ⟩                           ≡⟨ ColOrth-ip ColOrth-𝕀 r c ⟩
          δ r c                                           ∎))
      where open ≡-Reasoning
    self : adjoint G ≡ G
    self = begin
      adjoint G                          ≡⟨ sym (·*·-identityʳ (adjoint G)) ⟩
      adjoint G ·*· 𝕀                    ≡⟨ cong (adjoint G ·*·_) (sym gmatIH-invol) ⟩
      adjoint G ·*· (G ·*· G)            ≡⟨ sym (·*·-assoc (adjoint G) G G) ⟩
      (adjoint G ·*· G) ·*· G            ≡⟨ cong (_·*· G) o ⟩
      𝕀 ·*· G                            ≡⟨ ·*·-identityˡ G ⟩
      G                                  ∎
      where open ≡-Reasoning

  Unitary-gmatᴸ : (g : Genᴸ n) → Unitary (gmatᴸ g)
  Unitary-gmatᴸ ⌊ g ⌋ = Unitary-gmat g
  Unitary-gmatᴸ IH = Unitary-gmatIH

  Unitary-⟦⟧ᴸ : (w : Word (Genᴸ n)) → Unitary ⟦ w ⟧ᴸ
  Unitary-⟦⟧ᴸ [ g ]ʷ = subst Unitary (sym (⟦g⟧ᴸ≡ g)) (Unitary-gmatᴸ g)
  Unitary-⟦⟧ᴸ ε = Unitary-𝕀
  Unitary-⟦⟧ᴸ (u • w) = subst Unitary (sym (⟦•⟧ᴸ u w)) (Unitary-·*· (Unitary-⟦⟧ᴸ u) (Unitary-⟦⟧ᴸ w))
