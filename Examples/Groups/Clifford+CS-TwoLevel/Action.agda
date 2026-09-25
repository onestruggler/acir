------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators X_[a,b], K_[a,b], i_[a] as row operations on vectors
-- and matrices, over a commutative ring A with conjugation and two
-- constants: ci (the imaginary unit) and cg (the scalar of K, i.e.
-- γ⁻¹ = (1 - i)/2).  At 𝔻[i] (see Semantics) these are the one- and
-- two-level matrices of §2.2.
--
-- Acting by a generator is left multiplication by its matrix, and that
-- matrix is symmetric and unitary.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; _-_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.Clifford+CS-TwoLevel.Action
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (ci cg : A)
  (ci-unit : adj ci * ci ≡ 1#)
  (cg-half : adj cg * cg + adj cg * cg ≡ 1#)
  where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Vec.Base as Vec using (Vec ; tabulate)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_ ; id)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; recompute)
open import Relation.Nullary.Negation using (contradiction)

open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; unMatrix ; _·*·_ ; adjoint)
import Quantum.Synthesis.Ring.Properties.Common as Common
import Data.Integer.Base

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra as MatrixAlgebra

open MatrixAlgebra isCR adjI public

private
  module S = Common.ZSolver R
  variable
    n m : ℕ

-- Ordered indices are distinct.
<⇒≢ : {a b : Fin n} → .(a < b) → a ≢ b
<⇒≢ {a = a} {b} p a≡b = FinP.<-irrefl a≡b (recompute (a FinP.<? b) p)

------------------------------------------------------------------------
-- The action on vectors

actV : Gen n → Vec A n → Vec A n
actV (X-gen a b _) v = set₂ a b (v ! b) (v ! a) v
actV (K-gen a b _) v = set₂ a b (cg * (v ! a + v ! b)) (cg * (v ! a - v ! b)) v
actV (i-gen a)     v = set₁ a (ci * v ! a) v

-- Words act letter by letter, the rightmost letter first.
actVʷ : Word (Gen n) → Vec A n → Vec A n
actVʷ [ g ]ʷ   = actV g
actVʷ ε        = id
actVʷ (u • w)  = actVʷ u ∘ actVʷ w

------------------------------------------------------------------------
-- The action on matrices: on each column

actM : Gen n → Matrix n m A → Matrix n m A
actM g M = Matrix' (Vec.map (actV g) (unMatrix M))

actMʷ : Word (Gen n) → Matrix n m A → Matrix n m A
actMʷ [ g ]ʷ  = actM g
actMʷ ε       = id
actMʷ (u • w) = actMʷ u ∘ actMʷ w

col-actM : (g : Gen n) (M : Matrix n m A) (c : Fin m) → col (actM g M) c ≡ actV g (col M c)
col-actM g M c = VecP.lookup-map c (actV g) (unMatrix M)

col-actMʷ : (w : Word (Gen n)) (M : Matrix n m A) (c : Fin m) → col (actMʷ w M) c ≡ actVʷ w (col M c)
col-actMʷ [ g ]ʷ M c = col-actM g M c
col-actMʷ ε M c = refl
col-actMʷ (u • w) M c = trans (col-actMʷ u (actMʷ w M) c) (cong (actVʷ u) (col-actMʷ w M c))

------------------------------------------------------------------------
-- The matrix of a generator
--
-- coef g r x is the (r, x) entry: row r of g·v is Σₓ coef g r x · vₓ.

coef : Gen n → Fin n → Fin n → A
coef (X-gen a b _) r x with r FinP.≟ a | r FinP.≟ b
... | yes _ | _     = δ b x
... | no  _ | yes _ = δ a x
... | no  _ | no  _ = δ r x
coef (K-gen a b _) r x with r FinP.≟ a | r FinP.≟ b | x FinP.≟ a | x FinP.≟ b
... | yes _ | _     | yes _ | _     = cg
... | yes _ | _     | no  _ | yes _ = cg
... | yes _ | _     | no  _ | no  _ = 0#
... | no  _ | yes _ | yes _ | _     = cg
... | no  _ | yes _ | no  _ | yes _ = - cg
... | no  _ | yes _ | no  _ | no  _ = 0#
... | no  _ | no  _ | _     | _     = δ r x
coef (i-gen a) r x with r FinP.≟ a
... | yes _ = δ r x * ci
... | no  _ = δ r x

------------------------------------------------------------------------
-- Values of the coefficients

private
  +0 +1 : Data.Integer.Base.ℤ
  +0 = Data.Integer.Base.+ 0
  +1 = Data.Integer.Base.+ 1

module _ {a b : Fin n} .(p : a < b) where

  private
    a≢b : a ≢ b
    a≢b = <⇒≢ p

  coef-X-a : ∀ x → coef (X-gen a b p) a x ≡ δ b x
  coef-X-a x with a FinP.≟ a | a FinP.≟ b
  ... | yes _   | _ = refl
  ... | no  a≢a | _ = contradiction refl a≢a

  coef-X-b : ∀ x → coef (X-gen a b p) b x ≡ δ a x
  coef-X-b x with b FinP.≟ a | b FinP.≟ b
  ... | yes b≡a | _       = contradiction (sym b≡a) a≢b
  ... | no  _   | yes _   = refl
  ... | no  _   | no  b≢b = contradiction refl b≢b

  coef-X-≢ : ∀ {r} → r ≢ a → r ≢ b → ∀ x → coef (X-gen a b p) r x ≡ δ r x
  coef-X-≢ {r} r≢a r≢b x with r FinP.≟ a | r FinP.≟ b
  ... | yes r≡a | _       = contradiction r≡a r≢a
  ... | no  _   | yes r≡b = contradiction r≡b r≢b
  ... | no  _   | no  _   = refl

  -- Row a of K: cg at columns a and b.
  coef-K-a : ∀ x → coef (K-gen a b p) a x ≡ cg * (δ a x + δ b x)
  coef-K-a x with a FinP.≟ a | a FinP.≟ b | x FinP.≟ a | x FinP.≟ b
  ... | no a≢a | _ | _ | _ = contradiction refl a≢a
  ... | yes _ | _ | yes refl | _ = sym (begin
    cg * (δ x x + δ b x)     ≡⟨ cong₂ (λ y z → cg * (y + z)) (δ-refl x) (δ-≢ (≢-sym a≢b)) ⟩
    cg * (1# + 0#)           ≡⟨ S.solve 1 (λ c → c S.:* (S.con +1 S.:+ S.con +0) S.:= c) AR.refl cg ⟩
    cg                       ∎)
    where open ≡-Reasoning
  ... | yes _ | _ | no x≢a | yes refl = sym (begin
    cg * (δ a x + δ x x)     ≡⟨ cong₂ (λ y z → cg * (y + z)) (δ-≢ a≢b) (δ-refl x) ⟩
    cg * (0# + 1#)           ≡⟨ S.solve 1 (λ c → c S.:* (S.con +0 S.:+ S.con +1) S.:= c) AR.refl cg ⟩
    cg                       ∎)
    where open ≡-Reasoning
  ... | yes _ | _ | no x≢a | no x≢b = sym (begin
    cg * (δ a x + δ b x)     ≡⟨ cong₂ (λ y z → cg * (y + z)) (δ-≢ (≢-sym x≢a)) (δ-≢ (≢-sym x≢b)) ⟩
    cg * (0# + 0#)           ≡⟨ S.solve 1 (λ c → c S.:* (S.con +0 S.:+ S.con +0) S.:= S.con +0) AR.refl cg ⟩
    0#                       ∎)
    where open ≡-Reasoning

  -- Row b of K: cg at column a, -cg at column b.
  coef-K-b : ∀ x → coef (K-gen a b p) b x ≡ cg * (δ a x + - δ b x)
  coef-K-b x with b FinP.≟ a | b FinP.≟ b | x FinP.≟ a | x FinP.≟ b
  ... | yes b≡a | _ | _ | _ = contradiction (sym b≡a) a≢b
  ... | no _ | no b≢b | _ | _ = contradiction refl b≢b
  ... | no _ | yes _ | yes refl | _ = sym (begin
    cg * (δ x x + - δ b x)     ≡⟨ cong₂ (λ y z → cg * (y + - z)) (δ-refl x) (δ-≢ (≢-sym a≢b)) ⟩
    cg * (1# + - 0#)           ≡⟨ S.solve 1 (λ c → c S.:* (S.con +1 S.:+ S.:- S.con +0) S.:= c) AR.refl cg ⟩
    cg                         ∎)
    where open ≡-Reasoning
  ... | no _ | yes _ | no x≢a | yes refl = sym (begin
    cg * (δ a x + - δ x x)     ≡⟨ cong₂ (λ y z → cg * (y + - z)) (δ-≢ a≢b) (δ-refl x) ⟩
    cg * (0# + - 1#)           ≡⟨ S.solve 1 (λ c → c S.:* (S.con +0 S.:+ S.:- S.con +1) S.:= S.:- c) AR.refl cg ⟩
    - cg                       ∎)
    where open ≡-Reasoning
  ... | no _ | yes _ | no x≢a | no x≢b = sym (begin
    cg * (δ a x + - δ b x)     ≡⟨ cong₂ (λ y z → cg * (y + - z)) (δ-≢ (≢-sym x≢a)) (δ-≢ (≢-sym x≢b)) ⟩
    cg * (0# + - 0#)           ≡⟨ S.solve 1 (λ c → c S.:* (S.con +0 S.:+ S.:- S.con +0) S.:= S.con +0) AR.refl cg ⟩
    0#                         ∎)
    where open ≡-Reasoning

  coef-K-≢ : ∀ {r} → r ≢ a → r ≢ b → ∀ x → coef (K-gen a b p) r x ≡ δ r x
  coef-K-≢ {r} r≢a r≢b x with r FinP.≟ a | r FinP.≟ b
  ... | yes r≡a | _       = contradiction r≡a r≢a
  ... | no  _   | yes r≡b = contradiction r≡b r≢b
  ... | no  _   | no  _   = refl

coef-i-a : (a : Fin n) → ∀ x → coef (i-gen a) a x ≡ δ a x * ci
coef-i-a a x with a FinP.≟ a
... | yes _   = refl
... | no  a≢a = contradiction refl a≢a

coef-i-≢ : (a : Fin n) → ∀ {r} → r ≢ a → ∀ x → coef (i-gen a) r x ≡ δ r x
coef-i-≢ a {r} r≢a x with r FinP.≟ a
... | yes r≡a = contradiction r≡a r≢a
... | no  _   = refl

------------------------------------------------------------------------
-- Each row of g·v is Σₓ coef g r x · vₓ

private
  -- Σₓ (c · δ y x) vₓ = c · v_y.
  sum-cδ : (c : A) (y : Fin n) (v : Vec A n) → sum (λ x → (c * δ y x) * v ! x) ≡ c * v ! y
  sum-cδ c y v = begin
    sum (λ x → (c * δ y x) * v ! x)     ≡⟨ sum-cong-≗ (λ x → AR.*-assoc c (δ y x) (v ! x)) ⟩
    sum (λ x → c * (δ y x * v ! x))     ≡⟨ sym (*-distribˡ-sum c (λ x → δ y x * v ! x)) ⟩
    c * sum (λ x → δ y x * v ! x)       ≡⟨ cong (c *_) (sum-δˡ (v !_) y) ⟩
    c * v ! y                           ∎
    where open ≡-Reasoning

  -- Σₓ c (δ y x + δ z x) vₓ = c (v_y + v_z), and with a minus sign.
  sum-cδδ : (c : A) (y z : Fin n) (v : Vec A n) →
            sum (λ x → (c * (δ y x + δ z x)) * v ! x) ≡ c * (v ! y + v ! z)
  sum-cδδ c y z v = begin
    sum (λ x → (c * (δ y x + δ z x)) * v ! x)
      ≡⟨ sum-cong-≗ (λ x → S.solve 4 (λ c d e w → (c S.:* (d S.:+ e)) S.:* w
                                     S.:= (c S.:* d) S.:* w S.:+ (c S.:* e) S.:* w) AR.refl c (δ y x) (δ z x) (v ! x)) ⟩
    sum (λ x → (c * δ y x) * v ! x + (c * δ z x) * v ! x)
      ≡⟨ ∑-distrib-+ (λ x → (c * δ y x) * v ! x) (λ x → (c * δ z x) * v ! x) ⟩
    sum (λ x → (c * δ y x) * v ! x) + sum (λ x → (c * δ z x) * v ! x)
      ≡⟨ cong₂ _+_ (sum-cδ c y v) (sum-cδ c z v) ⟩
    c * v ! y + c * v ! z
      ≡⟨ sym (AR.distribˡ c (v ! y) (v ! z)) ⟩
    c * (v ! y + v ! z) ∎
    where open ≡-Reasoning

  sum-cδ-δ : (c : A) (y z : Fin n) (v : Vec A n) →
             sum (λ x → (c * (δ y x + - δ z x)) * v ! x) ≡ c * (v ! y - v ! z)
  sum-cδ-δ c y z v = begin
    sum (λ x → (c * (δ y x + - δ z x)) * v ! x)
      ≡⟨ sum-cong-≗ (λ x → S.solve 4 (λ c d e w → (c S.:* (d S.:+ S.:- e)) S.:* w
                                     S.:= (c S.:* d) S.:* w S.:+ ((S.:- c) S.:* e) S.:* w) AR.refl c (δ y x) (δ z x) (v ! x)) ⟩
    sum (λ x → (c * δ y x) * v ! x + ((- c) * δ z x) * v ! x)
      ≡⟨ ∑-distrib-+ (λ x → (c * δ y x) * v ! x) (λ x → ((- c) * δ z x) * v ! x) ⟩
    sum (λ x → (c * δ y x) * v ! x) + sum (λ x → ((- c) * δ z x) * v ! x)
      ≡⟨ cong₂ _+_ (sum-cδ c y v) (sum-cδ (- c) z v) ⟩
    c * v ! y + (- c) * v ! z
      ≡⟨ S.solve 3 (λ c y z → c S.:* y S.:+ (S.:- c) S.:* z S.:= c S.:* (y S.:+ S.:- z)) AR.refl c (v ! y) (v ! z) ⟩
    c * (v ! y - v ! z) ∎
    where open ≡-Reasoning

  sum-δ-row : (y : Fin n) (v : Vec A n) → sum (λ x → δ y x * v ! x) ≡ v ! y
  sum-δ-row y v = sum-δˡ (v !_) y

-- Case analysis on a decision without with-abstraction (which would
-- abstract the with-scrutinees inside coef in the goal as well).
byDec : {P Q : Set} → Dec P → (P → Q) → (¬ P → Q) → Q
byDec (yes p) f g = f p
byDec (no ¬p) f g = g ¬p

actV-row : (g : Gen n) (v : Vec A n) (r : Fin n) → actV g v ! r ≡ sum (λ x → coef g r x * v ! x)
actV-row {n} g v r = go g
  where
  Row : Gen n → Fin n → Set
  Row g r = actV g v ! r ≡ sum (λ x → coef g r x * v ! x)
  go : (g : Gen n) → Row g r
  go (X-gen a b p) =
    byDec (r FinP.≟ a)
      (λ r≡a → subst (Row (X-gen a b p)) (sym r≡a)
                 (trans (set₂-a a b (v ! b) (v ! a) v)
                        (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-X-a p x))) (sum-δ-row b v)))))
      (λ r≢a → byDec (r FinP.≟ b)
        (λ r≡b → subst (Row (X-gen a b p)) (sym r≡b)
                   (trans (set₂-b a b (v ! b) (v ! a) v (<⇒≢ p))
                          (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-X-b p x))) (sum-δ-row a v)))))
        (λ r≢b → trans (set₂-≢ a b (v ! b) (v ! a) v r≢a r≢b)
                       (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-X-≢ p r≢a r≢b x))) (sum-δ-row r v)))))
  go (K-gen a b p) =
    byDec (r FinP.≟ a)
      (λ r≡a → subst (Row (K-gen a b p)) (sym r≡a)
                 (trans (set₂-a a b (cg * (v ! a + v ! b)) (cg * (v ! a - v ! b)) v)
                        (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-K-a p x))) (sum-cδδ cg a b v)))))
      (λ r≢a → byDec (r FinP.≟ b)
        (λ r≡b → subst (Row (K-gen a b p)) (sym r≡b)
                   (trans (set₂-b a b (cg * (v ! a + v ! b)) (cg * (v ! a - v ! b)) v (<⇒≢ p))
                          (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-K-b p x))) (sum-cδ-δ cg a b v)))))
        (λ r≢b → trans (set₂-≢ a b (cg * (v ! a + v ! b)) (cg * (v ! a - v ! b)) v r≢a r≢b)
                       (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-K-≢ p r≢a r≢b x))) (sum-δ-row r v)))))
  go (i-gen a) =
    byDec (r FinP.≟ a)
      (λ r≡a → subst (Row (i-gen a)) (sym r≡a)
                 (trans (set₁-a a (ci * v ! a) v)
                        (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (trans (coef-i-a a x) (AR.*-comm (δ a x) ci))))
                                    (sum-cδ ci a v)))))
      (λ r≢a → trans (set₁-≢ a (ci * v ! a) v r≢a)
                     (sym (trans (sum-cong-≗ (λ x → cong (_* v ! x) (coef-i-≢ a r≢a x))) (sum-δ-row r v))))

------------------------------------------------------------------------
-- The matrix of a generator, and of a word

gmat : Gen n → Matrix n n A
gmat g = mk (coef g)

ent-gmat : (g : Gen n) (r c : Fin n) → ent (gmat g) r c ≡ coef g r c
ent-gmat g = ent-mk (coef g)

-- Acting by g is multiplying by its matrix.
actM≡ : (g : Gen n) (M : Matrix n m A) → actM g M ≡ gmat g ·*· M
actM≡ g M = mat-ext λ r c → begin
  ent (actM g M) r c                           ≡⟨ cong (_! r) (col-actM g M c) ⟩
  actV g (col M c) ! r                         ≡⟨ actV-row g (col M c) r ⟩
  sum (λ x → coef g r x * ent M x c)           ≡⟨ sum-cong-≗ (λ x → cong (_* ent M x c) (sym (ent-gmat g r x))) ⟩
  sum (λ x → ent (gmat g) r x * ent M x c)     ≡⟨ sym (ent-·*· (gmat g) M r c) ⟩
  ent (gmat g ·*· M) r c                       ∎
  where open ≡-Reasoning

-- The matrix of a word: its action on the identity.
⟦_⟧ᵐ : Word (Gen n) → Matrix n n A
⟦ w ⟧ᵐ = actMʷ w 𝕀

⟦g⟧ᵐ≡ : (g : Gen n) → ⟦ [ g ]ʷ ⟧ᵐ ≡ gmat g
⟦g⟧ᵐ≡ g = trans (actM≡ g 𝕀) (·*·-identityʳ (gmat g))

-- Acting by a word is multiplying by its matrix.
actMʷ≡ : (w : Word (Gen n)) (M : Matrix n m A) → actMʷ w M ≡ ⟦ w ⟧ᵐ ·*· M
actMʷ≡ [ g ]ʷ M = trans (actM≡ g M) (cong (_·*· M) (sym (⟦g⟧ᵐ≡ g)))
actMʷ≡ ε M = sym (·*·-identityˡ M)
actMʷ≡ (u • w) M = begin
  actMʷ u (actMʷ w M)            ≡⟨ actMʷ≡ u (actMʷ w M) ⟩
  ⟦ u ⟧ᵐ ·*· actMʷ w M           ≡⟨ cong (⟦ u ⟧ᵐ ·*·_) (actMʷ≡ w M) ⟩
  ⟦ u ⟧ᵐ ·*· (⟦ w ⟧ᵐ ·*· M)      ≡⟨ sym (·*·-assoc ⟦ u ⟧ᵐ ⟦ w ⟧ᵐ M) ⟩
  (⟦ u ⟧ᵐ ·*· ⟦ w ⟧ᵐ) ·*· M      ≡⟨ cong (_·*· M) (sym (actMʷ≡ u ⟦ w ⟧ᵐ)) ⟩
  ⟦ u • w ⟧ᵐ ·*· M               ∎
  where open ≡-Reasoning

⟦•⟧ᵐ : (u w : Word (Gen n)) → ⟦ u • w ⟧ᵐ ≡ ⟦ u ⟧ᵐ ·*· ⟦ w ⟧ᵐ
⟦•⟧ᵐ u w = actMʷ≡ u ⟦ w ⟧ᵐ

⟦ε⟧ᵐ : ⟦ ε ⟧ᵐ ≡ 𝕀 {n}
⟦ε⟧ᵐ = refl
