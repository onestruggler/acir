------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of real Clifford circuits, and its soundness
--
-- The coefficients are any commutative ring A with an element s that
-- plays 1/√2: s s + s s = 1.  H is s [[1 , 1] , [1 , −1]], Z and CZ
-- are diagonal with entries ±1, and −1 is the scalar.  A gate on wire
-- k of n wires is the gate tensored with identities (emb, up), and a
-- circuit is the product of its gates.
--
-- The relations are checked on integer matrices, H being taken without
-- its factor s: a circuit with h gates H is s^h times the image in A of
-- its integer matrix (⟦⟧-ℤ), so a relation whose sides have h + 2j and
-- h gates H holds as soon as the integer matrix of the left side is 2^j
-- times that of the right, which is computed (srel-sound).  The
-- structural rules are the tensor calculus of Semantics.Laws.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Real-Clifford.Semantics.Interpretation
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_ ; _^_ to _^ℕ_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
import Data.Integer.Properties as ℤP
open import Relation.Nullary using (yes ; no ; does)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Quantum.Synthesis.Ring.Properties.Common as Common
import Examples.Groups.Real-Clifford.Semantics.Ops

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Semantics.Laws isCR

module ZS = Common.ZSolver R
module ZI = Examples.Groups.Real-Clifford.Semantics.Ops ℤ ℤ._+_ ℤ._*_ (+ 0) (+ 1)

ι : ℤ → A
ι = ZS.⟦_⟧ℤ

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Scaling an operator

scale : A → Op n → Op n
scale c M x y = c * M x y

scale-cong : {c : A} {M N : Op n} → M ≐ N → scale c M ≐ scale c N
scale-cong e x y = Eq.cong (_ *_) (e x y)

scale-⊙ : (a b : A) (M N : Op n) → (scale a M ⊙ scale b N) ≐ scale (a * b) (M ⊙ N)
scale-⊙ a b M N x y = begin
  Σb (λ z → (a * M x z) * (b * N z y))   ≡⟨ Σ-cong (λ z → swap4 a (M x z) b (N z y)) ⟩
  Σb (λ z → (a * b) * (M x z * N z y))   ≡⟨ Σ-scaleˡ (a * b) (λ z → M x z * N z y) ⟩
  (a * b) * Σb (λ z → M x z * N z y)     ∎
  where
  open Eq.≡-Reasoning
  swap4 : (a b c d : A) → (a * b) * (c * d) ≡ (a * c) * (b * d)
  swap4 a b c d = begin
    (a * b) * (c * d)   ≡⟨ AR.*-assoc a b (c * d) ⟩
    a * (b * (c * d))   ≡⟨ Eq.cong (a *_) (Eq.sym (AR.*-assoc b c d)) ⟩
    a * ((b * c) * d)   ≡⟨ Eq.cong (λ x → a * (x * d)) (AR.*-comm b c) ⟩
    a * ((c * b) * d)   ≡⟨ Eq.cong (a *_) (AR.*-assoc c b d) ⟩
    a * (c * (b * d))   ≡⟨ Eq.sym (AR.*-assoc a c (b * d)) ⟩
    (a * c) * (b * d)   ∎

scale-1 : (M : Op n) → scale 1# M ≐ M
scale-1 M x y = AR.*-identityˡ (M x y)

------------------------------------------------------------------------
-- Integer operators, read in A

ιO : ZI.Op n → Op n
ιO M x y = ι (M x y)

ι-Σ : (f : ZI.Bits n → ℤ) → ι (ZI.Σb f) ≡ Σb (λ z → ι (f z))
ι-Σ {zero}  f = Eq.refl
ι-Σ {suc n} f = Eq.trans (ZS.+-homoℤ (ZI.Σb (λ bs → f (false ∷ bs))) (ZI.Σb (λ bs → f (true ∷ bs))))
  (Eq.cong₂ _+_ (ι-Σ {n} (λ bs → f (false ∷ bs))) (ι-Σ {n} (λ bs → f (true ∷ bs))))

ιO-⊙ : (M N : ZI.Op n) → ιO (M ZI.⊙ N) ≐ (ιO M ⊙ ιO N)
ιO-⊙ M N x y = Eq.trans (ι-Σ (λ z → M x z ℤ.* N z y)) (Σ-cong (λ z → ZS.*-homoℤ (M x z) (N z y)))

ιO-δ : ιO (ZI.Idₒ {n}) ≐ Idₒ
ιO-δ []           []           = Eq.refl
ιO-δ (true ∷ x)  (true ∷ y)    = ιO-δ x y
ιO-δ (false ∷ x) (false ∷ y)   = ιO-δ x y
ιO-δ (true ∷ x)  (false ∷ y)   = Eq.refl
ιO-δ (false ∷ x) (true ∷ y)    = Eq.refl

ιO-tensor : {m : ℕ} (M : ZI.Op m) (N : ZI.Op n) → ιO (ZI.tensor M N) ≐ tensor (ιO M) (ιO N)
ιO-tensor {m = zero}  M N x       y       = ZS.*-homoℤ (M [] []) (N x y)
ιO-tensor {m = suc m} M N (a ∷ x) (b ∷ y) = ιO-tensor {m = m} (λ u v → M (a ∷ u) (b ∷ v)) N x y

ιO-scal : (c : ℤ) → ιO (ZI.scal {n} c) ≐ scal (ι c)
ιO-scal {n} c x y = Eq.trans (ZS.*-homoℤ c (ZI.δb {n} x y)) (Eq.cong (ι c *_) (ιO-δ {n} x y))

------------------------------------------------------------------------
-- The gates

-- [[1 , 1] , [1 , −1]], diag(1 , −1), diag(1 , 1 , 1 , −1).
hZ zZ : ZI.Mat 1
hZ = ZI.matOf λ { (true ∷ []) (true ∷ []) → -[1+ 0 ] ; _ _ → + 1 }
zZ = ZI.matOf λ { (true ∷ []) (true ∷ []) → -[1+ 0 ] ; (false ∷ []) (false ∷ []) → + 1 ; _ _ → + 0 }

czZ : ZI.Mat 2
czZ = ZI.matOf λ x y → czφ x ℤ.* ZI.δb x y
  where
  czφ : ZI.Bits 2 → ℤ
  czφ (true ∷ true ∷ []) = -[1+ 0 ]
  czφ _                  = + 1

valA : Gen n → Op n
valA (gate₀ neg-gate) = scal (- 1#)
valA (gate₁ H-gate)   = emb (scale s (ιO (ZI.ix hZ)))
valA (gate₁ Z-gate)   = emb (ιO (ZI.ix zZ))
valA (gate₂ CZ-gate)  = emb (ιO (ZI.ix czZ))
valA (g ↥)            = up (valA g)

⟦_⟧ᴬ : Circuit n → Op n
⟦ [ g ]ʷ ⟧ᴬ = valA g
⟦ ε ⟧ᴬ      = Idₒ
⟦ w • v ⟧ᴬ  = ⟦ w ⟧ᴬ ⊙ ⟦ v ⟧ᴬ

-- The integer matrices, as tries, and the number of H gates.
valZ : Gen k → ZI.Mat k
valZ (gate₀ neg-gate) = ZI.scalM -[1+ 0 ]
valZ (gate₁ H-gate)   = ZI.tenM hZ ZI.idM
valZ (gate₁ Z-gate)   = ZI.tenM zZ ZI.idM
valZ (gate₂ CZ-gate)  = ZI.tenM czZ ZI.idM
valZ (g ↥)            = ZI.tenM (ZI.idM {1}) (valZ g)

⟦_⟧ᶻ : Circuit k → ZI.Mat k
⟦ [ g ]ʷ ⟧ᶻ = valZ g
⟦ ε ⟧ᶻ      = ZI.idM
⟦ w • v ⟧ᶻ  = ZI.mulM ⟦ w ⟧ᶻ ⟦ v ⟧ᶻ

hg : Gen k → ℕ
hg (gate₁ H-gate) = 1
hg (g ↥)          = hg g
hg _              = 0

#H : Circuit k → ℕ
#H [ g ]ʷ  = hg g
#H ε       = 0
#H (w • v) = #H w +ℕ #H v

infixr 8 _^_
_^_ : A → ℕ → A
c ^ zero  = 1#
c ^ suc j = c * (c ^ j)

^-+ : (c : A) (a b : ℕ) → c ^ (a +ℕ b) ≡ (c ^ a) * (c ^ b)
^-+ c zero    b = Eq.sym (AR.*-identityˡ _)
^-+ c (suc a) b = Eq.trans (Eq.cong (c *_) (^-+ c a b)) (Eq.sym (AR.*-assoc c _ _))

------------------------------------------------------------------------
-- A circuit is s^h times its integer matrix

private
  ixᶻ-id : (x y : ZI.Bits k) → ZI.ix (ZI.idM {k}) x y ≡ ZI.δb x y
  ixᶻ-id = ZI.ix-matOf ZI.Idₒ

  ιO-ix-ten : {l : ℕ} (M : ZI.Mat k) (N : ZI.Mat l) →
              ιO (ZI.ix (ZI.tenM M N)) ≐ tensor (ιO (ZI.ix M)) (ιO (ZI.ix N))
  ιO-ix-ten M N x y = Eq.trans (Eq.cong ι (ZI.ix-matOf (ZI.tensor (ZI.ix M) (ZI.ix N)) x y))
                               (ιO-tensor (ZI.ix M) (ZI.ix N) x y)

  ιO-ixᶻ-id : ιO (ZI.ix (ZI.idM {k})) ≐ Idₒ
  ιO-ixᶻ-id x y = Eq.trans (Eq.cong ι (ixᶻ-id x y)) (ιO-δ x y)

  -- A gate on the bottom wire, with its factor.
  bottom : {m : ℕ} (c : A) (M : ZI.Mat 1) →
           emb {1} {m} (scale c (ιO (ZI.ix M))) ≐ scale c (ιO (ZI.ix (ZI.tenM M (ZI.idM {m}))))
  bottom c M x y = Eq.trans (tensor-scaleˡ c (ιO (ZI.ix M)) Idₒ x y)
    (Eq.cong (c *_) (Eq.sym (Eq.trans (ιO-ix-ten M ZI.idM x y)
                                      (tensor-cong (≐-refl (ιO (ZI.ix M))) ιO-ixᶻ-id x y))))

  bottomₖ : {k m : ℕ} (M : ZI.Mat k) →
            emb {k} {m} (ιO (ZI.ix M)) ≐ scale 1# (ιO (ZI.ix (ZI.tenM M (ZI.idM {m}))))
  bottomₖ M x y = Eq.trans (Eq.sym (AR.*-identityˡ _))
    (Eq.cong (1# *_) (Eq.sym (Eq.trans (ιO-ix-ten M ZI.idM x y)
                                       (tensor-cong (≐-refl (ιO (ZI.ix M))) ιO-ixᶻ-id x y))))

bridge-gen : (g : Gen k) → valA g ≐ scale (s ^ hg g) (ιO (ZI.ix (valZ g)))
bridge-gen (gate₀ neg-gate) x y = Eq.trans
  (Eq.sym (Eq.trans (Eq.cong ι (ZI.ix-matOf (ZI.scal -[1+ 0 ]) x y)) (ιO-scal -[1+ 0 ] x y)))
  (Eq.sym (AR.*-identityˡ _))
bridge-gen (gate₁ H-gate) x y = Eq.trans (bottom s hZ x y)
  (Eq.cong (_* ι (ZI.ix (ZI.tenM hZ ZI.idM) x y)) (Eq.sym (AR.*-identityʳ s)))
bridge-gen (gate₁ Z-gate) = bottomₖ zZ
bridge-gen (gate₂ CZ-gate) = bottomₖ czZ
bridge-gen (g ↥) x y = Eq.trans (tensor-cong (≐-refl Idₒ) (bridge-gen g) x y)
  (Eq.trans (tensor-scaleʳ (s ^ hg g) Idₒ (ιO (ZI.ix (valZ g))) x y)
    (Eq.cong ((s ^ hg g) *_) (Eq.sym (Eq.trans (ιO-ix-ten (ZI.idM {1}) (valZ g) x y)
                                                (tensor-cong {m = 1} ιO-ixᶻ-id (≐-refl (ιO (ZI.ix (valZ g)))) x y)))))

bridge : (w : Circuit k) → ⟦ w ⟧ᴬ ≐ scale (s ^ #H w) (ιO (ZI.ix ⟦ w ⟧ᶻ))
bridge [ g ]ʷ  = bridge-gen g
bridge ε x y   = Eq.trans (Eq.sym (ιO-ixᶻ-id x y)) (Eq.sym (AR.*-identityˡ _))
bridge (w • v) = ≐-trans (⊙-cong (bridge w) (bridge v))
  (≐-trans (scale-⊙ (s ^ #H w) (s ^ #H v) _ _)
  (λ x y → Eq.cong₂ _*_ (Eq.sym (^-+ s (#H w) (#H v)))
    (Eq.sym (Eq.trans (Eq.cong ι (ZI.ix-matOf (ZI.ix ⟦ w ⟧ᶻ ZI.⊙ ZI.ix ⟦ v ⟧ᶻ) x y))
                      (ιO-⊙ (ZI.ix ⟦ w ⟧ᶻ) (ZI.ix ⟦ v ⟧ᶻ) x y)))))

------------------------------------------------------------------------
-- Checking a relation on integer matrices

allBits : (k : ℕ) → (ZI.Bits k → Bool) → Bool
allBits zero    p = p []
allBits (suc k) p = allBits k (λ x → p (false ∷ x)) ∧ allBits k (λ x → p (true ∷ x))

allBits-sound : (k : ℕ) (p : ZI.Bits k → Bool) → allBits k p ≡ true → ∀ x → p x ≡ true
allBits-sound zero    p e []           = e
allBits-sound (suc k) p e (false ∷ x) = allBits-sound k _ (∧-l e) x
  where
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = Eq.refl
allBits-sound (suc k) p e (true ∷ x)  = allBits-sound k _ (∧-r {allBits k (λ x → p (false ∷ x))} e) x
  where
  ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-r {true} e = e

-- Doubling j times.
dbl : ℕ → ℕ
dbl zero    = zero
dbl (suc j) = suc (suc (dbl j))

times2 : ℕ → ℤ → ℤ
times2 zero    x = x
times2 (suc j) x = + 2 ℤ.* times2 j x

ℤ-eq : ℤ → ℤ → Bool
ℤ-eq a b = does (a ℤP.≟ b)

check : (j : ℕ) → ZI.Mat k → ZI.Mat k → Bool
check {k} j L R = allBits k λ x → allBits k λ y → ℤ-eq (ZI.ix L x y) (times2 j (ZI.ix R x y))

check-sound : (j : ℕ) (L R : ZI.Mat k) → check j L R ≡ true →
              ∀ x y → ZI.ix L x y ≡ times2 j (ZI.ix R x y)
check-sound {k} j L R e x y with ZI.ix L x y ℤP.≟ times2 j (ZI.ix R x y)
    | allBits-sound k _ (allBits-sound k _ e x) y
... | yes p | _  = p
... | no _  | ()

-- s² 2 = 1, hence s^{2j} 2^j = 1.
s²2 : (s * s) * ι (+ 2) ≡ 1#
s²2 = Eq.trans (Eq.cong ((s * s) *_) two) (Eq.trans (AR.distribˡ (s * s) 1# 1#)
        (Eq.trans (Eq.cong₂ _+_ (AR.*-identityʳ _) (AR.*-identityʳ _)) s-half))
  where
  two : ι (+ 2) ≡ 1# + 1#
  two = ZS.+-homoℤ (+ 1) (+ 1)

ι-times2 : (j : ℕ) (x : ℤ) → ι (times2 j x) ≡ (ι (+ 2) ^ j) * ι x
ι-times2 zero    x = Eq.sym (AR.*-identityˡ (ι x))
ι-times2 (suc j) x = Eq.trans (ZS.*-homoℤ (+ 2) (times2 j x))
  (Eq.trans (Eq.cong (ι (+ 2) *_) (ι-times2 j x)) (Eq.sym (AR.*-assoc (ι (+ 2)) _ (ι x))))

s-dbl : (j : ℕ) → (s ^ dbl j) * (ι (+ 2) ^ j) ≡ 1#
s-dbl zero    = AR.*-identityˡ 1#
s-dbl (suc j) = begin
  (s * (s * (s ^ dbl j))) * (ι (+ 2) * (ι (+ 2) ^ j))
    ≡⟨ Eq.cong (_* (ι (+ 2) * (ι (+ 2) ^ j))) (Eq.sym (AR.*-assoc s s (s ^ dbl j))) ⟩
  ((s * s) * (s ^ dbl j)) * (ι (+ 2) * (ι (+ 2) ^ j))
    ≡⟨ cross4 (s * s) (s ^ dbl j) (ι (+ 2)) (ι (+ 2) ^ j) ⟩
  ((s * s) * ι (+ 2)) * ((s ^ dbl j) * (ι (+ 2) ^ j))
    ≡⟨ Eq.cong₂ _*_ s²2 (s-dbl j) ⟩
  1# * 1#
    ≡⟨ AR.*-identityˡ 1# ⟩
  1# ∎
  where
  open Eq.≡-Reasoning
  cross4 : (a b c d : A) → (a * b) * (c * d) ≡ (a * c) * (b * d)
  cross4 a b c d = begin
    (a * b) * (c * d)   ≡⟨ AR.*-assoc a b (c * d) ⟩
    a * (b * (c * d))   ≡⟨ Eq.cong (a *_) (Eq.sym (AR.*-assoc b c d)) ⟩
    a * ((b * c) * d)   ≡⟨ Eq.cong (λ x → a * (x * d)) (AR.*-comm b c) ⟩
    a * ((c * b) * d)   ≡⟨ Eq.cong (a *_) (AR.*-assoc c b d) ⟩
    a * (c * (b * d))   ≡⟨ Eq.sym (AR.*-assoc a c (b * d)) ⟩
    (a * c) * (b * d)   ∎

-- A relation whose left side has 2j more gates H, and whose integer
-- matrix is 2^j times the right one.
rel-sound : (l r : Circuit k) (j : ℕ) → #H l ≡ #H r +ℕ dbl j →
            check j ⟦ l ⟧ᶻ ⟦ r ⟧ᶻ ≡ true → ⟦ l ⟧ᴬ ≐ ⟦ r ⟧ᴬ
rel-sound l r j eh ec x y = begin
  ⟦ l ⟧ᴬ x y                                              ≡⟨ bridge l x y ⟩
  (s ^ #H l) * ι (ZI.ix ⟦ l ⟧ᶻ x y)                      ≡⟨ Eq.cong₂ (λ h v → (s ^ h) * ι v) eh (check-sound j _ _ ec x y) ⟩
  (s ^ (#H r +ℕ dbl j)) * ι (times2 j (ZI.ix ⟦ r ⟧ᶻ x y)) ≡⟨ Eq.cong₂ _*_ (^-+ s (#H r) (dbl j)) (ι-times2 j _) ⟩
  ((s ^ #H r) * (s ^ dbl j)) * ((ι (+ 2) ^ j) * ι (ZI.ix ⟦ r ⟧ᶻ x y))
    ≡⟨ regroup (s ^ #H r) (s ^ dbl j) (ι (+ 2) ^ j) (ι (ZI.ix ⟦ r ⟧ᶻ x y)) ⟩
  (s ^ #H r) * (((s ^ dbl j) * (ι (+ 2) ^ j)) * ι (ZI.ix ⟦ r ⟧ᶻ x y))
    ≡⟨ Eq.cong (λ c → (s ^ #H r) * (c * ι (ZI.ix ⟦ r ⟧ᶻ x y))) (s-dbl j) ⟩
  (s ^ #H r) * (1# * ι (ZI.ix ⟦ r ⟧ᶻ x y))                ≡⟨ Eq.cong ((s ^ #H r) *_) (AR.*-identityˡ _) ⟩
  (s ^ #H r) * ι (ZI.ix ⟦ r ⟧ᶻ x y)                       ≡⟨ Eq.sym (bridge r x y) ⟩
  ⟦ r ⟧ᴬ x y                                               ∎
  where
  open Eq.≡-Reasoning
  regroup : (a b c d : A) → (a * b) * (c * d) ≡ a * ((b * c) * d)
  regroup a b c d = Eq.trans (AR.*-assoc a b (c * d)) (Eq.cong (a *_) (Eq.sym (AR.*-assoc b c d)))

------------------------------------------------------------------------
-- A circuit at width k, read at width k + n

localise-gen : (g : Gen k) → valA (g ↧ᵏ n) ≐ emb {k} {n} (valA g)
localise-gen {k} {n} (gate₀ neg-gate) = scal-emb {k} {n} (- 1#)
localise-gen (gate₁ H-gate)  = emb-pad₁ _
localise-gen (gate₁ Z-gate)  = emb-pad₁ _
localise-gen (gate₂ CZ-gate) = emb-pad₂ _
localise-gen (g ↥) = ≐-trans (up-cong (localise-gen g)) (up-emb (valA g))

localise : (w : Circuit k) → ⟦ w ↓ᵏ n ⟧ᴬ ≐ emb {k} {n} ⟦ w ⟧ᴬ
localise [ g ]ʷ    = localise-gen g
localise {k} {n} ε = ≐-sym (emb-id {k} {n})
localise (w • v)   = ≐-trans (⊙-cong (localise w) (localise v)) (emb-⊙ ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ)

-- A relation checked at width k holds at every width k + n.
rel-sound↓ : (l r : Circuit k) (j : ℕ) → #H l ≡ #H r +ℕ dbl j →
             check j ⟦ l ⟧ᶻ ⟦ r ⟧ᶻ ≡ true → ⟦ l ↓ᵏ n ⟧ᴬ ≐ ⟦ r ↓ᵏ n ⟧ᴬ
rel-sound↓ l r j eh ec = ≐-trans (localise l) (≐-trans (emb-cong (rel-sound l r j eh ec)) (≐-sym (localise r)))

-- The same, for sides the caller spells at width k + n: they are
-- compared as circuits.  (Unifying ⟦ l ↓ᵏ n ⟧ᴬ with ⟦ w ⟧ᴬ directly
-- unfolds both operators, which takes exponential time.)
rel-sound≡ : (l r : Circuit k) (j : ℕ) {w v : Circuit (k +ℕ n)} →
             l ↓ᵏ n ≡ w → r ↓ᵏ n ≡ v → #H l ≡ #H r +ℕ dbl j →
             check j ⟦ l ⟧ᶻ ⟦ r ⟧ᶻ ≡ true → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ
rel-sound≡ l r j Eq.refl Eq.refl = rel-sound↓ l r j
