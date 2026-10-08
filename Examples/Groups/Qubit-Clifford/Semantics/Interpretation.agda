------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of Clifford circuits
--
-- The coefficients are any commutative ring A with an element s that
-- plays 1/√2, s s + s s = 1, and an element i with i i = −1.  ω is the
-- scalar s (1 + i), H is s [[1 , 1] , [1 , −1]], S = diag(1 , i) and
-- CZ = diag(1 , 1 , 1 , −1).  A gate on wire k of n wires is the gate
-- tensored with identities (emb, up), and a circuit is the product of
-- its gates.  The operators on bit vectors and their laws are those of
-- Real-Clifford, which are generic in the ring.
--
-- The relations are checked on matrices over the Gaussian integers, H
-- and ω being taken without their factor s: a circuit with h gates H or
-- ω is s^h times the image in A of its Gaussian matrix (bridge), so a
-- relation whose sides have h + 2j and h such gates holds as soon as
-- the Gaussian matrix of the left side is 2^j times that of the right,
-- which is computed (rel-sound).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Qubit-Clifford.Semantics.Interpretation
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  (i : A) (i² : i * i ≡ - 1#)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Nullary using (yes ; no ; does)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Examples.Groups.Real-Clifford.Semantics.Ops

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Semantics.Laws isCR public
open import Examples.Groups.Qubit-Clifford.Semantics.Gauss
open Image isCR i i² public
open ZS using (solve ; _:=_ ; _:+_ ; _:*_ ; con)

module GI = Examples.Groups.Real-Clifford.Semantics.Ops ℤi _+ᵍ_ _*ᵍ_ 0ᵍ 1ᵍ

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Scaling an operator

scale : A → Op n → Op n
scale c M x y = c * M x y

scale-cong : {c : A} {M N : Op n} → M ≐ N → scale c M ≐ scale c N
scale-cong e x y = Eq.cong (_ *_) (e x y)

private
  cross4 : (a b c d : A) → (a * b) * (c * d) ≡ (a * c) * (b * d)
  cross4 a b c d = begin
    (a * b) * (c * d)   ≡⟨ AR.*-assoc a b (c * d) ⟩
    a * (b * (c * d))   ≡⟨ Eq.cong (a *_) (Eq.sym (AR.*-assoc b c d)) ⟩
    a * ((b * c) * d)   ≡⟨ Eq.cong (λ x → a * (x * d)) (AR.*-comm b c) ⟩
    a * ((c * b) * d)   ≡⟨ Eq.cong (a *_) (AR.*-assoc c b d) ⟩
    a * (c * (b * d))   ≡⟨ Eq.sym (AR.*-assoc a c (b * d)) ⟩
    (a * c) * (b * d)   ∎
    where open Eq.≡-Reasoning

scale-⊙ : (a b : A) (M N : Op n) → (scale a M ⊙ scale b N) ≐ scale (a * b) (M ⊙ N)
scale-⊙ a b M N x y = begin
  Σb (λ z → (a * M x z) * (b * N z y))   ≡⟨ Σ-cong (λ z → cross4 a (M x z) b (N z y)) ⟩
  Σb (λ z → (a * b) * (M x z * N z y))   ≡⟨ Σ-scaleˡ (a * b) (λ z → M x z * N z y) ⟩
  (a * b) * Σb (λ z → M x z * N z y)     ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Gaussian operators, read in A

ιO : GI.Op n → Op n
ιO M x y = ιᵍ (M x y)

ι-Σ : (f : GI.Bits n → ℤi) → ιᵍ (GI.Σb f) ≡ Σb (λ z → ιᵍ (f z))
ι-Σ {zero}  f = Eq.refl
ι-Σ {suc n} f = Eq.trans (ιᵍ-+ (GI.Σb (λ bs → f (false ∷ bs))) (GI.Σb (λ bs → f (true ∷ bs))))
  (Eq.cong₂ _+_ (ι-Σ {n} (λ bs → f (false ∷ bs))) (ι-Σ {n} (λ bs → f (true ∷ bs))))

ιO-⊙ : (M N : GI.Op n) → ιO (M GI.⊙ N) ≐ (ιO M ⊙ ιO N)
ιO-⊙ M N x y = Eq.trans (ι-Σ (λ z → M x z *ᵍ N z y)) (Σ-cong (λ z → ιᵍ-* (M x z) (N z y)))

ιO-δ : ιO (GI.Idₒ {n}) ≐ Idₒ
ιO-δ []           []          = ιᵍ-1
ιO-δ (true ∷ x)  (true ∷ y)   = ιO-δ x y
ιO-δ (false ∷ x) (false ∷ y)  = ιO-δ x y
ιO-δ (true ∷ x)  (false ∷ y)  = ιᵍ-0
ιO-δ (false ∷ x) (true ∷ y)   = ιᵍ-0

ιO-tensor : {m : ℕ} (M : GI.Op m) (N : GI.Op n) → ιO (GI.tensor M N) ≐ tensor (ιO M) (ιO N)
ιO-tensor {m = zero}  M N x       y       = ιᵍ-* (M [] []) (N x y)
ιO-tensor {m = suc m} M N (a ∷ x) (b ∷ y) = ιO-tensor {m = m} (λ u v → M (a ∷ u) (b ∷ v)) N x y

ιO-scal : (c : ℤi) → ιO (GI.scal {n} c) ≐ scal (ιᵍ c)
ιO-scal {n} c x y = Eq.trans (ιᵍ-* c (GI.δb {n} x y)) (Eq.cong (ιᵍ c *_) (ιO-δ {n} x y))

------------------------------------------------------------------------
-- The gates

-- ω = s (1 + i).
ω̂ : A
ω̂ = s * (1# + i)

-- [[1 , 1] , [1 , −1]], diag(1 , i), diag(1 , 1 , 1 , −1), and 1 + i.
hG sG : GI.Mat 1
hG = GI.matOf λ { (true ∷ []) (true ∷ []) → -[1+ 0 ] +i + 0 ; _ _ → 1ᵍ }
sG = GI.matOf λ { (true ∷ []) (true ∷ []) → iᵍ ; (false ∷ []) (false ∷ []) → 1ᵍ ; _ _ → 0ᵍ }

czG : GI.Mat 2
czG = GI.matOf λ x y → czφ x *ᵍ GI.δb x y
  where
  czφ : GI.Bits 2 → ℤi
  czφ (true ∷ true ∷ []) = -[1+ 0 ] +i + 0
  czφ _                  = 1ᵍ

ωᵍ : ℤi
ωᵍ = + 1 +i + 1

valA : Gen n → Op n
valA (gate₀ ω-gate)  = scal ω̂
valA (gate₁ H-gate)  = emb (scale s (ιO (GI.ix hG)))
valA (gate₁ S-gate)  = emb (ιO (GI.ix sG))
valA (gate₂ CZ-gate) = emb (ιO (GI.ix czG))
valA (g ↥)           = up (valA g)

⟦_⟧ᴬ : Circuit n → Op n
⟦ [ g ]ʷ ⟧ᴬ = valA g
⟦ ε ⟧ᴬ      = Idₒ
⟦ w • v ⟧ᴬ  = ⟦ w ⟧ᴬ ⊙ ⟦ v ⟧ᴬ

-- The Gaussian matrices, as tries, and the number of gates H and ω.
valG : Gen k → GI.Mat k
valG (gate₀ ω-gate)  = GI.scalM ωᵍ
valG (gate₁ H-gate)  = GI.tenM hG GI.idM
valG (gate₁ S-gate)  = GI.tenM sG GI.idM
valG (gate₂ CZ-gate) = GI.tenM czG GI.idM
valG (g ↥)           = GI.tenM (GI.idM {1}) (valG g)

⟦_⟧ᴳ : Circuit k → GI.Mat k
⟦ [ g ]ʷ ⟧ᴳ = valG g
⟦ ε ⟧ᴳ      = GI.idM
⟦ w • v ⟧ᴳ  = GI.mulM ⟦ w ⟧ᴳ ⟦ v ⟧ᴳ

sg : Gen k → ℕ
sg (gate₀ ω-gate) = 1
sg (gate₁ H-gate) = 1
sg (g ↥)          = sg g
sg _              = 0

#s : Circuit k → ℕ
#s [ g ]ʷ  = sg g
#s ε       = 0
#s (w • v) = #s w +ℕ #s v

infixr 8 _^_
_^_ : A → ℕ → A
c ^ zero  = 1#
c ^ suc j = c * (c ^ j)

^-+ : (c : A) (a b : ℕ) → c ^ (a +ℕ b) ≡ (c ^ a) * (c ^ b)
^-+ c zero    b = Eq.sym (AR.*-identityˡ _)
^-+ c (suc a) b = Eq.trans (Eq.cong (c *_) (^-+ c a b)) (Eq.sym (AR.*-assoc c _ _))

------------------------------------------------------------------------
-- A circuit is s^h times its Gaussian matrix

private
  ixᴳ-id : (x y : GI.Bits k) → GI.ix (GI.idM {k}) x y ≡ GI.δb x y
  ixᴳ-id = GI.ix-matOf GI.Idₒ

  ιO-ix-ten : {l : ℕ} (M : GI.Mat k) (N : GI.Mat l) →
              ιO (GI.ix (GI.tenM M N)) ≐ tensor (ιO (GI.ix M)) (ιO (GI.ix N))
  ιO-ix-ten M N x y = Eq.trans (Eq.cong ιᵍ (GI.ix-matOf (GI.tensor (GI.ix M) (GI.ix N)) x y))
                               (ιO-tensor (GI.ix M) (GI.ix N) x y)

  ιO-ixᴳ-id : ιO (GI.ix (GI.idM {k})) ≐ Idₒ
  ιO-ixᴳ-id x y = Eq.trans (Eq.cong ιᵍ (ixᴳ-id x y)) (ιO-δ x y)

  -- A gate on the bottom wire, with its factor.
  bottom : {m : ℕ} (c : A) (M : GI.Mat 1) →
           emb {1} {m} (scale c (ιO (GI.ix M))) ≐ scale c (ιO (GI.ix (GI.tenM M (GI.idM {m}))))
  bottom c M x y = Eq.trans (tensor-scaleˡ c (ιO (GI.ix M)) Idₒ x y)
    (Eq.cong (c *_) (Eq.sym (Eq.trans (ιO-ix-ten M GI.idM x y)
                                      (tensor-cong (≐-refl (ιO (GI.ix M))) ιO-ixᴳ-id x y))))

  bottomₖ : {k m : ℕ} (M : GI.Mat k) →
            emb {k} {m} (ιO (GI.ix M)) ≐ scale 1# (ιO (GI.ix (GI.tenM M (GI.idM {m}))))
  bottomₖ M x y = Eq.trans (Eq.sym (AR.*-identityˡ _))
    (Eq.cong (1# *_) (Eq.sym (Eq.trans (ιO-ix-ten M GI.idM x y)
                                       (tensor-cong (≐-refl (ιO (GI.ix M))) ιO-ixᴳ-id x y))))

  -- ω is s times 1 + i.
  ω-s : (d : A) → ω̂ * d ≡ (s * 1#) * (ιᵍ ωᵍ * d)
  ω-s d = solve 3 (λ s i d → (s :* (con (+ 1) :+ i)) :* d := (s :* con (+ 1)) :* ((con (+ 1) :+ i :* con (+ 1)) :* d))
            Eq.refl s i d

bridge-gen : (g : Gen k) → valA g ≐ scale (s ^ sg g) (ιO (GI.ix (valG g)))
bridge-gen (gate₀ ω-gate) x y = Eq.trans (ω-s _)
  (Eq.cong ((s * 1#) *_) (Eq.sym (Eq.trans (Eq.cong ιᵍ (GI.ix-matOf (GI.scal ωᵍ) x y)) (ιO-scal ωᵍ x y))))
bridge-gen (gate₁ H-gate) x y = Eq.trans (bottom s hG x y)
  (Eq.cong (_* ιᵍ (GI.ix (GI.tenM hG GI.idM) x y)) (Eq.sym (AR.*-identityʳ s)))
bridge-gen (gate₁ S-gate) = bottomₖ sG
bridge-gen (gate₂ CZ-gate) = bottomₖ czG
bridge-gen (g ↥) x y = Eq.trans (tensor-cong (≐-refl Idₒ) (bridge-gen g) x y)
  (Eq.trans (tensor-scaleʳ (s ^ sg g) Idₒ (ιO (GI.ix (valG g))) x y)
    (Eq.cong ((s ^ sg g) *_) (Eq.sym (Eq.trans (ιO-ix-ten (GI.idM {1}) (valG g) x y)
                                                (tensor-cong {m = 1} ιO-ixᴳ-id (≐-refl (ιO (GI.ix (valG g)))) x y)))))

bridge : (w : Circuit k) → ⟦ w ⟧ᴬ ≐ scale (s ^ #s w) (ιO (GI.ix ⟦ w ⟧ᴳ))
bridge [ g ]ʷ  = bridge-gen g
bridge ε x y   = Eq.trans (Eq.sym (ιO-ixᴳ-id x y)) (Eq.sym (AR.*-identityˡ _))
bridge (w • v) = ≐-trans (⊙-cong (bridge w) (bridge v))
  (≐-trans (scale-⊙ (s ^ #s w) (s ^ #s v) _ _)
  (λ x y → Eq.cong₂ _*_ (Eq.sym (^-+ s (#s w) (#s v)))
    (Eq.sym (Eq.trans (Eq.cong ιᵍ (GI.ix-matOf (GI.ix ⟦ w ⟧ᴳ GI.⊙ GI.ix ⟦ v ⟧ᴳ) x y))
                      (ιO-⊙ (GI.ix ⟦ w ⟧ᴳ) (GI.ix ⟦ v ⟧ᴳ) x y)))))

------------------------------------------------------------------------
-- Checking a relation on Gaussian matrices

allBits : (k : ℕ) → (GI.Bits k → Bool) → Bool
allBits zero    p = p []
allBits (suc k) p = allBits k (λ x → p (false ∷ x)) ∧ allBits k (λ x → p (true ∷ x))

allBits-sound : (k : ℕ) (p : GI.Bits k → Bool) → allBits k p ≡ true → ∀ x → p x ≡ true
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

times2 : ℕ → ℤi → ℤi
times2 zero    x = x
times2 (suc j) x = dblᵍ (times2 j x)

check : (j : ℕ) → GI.Mat k → GI.Mat k → Bool
check {k} j L R = allBits k λ x → allBits k λ y → does (GI.ix L x y ≟ᵍ times2 j (GI.ix R x y))

check-sound : (j : ℕ) (L R : GI.Mat k) → check j L R ≡ true →
              ∀ x y → GI.ix L x y ≡ times2 j (GI.ix R x y)
check-sound {k} j L R e x y with GI.ix L x y ≟ᵍ times2 j (GI.ix R x y)
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

ι-times2 : (j : ℕ) (x : ℤi) → ιᵍ (times2 j x) ≡ (ι (+ 2) ^ j) * ιᵍ x
ι-times2 zero    x = Eq.sym (AR.*-identityˡ (ιᵍ x))
ι-times2 (suc j) x = Eq.trans (ιᵍ-dbl (times2 j x))
  (Eq.trans (Eq.cong (ι (+ 2) *_) (ι-times2 j x)) (Eq.sym (AR.*-assoc (ι (+ 2)) _ (ιᵍ x))))

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
  where open Eq.≡-Reasoning

-- A relation whose left side has 2j more gates H or ω, and whose
-- Gaussian matrix is 2^j times the right one.
rel-sound : (l r : Circuit k) (j : ℕ) → #s l ≡ #s r +ℕ dbl j →
            check j ⟦ l ⟧ᴳ ⟦ r ⟧ᴳ ≡ true → ⟦ l ⟧ᴬ ≐ ⟦ r ⟧ᴬ
rel-sound l r j eh ec x y = begin
  ⟦ l ⟧ᴬ x y                                              ≡⟨ bridge l x y ⟩
  (s ^ #s l) * ιᵍ (GI.ix ⟦ l ⟧ᴳ x y)                     ≡⟨ Eq.cong₂ (λ h v → (s ^ h) * ιᵍ v) eh (check-sound j _ _ ec x y) ⟩
  (s ^ (#s r +ℕ dbl j)) * ιᵍ (times2 j (GI.ix ⟦ r ⟧ᴳ x y)) ≡⟨ Eq.cong₂ _*_ (^-+ s (#s r) (dbl j)) (ι-times2 j _) ⟩
  ((s ^ #s r) * (s ^ dbl j)) * ((ι (+ 2) ^ j) * ιᵍ (GI.ix ⟦ r ⟧ᴳ x y))
    ≡⟨ regroup (s ^ #s r) (s ^ dbl j) (ι (+ 2) ^ j) (ιᵍ (GI.ix ⟦ r ⟧ᴳ x y)) ⟩
  (s ^ #s r) * (((s ^ dbl j) * (ι (+ 2) ^ j)) * ιᵍ (GI.ix ⟦ r ⟧ᴳ x y))
    ≡⟨ Eq.cong (λ c → (s ^ #s r) * (c * ιᵍ (GI.ix ⟦ r ⟧ᴳ x y))) (s-dbl j) ⟩
  (s ^ #s r) * (1# * ιᵍ (GI.ix ⟦ r ⟧ᴳ x y))                ≡⟨ Eq.cong ((s ^ #s r) *_) (AR.*-identityˡ _) ⟩
  (s ^ #s r) * ιᵍ (GI.ix ⟦ r ⟧ᴳ x y)                       ≡⟨ Eq.sym (bridge r x y) ⟩
  ⟦ r ⟧ᴬ x y                                               ∎
  where
  open Eq.≡-Reasoning
  regroup : (a b c d : A) → (a * b) * (c * d) ≡ a * ((b * c) * d)
  regroup a b c d = Eq.trans (AR.*-assoc a b (c * d)) (Eq.cong (a *_) (Eq.sym (AR.*-assoc b c d)))

------------------------------------------------------------------------
-- A circuit at width k, read at width k + n

localise-gen : (g : Gen k) → valA (g ↧ᵏ n) ≐ emb {k} {n} (valA g)
localise-gen {k} {n} (gate₀ ω-gate) = scal-emb {k} {n} ω̂
localise-gen (gate₁ H-gate)  = emb-pad₁ _
localise-gen (gate₁ S-gate)  = emb-pad₁ _
localise-gen (gate₂ CZ-gate) = emb-pad₂ _
localise-gen (g ↥) = ≐-trans (up-cong (localise-gen g)) (up-emb (valA g))

localise : (w : Circuit k) → ⟦ w ↓ᵏ n ⟧ᴬ ≐ emb {k} {n} ⟦ w ⟧ᴬ
localise [ g ]ʷ    = localise-gen g
localise {k} {n} ε = ≐-sym (emb-id {k} {n})
localise (w • v)   = ≐-trans (⊙-cong (localise w) (localise v)) (emb-⊙ ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ)

-- A relation checked at width k holds at every width k + n.
rel-sound↓ : (l r : Circuit k) (j : ℕ) → #s l ≡ #s r +ℕ dbl j →
             check j ⟦ l ⟧ᴳ ⟦ r ⟧ᴳ ≡ true → ⟦ l ↓ᵏ n ⟧ᴬ ≐ ⟦ r ↓ᵏ n ⟧ᴬ
rel-sound↓ l r j eh ec = ≐-trans (localise l) (≐-trans (emb-cong (rel-sound l r j eh ec)) (≐-sym (localise r)))

-- The same, for sides the caller spells at width k + n: they are
-- compared as circuits.  (Unifying ⟦ l ↓ᵏ n ⟧ᴬ with ⟦ w ⟧ᴬ directly
-- unfolds both operators, which takes exponential time.)
rel-sound≡ : (l r : Circuit k) (j : ℕ) {w v : Circuit (k +ℕ n)} →
             l ↓ᵏ n ≡ w → r ↓ᵏ n ≡ v → #s l ≡ #s r +ℕ dbl j →
             check j ⟦ l ⟧ᴳ ⟦ r ⟧ᴳ ≡ true → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ
rel-sound≡ l r j Eq.refl Eq.refl = rel-sound↓ l r j
