------------------------------------------------------------------------
-- Presentations of groups
--
-- Pauli operators as matrices, and the action of circuits on them
--
-- The matrix of ±X^a Z^b ⊗ … is ± the Kronecker product of the 2 × 2
-- matrices X^a Z^b, whose entry in row x of column y is (−1)^(y b) if
-- x = y + a and 0 otherwise (pmat).  A circuit w conjugates them as
-- Pauli.act says: ⟦ w ⟧ P = (act w P) ⟦ w ⟧ (pmat-act).  For a gate
-- this is an identity of 2 × 2 or 4 × 4 integer matrices, checked by
-- evaluation (H-loc, Z-loc, CZ-loc), which the tensor calculus carries
-- to every wire.
--
-- Over a nontrivial ring the matrix determines the Pauli operator
-- (pmat-injective): column y has a single nonzero entry, in row y + a,
-- and it is (−1)^(σ + y · b), so it tells a, then σ and b; 1 ≠ −1
-- because 2 s² = 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Real-Clifford.Semantics.PauliMatrix
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _xor_ ; if_then_else_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail ; replicate)
open import Data.Vec.Properties using (≡-dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_ ; refl)
open import Relation.Nullary using (yes ; no)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Pauli using (Letter ; Pauli ; actL ; act ; actL-sign)
open import Examples.Groups.Real-Clifford.Semantics.Laws isCR
open import Examples.Groups.Real-Clifford.Semantics.Interpretation isCR s s-half hiding (_^_)

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- Pauli matrices

sgnℤ : Bool → ℤ
sgnℤ false = + 1
sgnℤ true  = -[1+ 0 ]

sg : Bool → A
sg σ = ι (sgnℤ σ)

-- X^a Z^b, with integer entries.
lZ : Letter → ZI.Op 1
lZ (a , b) (x ∷ []) (y ∷ []) = if x xor (y xor a) then + 0 else sgnℤ (y ∧ b)

pv : Vec Letter n → Op n
pv []       = Idₒ
pv (p ∷ ps) = tensor {1} (ιO (lZ p)) (pv ps)

pmat : Pauli n → Op n
pmat P = scale (sg (proj₁ P)) (pv (proj₂ P))

------------------------------------------------------------------------
-- Scalars and signs

scale-⊙ˡ : (a : A) (M N : Op n) → (scale a M ⊙ N) ≐ scale a (M ⊙ N)
scale-⊙ˡ a M N x y =
  Eq.trans (Σ-cong (λ z → AR.*-assoc a (M x z) (N z y))) (Σ-scaleˡ a (λ z → M x z * N z y))

scale-⊙ʳ : (a : A) (M N : Op n) → (M ⊙ scale a N) ≐ scale a (M ⊙ N)
scale-⊙ʳ a M N x y =
  Eq.trans (Σ-cong (λ z → swap (M x z) (N z y))) (Σ-scaleˡ a (λ z → M x z * N z y))
  where
  swap : (b c : A) → b * (a * c) ≡ a * (b * c)
  swap b c = Eq.trans (Eq.sym (AR.*-assoc b a c))
    (Eq.trans (Eq.cong (_* c) (AR.*-comm b a)) (AR.*-assoc a b c))

sgnℤ-xor : (σ τ : Bool) → sgnℤ (σ xor τ) ≡ sgnℤ σ ℤ.* sgnℤ τ
sgnℤ-xor false false = refl
sgnℤ-xor false true  = refl
sgnℤ-xor true  false = refl
sgnℤ-xor true  true  = refl

sg-xor : (σ τ : Bool) → sg (σ xor τ) ≡ sg σ * sg τ
sg-xor σ τ = Eq.trans (Eq.cong ι (sgnℤ-xor σ τ)) (ZS.*-homoℤ (sgnℤ σ) (sgnℤ τ))

------------------------------------------------------------------------
-- The gates, on one or two wires

-- G P = c P' G, at every entry, checked by evaluation.
private
  ℤ-eq-sound : {a b : ℤ} → ℤ-eq a b ≡ true → a ≡ b
  ℤ-eq-sound {a} {b} e with a ℤP.≟ b | e
  ... | yes p | _  = p
  ... | no _  | ()

loc? : ZI.Op k → ZI.Op k → ZI.Op k → ℤ → Bool
loc? {k} G P P' c = allBits k λ x → allBits k λ y → ℤ-eq ((G ZI.⊙ P) x y) (c ℤ.* (P' ZI.⊙ G) x y)

loc-sound : (G P P' : ZI.Op k) (c : ℤ) → loc? G P P' c ≡ true →
            ∀ x y → (G ZI.⊙ P) x y ≡ c ℤ.* (P' ZI.⊙ G) x y
loc-sound {k} G P P' c e x y = ℤ-eq-sound (allBits-sound k _ (allBits-sound k _ e x) y)

H? Z? : ZI.Bits 2 → Bool
H? (a ∷ b ∷ []) = loc? (ZI.ix hZ) (lZ (a , b)) (lZ (b , a)) (sgnℤ (a ∧ b))
Z? (a ∷ b ∷ []) = loc? (ZI.ix zZ) (lZ (a , b)) (lZ (a , b)) (sgnℤ a)

CZ? : ZI.Bits 4 → Bool
CZ? (a ∷ b ∷ c ∷ d ∷ []) =
  loc? (ZI.ix czZ) (ZI.tensor (lZ (a , b)) (lZ (c , d)))
       (ZI.tensor (lZ (a , b xor c)) (lZ (c , d xor a))) (sgnℤ (a ∧ c))

H-loc : (a b : Bool) → ∀ x y →
        (ZI.ix hZ ZI.⊙ lZ (a , b)) x y ≡ sgnℤ (a ∧ b) ℤ.* (lZ (b , a) ZI.⊙ ZI.ix hZ) x y
H-loc a b = loc-sound (ZI.ix hZ) (lZ (a , b)) (lZ (b , a)) (sgnℤ (a ∧ b))
  (allBits-sound 2 H? refl (a ∷ b ∷ []))

Z-loc : (a b : Bool) → ∀ x y →
        (ZI.ix zZ ZI.⊙ lZ (a , b)) x y ≡ sgnℤ a ℤ.* (lZ (a , b) ZI.⊙ ZI.ix zZ) x y
Z-loc a b = loc-sound (ZI.ix zZ) (lZ (a , b)) (lZ (a , b)) (sgnℤ a)
  (allBits-sound 2 Z? refl (a ∷ b ∷ []))

CZ-loc : (a b c d : Bool) → ∀ x y →
         (ZI.ix czZ ZI.⊙ ZI.tensor (lZ (a , b)) (lZ (c , d))) x y ≡
         sgnℤ (a ∧ c) ℤ.* (ZI.tensor (lZ (a , b xor c)) (lZ (c , d xor a)) ZI.⊙ ZI.ix czZ) x y
CZ-loc a b c d = loc-sound (ZI.ix czZ) (ZI.tensor (lZ (a , b)) (lZ (c , d)))
  (ZI.tensor (lZ (a , b xor c)) (lZ (c , d xor a))) (sgnℤ (a ∧ c))
  (allBits-sound 4 CZ? refl (a ∷ b ∷ c ∷ d ∷ []))

-- The same in A.
transport : (G P P' : ZI.Op k) (c : ℤ) →
            (∀ x y → (G ZI.⊙ P) x y ≡ c ℤ.* (P' ZI.⊙ G) x y) →
            (ιO G ⊙ ιO P) ≐ (scale (ι c) (ιO P') ⊙ ιO G)
transport G P P' c e x y = begin
  (ιO G ⊙ ιO P) x y                  ≡⟨ Eq.sym (ιO-⊙ G P x y) ⟩
  ι ((G ZI.⊙ P) x y)                 ≡⟨ Eq.cong ι (e x y) ⟩
  ι (c ℤ.* (P' ZI.⊙ G) x y)          ≡⟨ ZS.*-homoℤ c _ ⟩
  ι c * ι ((P' ZI.⊙ G) x y)          ≡⟨ Eq.cong (ι c *_) (ιO-⊙ P' G x y) ⟩
  ι c * (ιO P' ⊙ ιO G) x y           ≡⟨ Eq.sym (scale-⊙ˡ (ι c) (ιO P') (ιO G) x y) ⟩
  (scale (ι c) (ιO P') ⊙ ιO G) x y   ∎
  where open Eq.≡-Reasoning

scaled : (a : A) {G P Q : Op k} → (G ⊙ P) ≐ (Q ⊙ G) → (scale a G ⊙ P) ≐ (Q ⊙ scale a G)
scaled a {G} {P} {Q} e =
  ≐-trans (scale-⊙ˡ a G P) (≐-trans (scale-cong e) (≐-sym (scale-⊙ʳ a Q G)))

------------------------------------------------------------------------
-- Gates on every wire

-- A gate on the bottom wires, and an operator moved up.
liftT : (G Lp Lq : Op m) (c : A) (R : Op n) → (G ⊙ Lp) ≐ (scale c Lq ⊙ G) →
        (tensor G (Idₒ {n}) ⊙ tensor Lp R) ≐ (scale c (tensor Lq R) ⊙ tensor G (Idₒ {n}))
liftT G Lp Lq c R e =
  ≐-trans (tensor-⊙ G Lp Idₒ R)
  (≐-trans (tensor-cong e (≐-trans (⊙-identityˡ R) (≐-sym (⊙-identityʳ R))))
  (≐-trans (≐-sym (tensor-⊙ (scale c Lq) G R Idₒ))
           (⊙-cong (tensor-scaleˡ c Lq R) (≐-refl (tensor G Idₒ)))))

upT : (Lp : Op m) (G R R' : Op n) (c : A) → (G ⊙ R) ≐ (scale c R' ⊙ G) →
      (tensor (Idₒ {m}) G ⊙ tensor Lp R) ≐ (scale c (tensor Lp R') ⊙ tensor (Idₒ {m}) G)
upT Lp G R R' c e =
  ≐-trans (tensor-⊙ Idₒ Lp G R)
  (≐-trans (tensor-cong (≐-trans (⊙-identityˡ Lp) (≐-sym (⊙-identityʳ Lp))) e)
  (≐-trans (≐-sym (tensor-⊙ Lp Idₒ (scale c R') G))
           (⊙-cong (tensor-scaleʳ c Lp R') (≐-refl (tensor Idₒ G)))))

-- A letter, on a Pauli operator with sign +.
pv-gen : (g : Gen n) (ps : Vec Letter n) → (valA g ⊙ pv ps) ≐ (pmat (actL g (false , ps)) ⊙ valA g)
pv-gen (gate₀ neg-gate) ps =
  ≐-trans (scal-central (- 1#) (pv ps)) (⊙-cong (≐-sym (scale-1 (pv ps))) (≐-refl (scal (- 1#))))
pv-gen (gate₁ H-gate) ((a , b) ∷ ps) =
  liftT (scale s (ιO (ZI.ix hZ))) (ιO (lZ (a , b))) (ιO (lZ (b , a))) (sg (a ∧ b)) (pv ps)
    (scaled s {ιO (ZI.ix hZ)} {ιO (lZ (a , b))} {scale (sg (a ∧ b)) (ιO (lZ (b , a)))}
      (transport (ZI.ix hZ) (lZ (a , b)) (lZ (b , a)) (sgnℤ (a ∧ b)) (H-loc a b)))
pv-gen (gate₁ Z-gate) ((a , b) ∷ ps) =
  liftT (ιO (ZI.ix zZ)) (ιO (lZ (a , b))) (ιO (lZ (a , b))) (sg a) (pv ps)
    (transport (ZI.ix zZ) (lZ (a , b)) (lZ (a , b)) (sgnℤ a) (Z-loc a b))
pv-gen (gate₂ CZ-gate) ((a , b) ∷ (c , d) ∷ ps) =
  ≐-trans (⊙-cong (≐-refl (tensor G Idₒ)) (≐-sym (tensor-assoc₁ l₁ l₂ (pv ps))))
  (≐-trans (liftT G (tensor l₁ l₂) (tensor l₁' l₂') (sg (a ∧ c)) (pv ps) loc)
           (⊙-cong (scale-cong (tensor-assoc₁ l₁' l₂' (pv ps))) (≐-refl (tensor G Idₒ))))
  where
  G = ιO (ZI.ix czZ)
  l₁ = ιO (lZ (a , b))
  l₂ = ιO (lZ (c , d))
  l₁' = ιO (lZ (a , b xor c))
  l₂' = ιO (lZ (c , d xor a))
  loc : (G ⊙ tensor l₁ l₂) ≐ (scale (sg (a ∧ c)) (tensor l₁' l₂') ⊙ G)
  loc = ≐-trans (⊙-cong (≐-refl G) (≐-sym (ιO-tensor (lZ (a , b)) (lZ (c , d)))))
    (≐-trans (transport (ZI.ix czZ) (ZI.tensor (lZ (a , b)) (lZ (c , d)))
                        (ZI.tensor (lZ (a , b xor c)) (lZ (c , d xor a))) (sgnℤ (a ∧ c))
                        (CZ-loc a b c d))
             (⊙-cong (scale-cong (ιO-tensor (lZ (a , b xor c)) (lZ (c , d xor a)))) (≐-refl G)))
pv-gen (g ↥) (p ∷ ps) =
  upT (ιO (lZ p)) (valA g) (pv ps) (pv (proj₂ (actL g (false , ps)))) (sg (proj₁ (actL g (false , ps))))
    (pv-gen g ps)

-- A letter, on any Pauli operator.
pmat-gen : (g : Gen n) (P : Pauli n) → (valA g ⊙ pmat P) ≐ (pmat (actL g P) ⊙ valA g)
pmat-gen g (σ , ps) x y = begin
  (valA g ⊙ scale (sg σ) (pv ps)) x y            ≡⟨ scale-⊙ʳ (sg σ) (valA g) (pv ps) x y ⟩
  sg σ * (valA g ⊙ pv ps) x y                     ≡⟨ Eq.cong (sg σ *_) (pv-gen g ps x y) ⟩
  sg σ * (scale (sg σ') (pv ps') ⊙ valA g) x y   ≡⟨ Eq.cong (sg σ *_) (scale-⊙ˡ (sg σ') (pv ps') (valA g) x y) ⟩
  sg σ * (sg σ' * (pv ps' ⊙ valA g) x y)         ≡⟨ Eq.sym (AR.*-assoc (sg σ) (sg σ') _) ⟩
  (sg σ * sg σ') * (pv ps' ⊙ valA g) x y         ≡⟨ Eq.cong (_* (pv ps' ⊙ valA g) x y) (Eq.sym (sg-xor σ σ')) ⟩
  sg (σ xor σ') * (pv ps' ⊙ valA g) x y          ≡⟨ Eq.sym (scale-⊙ˡ (sg (σ xor σ')) (pv ps') (valA g) x y) ⟩
  (pmat (σ xor σ' , ps') ⊙ valA g) x y           ≡⟨ Eq.cong (λ P → (pmat P ⊙ valA g) x y) (Eq.sym (actL-sign g σ ps)) ⟩
  (pmat (actL g (σ , ps)) ⊙ valA g) x y          ∎
  where
  open Eq.≡-Reasoning
  σ'  = proj₁ (actL g (false , ps))
  ps' = proj₂ (actL g (false , ps))

-- A circuit.
pmat-act : (w : Circuit n) (P : Pauli n) → (⟦ w ⟧ᴬ ⊙ pmat P) ≐ (pmat (act w P) ⊙ ⟦ w ⟧ᴬ)
pmat-act [ g ]ʷ  P = pmat-gen g P
pmat-act ε       P = ≐-trans (⊙-identityˡ (pmat P)) (≐-sym (⊙-identityʳ (pmat P)))
pmat-act (w • v) P =
  ≐-trans (⊙-assoc ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ (pmat P))
  (≐-trans (⊙-cong (≐-refl ⟦ w ⟧ᴬ) (pmat-act v P))
  (≐-trans (≐-sym (⊙-assoc ⟦ w ⟧ᴬ (pmat (act v P)) ⟦ v ⟧ᴬ))
  (≐-trans (⊙-cong (pmat-act w (act v P)) (≐-refl ⟦ v ⟧ᴬ))
           (⊙-assoc (pmat (act w (act v P))) ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ))))

------------------------------------------------------------------------
-- The entries of a Pauli matrix

-- Column y has its nonzero entry in row y + a, where it is (−1)^(y · b).
row : Vec Letter n → ZI.Bits n → ZI.Bits n
row []             []       = []
row ((a , _) ∷ ps) (y ∷ ys) = (y xor a) ∷ row ps ys

ph : Vec Letter n → ZI.Bits n → Bool
ph []             []       = false
ph ((_ , b) ∷ ps) (y ∷ ys) = (y ∧ b) xor ph ps ys

private
  lZ-diag : (a b y : Bool) → ι (lZ (a , b) ((y xor a) ∷ []) (y ∷ [])) ≡ sg (y ∧ b)
  lZ-diag false b false = refl
  lZ-diag false b true  = refl
  lZ-diag true  b false = refl
  lZ-diag true  b true  = refl

  lZ-off : (a b x y : Bool) → x ≢ y xor a → ι (lZ (a , b) (x ∷ []) (y ∷ [])) ≡ 0#
  lZ-off false b false false ne = ⊥-elim (ne refl)
  lZ-off false b false true  ne = refl
  lZ-off false b true  false ne = refl
  lZ-off false b true  true  ne = ⊥-elim (ne refl)
  lZ-off true  b false false ne = refl
  lZ-off true  b false true  ne = ⊥-elim (ne refl)
  lZ-off true  b true  false ne = ⊥-elim (ne refl)
  lZ-off true  b true  true  ne = refl

pv-diag : (ps : Vec Letter n) (y : ZI.Bits n) → pv ps (row ps y) y ≡ sg (ph ps y)
pv-diag []             []       = refl
pv-diag ((a , b) ∷ ps) (y ∷ ys) =
  Eq.trans (Eq.cong₂ _*_ (lZ-diag a b y) (pv-diag ps ys)) (Eq.sym (sg-xor (y ∧ b) (ph ps ys)))

pv-off : (ps : Vec Letter n) (x y : ZI.Bits n) → x ≢ row ps y → pv ps x y ≡ 0#
pv-off []             []       []       ne = ⊥-elim (ne refl)
pv-off ((a , b) ∷ ps) (x ∷ xs) (y ∷ ys) ne with x BoolP.≟ (y xor a)
... | no x≢    = Eq.trans (Eq.cong (_* pv ps xs ys) (lZ-off a b x y x≢)) (AR.zeroˡ (pv ps xs ys))
... | yes refl = Eq.trans (Eq.cong (ι (lZ (a , b) ((y xor a) ∷ []) (y ∷ [])) *_)
                   (pv-off ps xs ys (λ e → ne (Eq.cong ((y xor a) ∷_) e))))
                   (AR.zeroʳ _)

-- The rows and the signs determine the Pauli operator.
private
  xor-false : (σ : Bool) → σ xor false ≡ σ
  xor-false false = refl
  xor-false true  = refl

  xor-cancel : (σ b d c : Bool) → σ xor (b xor c) ≡ σ xor (d xor c) → b ≡ d
  xor-cancel σ     false false c     e = refl
  xor-cancel σ     true  true  c     e = refl
  xor-cancel false false true  false ()
  xor-cancel false false true  true  ()
  xor-cancel true  false true  false ()
  xor-cancel true  false true  true  ()
  xor-cancel false true  false false ()
  xor-cancel false true  false true  ()
  xor-cancel true  true  false false ()
  xor-cancel true  true  false true  ()

decode : (σ τ : Bool) (ps qs : Vec Letter n) →
         (∀ y → row ps y ≡ row qs y) → (∀ y → σ xor ph ps y ≡ τ xor ph qs y) → (σ , ps) ≡ (τ , qs)
decode σ τ [] [] _ h = Eq.cong (_, []) (Eq.trans (Eq.sym (xor-false σ)) (Eq.trans (h []) (xor-false τ)))
decode σ τ ((a , b) ∷ ps) ((c , d) ∷ qs) hr hp
  with refl ← decode σ τ ps qs (λ y → Eq.cong tail (hr (false ∷ y))) (λ y → hp (false ∷ y))
  with refl ← Eq.cong head (hr (false ∷ replicate _ false))
  with refl ← xor-cancel σ b d (ph ps (replicate _ false)) (hp (true ∷ replicate _ false))
  = refl

------------------------------------------------------------------------
-- Over a nontrivial ring, the matrix determines the Pauli operator

module _ (nontrivial : 1# ≢ 0#) where

  -- 1 ≠ −1, as 2 s² = 1.
  one≢-one : 1# ≢ - 1#
  one≢-one e = nontrivial (begin
    1#                            ≡⟨ Eq.sym s-half ⟩
    s * s + s * s                 ≡⟨ Eq.sym (Eq.cong₂ _+_ (AR.*-identityˡ (s * s)) (AR.*-identityˡ (s * s))) ⟩
    1# * (s * s) + 1# * (s * s)   ≡⟨ Eq.sym (AR.distribʳ (s * s) 1# 1#) ⟩
    (1# + 1#) * (s * s)           ≡⟨ Eq.cong (λ a → (1# + a) * (s * s)) e ⟩
    (1# + - 1#) * (s * s)         ≡⟨ Eq.cong (_* (s * s)) (AR.-‿inverseʳ 1#) ⟩
    0# * (s * s)                  ≡⟨ AR.zeroˡ (s * s) ⟩
    0#                            ∎)
    where open Eq.≡-Reasoning

  sg-inj : (σ τ : Bool) → sg σ ≡ sg τ → σ ≡ τ
  sg-inj false false _ = refl
  sg-inj true  true  _ = refl
  sg-inj false true  e = ⊥-elim (one≢-one e)
  sg-inj true  false e = ⊥-elim (one≢-one (Eq.sym e))

  sg≢0 : (σ : Bool) → sg σ ≢ 0#
  sg≢0 σ e = nontrivial (begin
    1#             ≡⟨ Eq.cong sg (xx σ) ⟨
    sg (σ xor σ)   ≡⟨ sg-xor σ σ ⟩
    sg σ * sg σ    ≡⟨ Eq.cong (_* sg σ) e ⟩
    0# * sg σ      ≡⟨ AR.zeroˡ (sg σ) ⟩
    0#             ∎)
    where
    open Eq.≡-Reasoning
    xx : (σ : Bool) → σ xor σ ≡ false
    xx false = refl
    xx true  = refl

  pmat-injective : (P Q : Pauli n) → pmat P ≐ pmat Q → P ≡ Q
  pmat-injective (σ , ps) (τ , qs) e = decode σ τ ps qs rows phases
    where
    open Eq.≡-Reasoning
    entry : (σ : Bool) (ps : Vec Letter _) (y : ZI.Bits _) →
            sg σ * pv ps (row ps y) y ≡ sg (σ xor ph ps y)
    entry σ ps y = Eq.trans (Eq.cong (sg σ *_) (pv-diag ps y)) (Eq.sym (sg-xor σ (ph ps y)))
    rows : ∀ y → row ps y ≡ row qs y
    rows y with ≡-dec BoolP._≟_ (row ps y) (row qs y)
    ... | yes r = r
    ... | no r  = ⊥-elim (sg≢0 (σ xor ph ps y) (begin
      sg (σ xor ph ps y)          ≡⟨ entry σ ps y ⟨
      sg σ * pv ps (row ps y) y   ≡⟨ e (row ps y) y ⟩
      sg τ * pv qs (row ps y) y   ≡⟨ Eq.cong (sg τ *_) (pv-off qs (row ps y) y r) ⟩
      sg τ * 0#                   ≡⟨ AR.zeroʳ (sg τ) ⟩
      0#                          ∎))
    phases : ∀ y → σ xor ph ps y ≡ τ xor ph qs y
    phases y = sg-inj _ _ (begin
      sg (σ xor ph ps y)          ≡⟨ entry σ ps y ⟨
      sg σ * pv ps (row ps y) y   ≡⟨ e (row ps y) y ⟩
      sg τ * pv qs (row ps y) y   ≡⟨ Eq.cong (λ x → sg τ * pv qs x y) (rows y) ⟩
      sg τ * pv qs (row qs y) y   ≡⟨ entry τ qs y ⟩
      sg (τ xor ph qs y)          ∎)
