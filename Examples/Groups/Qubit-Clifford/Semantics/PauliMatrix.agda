------------------------------------------------------------------------
-- Presentations of groups
--
-- Pauli operators as matrices, and the action of circuits on them
--
-- The matrix of i^σ X^a Z^b ⊗ … is i^σ times the Kronecker product of
-- the 2 × 2 matrices X^a Z^b, whose entry in row x of column y is
-- (−1)^(y b) if x = y + a and 0 otherwise (pmat).  A circuit w
-- conjugates them as Pauli.act says: ⟦ w ⟧ P = (act w P) ⟦ w ⟧
-- (pmat-act).  For a gate this is an identity of 2 × 2 or 4 × 4
-- Gaussian matrices, checked by evaluation (H-loc, S-loc, CZ-loc),
-- which the tensor calculus carries to every wire.
--
-- Over a nontrivial ring the matrix determines the Pauli operator
-- (pmat-injective): column y has a single nonzero entry, in row y + a,
-- and it is i^(σ + 2 y · b), so it tells a, then σ and b; the four
-- powers of i are distinct because 1 ≠ −1, as 2 s² = 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Qubit-Clifford.Semantics.PauliMatrix
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  (i : A) (i² : i * i ≡ - 1#)
  where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _xor_ ; if_then_else_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail ; replicate)
open import Data.Vec.Properties using (≡-dec)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_ ; refl)
open import Relation.Nullary using (yes ; no ; does)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Pauli
  using (Ph ; p0 ; p1 ; p2 ; p3 ; _⊕_ ; minus ; ⊕-cancel ; twice ; once ; Letter ; Pauli ; actL ; act)
open import Examples.Groups.Qubit-Clifford.Semantics.Gauss
open import Examples.Groups.Qubit-Clifford.Semantics.Interpretation isCR s s-half i i² hiding (_^_)
open ZS using (solve ; _:=_ ; _:+_ ; _:*_ ; :-_ ; con)

private
  variable
    k m n : ℕ

------------------------------------------------------------------------
-- Phases as Gaussian integers

gph : Ph → ℤi
gph p0 = 1ᵍ
gph p1 = iᵍ
gph p2 = -[1+ 0 ] +i + 0
gph p3 = + 0 +i -[1+ 0 ]

gph-⊕ : (σ τ : Ph) → gph (σ ⊕ τ) ≡ gph σ *ᵍ gph τ
gph-⊕ p0 p0 = refl
gph-⊕ p0 p1 = refl
gph-⊕ p0 p2 = refl
gph-⊕ p0 p3 = refl
gph-⊕ p1 p0 = refl
gph-⊕ p1 p1 = refl
gph-⊕ p1 p2 = refl
gph-⊕ p1 p3 = refl
gph-⊕ p2 p0 = refl
gph-⊕ p2 p1 = refl
gph-⊕ p2 p2 = refl
gph-⊕ p2 p3 = refl
gph-⊕ p3 p0 = refl
gph-⊕ p3 p1 = refl
gph-⊕ p3 p2 = refl
gph-⊕ p3 p3 = refl

-- i^σ.
iph : Ph → A
iph σ = ιᵍ (gph σ)

iph-⊕ : (σ τ : Ph) → iph (σ ⊕ τ) ≡ iph σ * iph τ
iph-⊕ σ τ = Eq.trans (Eq.cong ιᵍ (gph-⊕ σ τ)) (ιᵍ-* (gph σ) (gph τ))

iph-p2 : iph p2 ≡ - 1#
iph-p2 = solve 1 (λ i → con -[1+ 0 ] :+ i :* con (+ 0) := :- con (+ 1)) refl i

------------------------------------------------------------------------
-- Pauli matrices

-- X^a Z^b, with Gaussian entries.
lG : Letter → GI.Op 1
lG (a , b) (x ∷ []) (y ∷ []) = if x xor (y xor a) then 0ᵍ else gph (twice (y ∧ b) p0)

pv : Vec Letter n → Op n
pv []       = Idₒ
pv (p ∷ ps) = tensor {1} (ιO (lG p)) (pv ps)

pmat : Pauli n → Op n
pmat P = scale (iph (proj₁ P)) (pv (proj₂ P))

------------------------------------------------------------------------
-- Scalars

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

scale-1 : (M : Op n) → scale (iph p0) M ≐ M
scale-1 M x y = Eq.trans (Eq.cong (_* M x y) ιᵍ-1) (AR.*-identityˡ (M x y))

-- The phase goes along: σ is added to what a letter does to P.
private
  twice-⊕ : (x : Bool) (σ : Ph) → twice x σ ≡ σ ⊕ twice x p0
  twice-⊕ false σ = refl
  twice-⊕ true  σ = refl

  once-⊕ : (x : Bool) (σ : Ph) → once x σ ≡ σ ⊕ once x p0
  once-⊕ false σ = refl
  once-⊕ true  σ = refl

actL-phase : (g : Gen n) (σ : Ph) (ps : Vec Letter n) →
             actL g (σ , ps) ≡ (σ ⊕ proj₁ (actL g (p0 , ps)) , proj₂ (actL g (p0 , ps)))
actL-phase (gate₀ ω-gate) σ ps = refl
actL-phase (gate₁ H-gate) σ ((a , b) ∷ ps) = Eq.cong (_, _) (twice-⊕ (a ∧ b) σ)
actL-phase (gate₁ S-gate) σ ((a , b) ∷ ps) = Eq.cong (_, _) (once-⊕ a σ)
actL-phase (gate₂ CZ-gate) σ ((a , b) ∷ (c , d) ∷ ps) = Eq.cong (_, _) (twice-⊕ (a ∧ c) σ)
actL-phase (g ↥) σ (p ∷ ps) =
  Eq.cong₂ (λ x y → x , p ∷ y) (Eq.cong proj₁ (actL-phase g σ ps)) (Eq.cong proj₂ (actL-phase g σ ps))

------------------------------------------------------------------------
-- The gates, on one or two wires

-- G P = c P' G, at every entry, checked by evaluation.
private
  ℤi-eq-sound : {a b : ℤi} → does (a ≟ᵍ b) ≡ true → a ≡ b
  ℤi-eq-sound {a} {b} e with a ≟ᵍ b | e
  ... | yes p | _  = p
  ... | no _  | ()

loc? : GI.Op k → GI.Op k → GI.Op k → ℤi → Bool
loc? {k} G P P' c = allBits k λ x → allBits k λ y → does ((G GI.⊙ P) x y ≟ᵍ c *ᵍ (P' GI.⊙ G) x y)

loc-sound : (G P P' : GI.Op k) (c : ℤi) → loc? G P P' c ≡ true →
            ∀ x y → (G GI.⊙ P) x y ≡ c *ᵍ (P' GI.⊙ G) x y
loc-sound {k} G P P' c e x y = ℤi-eq-sound (allBits-sound k _ (allBits-sound k _ e x) y)

H? S? : GI.Bits 2 → Bool
H? (a ∷ b ∷ []) = loc? (GI.ix hG) (lG (a , b)) (lG (b , a)) (gph (twice (a ∧ b) p0))
S? (a ∷ b ∷ []) = loc? (GI.ix sG) (lG (a , b)) (lG (a , b xor a)) (gph (once a p0))

CZ? : GI.Bits 4 → Bool
CZ? (a ∷ b ∷ c ∷ d ∷ []) =
  loc? (GI.ix czG) (GI.tensor (lG (a , b)) (lG (c , d)))
       (GI.tensor (lG (a , b xor c)) (lG (c , d xor a))) (gph (twice (a ∧ c) p0))

H-loc : (a b : Bool) → ∀ x y →
        (GI.ix hG GI.⊙ lG (a , b)) x y ≡ gph (twice (a ∧ b) p0) *ᵍ (lG (b , a) GI.⊙ GI.ix hG) x y
H-loc a b = loc-sound (GI.ix hG) (lG (a , b)) (lG (b , a)) (gph (twice (a ∧ b) p0))
  (allBits-sound 2 H? refl (a ∷ b ∷ []))

S-loc : (a b : Bool) → ∀ x y →
        (GI.ix sG GI.⊙ lG (a , b)) x y ≡ gph (once a p0) *ᵍ (lG (a , b xor a) GI.⊙ GI.ix sG) x y
S-loc a b = loc-sound (GI.ix sG) (lG (a , b)) (lG (a , b xor a)) (gph (once a p0))
  (allBits-sound 2 S? refl (a ∷ b ∷ []))

CZ-loc : (a b c d : Bool) → ∀ x y →
         (GI.ix czG GI.⊙ GI.tensor (lG (a , b)) (lG (c , d))) x y ≡
         gph (twice (a ∧ c) p0) *ᵍ (GI.tensor (lG (a , b xor c)) (lG (c , d xor a)) GI.⊙ GI.ix czG) x y
CZ-loc a b c d = loc-sound (GI.ix czG) (GI.tensor (lG (a , b)) (lG (c , d)))
  (GI.tensor (lG (a , b xor c)) (lG (c , d xor a))) (gph (twice (a ∧ c) p0))
  (allBits-sound 4 CZ? refl (a ∷ b ∷ c ∷ d ∷ []))

-- The same in A.
transport : (G P P' : GI.Op k) (c : ℤi) →
            (∀ x y → (G GI.⊙ P) x y ≡ c *ᵍ (P' GI.⊙ G) x y) →
            (ιO G ⊙ ιO P) ≐ (scale (ιᵍ c) (ιO P') ⊙ ιO G)
transport G P P' c e x y = begin
  (ιO G ⊙ ιO P) x y                  ≡⟨ Eq.sym (ιO-⊙ G P x y) ⟩
  ιᵍ ((G GI.⊙ P) x y)                ≡⟨ Eq.cong ιᵍ (e x y) ⟩
  ιᵍ (c *ᵍ (P' GI.⊙ G) x y)          ≡⟨ ιᵍ-* c _ ⟩
  ιᵍ c * ιᵍ ((P' GI.⊙ G) x y)        ≡⟨ Eq.cong (ιᵍ c *_) (ιO-⊙ P' G x y) ⟩
  ιᵍ c * (ιO P' ⊙ ιO G) x y          ≡⟨ Eq.sym (scale-⊙ˡ (ιᵍ c) (ιO P') (ιO G) x y) ⟩
  (scale (ιᵍ c) (ιO P') ⊙ ιO G) x y  ∎
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

-- A letter, on a Pauli operator with phase 1.
pv-gen : (g : Gen n) (ps : Vec Letter n) → (valA g ⊙ pv ps) ≐ (pmat (actL g (p0 , ps)) ⊙ valA g)
pv-gen (gate₀ ω-gate) ps =
  ≐-trans (scal-central ω̂ (pv ps)) (⊙-cong (≐-sym (scale-1 (pv ps))) (≐-refl (scal ω̂)))
pv-gen (gate₁ H-gate) ((a , b) ∷ ps) =
  liftT (scale s (ιO (GI.ix hG))) (ιO (lG (a , b))) (ιO (lG (b , a))) (iph (twice (a ∧ b) p0)) (pv ps)
    (scaled s {ιO (GI.ix hG)} {ιO (lG (a , b))} {scale (iph (twice (a ∧ b) p0)) (ιO (lG (b , a)))}
      (transport (GI.ix hG) (lG (a , b)) (lG (b , a)) (gph (twice (a ∧ b) p0)) (H-loc a b)))
pv-gen (gate₁ S-gate) ((a , b) ∷ ps) =
  liftT (ιO (GI.ix sG)) (ιO (lG (a , b))) (ιO (lG (a , b xor a))) (iph (once a p0)) (pv ps)
    (transport (GI.ix sG) (lG (a , b)) (lG (a , b xor a)) (gph (once a p0)) (S-loc a b))
pv-gen (gate₂ CZ-gate) ((a , b) ∷ (c , d) ∷ ps) =
  ≐-trans (⊙-cong (≐-refl (tensor G Idₒ)) (≐-sym (tensor-assoc₁ l₁ l₂ (pv ps))))
  (≐-trans (liftT G (tensor l₁ l₂) (tensor l₁' l₂') (iph (twice (a ∧ c) p0)) (pv ps) loc)
           (⊙-cong (scale-cong (tensor-assoc₁ l₁' l₂' (pv ps))) (≐-refl (tensor G Idₒ))))
  where
  G = ιO (GI.ix czG)
  l₁ = ιO (lG (a , b))
  l₂ = ιO (lG (c , d))
  l₁' = ιO (lG (a , b xor c))
  l₂' = ιO (lG (c , d xor a))
  loc : (G ⊙ tensor l₁ l₂) ≐ (scale (iph (twice (a ∧ c) p0)) (tensor l₁' l₂') ⊙ G)
  loc = ≐-trans (⊙-cong (≐-refl G) (≐-sym (ιO-tensor (lG (a , b)) (lG (c , d)))))
    (≐-trans (transport (GI.ix czG) (GI.tensor (lG (a , b)) (lG (c , d)))
                        (GI.tensor (lG (a , b xor c)) (lG (c , d xor a))) (gph (twice (a ∧ c) p0))
                        (CZ-loc a b c d))
             (⊙-cong (scale-cong (ιO-tensor (lG (a , b xor c)) (lG (c , d xor a)))) (≐-refl G)))
pv-gen (g ↥) (p ∷ ps) =
  upT (ιO (lG p)) (valA g) (pv ps) (pv (proj₂ (actL g (p0 , ps)))) (iph (proj₁ (actL g (p0 , ps))))
    (pv-gen g ps)

-- A letter, on any Pauli operator.
pmat-gen : (g : Gen n) (P : Pauli n) → (valA g ⊙ pmat P) ≐ (pmat (actL g P) ⊙ valA g)
pmat-gen g (σ , ps) x y = begin
  (valA g ⊙ scale (iph σ) (pv ps)) x y            ≡⟨ scale-⊙ʳ (iph σ) (valA g) (pv ps) x y ⟩
  iph σ * (valA g ⊙ pv ps) x y                     ≡⟨ Eq.cong (iph σ *_) (pv-gen g ps x y) ⟩
  iph σ * (scale (iph σ') (pv ps') ⊙ valA g) x y   ≡⟨ Eq.cong (iph σ *_) (scale-⊙ˡ (iph σ') (pv ps') (valA g) x y) ⟩
  iph σ * (iph σ' * (pv ps' ⊙ valA g) x y)         ≡⟨ Eq.sym (AR.*-assoc (iph σ) (iph σ') _) ⟩
  (iph σ * iph σ') * (pv ps' ⊙ valA g) x y         ≡⟨ Eq.cong (_* (pv ps' ⊙ valA g) x y) (Eq.sym (iph-⊕ σ σ')) ⟩
  iph (σ ⊕ σ') * (pv ps' ⊙ valA g) x y             ≡⟨ Eq.sym (scale-⊙ˡ (iph (σ ⊕ σ')) (pv ps') (valA g) x y) ⟩
  (pmat (σ ⊕ σ' , ps') ⊙ valA g) x y               ≡⟨ Eq.cong (λ P → (pmat P ⊙ valA g) x y) (Eq.sym (actL-phase g σ ps)) ⟩
  (pmat (actL g (σ , ps)) ⊙ valA g) x y            ∎
  where
  open Eq.≡-Reasoning
  σ'  = proj₁ (actL g (p0 , ps))
  ps' = proj₂ (actL g (p0 , ps))

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
row : Vec Letter n → GI.Bits n → GI.Bits n
row []             []       = []
row ((a , _) ∷ ps) (y ∷ ys) = (y xor a) ∷ row ps ys

ph : Vec Letter n → GI.Bits n → Ph
ph []             []       = p0
ph ((_ , b) ∷ ps) (y ∷ ys) = twice (y ∧ b) (ph ps ys)

private
  lG-diag : (a b y : Bool) → lG (a , b) ((y xor a) ∷ []) (y ∷ []) ≡ gph (twice (y ∧ b) p0)
  lG-diag false b false = refl
  lG-diag false b true  = refl
  lG-diag true  b false = refl
  lG-diag true  b true  = refl

  lG-off : (a b x y : Bool) → x ≢ y xor a → lG (a , b) (x ∷ []) (y ∷ []) ≡ 0ᵍ
  lG-off false b false false ne = ⊥-elim (ne refl)
  lG-off false b false true  ne = refl
  lG-off false b true  false ne = refl
  lG-off false b true  true  ne = ⊥-elim (ne refl)
  lG-off true  b false false ne = refl
  lG-off true  b false true  ne = ⊥-elim (ne refl)
  lG-off true  b true  false ne = ⊥-elim (ne refl)
  lG-off true  b true  true  ne = refl

  ⊕-comm : (σ τ : Ph) → σ ⊕ τ ≡ τ ⊕ σ
  ⊕-comm p0 p0 = refl
  ⊕-comm p0 p1 = refl
  ⊕-comm p0 p2 = refl
  ⊕-comm p0 p3 = refl
  ⊕-comm p1 p0 = refl
  ⊕-comm p1 p1 = refl
  ⊕-comm p1 p2 = refl
  ⊕-comm p1 p3 = refl
  ⊕-comm p2 p0 = refl
  ⊕-comm p2 p1 = refl
  ⊕-comm p2 p2 = refl
  ⊕-comm p2 p3 = refl
  ⊕-comm p3 p0 = refl
  ⊕-comm p3 p1 = refl
  ⊕-comm p3 p2 = refl
  ⊕-comm p3 p3 = refl

  twice-p0 : (x : Bool) (σ : Ph) → twice x σ ≡ twice x p0 ⊕ σ
  twice-p0 x σ = Eq.trans (twice-⊕ x σ) (⊕-comm σ (twice x p0))

pv-diag : (ps : Vec Letter n) (y : GI.Bits n) → pv ps (row ps y) y ≡ iph (ph ps y)
pv-diag []             []       = Eq.sym ιᵍ-1
pv-diag ((a , b) ∷ ps) (y ∷ ys) = begin
  ιᵍ (lG (a , b) ((y xor a) ∷ []) (y ∷ [])) * pv ps (row ps ys) ys
    ≡⟨ Eq.cong₂ _*_ (Eq.cong ιᵍ (lG-diag a b y)) (pv-diag ps ys) ⟩
  iph (twice (y ∧ b) p0) * iph (ph ps ys)
    ≡⟨ Eq.sym (iph-⊕ (twice (y ∧ b) p0) (ph ps ys)) ⟩
  iph (twice (y ∧ b) p0 ⊕ ph ps ys)
    ≡⟨ Eq.cong iph (Eq.sym (twice-p0 (y ∧ b) (ph ps ys))) ⟩
  iph (twice (y ∧ b) (ph ps ys))   ∎
  where open Eq.≡-Reasoning

pv-off : (ps : Vec Letter n) (x y : GI.Bits n) → x ≢ row ps y → pv ps x y ≡ 0#
pv-off []             []       []       ne = ⊥-elim (ne refl)
pv-off ((a , b) ∷ ps) (x ∷ xs) (y ∷ ys) ne with x BoolP.≟ (y xor a)
... | no x≢    = Eq.trans (Eq.cong (λ c → ιᵍ c * pv ps xs ys) (lG-off a b x y x≢))
                   (Eq.trans (Eq.cong (_* pv ps xs ys) ιᵍ-0) (AR.zeroˡ (pv ps xs ys)))
... | yes refl = Eq.trans (Eq.cong (ιᵍ (lG (a , b) ((y xor a) ∷ []) (y ∷ [])) *_)
                   (pv-off ps xs ys (λ e → ne (Eq.cong ((y xor a) ∷_) e))))
                   (AR.zeroʳ _)

-- The rows and the phases determine the Pauli operator.
private
  twice-inj : (b d : Bool) (σ : Ph) → twice b σ ≡ twice d σ → b ≡ d
  twice-inj false false σ  _ = refl
  twice-inj true  true  σ  _ = refl
  twice-inj false true  p0 ()
  twice-inj false true  p1 ()
  twice-inj false true  p2 ()
  twice-inj false true  p3 ()
  twice-inj true  false p0 ()
  twice-inj true  false p1 ()
  twice-inj true  false p2 ()
  twice-inj true  false p3 ()

  ⊕-cancelˡ : (σ τ τ' : Ph) → σ ⊕ τ ≡ σ ⊕ τ' → τ ≡ τ'
  ⊕-cancelˡ σ τ τ' e = ⊕-cancel τ τ' σ (Eq.trans (⊕-comm τ σ) (Eq.trans e (⊕-comm σ τ')))

  ph-0 : (ps : Vec Letter n) → ph ps (replicate n false) ≡ p0
  ph-0 []            = refl
  ph-0 ((a , b) ∷ ps) = ph-0 ps

decode : (σ τ : Ph) (ps qs : Vec Letter n) →
         (∀ y → row ps y ≡ row qs y) → (∀ y → σ ⊕ ph ps y ≡ τ ⊕ ph qs y) → (σ , ps) ≡ (τ , qs)
decode σ τ [] [] _ h = Eq.cong (_, []) (h [])
decode σ τ ((a , b) ∷ ps) ((c , d) ∷ qs) hr hp
  with refl ← decode σ τ ps qs (λ y → Eq.cong tail (hr (false ∷ y))) (λ y → hp (false ∷ y))
  with refl ← Eq.cong head (hr (false ∷ replicate _ false))
  with refl ← twice-inj b d (ph ps (replicate _ false))
                (⊕-cancelˡ σ _ _ (hp (true ∷ replicate _ false)))
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

  private
    iph-p3 : iph p3 ≡ - i
    iph-p3 = solve 1 (λ i → con (+ 0) :+ i :* con -[1+ 0 ] := :- i) refl i

    -- x = 1 and x x = −1 cannot both hold, nor x = −1 and x x = −1.
    sq-1 : 1# * 1# ≡ 1#
    sq-1 = AR.*-identityˡ 1#

    sq-neg : (- 1#) * (- 1#) ≡ 1#
    sq-neg = solve 0 (:- con (+ 1) :* :- con (+ 1) := con (+ 1)) refl

    -- The only power of i that is 1 is i⁰.
    iph-one : (δ : Ph) → iph δ ≡ 1# → δ ≡ p0
    iph-one p0 _ = refl
    iph-one p1 e = ⊥-elim (one≢-one (begin
      1#        ≡⟨ Eq.sym sq-1 ⟩
      1# * 1#   ≡⟨ Eq.cong₂ _*_ (Eq.sym e') (Eq.sym e') ⟩
      i * i     ≡⟨ i² ⟩
      - 1#      ∎))
      where
      open Eq.≡-Reasoning
      e' : i ≡ 1#
      e' = Eq.trans (Eq.sym ιᵍ-i) e
    iph-one p2 e = ⊥-elim (one≢-one (Eq.sym (Eq.trans (Eq.sym iph-p2) e)))
    iph-one p3 e = ⊥-elim (one≢-one (begin
      1#                ≡⟨ Eq.sym sq-neg ⟩
      (- 1#) * (- 1#)   ≡⟨ Eq.cong₂ _*_ (Eq.sym e') (Eq.sym e') ⟩
      i * i             ≡⟨ i² ⟩
      - 1#              ∎))
      where
      open Eq.≡-Reasoning
      e' : i ≡ - 1#
      e' = Eq.trans (solve 1 (λ i → i := :- (:- i)) refl i)
             (Eq.trans (Eq.cong -_ (Eq.trans (Eq.sym iph-p3) e)) refl)

    ⊕-minus' : (σ τ : Ph) → σ ⊕ minus τ ⊕ τ ≡ σ
    ⊕-minus' p0 p0 = refl
    ⊕-minus' p0 p1 = refl
    ⊕-minus' p0 p2 = refl
    ⊕-minus' p0 p3 = refl
    ⊕-minus' p1 p0 = refl
    ⊕-minus' p1 p1 = refl
    ⊕-minus' p1 p2 = refl
    ⊕-minus' p1 p3 = refl
    ⊕-minus' p2 p0 = refl
    ⊕-minus' p2 p1 = refl
    ⊕-minus' p2 p2 = refl
    ⊕-minus' p2 p3 = refl
    ⊕-minus' p3 p0 = refl
    ⊕-minus' p3 p1 = refl
    ⊕-minus' p3 p2 = refl
    ⊕-minus' p3 p3 = refl

    p0-⊕ : (τ : Ph) → p0 ⊕ τ ≡ τ
    p0-⊕ p0 = refl
    p0-⊕ p1 = refl
    p0-⊕ p2 = refl
    p0-⊕ p3 = refl

    minus-⊕ : (τ : Ph) → τ ⊕ minus τ ≡ p0
    minus-⊕ p0 = refl
    minus-⊕ p1 = refl
    minus-⊕ p2 = refl
    minus-⊕ p3 = refl

  iph-inj : (σ τ : Ph) → iph σ ≡ iph τ → σ ≡ τ
  iph-inj σ τ e = Eq.trans (Eq.sym (⊕-minus' σ τ))
    (Eq.trans (Eq.cong (_⊕ τ) (iph-one (σ ⊕ minus τ) one)) (p0-⊕ τ))
    where
    open Eq.≡-Reasoning
    one : iph (σ ⊕ minus τ) ≡ 1#
    one = begin
      iph (σ ⊕ minus τ)        ≡⟨ iph-⊕ σ (minus τ) ⟩
      iph σ * iph (minus τ)    ≡⟨ Eq.cong (_* iph (minus τ)) e ⟩
      iph τ * iph (minus τ)    ≡⟨ Eq.sym (iph-⊕ τ (minus τ)) ⟩
      iph (τ ⊕ minus τ)        ≡⟨ Eq.cong iph (minus-⊕ τ) ⟩
      iph p0                   ≡⟨ ιᵍ-1 ⟩
      1#                       ∎

  iph≢0 : (σ : Ph) → iph σ ≢ 0#
  iph≢0 σ e = nontrivial (begin
    1#                       ≡⟨ Eq.sym ιᵍ-1 ⟩
    iph p0                   ≡⟨ Eq.cong iph (Eq.sym (minus-⊕ σ)) ⟩
    iph (σ ⊕ minus σ)        ≡⟨ iph-⊕ σ (minus σ) ⟩
    iph σ * iph (minus σ)    ≡⟨ Eq.cong (_* iph (minus σ)) e ⟩
    0# * iph (minus σ)       ≡⟨ AR.zeroˡ (iph (minus σ)) ⟩
    0#                       ∎)
    where open Eq.≡-Reasoning

  pmat-injective : (P Q : Pauli n) → pmat P ≐ pmat Q → P ≡ Q
  pmat-injective (σ , ps) (τ , qs) e = decode σ τ ps qs rows phases
    where
    open Eq.≡-Reasoning
    entry : (σ : Ph) (ps : Vec Letter _) (y : GI.Bits _) →
            iph σ * pv ps (row ps y) y ≡ iph (σ ⊕ ph ps y)
    entry σ ps y = Eq.trans (Eq.cong (iph σ *_) (pv-diag ps y)) (Eq.sym (iph-⊕ σ (ph ps y)))
    rows : ∀ y → row ps y ≡ row qs y
    rows y with ≡-dec BoolP._≟_ (row ps y) (row qs y)
    ... | yes r = r
    ... | no r  = ⊥-elim (iph≢0 (σ ⊕ ph ps y) (begin
      iph (σ ⊕ ph ps y)            ≡⟨ entry σ ps y ⟨
      iph σ * pv ps (row ps y) y   ≡⟨ e (row ps y) y ⟩
      iph τ * pv qs (row ps y) y   ≡⟨ Eq.cong (iph τ *_) (pv-off qs (row ps y) y r) ⟩
      iph τ * 0#                   ≡⟨ AR.zeroʳ (iph τ) ⟩
      0#                           ∎))
    phases : ∀ y → σ ⊕ ph ps y ≡ τ ⊕ ph qs y
    phases y = iph-inj _ _ (begin
      iph (σ ⊕ ph ps y)            ≡⟨ entry σ ps y ⟨
      iph σ * pv ps (row ps y) y   ≡⟨ e (row ps y) y ⟩
      iph τ * pv qs (row ps y) y   ≡⟨ Eq.cong (λ x → iph τ * pv qs x y) (rows y) ⟩
      iph τ * pv qs (row qs y) y   ≡⟨ entry τ qs y ⟩
      iph (τ ⊕ ph qs y)            ∎)
