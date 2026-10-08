------------------------------------------------------------------------
-- Presentations of groups
--
-- The real Clifford group, and its order (Corollary 4.16)
--
-- The real Clifford group on n qubits (Definition 2.3) is the group of
-- orthogonal matrices U that normalise the Pauli group: U P Uᵀ is a
-- Pauli matrix for every Pauli matrix P.  Over a nontrivial
-- commutative ring with s s + s s = 1 in which 1 and −1 are the only
-- square roots of 1 (ℝ, or any integral domain containing 1/√2):
--
-- * the matrix of a circuit is in it (circuit-orthogonal, circuit-normalises);
-- * every element is the matrix of a circuit (generation).  U conjugates
--   Pauli operators by a map that respects products (conj-·), so the
--   images of the X's and Z's form a Frame, realised by a normal form W
--   (PauliAlgebra.realise, Proposition 4.15).  Then ⟦ W ⟧ U commutes with
--   every X and Z, so is a scalar c (scalar, Proposition 2.4), and c² = 1;
--   so U = ±⟦ W ⟧⁻¹;
-- * so it is in bijection with the circuits modulo R1–R16 (clifford≃circuits),
--   hence with the normal forms, of which there are
--   2 · ∏ᵢ₌₁ⁿ (4ⁱ + 2ⁱ − 2)(2 · 4ⁱ⁻¹) (corollary-4-16).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Real-Clifford.Semantics.Clifford
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  (nontrivial : 1# ≢ 0#)
  (±1 : ∀ (c : A) → c * c ≡ 1# → c ≡ 1# ⊎ c ≡ - 1#)
  where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; replicate)
open import Data.Vec.Properties using (≡-dec)
open import Function.Bundles using (Inverse)
import Function.Construct.Composition as Compose
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Notations using (₁₊)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Reasoning using (module Width)
open import Examples.Groups.Real-Clifford.NormalForm using (NF ; ⟦_⟧ⁿ)
open import Examples.Groups.Real-Clifford.Normalise using (normalise ; normalise-ok)
open import Examples.Groups.Real-Clifford.Count using (order ; NF≅order)
open import Examples.Groups.Real-Clifford.Pauli using (Letter ; Pauli ; act ; inv ; inv-act ; I^)
open import Examples.Groups.Real-Clifford.PauliAlgebra
  using ( _·_ ; mulV ; flipIf ; ω ; ypar ; ·-sq ; ·-comm ; flipIf-inj ; single ; Xb ; Zb
        ; Frame ; standard ; Realised ; realise )
open import Examples.Groups.Real-Clifford.Semantics.Laws isCR
open import Examples.Groups.Real-Clifford.Semantics.Interpretation isCR s s-half
  using (ι ; module ZS ; module ZI ; ιO ; ιO-⊙ ; scale ; scale-cong ; scale-⊙ ; scale-1 ; hZ ; zZ ; czZ
        ; valA ; ⟦_⟧ᴬ ; allBits ; allBits-sound ; ℤ-eq ; check ; check-sound)
open import Examples.Groups.Real-Clifford.Semantics.Soundness isCR s s-half using (sound)
open import Examples.Groups.Real-Clifford.Semantics.Completeness isCR s s-half nontrivial
  using (inv-r ; completeness ; nf-injective)
open import Examples.Groups.Real-Clifford.Semantics.PauliMatrix isCR s s-half
  using (sgnℤ ; sg ; sg-xor ; lZ ; pv ; pmat ; pmat-act ; row ; ph ; pv-diag ; pv-off ; scale-⊙ˡ ; scale-⊙ʳ)
  renaming (pmat-injective to pmat-injective′)

private
  variable
    k m n : ℕ

  pmat-injective : (P Q : Pauli n) → pmat P ≐ pmat Q → P ≡ Q
  pmat-injective = pmat-injective′ nontrivial

  open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Transposes

infix 9 _ᵀ
_ᵀ : Op n → Op n
(M ᵀ) x y = M y x

ᵀ-cong : {M N : Op n} → M ≐ N → M ᵀ ≐ N ᵀ
ᵀ-cong e x y = e y x

ᵀ-⊙ : (M N : Op n) → ((M ⊙ N) ᵀ) ≐ (N ᵀ ⊙ M ᵀ)
ᵀ-⊙ M N x y = Σ-cong (λ z → AR.*-comm (M y z) (N z x))

δb-sym : (x y : Bits n) → δb x y ≡ δb y x
δb-sym []          []          = refl
δb-sym (true  ∷ x) (true  ∷ y) = δb-sym x y
δb-sym (false ∷ x) (false ∷ y) = δb-sym x y
δb-sym (true  ∷ x) (false ∷ y) = refl
δb-sym (false ∷ x) (true  ∷ y) = refl

private
  tensorᵀ : (M M' : Op m) (N N' : Op n) → (∀ x y → M x y ≡ M' y x) → (∀ x y → N x y ≡ N' y x) →
            ∀ x y → tensor M N x y ≡ tensor M' N' y x
  tensorᵀ {zero}  M M' N N' tM tN x       y       = Eq.cong₂ _*_ (tM [] []) (tN x y)
  tensorᵀ {suc m} M M' N N' tM tN (a ∷ x) (b ∷ y) =
    tensorᵀ {m} (λ u v → M (a ∷ u) (b ∷ v)) (λ u v → M' (b ∷ u) (a ∷ v)) N N'
      (λ u v → tM (a ∷ u) (b ∷ v)) tN x y

  Sym : Op n → Set
  Sym M = ∀ x y → M x y ≡ M y x

  symℤ : (M : ZI.Mat k) → check 0 M (ZI.matOf λ x y → ZI.ix M y x) ≡ true → Sym (ιO (ZI.ix M))
  symℤ M e x y = Eq.cong ι (Eq.trans (check-sound 0 M _ e x y) (ZI.ix-matOf (λ x y → ZI.ix M y x) x y))

  valA-sym : (g : Gen n) → Sym (valA g)
  valA-sym (gate₀ neg-gate) x y = Eq.cong (- 1# *_) (δb-sym x y)
  valA-sym (gate₁ H-gate) = tensorᵀ _ _ Idₒ Idₒ
    (λ x y → Eq.cong (s *_) (symℤ hZ refl x y)) δb-sym
  valA-sym (gate₁ Z-gate)  = tensorᵀ _ _ Idₒ Idₒ (symℤ zZ refl) δb-sym
  valA-sym (gate₂ CZ-gate) = tensorᵀ _ _ Idₒ Idₒ (symℤ czZ refl) δb-sym
  valA-sym (g ↥) = tensorᵀ (Idₒ {1}) Idₒ (valA g) (valA g) δb-sym (valA-sym g)

-- The transpose of the matrix of a circuit is that of the circuit
-- reversed.
⟦⟧ᵀ : (w : Circuit n) → ⟦ w ⟧ᴬ ᵀ ≐ ⟦ inv w ⟧ᴬ
⟦⟧ᵀ [ g ]ʷ  x y = valA-sym g y x
⟦⟧ᵀ ε       x y = δb-sym y x
⟦⟧ᵀ (w • v) x y = Eq.trans (ᵀ-⊙ ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ x y) (⊙-cong (⟦⟧ᵀ v) (⟦⟧ᵀ w) x y)

private
  inv-inv : (w : Circuit n) → inv (inv w) ≡ w
  inv-inv [ g ]ʷ  = refl
  inv-inv ε       = refl
  inv-inv (w • v) = Eq.cong₂ _•_ (inv-inv w) (inv-inv v)

inv-l : (w : Circuit n) → n ⊢ inv w • w ≈ ε
inv-l {n} w = Eq.subst (λ u → n ⊢ inv w • u ≈ ε) (inv-inv w) (inv-r (inv w))

------------------------------------------------------------------------
-- The real Clifford group

Orthogonal : Op n → Set
Orthogonal U = ((U ⊙ U ᵀ) ≐ Idₒ) × ((U ᵀ ⊙ U) ≐ Idₒ)

-- U P Uᵀ is a Pauli matrix for every Pauli matrix P.
Normalises : Op n → Set
Normalises {n} U = (P : Pauli n) → Σ (Pauli n) λ Q → ((U ⊙ pmat P) ⊙ U ᵀ) ≐ pmat Q

Clifford : ℕ → Set
Clifford n = Σ (Op n) λ U → Orthogonal U × Normalises U

-- Compared as matrices.
Clifford-setoid : ℕ → Setoid 0ℓ 0ℓ
Clifford-setoid n = record
  { Carrier       = Clifford n
  ; _≈_           = λ U V → proj₁ U ≐ proj₁ V
  ; isEquivalence = record { refl = ≐-refl _ ; sym = ≐-sym ; trans = ≐-trans }
  }

-- Circuits are real Clifford operators.
circuit-orthogonal : (w : Circuit n) → Orthogonal ⟦ w ⟧ᴬ
circuit-orthogonal w =
  ≐-trans (⊙-cong (≐-refl ⟦ w ⟧ᴬ) (⟦⟧ᵀ w)) (sound (inv-r w)) ,
  ≐-trans (⊙-cong (⟦⟧ᵀ w) (≐-refl ⟦ w ⟧ᴬ)) (sound (inv-l w))

conj-circuit : (w : Circuit n) (P : Pauli n) → ((⟦ w ⟧ᴬ ⊙ pmat P) ⊙ ⟦ inv w ⟧ᴬ) ≐ pmat (act w P)
conj-circuit w P =
  ≐-trans (⊙-cong (pmat-act w P) (≐-refl ⟦ inv w ⟧ᴬ))
  (≐-trans (⊙-assoc (pmat (act w P)) ⟦ w ⟧ᴬ ⟦ inv w ⟧ᴬ)
  (≐-trans (⊙-cong (≐-refl (pmat (act w P))) (sound (inv-r w))) (⊙-identityʳ (pmat (act w P)))))

circuit-normalises : (w : Circuit n) → Normalises ⟦ w ⟧ᴬ
circuit-normalises w P = act w P ,
  ≐-trans (⊙-cong (≐-refl (⟦ w ⟧ᴬ ⊙ pmat P)) (⟦⟧ᵀ w)) (conj-circuit w P)

circuit : Circuit n → Clifford n
circuit w = ⟦ w ⟧ᴬ , circuit-orthogonal w , circuit-normalises w

------------------------------------------------------------------------
-- Products of Pauli matrices

private
  ℤ-eq-sound : {a b : ℤ} → ℤ-eq a b ≡ true → a ≡ b
  ℤ-eq-sound {a} {b} e with a ℤP.≟ b | e
  ... | yes p | _  = p
  ... | no _  | ()

  mulP : (a b c d : Bool) → ZI.Bits 1 → ZI.Bits 1 → Bool
  mulP a b c d x y = ℤ-eq ((lZ (a , b) ZI.⊙ lZ (c , d)) x y) (sgnℤ (b ∧ c) ℤ.* lZ (a xor c , b xor d) x y)

  mul? : ZI.Bits 4 → Bool
  mul? (a ∷ b ∷ c ∷ d ∷ []) = allBits 1 λ x → allBits 1 (mulP a b c d x)

  -- X^a Z^b · X^c Z^d = (−1)^(b c) X^(a+c) Z^(b+d), as integer matrices.
  mul-loc : (a b c d : Bool) → ∀ x y →
            (lZ (a , b) ZI.⊙ lZ (c , d)) x y ≡ sgnℤ (b ∧ c) ℤ.* lZ (a xor c , b xor d) x y
  mul-loc a b c d x y = ℤ-eq-sound (allBits-sound 1 (mulP a b c d x)
    (allBits-sound 1 (λ x → allBits 1 (mulP a b c d x)) (allBits-sound 4 mul? refl (a ∷ b ∷ c ∷ d ∷ [])) x) y)

  mul-A : (a b c d : Bool) →
          (ιO (lZ (a , b)) ⊙ ιO (lZ (c , d))) ≐ scale (sg (b ∧ c)) (ιO (lZ (a xor c , b xor d)))
  mul-A a b c d x y = Eq.trans (Eq.sym (ιO-⊙ (lZ (a , b)) (lZ (c , d)) x y))
    (Eq.trans (Eq.cong ι (mul-loc a b c d x y)) (ZS.*-homoℤ (sgnℤ (b ∧ c)) _))

  tensor-scale₂ : (c d : A) (M : Op m) (N : Op n) →
                  tensor (scale c M) (scale d N) ≐ scale (c * d) (tensor M N)
  tensor-scale₂ c d M N x y = Eq.trans (tensor-scaleˡ c M (scale d N) x y)
    (Eq.trans (Eq.cong (c *_) (tensor-scaleʳ d M N x y)) (Eq.sym (AR.*-assoc c d (tensor M N x y))))

  scale-scale : (c d : A) (M : Op n) → scale c (scale d M) ≐ scale (c * d) M
  scale-scale c d M x y = Eq.sym (AR.*-assoc c d (M x y))

pv-mul : (ps qs : Vec Letter n) →
         (pv ps ⊙ pv qs) ≐ scale (sg (proj₁ (mulV ps qs))) (pv (proj₂ (mulV ps qs)))
pv-mul []             []             = ≐-trans (⊙-identityˡ Idₒ) (≐-sym (scale-1 Idₒ))
pv-mul ((a , b) ∷ ps) ((c , d) ∷ qs) =
  ≐-trans (tensor-⊙ (ιO (lZ (a , b))) (ιO (lZ (c , d))) (pv ps) (pv qs))
  (≐-trans (tensor-cong {m = 1} (mul-A a b c d) (pv-mul ps qs))
  (≐-trans (tensor-scale₂ (sg (b ∧ c)) (sg ρ) (ιO (lZ (a xor c , b xor d))) (pv (proj₂ (mulV ps qs))))
           (λ x y → Eq.cong (_* tensor (ιO (lZ (a xor c , b xor d))) (pv (proj₂ (mulV ps qs))) x y)
                             (Eq.sym (sg-xor (b ∧ c) ρ)))))
  where
  ρ = proj₁ (mulV ps qs)

-- The matrix of a product is the product of the matrices.
pmat-· : (P Q : Pauli n) → pmat (P · Q) ≐ (pmat P ⊙ pmat Q)
pmat-· (σ , ps) (τ , qs) = ≐-sym
  (≐-trans (scale-⊙ (sg σ) (sg τ) (pv ps) (pv qs))
  (≐-trans (scale-cong (pv-mul ps qs))
  (≐-trans (scale-scale (sg σ * sg τ) (sg (proj₁ (mulV ps qs))) (pv (proj₂ (mulV ps qs))))
           (λ x y → Eq.cong (_* pv (proj₂ (mulV ps qs)) x y)
                      (Eq.sym (Eq.trans (sg-xor (σ xor τ) (proj₁ (mulV ps qs)))
                                        (Eq.cong (_* sg (proj₁ (mulV ps qs))) (sg-xor σ τ))))))))

pmat-flip : (b : Bool) (P : Pauli n) → pmat (flipIf b P) ≐ scale (sg b) (pmat P)
pmat-flip b (σ , ps) x y = Eq.trans (Eq.cong (_* pv ps x y) (Eq.trans (sg-xor σ b) (AR.*-comm (sg σ) (sg b))))
  (AR.*-assoc (sg b) (sg σ) (pv ps x y))

private
  lZ-I : ιO (lZ (false , false)) ≐ Idₒ {1}
  lZ-I (false ∷ []) (false ∷ []) = refl
  lZ-I (false ∷ []) (true ∷ [])  = refl
  lZ-I (true ∷ [])  (false ∷ []) = refl
  lZ-I (true ∷ [])  (true ∷ [])  = refl

pv-I : (n : ℕ) → pv (I^ n) ≐ Idₒ
pv-I zero    = ≐-refl Idₒ
pv-I (suc n) = ≐-trans (tensor-cong {m = 1} lZ-I (pv-I n)) (≐-sym (tensor-Id {1} {n}))

------------------------------------------------------------------------
-- Conjugation by an invertible matrix respects products

record Conj (V V⁻ : Op n) (ψ : Pauli n → Pauli n) : Set where
  field
    right : (V ⊙ V⁻) ≐ Idₒ
    left  : (V⁻ ⊙ V) ≐ Idₒ
    conj  : ∀ P → ((V ⊙ pmat P) ⊙ V⁻) ≐ pmat (ψ P)

module ConjLemmas {V V⁻ : Op n} {ψ : Pauli n → Pauli n} (C : Conj V V⁻ ψ) where
  open Conj C

  private
    -- V M V⁻ V N V⁻ = V M N V⁻.
    split : (M N : Op n) → ((V ⊙ (M ⊙ N)) ⊙ V⁻) ≐ (((V ⊙ M) ⊙ V⁻) ⊙ ((V ⊙ N) ⊙ V⁻))
    split M N = ≐-sym (begin≐)
      where
      begin≐ : (((V ⊙ M) ⊙ V⁻) ⊙ ((V ⊙ N) ⊙ V⁻)) ≐ ((V ⊙ (M ⊙ N)) ⊙ V⁻)
      begin≐ =
        ≐-trans (⊙-assoc (V ⊙ M) V⁻ ((V ⊙ N) ⊙ V⁻))
        (≐-trans (⊙-cong (≐-refl (V ⊙ M)) (≐-sym (⊙-assoc V⁻ (V ⊙ N) V⁻)))
        (≐-trans (⊙-cong (≐-refl (V ⊙ M)) (⊙-cong (≐-sym (⊙-assoc V⁻ V N)) (≐-refl V⁻)))
        (≐-trans (⊙-cong (≐-refl (V ⊙ M)) (⊙-cong (⊙-cong left (≐-refl N)) (≐-refl V⁻)))
        (≐-trans (⊙-cong (≐-refl (V ⊙ M)) (⊙-cong (⊙-identityˡ N) (≐-refl V⁻)))
        (≐-trans (≐-sym (⊙-assoc (V ⊙ M) N V⁻))
                 (⊙-cong (⊙-assoc V M N) (≐-refl V⁻)))))))

    scale-in : (c : A) (M : Op n) → ((V ⊙ scale c M) ⊙ V⁻) ≐ scale c ((V ⊙ M) ⊙ V⁻)
    scale-in c M = ≐-trans (⊙-cong (scale-⊙ʳ c V M) (≐-refl V⁻)) (scale-⊙ˡ c (V ⊙ M) V⁻)

  conj-· : (P Q : Pauli n) → ψ (P · Q) ≡ ψ P · ψ Q
  conj-· P Q = pmat-injective (ψ (P · Q)) (ψ P · ψ Q)
    (≐-trans (≐-sym (conj (P · Q)))
    (≐-trans (⊙-cong (⊙-cong (≐-refl V) (pmat-· P Q)) (≐-refl V⁻))
    (≐-trans (split (pmat P) (pmat Q))
    (≐-trans (⊙-cong (conj P) (conj Q)) (≐-sym (pmat-· (ψ P) (ψ Q)))))))

  conj-flip : (b : Bool) (P : Pauli n) → ψ (flipIf b P) ≡ flipIf b (ψ P)
  conj-flip b P = pmat-injective (ψ (flipIf b P)) (flipIf b (ψ P))
    (≐-trans (≐-sym (conj (flipIf b P)))
    (≐-trans (⊙-cong (⊙-cong (≐-refl V) (pmat-flip b P)) (≐-refl V⁻))
    (≐-trans (scale-in (sg b) (pmat P))
    (≐-trans (scale-cong (conj P)) (≐-sym (pmat-flip b (ψ P)))))))

  conj-𝟙 : ψ (false , I^ n) ≡ (false , I^ n)
  conj-𝟙 = pmat-injective (ψ (false , I^ n)) (false , I^ n)
    (≐-trans (≐-sym (conj (false , I^ n)))
    (≐-trans (⊙-cong (⊙-cong (≐-refl V) (≐-trans (scale-1 (pv (I^ n))) (pv-I n))) (≐-refl V⁻))
    (≐-trans (⊙-cong (⊙-identityʳ V) (≐-refl V⁻))
    (≐-trans right (≐-sym (≐-trans (scale-1 (pv (I^ n))) (pv-I n)))))))

  -- So ψ keeps the squares and the commutations.
  conj-ypar : (P : Pauli n) → ypar (proj₂ (ψ P)) ≡ ypar (proj₂ P)
  conj-ypar P = Eq.cong proj₁ (begin
    (ypar (proj₂ (ψ P)) , I^ n)        ≡⟨ ·-sq (ψ P) ⟨
    ψ P · ψ P                          ≡⟨ conj-· P P ⟨
    ψ (P · P)                          ≡⟨ Eq.cong ψ (·-sq P) ⟩
    ψ (flipIf (ypar (proj₂ P)) (false , I^ n))   ≡⟨ conj-flip (ypar (proj₂ P)) (false , I^ n) ⟩
    flipIf (ypar (proj₂ P)) (ψ (false , I^ n))   ≡⟨ Eq.cong (flipIf (ypar (proj₂ P))) conj-𝟙 ⟩
    (ypar (proj₂ P) , I^ n)            ∎)

  conj-ω : (P Q : Pauli n) → ω (proj₂ (ψ P)) (proj₂ (ψ Q)) ≡ ω (proj₂ P) (proj₂ Q)
  conj-ω P Q = flipIf-inj _ _ (ψ P · ψ Q) (begin
    flipIf (ω (proj₂ (ψ P)) (proj₂ (ψ Q))) (ψ P · ψ Q)   ≡⟨ ·-comm (ψ P) (ψ Q) ⟨
    ψ Q · ψ P                                            ≡⟨ conj-· Q P ⟨
    ψ (Q · P)                                            ≡⟨ Eq.cong ψ (·-comm P Q) ⟩
    ψ (flipIf (ω (proj₂ P) (proj₂ Q)) (P · Q))           ≡⟨ conj-flip _ (P · Q) ⟩
    flipIf (ω (proj₂ P) (proj₂ Q)) (ψ (P · Q))           ≡⟨ Eq.cong (flipIf _) (conj-· P Q) ⟩
    flipIf (ω (proj₂ P) (proj₂ Q)) (ψ P · ψ Q)           ∎)

  -- The images of the generators form a frame.
  frame : Frame n
  frame = record
    { x    = λ i → ψ (Xb i)
    ; z    = λ i → ψ (Zb i)
    ; x-sq = λ i → Eq.trans (conj-ypar (Xb i)) (Frame.x-sq standard i)
    ; z-sq = λ i → Eq.trans (conj-ypar (Zb i)) (Frame.z-sq standard i)
    ; xx   = λ i j → Eq.trans (conj-ω (Xb i) (Xb j)) (Frame.xx standard i j)
    ; zz   = λ i j → Eq.trans (conj-ω (Zb i) (Zb j)) (Frame.zz standard i j)
    ; xz   = λ i j → Eq.trans (conj-ω (Xb i) (Zb j)) (Frame.xz standard i j)
    }

------------------------------------------------------------------------
-- A matrix that commutes with every X and Z is a scalar
-- (Proposition 2.4)

private
  δb-refl : (x : Bits n) → δb x x ≡ 1#
  δb-refl []          = refl
  δb-refl (true  ∷ x) = δb-refl x
  δb-refl (false ∷ x) = δb-refl x

  δb-≢ : {x y : Bits n} → x ≢ y → δb x y ≡ 0#
  δb-≢ {x = []}        {[]}        ne = ⊥-elim (ne refl)
  δb-≢ {x = true ∷ x}  {true ∷ y}  ne = δb-≢ (λ e → ne (Eq.cong (true ∷_) e))
  δb-≢ {x = false ∷ x} {false ∷ y} ne = δb-≢ (λ e → ne (Eq.cong (false ∷_) e))
  δb-≢ {x = true ∷ x}  {false ∷ y} ne = refl
  δb-≢ {x = false ∷ x} {true ∷ y}  ne = refl

  _≟ᵇ_ : (x y : Bits n) → Dec (x ≡ y)
  _≟ᵇ_ = ≡-dec BoolP._≟_

  xor-xor : (y a : Bool) → (y xor a) xor a ≡ y
  xor-xor false false = refl
  xor-xor false true  = refl
  xor-xor true  false = refl
  xor-xor true  true  = refl

  row-row : (ps : Vec Letter n) (y : Bits n) → row ps (row ps y) ≡ y
  row-row []             []       = refl
  row-row ((a , b) ∷ ps) (y ∷ ys) = Eq.cong₂ _∷_ (xor-xor y a) (row-row ps ys)

  -- The entries of a Pauli matrix.
  pv-δ : (ps : Vec Letter n) (x y : Bits n) → pv ps x y ≡ δb x (row ps y) * sg (ph ps y)
  pv-δ ps x y with x ≟ᵇ row ps y
  ... | yes refl = Eq.trans (pv-diag ps y)
                     (Eq.sym (Eq.trans (Eq.cong (_* sg (ph ps y)) (δb-refl (row ps y))) (AR.*-identityˡ (sg (ph ps y)))))
  ... | no ne    = Eq.trans (pv-off ps x y ne)
                     (Eq.sym (Eq.trans (Eq.cong (_* sg (ph ps y)) (δb-≢ ne)) (AR.zeroˡ (sg (ph ps y)))))

  δb-row : (ps : Vec Letter n) (x z : Bits n) → δb x (row ps z) ≡ δb (row ps x) z
  δb-row ps x z with x ≟ᵇ row ps z
  ... | yes refl = Eq.trans (δb-refl (row ps z)) (Eq.sym (Eq.trans (Eq.cong (λ u → δb u z) (row-row ps z)) (δb-refl z)))
  ... | no ne    = Eq.trans (δb-≢ ne) (Eq.sym (δb-≢ λ e → ne (Eq.trans (Eq.sym (row-row ps x)) (Eq.cong (row ps) e))))

  -- V P and P V, entrywise.
  mulʳ : (V : Op n) (ps : Vec Letter n) (x y : Bits n) → (V ⊙ pv ps) x y ≡ V x (row ps y) * sg (ph ps y)
  mulʳ V ps x y = Eq.trans
    (Σ-cong (λ z → Eq.trans (Eq.cong (V x z *_) (pv-δ ps z y))
      (Eq.trans (Eq.sym (AR.*-assoc (V x z) _ _))
        (Eq.trans (Eq.cong (_* sg (ph ps y)) (AR.*-comm (V x z) _))
          (Eq.trans (AR.*-assoc _ (V x z) _) (AR.*-comm _ _))))))
    (Σ-δʳ (row ps y) (λ z → V x z * sg (ph ps y)))

  mulˡ : (V : Op n) (ps : Vec Letter n) (x y : Bits n) →
         (pv ps ⊙ V) x y ≡ sg (ph ps (row ps x)) * V (row ps x) y
  mulˡ V ps x y = Eq.trans
    (Σ-cong (λ z → Eq.trans (Eq.cong (_* V z y) (Eq.trans (pv-δ ps x z) (Eq.cong (_* sg (ph ps z)) (δb-row ps x z))))
      (AR.*-assoc (δb (row ps x) z) (sg (ph ps z)) (V z y))))
    (Σ-δˡ (row ps x) (λ z → sg (ph ps z) * V z y))

  -- Flipping one bit.
  flipAt : Fin n → Bits n → Bits n
  flipAt zero    (b ∷ x) = not b ∷ x
  flipAt (suc i) (b ∷ x) = b ∷ flipAt i x

  flip-flip : (i : Fin n) (x : Bits n) → flipAt i (flipAt i x) ≡ x
  flip-flip zero    (b ∷ x) = Eq.cong (_∷ x) (BoolP.not-involutive b)
  flip-flip (suc i) (b ∷ x) = Eq.cong (b ∷_) (flip-flip i x)

  row-I : (y : Bits n) → row (I^ n) y ≡ y
  row-I []       = refl
  row-I (y ∷ ys) = Eq.cong₂ _∷_ (BoolP.xor-identityʳ y) (row-I ys)

  ph-I : (y : Bits n) → ph (I^ n) y ≡ false
  ph-I []       = refl
  ph-I (y ∷ ys) = Eq.trans (Eq.cong ((y ∧ false) xor_) (ph-I ys))
                    (Eq.trans (BoolP.xor-identityʳ (y ∧ false)) (BoolP.∧-zeroʳ y))

  row-Z : (i : Fin n) (y : Bits n) → row (single (false , true) i) y ≡ y
  row-Z zero    (y ∷ ys) = Eq.cong₂ _∷_ (BoolP.xor-identityʳ y) (row-I ys)
  row-Z (suc i) (y ∷ ys) = Eq.cong₂ _∷_ (BoolP.xor-identityʳ y) (row-Z i ys)

  ph-Z : (i : Fin n) (y : Bits n) → ph (single (false , true) i) y ≡ lookup y i
  ph-Z zero    (y ∷ ys) = Eq.trans (Eq.cong ((y ∧ true) xor_) (ph-I ys))
                            (Eq.trans (BoolP.xor-identityʳ (y ∧ true)) (BoolP.∧-identityʳ y))
  ph-Z (suc i) (y ∷ ys) = Eq.trans (Eq.cong ((y ∧ false) xor_) (ph-Z i ys))
                            (Eq.cong (_xor lookup ys i) (BoolP.∧-zeroʳ y))

  row-X : (i : Fin n) (y : Bits n) → row (single (true , false) i) y ≡ flipAt i y
  row-X zero    (y ∷ ys) = Eq.cong₂ _∷_ (xor-true y) (row-I ys)
    where
    xor-true : (y : Bool) → y xor true ≡ not y
    xor-true false = refl
    xor-true true  = refl
  row-X (suc i) (y ∷ ys) = Eq.cong₂ _∷_ (BoolP.xor-identityʳ y) (row-X i ys)

  ph-X : (i : Fin n) (y : Bits n) → ph (single (true , false) i) y ≡ false
  ph-X zero    (y ∷ ys) = Eq.trans (Eq.cong ((y ∧ false) xor_) (ph-I ys))
                            (Eq.trans (BoolP.xor-identityʳ (y ∧ false)) (BoolP.∧-zeroʳ y))
  ph-X (suc i) (y ∷ ys) = Eq.trans (Eq.cong ((y ∧ false) xor_) (ph-X i ys))
                            (Eq.trans (BoolP.xor-identityʳ (y ∧ false)) (BoolP.∧-zeroʳ y))

  -- a = −a forces a = 0, 2 being invertible.
  self-neg : (a : A) → a ≡ - a → a ≡ 0#
  self-neg a e = begin
    a                              ≡⟨ AR.*-identityˡ a ⟨
    1# * a                         ≡⟨ Eq.cong (_* a) s-half ⟨
    (s * s + s * s) * a            ≡⟨ AR.distribʳ a (s * s) (s * s) ⟩
    (s * s) * a + (s * s) * a      ≡⟨ AR.distribˡ (s * s) a a ⟨
    (s * s) * (a + a)              ≡⟨ Eq.cong (λ b → (s * s) * (a + b)) e ⟩
    (s * s) * (a + - a)            ≡⟨ Eq.cong ((s * s) *_) (AR.-‿inverseʳ a) ⟩
    (s * s) * 0#                   ≡⟨ AR.zeroʳ (s * s) ⟩
    0#                             ∎

  -1*a : (a : A) → - 1# * a ≡ - a
  -1*a a = Eq.trans (Eq.sym (Eq.cong (_* a) refl)) (RingProps.-1*x≈-x AR.ring a)
    where import Algebra.Properties.Ring as RingProps

  -- An entry that Z on a wire where its row and column differ negates.
  off : (a : A) (b c : Bool) → b ≢ c → a * sg c ≡ sg b * a → a ≡ 0#
  off a false false ne e = ⊥-elim (ne refl)
  off a true  true  ne e = ⊥-elim (ne refl)
  off a false true  ne e = self-neg a (begin
    a                ≡⟨ AR.*-identityˡ a ⟨
    1# * a           ≡⟨ e ⟨
    a * - 1#         ≡⟨ AR.*-comm a (- 1#) ⟩
    - 1# * a         ≡⟨ -1*a a ⟩
    - a              ∎)
  off a true  false ne e = self-neg a (begin
    a                ≡⟨ AR.*-identityʳ a ⟨
    a * 1#           ≡⟨ e ⟩
    - 1# * a         ≡⟨ -1*a a ⟩
    - a              ∎)

  differ : (x y : Bits n) → x ≢ y → Σ (Fin n) λ i → lookup x i ≢ lookup y i
  differ []      []      ne = ⊥-elim (ne refl)
  differ (a ∷ x) (b ∷ y) ne with a BoolP.≟ b
  ... | no a≢b   = zero , a≢b
  ... | yes refl = let (i , d) = differ x y (λ e → ne (Eq.cong (a ∷_) e)) in suc i , d

  -- A function on bit vectors that no single flip changes is constant.
  flip-const : (f : Bits n → A) → (∀ i x → f (flipAt i x) ≡ f x) → ∀ x → f x ≡ f (replicate n false)
  flip-const {zero}  f h []      = refl
  flip-const {suc n} f h (b ∷ x) =
    Eq.trans (flip-const (λ x' → f (b ∷ x')) (λ i x' → h (suc i) (b ∷ x')) x) (to0 b)
    where
    to0 : (b : Bool) → f (b ∷ replicate n false) ≡ f (false ∷ replicate n false)
    to0 false = refl
    to0 true  = Eq.sym (h zero (true ∷ replicate n false))

scalar : (V : Op n) →
         (∀ i → (V ⊙ pmat (Xb i)) ≐ (pmat (Xb i) ⊙ V)) →
         (∀ i → (V ⊙ pmat (Zb i)) ≐ (pmat (Zb i) ⊙ V)) →
         V ≐ scal (V (replicate n false) (replicate n false))
scalar {n} V cx cz x y with x ≟ᵇ y
... | yes refl = Eq.trans (flip-const (λ u → V u u) diag x)
                   (Eq.sym (Eq.trans (Eq.cong (V 0ᵇ 0ᵇ *_) (δb-refl x)) (AR.*-identityʳ (V 0ᵇ 0ᵇ))))
  where
  0ᵇ = replicate n false
  diag : ∀ i u → V (flipAt i u) (flipAt i u) ≡ V u u
  diag i u = Eq.sym (Eq.trans (Eq.cong (V u) (Eq.sym (flip-flip i u))) (x-comm i u (flipAt i u)))
    where
    x-comm : ∀ i u v → V u (flipAt i v) ≡ V (flipAt i u) v
    x-comm i u v = begin
      V u (flipAt i v)                                     ≡⟨ AR.*-identityʳ _ ⟨
      V u (flipAt i v) * 1#                                ≡⟨ Eq.cong₂ (λ r p → V u r * sg p) (row-X i v) (ph-X i v) ⟨
      V u (row px v) * sg (ph px v)                        ≡⟨ mulʳ V px u v ⟨
      (V ⊙ pv px) u v                                      ≡⟨ ⊙-cong (≐-refl V) (scale-1 (pv px)) u v ⟨
      (V ⊙ pmat (Xb i)) u v                                ≡⟨ cx i u v ⟩
      (pmat (Xb i) ⊙ V) u v                                ≡⟨ ⊙-cong (scale-1 (pv px)) (≐-refl V) u v ⟩
      (pv px ⊙ V) u v                                      ≡⟨ mulˡ V px u v ⟩
      sg (ph px (row px u)) * V (row px u) v               ≡⟨ Eq.cong₂ (λ p r → sg p * V r v) (ph-X i (row px u)) (row-X i u) ⟩
      1# * V (flipAt i u) v                                ≡⟨ AR.*-identityˡ _ ⟩
      V (flipAt i u) v                                     ∎
      where
      px = single (true , false) i
... | no ne    = Eq.trans (off (V x y) (lookup x i) (lookup y i) d (z-comm i))
                   (Eq.sym (Eq.trans (Eq.cong (_ *_) (δb-≢ ne)) (AR.zeroʳ _)))
  where
  i = proj₁ (differ x y ne)
  d = proj₂ (differ x y ne)
  z-comm : ∀ i → V x y * sg (lookup y i) ≡ sg (lookup x i) * V x y
  z-comm i = begin
    V x y * sg (lookup y i)                              ≡⟨ Eq.cong₂ (λ r p → V x r * sg p) (row-Z i y) (ph-Z i y) ⟨
    V x (row pz y) * sg (ph pz y)                        ≡⟨ mulʳ V pz x y ⟨
    (V ⊙ pv pz) x y                                      ≡⟨ ⊙-cong (≐-refl V) (scale-1 (pv pz)) x y ⟨
    (V ⊙ pmat (Zb i)) x y                                ≡⟨ cz i x y ⟩
    (pmat (Zb i) ⊙ V) x y                                ≡⟨ ⊙-cong (scale-1 (pv pz)) (≐-refl V) x y ⟩
    (pv pz ⊙ V) x y                                      ≡⟨ mulˡ V pz x y ⟩
    sg (ph pz (row pz x)) * V (row pz x) y               ≡⟨ Eq.cong₂ (λ r' r → sg (ph pz r') * V r y) (row-Z i x) (row-Z i x) ⟩
    sg (ph pz x) * V x y                                 ≡⟨ Eq.cong (λ p → sg p * V x y) (ph-Z i x) ⟩
    sg (lookup x i) * V x y                              ∎
    where
    pz = single (false , true) i

------------------------------------------------------------------------
-- Every real Clifford operator is the matrix of a circuit

module Generation (U : Clifford n) where

  private
    Uₘ = proj₁ U
    orth = proj₁ (proj₂ U)
    norm = proj₂ (proj₂ U)

  -- U conjugates Pauli matrices by φ.
  φ : Pauli n → Pauli n
  φ P = proj₁ (norm P)

  conj-U : Conj Uₘ (Uₘ ᵀ) φ
  conj-U = record { right = proj₁ orth ; left = proj₂ orth ; conj = λ P → proj₂ (norm P) }

  open ConjLemmas conj-U using (frame)

  -- A normal form W whose inverse acts as φ on the X's and Z's
  -- (Proposition 4.15).
  realised : Realised frame
  realised = realise frame

  W : Circuit n
  W = ⟦ Realised.nf realised ⟧ⁿ

  -- Then ⟦ W ⟧ U commutes with every X and Z.
  V : Op n
  V = ⟦ W ⟧ᴬ ⊙ Uₘ

  private
    U-comm : ∀ P → (Uₘ ⊙ pmat P) ≐ (pmat (φ P) ⊙ Uₘ)
    U-comm P =
      ≐-trans (≐-sym (⊙-identityʳ (Uₘ ⊙ pmat P)))
      (≐-trans (⊙-cong (≐-refl (Uₘ ⊙ pmat P)) (≐-sym (proj₂ orth)))
      (≐-trans (≐-sym (⊙-assoc (Uₘ ⊙ pmat P) (Uₘ ᵀ) Uₘ))
               (⊙-cong (proj₂ (norm P)) (≐-refl Uₘ))))

    V-comm : (b : Pauli n) → act (inv W) b ≡ φ b → (V ⊙ pmat b) ≐ (pmat b ⊙ V)
    V-comm b e =
      ≐-trans (⊙-assoc ⟦ W ⟧ᴬ Uₘ (pmat b))
      (≐-trans (⊙-cong (≐-refl ⟦ W ⟧ᴬ) (U-comm b))
      (≐-trans (≐-sym (⊙-assoc ⟦ W ⟧ᴬ (pmat (φ b)) Uₘ))
      (≐-trans (⊙-cong (pmat-act W (φ b)) (≐-refl Uₘ))
      (≐-trans (⊙-assoc (pmat (act W (φ b))) ⟦ W ⟧ᴬ Uₘ)
               (λ x y → Eq.cong (λ Q → (pmat Q ⊙ V) x y)
                          (Eq.trans (Eq.cong (act W) (Eq.sym e)) (inv-act W b)))))))

  c : A
  c = V (replicate n false) (replicate n false)

  V-scal : V ≐ scal c
  V-scal = scalar V (λ i → V-comm (Xb i) (Realised.on-x realised i))
                    (λ i → V-comm (Zb i) (Realised.on-z realised i))

  -- c² = 1, V being orthogonal.
  private
    V-orth : (V ⊙ V ᵀ) ≐ Idₒ
    V-orth =
      ≐-trans (⊙-cong (≐-refl V) (ᵀ-⊙ ⟦ W ⟧ᴬ Uₘ))
      (≐-trans (⊙-assoc ⟦ W ⟧ᴬ Uₘ (Uₘ ᵀ ⊙ ⟦ W ⟧ᴬ ᵀ))
      (≐-trans (⊙-cong (≐-refl ⟦ W ⟧ᴬ) (≐-sym (⊙-assoc Uₘ (Uₘ ᵀ) (⟦ W ⟧ᴬ ᵀ))))
      (≐-trans (⊙-cong (≐-refl ⟦ W ⟧ᴬ) (⊙-cong (proj₁ orth) (≐-refl (⟦ W ⟧ᴬ ᵀ))))
      (≐-trans (⊙-cong (≐-refl ⟦ W ⟧ᴬ) (⊙-identityˡ (⟦ W ⟧ᴬ ᵀ)))
               (proj₁ (circuit-orthogonal W))))))

    0ᵇ = replicate n false

  c² : c * c ≡ 1#
  c² = begin
    c * c                          ≡⟨ AR.*-identityʳ (c * c) ⟨
    (c * c) * 1#                   ≡⟨ Eq.cong ((c * c) *_) (δb-refl 0ᵇ) ⟨
    scal (c * c) 0ᵇ 0ᵇ             ≡⟨ scal-⊙ c c 0ᵇ 0ᵇ ⟨
    (scal c ⊙ scal c) 0ᵇ 0ᵇ        ≡⟨ ⊙-cong (≐-sym V-scal) (λ x y → Eq.trans (Eq.cong (c *_) (δb-sym x y)) (Eq.sym (V-scal y x))) 0ᵇ 0ᵇ ⟩
    (V ⊙ V ᵀ) 0ᵇ 0ᵇ                ≡⟨ V-orth 0ᵇ 0ᵇ ⟩
    δb 0ᵇ 0ᵇ                       ≡⟨ δb-refl 0ᵇ ⟩
    1#                             ∎

  -- So U = c ⟦ W ⟧⁻¹, with c = ±1.
  private
    U-V : Uₘ ≐ (⟦ inv W ⟧ᴬ ⊙ V)
    U-V = ≐-sym
      (≐-trans (≐-sym (⊙-assoc ⟦ inv W ⟧ᴬ ⟦ W ⟧ᴬ Uₘ))
      (≐-trans (⊙-cong (sound (inv-l W)) (≐-refl Uₘ)) (⊙-identityˡ Uₘ)))

    U-c : Uₘ ≐ (scal c ⊙ ⟦ inv W ⟧ᴬ)
    U-c = ≐-trans U-V (≐-trans (⊙-cong (≐-refl ⟦ inv W ⟧ᴬ) V-scal) (≐-sym (scal-central c ⟦ inv W ⟧ᴬ)))

    pick : (c ≡ 1# ⊎ c ≡ - 1#) → Σ (Circuit n) λ w → ⟦ w ⟧ᴬ ≐ Uₘ
    pick (inj₁ e) = inv W , ≐-sym (≐-trans U-c
      (≐-trans (⊙-cong (λ x y → Eq.cong (_* δb x y) e) (≐-refl ⟦ inv W ⟧ᴬ))
      (≐-trans (⊙-cong scal-1 (≐-refl ⟦ inv W ⟧ᴬ)) (⊙-identityˡ ⟦ inv W ⟧ᴬ))))
    pick (inj₂ e) = neg • inv W , ≐-sym (≐-trans U-c
      (⊙-cong (λ x y → Eq.cong (_* δb x y) e) (≐-refl ⟦ inv W ⟧ᴬ)))

  circuit-of : Σ (Circuit n) λ w → ⟦ w ⟧ᴬ ≐ Uₘ
  circuit-of = pick (±1 c c²)

-- Every real Clifford operator is the matrix of a circuit.
generation : (U : Clifford n) → Σ (Circuit n) λ w → ⟦ w ⟧ᴬ ≐ proj₁ U
generation U = Generation.circuit-of U

------------------------------------------------------------------------
-- Corollary 4.16

-- The real Clifford group is the group the rules present ...
clifford≃circuits : Inverse (Clifford-setoid n) (Width.word-setoid n)
clifford≃circuits {n} = record
  { to        = λ U → proj₁ (generation U)
  ; from      = circuit
  ; to-cong   = λ {U} {U'} e → completeness
                  (≐-trans (proj₂ (generation U)) (≐-trans e (≐-sym (proj₂ (generation U')))))
  ; from-cong = sound
  ; inverse   = (λ {w} {U} e → completeness (≐-trans (proj₂ (generation U)) e))
              , (λ {U} {w} e → ≐-trans (sound e) (proj₂ (generation U)))
  }

-- ... whose elements are the normal forms ...
circuits≃nf : Inverse (Width.word-setoid n) (Eq.setoid (NF n))
circuits≃nf {n} = record
  { to        = normalise n
  ; from      = ⟦_⟧ⁿ
  ; to-cong   = λ {w} {v} e → nf-injective (normalise n w) (normalise n v)
                  (≐-trans (≐-sym (sound (normalise-ok n w))) (≐-trans (sound e) (sound (normalise-ok n v))))
  ; from-cong = λ e → Width.refl' n (Eq.cong ⟦_⟧ⁿ e)
  ; inverse   = (λ {N} {w} e → nf-injective (normalise n w) N
                   (≐-trans (≐-sym (sound (normalise-ok n w))) (sound e)))
              , (λ {w} {N} e → Width.trans (Width.refl' n (Eq.cong ⟦_⟧ⁿ e)) (Width.sym (normalise-ok n w)))
  }

-- ... of which there are 2 · ∏ᵢ₌₁ⁿ (4ⁱ + 2ⁱ − 2)(2 · 4ⁱ⁻¹): there are
-- exactly that many real stabilizer operators on n qubits.
corollary-4-16 : Inverse (Clifford-setoid n) (Eq.setoid (Fin (order n)))
corollary-4-16 {n} = Compose.inverse clifford≃circuits (Compose.inverse circuits≃nf (NF≅order n))
