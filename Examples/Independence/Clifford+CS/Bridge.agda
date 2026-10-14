------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffCS₂'s matrices against Bian and Selinger's: matrices over 𝔻[i]
-- read in 𝔻[ω], and scalars
--
-- Bian and Selinger's Clifford+CS presentations (the two-level one,
-- Examples.Groups.Clifford+CS-TwoLevel, and the 3-qubit one,
-- Examples.Groups.Clifford+CS-3qubit) have their matrices over 𝔻[i] =
-- ℤ[½,i]; CliffCS₂'s are read in 𝔻[ω] (Semantics.Reading).  A matrix
-- over 𝔻[i] is read in 𝔻[ω] entrywise (mapι, through Clifford+CS.Ring.ι),
-- which respects products and the identity and is injective.
--
-- Their scalars are ⟨i⟩ and ours ⟨ω⟩ — the paper's scalar refinement.
-- A circuit's matrix is ω^c times the reading of its encoding's, c the
-- number of its ω and H gates (H = ω K, K their γ⁻¹ [[1,1],[1,-1]]); two
-- circuits with the same matrix have c of the same parity (no ι-read
-- matrix with an entry ≠ 0 is ω times another: ω ∉ ℚ(i)), so their
-- encodings differ by a power of i (twice the difference).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Bridge where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_)
import Data.Nat.Properties as ℕP
open import Data.Nat.DivMod using (_%_ ; _/_ ; m≡m%n+[m/n]*n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Vec.Base using (replicate)
open import Data.Bool.Base using (false)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl ; cong ; sym ; trans)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

import Examples.Groups.Clifford+CS-TwoLevel.Ring as CSR
import Examples.Groups.Clifford+CS-TwoLevel.Semantics as CSS
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; module DR ; module DS ; SemiRingD ; RingD ; AdjointD ; ωᴰ ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics as TS

open import Examples.Independence.Clifford+CS.Ring using (ι ; ι-+ ; ι-* ; ι-0 ; ι-1 ; ι-i ; ι-injective ; odd-ι)
open import Examples.Independence.Clifford+CS.Syntactics using (Gate ; Gen ; Circuit)
import Examples.Independence.Clifford+CS.Semantics as Sem
open import Examples.Independence.Semantics.Reading using (⟪_⟫ ; _ᵀ ; ᵀ-cong ; matᵀ-ε ; matᵀ-∙ ; module Mat ; module Transfer)
import Examples.Independence.Semantics.Reading as Reading

private
  variable
    m n p : ℕ

------------------------------------------------------------------------
-- Matrices over 𝔻[i] read in 𝔻[ω]

mapι : Matrix m n CSR.D → Matrix m n D
mapι M = TS.mk (λ r c → ι (CSS.ent M r c))

ent-mapι : (M : Matrix m n CSR.D) (r : Fin m) (c : Fin n) → TS.ent (mapι M) r c ≡ ι (CSS.ent M r c)
ent-mapι M = TS.ent-mk (λ r c → ι (CSS.ent M r c))

ι-sum : (f : Fin n → CSR.D) → ι (CSS.sum f) ≡ TS.sum (ι ∘ f)
ι-sum {zero}  f = ι-0
ι-sum {suc n} f =
  trans (ι-+ (f zero) (CSS.sum (f ∘ suc))) (cong (ι (f zero) DR.+_) (ι-sum (f ∘ suc)))

-- (The instance at 𝔻[ω] is given: EucDomain's generic one is in scope
-- too, with the 𝔻[i] instances.)
_·ω·_ : Matrix m n D → Matrix n p D → Matrix m p D
_·ω·_ = _·*·_ ⦃ RingD ⦄

mapι-·*· : (A : Matrix m n CSR.D) (B : Matrix n p CSR.D) → mapι (A ·*· B) ≡ mapι A ·ω· mapι B
mapι-·*· A B = TS.mat-ext λ r c →
  trans (ent-mapι (A ·*· B) r c)
  (trans (cong ι (CSS.ent-·*· A B r c))
  (trans (ι-sum (λ x → CSS.ent A r x CSR.DR.* CSS.ent B x c))
  (trans (TS.sum-cong-≗ (λ x → trans (ι-* (CSS.ent A r x) (CSS.ent B x c))
                                     (sym (Eq.cong₂ DR._*_ (ent-mapι A r x) (ent-mapι B x c)))))
         (sym (TS.ent-·*· (mapι A) (mapι B) r c)))))

private
  -- (By a helper on the decision: a with on it exhausts the heap.)
  ι-δ : (r c : Fin n) → ι (CSS.δ r c) ≡ TS.δ r c
  ι-δ r c = by (r ≟ c)
    where
    by : Dec (r ≡ c) → ι (CSS.δ r c) ≡ TS.δ r c
    by (yes refl) = trans (cong ι (CSS.δ-refl r)) (trans ι-1 (sym (TS.δ-refl r)))
    by (no ne)    = trans (cong ι (CSS.δ-≢ ne)) (trans ι-0 (sym (TS.δ-≢ ne)))

mapι-𝕀 : mapι (CSS.𝕀 {n}) ≡ TS.𝕀
mapι-𝕀 = TS.mat-ext λ r c →
  trans (ent-mapι CSS.𝕀 r c) (trans (cong ι (CSS.ent-𝕀 r c)) (trans (ι-δ r c) (sym (TS.ent-𝕀 r c))))

mapι-injective : {A B : Matrix m n CSR.D} → mapι A ≡ mapι B → A ≡ B
mapι-injective {A = A} {B} e = CSS.mat-ext λ r c →
  ι-injective (trans (sym (ent-mapι A r c)) (trans (cong (λ M → TS.ent M r c) e) (ent-mapι B r c)))

------------------------------------------------------------------------
-- Powers of ω, and ω^k times a matrix

ωp : ℕ → D
ωp zero    = DR.1#
ωp (suc k) = ωᴰ DR.* ωp k

ωp-+ : (a b : ℕ) → ωp (a + b) ≡ ωp a DR.* ωp b
ωp-+ zero    b = sym (DR.*-identityˡ (ωp b))
ωp-+ (suc a) b = trans (cong (ωᴰ DR.*_) (ωp-+ a b)) (sym (DR.*-assoc ωᴰ (ωp a) (ωp b)))

opaque
  unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

  ωp-8 : ωp 8 ≡ DR.1#
  ωp-8 = refl

  -- ω² is i.
  ωp-2 : ωp 2 ≡ ι CSR.ⅈ
  ωp-2 = refl

ωs : ℕ → Matrix m n D → Matrix m n D
ωs k M = TS.mk (λ r c → ωp k DR.* TS.ent M r c)

ent-ωs : (k : ℕ) (M : Matrix m n D) (r : Fin m) (c : Fin n) →
         TS.ent (ωs k M) r c ≡ ωp k DR.* TS.ent M r c
ent-ωs k M = TS.ent-mk (λ r c → ωp k DR.* TS.ent M r c)

ωs-0 : (M : Matrix m n D) → ωs 0 M ≡ M
ωs-0 M = TS.mat-ext λ r c → trans (ent-ωs 0 M r c) (DR.*-identityˡ (TS.ent M r c))

private
  shuffle : (p q x y : D) → (p DR.* x) DR.* (q DR.* y) ≡ (p DR.* q) DR.* (x DR.* y)
  shuffle = solve 4 (λ p q x y → (p :* x) :* (q :* y) := (p :* q) :* (x :* y)) refl
    where open DS using (solve ; _:=_ ; _:*_)

ωs-· : (a b : ℕ) (A : Matrix m n D) (B : Matrix n p D) →
       ωs a A ·ω· ωs b B ≡ ωs (a + b) (A ·ω· B)
ωs-· a b A B = TS.mat-ext λ r c →
  trans (TS.ent-·*· (ωs a A) (ωs b B) r c)
  (trans (TS.sum-cong-≗ (λ x →
            trans (Eq.cong₂ DR._*_ (ent-ωs a A r x) (ent-ωs b B x c))
                  (shuffle (ωp a) (ωp b) (TS.ent A r x) (TS.ent B x c))))
  (trans (sym (TS.*-distribˡ-sum (ωp a DR.* ωp b) (λ x → TS.ent A r x DR.* TS.ent B x c)))
  (trans (Eq.cong₂ DR._*_ (sym (ωp-+ a b)) (sym (TS.ent-·*· A B r c)))
         (sym (ent-ωs (a + b) (A ·ω· B) r c)))))

ωs-ωs : (a b : ℕ) (M : Matrix m n D) → ωs a (ωs b M) ≡ ωs (a + b) M
ωs-ωs a b M = TS.mat-ext λ r c →
  trans (ent-ωs a (ωs b M) r c)
  (trans (cong (ωp a DR.*_) (ent-ωs b M r c))
  (trans (sym (DR.*-assoc (ωp a) (ωp b) (TS.ent M r c)))
  (trans (cong (DR._* TS.ent M r c) (sym (ωp-+ a b))) (sym (ent-ωs (a + b) M r c)))))

ωp-8* : (q t : ℕ) → ωp (q * 8 + t) ≡ ωp t
ωp-8* zero    t = refl
ωp-8* (suc q) t =
  trans (cong ωp (ℕP.+-assoc 8 (q * 8) t))
  (trans (ωp-+ 8 (q * 8 + t))
  (trans (Eq.cong₂ DR._*_ ωp-8 (ωp-8* q t)) (DR.*-identityˡ (ωp t))))

ωs-8* : (q t : ℕ) (M : Matrix m n D) → ωs (q * 8 + t) M ≡ ωs t M
ωs-8* q t M = TS.mat-ext λ r c →
  trans (ent-ωs (q * 8 + t) M r c) (trans (cong (DR._* TS.ent M r c) (ωp-8* q t)) (sym (ent-ωs t M r c)))

------------------------------------------------------------------------
-- A unitary matrix is not 0

-- (Stated in the ring of the semantics' own matrix algebra, CSS.AR:
-- comparing its operations with CSR.DR's on a symbolic matrix exhausts
-- the heap.)
private
  1≢0ⁱ : CSS.AR.1# ≢ CSS.AR.0#
  1≢0ⁱ ()

  -- (Every term given: a hole standing for an entry is a record of
  -- dyadic fractions, which Agda would solve by computing with them.)
  not-zero : {M : Matrix n n CSR.D} → Fin n → CSS.Unitary M →
             (∀ r c → CSS.ent M r c ≡ CSS.AR.0#) → ⊥
  not-zero {n} {M = M} o (u , _) z =
    1≢0ⁱ (trans (sym (trans (CSS.ent-𝕀 o o) (CSS.δ-refl o)))
         (trans (sym (cong (λ X → CSS.ent X o o) u))
         (trans (CSS.ent-·*· M† M o o)
                (CSS.sum-zero f (λ x → trans (cong (CSS.ent M† o x CSS.AR.*_) (z x o))
                                             (CSS.AR.zeroʳ (CSS.ent M† o x)))))))
    where
    M† = adjoint M
    f : Fin n → CSR.D
    f x = CSS.ent M† o x CSS.AR.* CSS.ent M x o

  0≡0 : CSR.DR.0# ≡ CSS.AR.0#
  0≡0 = refl

------------------------------------------------------------------------
-- Parity

private
  parity : (t : ℕ) → Σ ℕ (λ k → t ≡ k + k) ⊎ Σ ℕ (λ k → t ≡ suc (k + k))
  parity zero = inj₁ (0 , refl)
  parity (suc t) with parity t
  ... | inj₁ (k , e) = inj₂ (k , cong suc e)
  ... | inj₂ (k , e) = inj₁ (suc k , trans (cong suc e) (cong suc (sym (ℕP.+-suc k k))))

------------------------------------------------------------------------
-- Transfer with scalars

open Transfer Sem.val public using (exact)

private
  module NS = +-*-Solver
  open NS using (_:=_ ; _:+_ ; _:*_ ; con)

  -- b + (k + k) + q 8 = a + b 8, given b 7 + a = q 8 + (k + k).
  arith : (a b q t : ℕ) → b * 7 + a ≡ q * 8 + t → b + t + q * 8 ≡ a + b * 8
  arith a b q t e = begin
    b + t + q * 8          ≡⟨ NS.solve 3 (λ b t q → b :+ t :+ q :* con 8 := b :+ (q :* con 8 :+ t)) refl b t q ⟩
    b + (q * 8 + t)        ≡⟨ cong (b +_) (sym e) ⟩
    b + (b * 7 + a)        ≡⟨ NS.solve 2 (λ a b → b :+ (b :* con 7 :+ a) := a :+ b :* con 8) refl a b ⟩
    a + b * 8              ∎
    where open Eq.≡-Reasoning

module ViaS {n : ℕ} {G : Set}
  (F   : Word G → Matrix (2 ^ n) (2 ^ n) CSR.D)
  (F-ε : F ε ≡ CSS.𝕀)
  (F-• : ∀ u v → F (u • v) ≡ F u ·*· F v)
  (F-u : ∀ u → CSS.Unitary (F u))
  -- a word for i, the scalar
  (J   : Word G)
  (F-J : ∀ u → mapι (F (J • u)) ≡ ωs 2 (mapι (F u)))
  -- the encoding, a gate g being ω^(c g) times the reading of ℰ g
  (ℰ   : Gen n → Word G)
  (c   : Gen n → ℕ)
  (gen : ∀ g → Mat.mat (⟪ Sem.⟦ g ⟧₀ ⟫ ᵀ) ≡ ωs (c g) (mapι (F (ℰ g))))
  where

  ℰʷ : Circuit n → Word G
  ℰʷ [ g ]ʷ  = ℰ g
  ℰʷ ε       = ε
  ℰʷ (w • v) = ℰʷ w • ℰʷ v

  cʷ : Circuit n → ℕ
  cʷ [ g ]ʷ  = c g
  cʷ ε       = 0
  cʷ (w • v) = cʷ w + cʷ v

  bridge : (w : Circuit n) → Mat.mat (⟪ Sem.⟦ w ⟧ ⟫ ᵀ) ≡ ωs (cʷ w) (mapι (F (ℰʷ w)))
  bridge [ g ]ʷ  = gen g
  bridge ε       =
    trans (matᵀ-ε {n})
      (sym (trans (ωs-0 (mapι (F ε))) (trans (cong mapι F-ε) mapι-𝕀)))
  bridge (w • v) =
    trans (matᵀ-∙ Sem.⟦ w ⟧ Sem.⟦ v ⟧)
    (trans (Eq.cong₂ _·ω·_ (bridge w) (bridge v))
    (trans (ωs-· (cʷ w) (cʷ v) (mapι (F (ℰʷ w))) (mapι (F (ℰʷ v))))
           (cong (ωs (cʷ w + cʷ v)) (trans (sym (mapι-·*· (F (ℰʷ w)) (F (ℰʷ v))))
                                            (cong mapι (sym (F-• (ℰʷ w) (ℰʷ v))))))))

  -- i^k times a word.
  Jʷ : ℕ → Word G → Word G
  Jʷ zero    u = u
  Jʷ (suc k) u = J • Jʷ k u

  F-Jʷ : (k : ℕ) (u : Word G) → mapι (F (Jʷ k u)) ≡ ωs (k + k) (mapι (F u))
  F-Jʷ zero    u = sym (ωs-0 (mapι (F u)))
  F-Jʷ (suc k) u =
    trans (F-J (Jʷ k u))
    (trans (cong (ωs 2) (F-Jʷ k u))
    (trans (ωs-ωs 2 (k + k) (mapι (F u))) (cong (λ x → ωs (suc x) (mapι (F u))) (sym (ℕP.+-suc k k)))))

  -- Circuits with the same matrix: their encodings differ by a power
  -- of i, twice the difference of their ω counts mod 8.
  transfer : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ →
             Σ ℕ λ k → Σ ℕ λ q →
               (cʷ v + (k + k) + q * 8 ≡ cʷ w + cʷ v * 8) × (F (Jʷ k (ℰʷ w)) ≡ F (ℰʷ v))
  transfer {w} {v} e = split (parity t) (m≡m%n+[m/n]*n (b * 7 + a) 8)
    where
    a = cʷ w
    b = cʷ v
    A = F (ℰʷ w)
    B = F (ℰʷ v)
    t = (b * 7 + a) % 8
    q = (b * 7 + a) / 8

    H₀ : ωs a (mapι A) ≡ ωs b (mapι B)
    H₀ = trans (sym (bridge w)) (trans (Mat.mat-≐ (ᵀ-cong (exact e))) (bridge v))

    8b : b * 7 + b ≡ b * 8 + 0
    8b = NS.solve 1 (λ b → b :* con 7 :+ b := b :* con 8 :+ con 0) refl b

    H₁ : ωs (b * 7 + a) (mapι A) ≡ mapι B
    H₁ = trans (sym (ωs-ωs (b * 7) a (mapι A)))
         (trans (cong (ωs (b * 7)) H₀)
         (trans (ωs-ωs (b * 7) b (mapι B))
         (trans (cong (λ x → ωs x (mapι B)) 8b)
         (trans (ωs-8* b 0 (mapι B)) (ωs-0 (mapι B))))))

    H₂ : b * 7 + a ≡ t + q * 8 → ωs t (mapι A) ≡ mapι B
    H₂ d = trans (sym (ωs-8* q t (mapι A))) H₁′
      where
      H₁′ : ωs (q * 8 + t) (mapι A) ≡ mapι B
      H₁′ = trans (cong (λ x → ωs x (mapι A)) (trans (ℕP.+-comm (q * 8) t) (sym d))) H₁

    o : Fin (2 ^ n)
    o = Mat.idx (replicate n false)

    split : (Σ ℕ λ k → t ≡ k + k) ⊎ (Σ ℕ λ k → t ≡ suc (k + k)) → b * 7 + a ≡ t + q * 8 → _
    split (inj₁ (k , tk)) d =
      k , q , arith a b q (k + k) (trans d′ (cong (q * 8 +_) tk)) ,
      mapι-injective (trans (F-Jʷ k (ℰʷ w))
                            (trans (cong (λ x → ωs x (mapι A)) (sym tk)) (H₂ d)))
      where
      d′ : b * 7 + a ≡ q * 8 + t
      d′ = trans d (ℕP.+-comm t (q * 8))
    split (inj₂ (k , tk)) d = ⊥-elim (not-zero o (F-u (Jʷ k (ℰʷ w))) zero-entries)
      where
      A′ = F (Jʷ k (ℰʷ w))
      odd : ωs 1 (mapι A′) ≡ mapι B
      odd = trans (cong (ωs 1) (F-Jʷ k (ℰʷ w)))
            (trans (ωs-ωs 1 (k + k) (mapι A))
            (trans (cong (λ x → ωs x (mapι A)) (sym tk)) (H₂ d)))
      zero-entries : ∀ r c → CSS.ent A′ r c ≡ CSS.AR.0#
      zero-entries r c = trans (odd-ι (CSS.ent A′ r c) (CSS.ent B r c) entry) 0≡0
        where
        entry : ωᴰ DR.* ι (CSS.ent A′ r c) ≡ ι (CSS.ent B r c)
        entry = trans (cong (DR._* ι (CSS.ent A′ r c)) (sym (DR.*-identityʳ ωᴰ)))
                (trans (cong (ωp 1 DR.*_) (sym (ent-mapι A′ r c)))
                (trans (sym (ent-ωs 1 (mapι A′) r c))
                (trans (cong (λ X → TS.ent X r c) odd) (ent-mapι B r c))))
