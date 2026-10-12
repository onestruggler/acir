------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics of CNOT-dihedral circuits against the
-- phase-polynomial semantics of Amy, Chen and Ross
--
-- Examples.Groups.CNOT+Dihedral reads a circuit as an operator
-- x ↦ (f x , p x), a basis vector sent to a basis vector with a phase
-- ω^{p x}, words in operator order.  Its matrix, transposed, is matT:
-- row u holds ω^{p u} in column f u.  Every gate of the fragment is a
-- symmetric matrix, so reading a word in diagram order, as here, gives
-- the transpose of reading it in operator order: matT turns their
-- products into ours the other way round (matT-⊙), and a circuit's
-- matrix is matT of their operator for the same word (bridge), with no
-- factor 1/√2.  matT is injective, so two circuits with the same matrix
-- have the same operator in their sense (same-operator).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.CNOT-Dihedral.Bridge where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec.Base using ([] ; _∷_)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (toWitness ; _→?_ ; ¬?)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; wmap)

import Examples.Groups.CNOT+Dihedral.Syntactics as ACR
import Examples.Groups.CNOT+Dihedral.Semantics as A
import Examples.Groups.CNOT+Dihedral.Interpretation as AI

open import Examples.Independence.CNOT-Dihedral.Syntactics
import Examples.Independence.CNOT-Dihedral.Semantics as Sem
open import Examples.Independence.Semantics.Qubit
  using ( Q ; Op ; Digits ; R ; δ₁ ; δv ; Σv ; Σ-cong ; Σ-δˡ ; _⊙_ ; _≐_ ; Idₒ ; up
        ; ix ; ix-mul ; ix-id ; ix-up ; ix-emb ; ix-scalM ; ⊙-cong
        ; ≐-trans ; ≐-sym ; up-cong ; _^_ ; _*_ ; 1# ; 0# ; _≟_ ; √2
        ; module Circuits ; Xᵍ ; Tᵍ ; CXᵍ ; SWᵍ )
  renaming (x to ω̂)

open CommutativeRing R using (*-assoc ; *-comm ; *-identityˡ ; *-identityʳ ; zeroˡ ; zeroʳ)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Digits and bits

fB : Fin 2 → Bool
fB zero       = false
fB (suc zero) = true

bF : Bool → Fin 2
bF false = zero
bF true  = suc zero

bF-fB : (a : Fin 2) → bF (fB a) ≡ a
bF-fB zero       = refl
bF-fB (suc zero) = refl

toB : Digits n → A.Bits n
toB []      = []
toB (a ∷ u) = fB a ∷ toB u

toD : A.Bits n → Digits n
toD []      = []
toD (b ∷ c) = bF b ∷ toD c

toD-toB : (u : Digits n) → toD (toB u) ≡ u
toD-toB []      = refl
toD-toB (a ∷ u) = Eq.cong₂ _∷_ (bF-fB a) (toD-toB u)

toB-toD : (c : A.Bits n) → toB (toD c) ≡ c
toB-toD []          = refl
toB-toD (false ∷ c) = Eq.cong (false ∷_) (toB-toD c)
toB-toD (true ∷ c)  = Eq.cong (true ∷_) (toB-toD c)

------------------------------------------------------------------------
-- Deltas and phases

δ₁-sym : (a b : Fin k) → δ₁ a b ≡ δ₁ b a
δ₁-sym zero    zero    = refl
δ₁-sym zero    (suc b) = refl
δ₁-sym (suc a) zero    = refl
δ₁-sym (suc a) (suc b) = δ₁-sym a b

δv-sym : (u v : Digits n) → δv u v ≡ δv v u
δv-sym []      []      = refl
δv-sym (a ∷ u) (b ∷ v) = Eq.cong₂ _*_ (δ₁-sym a b) (δv-sym u v)

δ₁-refl : (a : Fin k) → δ₁ a a ≡ 1#
δ₁-refl zero    = refl
δ₁-refl (suc a) = δ₁-refl a

δv-refl : (u : Digits n) → δv u u ≡ 1#
δv-refl []      = refl
δv-refl (a ∷ u) = Eq.trans (Eq.cong₂ _*_ (δ₁-refl a) (δv-refl u)) (*-identityˡ 1#)

δ₁-≢ : {a b : Fin k} → a ≢ b → δ₁ a b ≡ 0#
δ₁-≢ {a = zero}  {zero}  ne = ⊥-elim (ne refl)
δ₁-≢ {a = zero}  {suc b} ne = refl
δ₁-≢ {a = suc a} {zero}  ne = refl
δ₁-≢ {a = suc a} {suc b} ne = δ₁-≢ λ e → ne (Eq.cong suc e)

δv-≢ : {u v : Digits n} → u ≢ v → δv u v ≡ 0#
δv-≢ {u = []}    {[]}    ne = ⊥-elim (ne refl)
δv-≢ {u = a ∷ u} {b ∷ v} ne = cases (a FinP.≟ b)
  where
  cases : Dec (a ≡ b) → δ₁ a b * δv u v ≡ 0#
  cases (yes refl) =
    Eq.trans (Eq.cong (δ₁ a a *_) (δv-≢ λ e → ne (Eq.cong (a ∷_) e))) (zeroʳ (δ₁ a a))
  cases (no a≢b) = Eq.trans (Eq.cong (_* δv u v) (δ₁-≢ a≢b)) (zeroˡ (δv u v))

-- The phase ω^a.
ph : A.ℤ₈ → Q
ph a = ω̂ ^ toℕ a

private
  ph-+ : (a b : A.ℤ₈) → ph (a A.+ b) ≡ ph a * ph b
  ph-+ = toWitness {a? = FinP.all? λ a → FinP.all? λ b → ph (a A.+ b) ≟ ph a * ph b} tt

  ph-inj : (a b : A.ℤ₈) → ph a ≡ ph b → a ≡ b
  ph-inj = toWitness {a? = FinP.all? λ a → FinP.all? λ b → (ph a ≟ ph b) →? (a FinP.≟ b)} tt

  ph-nz : (a : A.ℤ₈) → ph a ≢ 0#
  ph-nz = toWitness {a? = FinP.all? λ a → ¬? (ph a ≟ 0#)} tt

------------------------------------------------------------------------
-- The transposed matrix of an operator

matT : A.Op n → Op n
matT M u v = δv v (toD (proj₁ (M (toB u)))) * ph (proj₂ (M (toB u)))

matT-cong : {M N : A.Op n} → M A.≐ N → matT M ≐ matT N
matT-cong {M = M} {N} e u v =
  Eq.cong (λ p → δv v (toD (proj₁ p)) * ph (proj₂ p)) (e (toB u))

private
  swap* : (a b c : Q) → a * (b * c) ≡ b * (a * c)
  swap* a b c =
    Eq.trans (Eq.sym (*-assoc a b c))
      (Eq.trans (Eq.cong (_* c) (*-comm a b)) (*-assoc b a c))

-- Their products, ours the other way round.
matT-⊙ : (M N : A.Op n) → matT (M A.⊙ N) ≐ (matT N ⊙ matT M)
matT-⊙ M N u v = Eq.sym (begin
  Σv (λ z → (δv z d * ph pN) * matT M z v)
    ≡⟨ Σ-cong (λ z → Eq.trans (*-assoc (δv z d) (ph pN) (matT M z v))
                               (Eq.cong (_* (ph pN * matT M z v)) (δv-sym z d))) ⟩
  Σv (λ z → δv d z * (ph pN * matT M z v))
    ≡⟨ Σ-δˡ d (λ z → ph pN * matT M z v) ⟩
  ph pN * matT M d v
    ≡⟨ Eq.cong (λ c → ph pN * (δv v (toD (proj₁ (M c))) * ph (proj₂ (M c)))) (toB-toD fN) ⟩
  ph pN * (δv v (toD fM) * ph pM)
    ≡⟨ swap* (ph pN) (δv v (toD fM)) (ph pM) ⟩
  δv v (toD fM) * (ph pN * ph pM)
    ≡⟨ Eq.cong (δv v (toD fM) *_) (Eq.sym (ph-+ pN pM)) ⟩
  δv v (toD fM) * ph (pN A.+ pM) ∎)
  where
  open Eq.≡-Reasoning
  fN = proj₁ (N (toB u))
  pN = proj₂ (N (toB u))
  d  = toD fN
  fM = proj₁ (M fN)
  pM = proj₂ (M fN)

matT-Id : matT (A.Idₒ {n}) ≐ Idₒ
matT-Id u v =
  Eq.trans (Eq.cong (λ c → δv v c * ph A.0₈) (toD-toB u))
    (Eq.trans (*-identityʳ (δv v u)) (δv-sym v u))

matT-up : (M : A.Op n) → matT (A.up M) ≐ up (matT M)
matT-up M (a ∷ u) (b ∷ v) = begin
  (δ₁ b (bF (fB a)) * δv v e) * ph p
    ≡⟨ Eq.cong (λ c → (δ₁ b c * δv v e) * ph p) (bF-fB a) ⟩
  (δ₁ b a * δv v e) * ph p
    ≡⟨ *-assoc (δ₁ b a) (δv v e) (ph p) ⟩
  δ₁ b a * (δv v e * ph p)
    ≡⟨ Eq.cong (_* (δv v e * ph p))
               (Eq.trans (δ₁-sym b a) (Eq.sym (*-identityʳ (δ₁ a b)))) ⟩
  (δ₁ a b * 1#) * (δv v e * ph p) ∎
  where
  open Eq.≡-Reasoning
  e = toD (proj₁ (M (toB u)))
  p = proj₂ (M (toB u))

------------------------------------------------------------------------
-- The gates

private
  -- The rest of the wires, untouched.
  tail₁ : (c d : Q) (q : A.ℤ₈) (u v : Digits n) → c ≡ d * ph q →
          c * δv u v ≡ (d * δv v (toD (toB u))) * ph q
  tail₁ c d q u v e = begin
    c * δv u v                        ≡⟨ Eq.cong₂ _*_ e (Eq.trans (δv-sym u v) (Eq.cong (δv v) (Eq.sym (toD-toB u)))) ⟩
    (d * ph q) * δv v (toD (toB u))   ≡⟨ *-assoc d (ph q) _ ⟩
    d * (ph q * δv v (toD (toB u)))   ≡⟨ Eq.cong (d *_) (*-comm (ph q) _) ⟩
    d * (δv v (toD (toB u)) * ph q)   ≡⟨ Eq.sym (*-assoc d _ (ph q)) ⟩
    (d * δv v (toD (toB u))) * ph q   ∎
    where open Eq.≡-Reasoning

  tail₂ : (c d₀ d₁ : Q) (q : A.ℤ₈) (u v : Digits n) → c ≡ (d₀ * d₁) * ph q →
          c * δv u v ≡ (d₀ * (d₁ * δv v (toD (toB u)))) * ph q
  tail₂ c d₀ d₁ q u v e =
    Eq.trans (tail₁ c (d₀ * d₁) q u v e)
             (Eq.cong (_* ph q) (*-assoc d₀ d₁ _))

  Tph : Fin 2 → A.ℤ₈
  Tph a = if fB a then A.1₈ else A.0₈

  X-tab : (a b : Fin 2) → ix (proj₂ Xᵍ) (a ∷ []) (b ∷ []) ≡ δ₁ b (bF (not (fB a))) * ph A.0₈
  X-tab zero       zero       = refl
  X-tab zero       (suc zero) = refl
  X-tab (suc zero) zero       = refl
  X-tab (suc zero) (suc zero) = refl

  T-tab : (a b : Fin 2) → ix (proj₂ Tᵍ) (a ∷ []) (b ∷ []) ≡ δ₁ b (bF (fB a)) * ph (Tph a)
  T-tab zero       zero       = refl
  T-tab zero       (suc zero) = refl
  T-tab (suc zero) zero       = refl
  T-tab (suc zero) (suc zero) = refl

  CX-tab : (a₀ a₁ b₀ b₁ : Fin 2) →
           ix (proj₂ CXᵍ) (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []) ≡
           (δ₁ b₀ (bF (fB a₁ xor fB a₀)) * δ₁ b₁ (bF (fB a₁))) * ph A.0₈
  CX-tab zero       zero       zero       zero       = refl
  CX-tab zero       zero       zero       (suc zero) = refl
  CX-tab zero       zero       (suc zero) zero       = refl
  CX-tab zero       zero       (suc zero) (suc zero) = refl
  CX-tab zero       (suc zero) zero       zero       = refl
  CX-tab zero       (suc zero) zero       (suc zero) = refl
  CX-tab zero       (suc zero) (suc zero) zero       = refl
  CX-tab zero       (suc zero) (suc zero) (suc zero) = refl
  CX-tab (suc zero) zero       zero       zero       = refl
  CX-tab (suc zero) zero       zero       (suc zero) = refl
  CX-tab (suc zero) zero       (suc zero) zero       = refl
  CX-tab (suc zero) zero       (suc zero) (suc zero) = refl
  CX-tab (suc zero) (suc zero) zero       zero       = refl
  CX-tab (suc zero) (suc zero) zero       (suc zero) = refl
  CX-tab (suc zero) (suc zero) (suc zero) zero       = refl
  CX-tab (suc zero) (suc zero) (suc zero) (suc zero) = refl

  SW-tab : (a₀ a₁ b₀ b₁ : Fin 2) →
           ix (proj₂ SWᵍ) (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []) ≡
           (δ₁ b₀ (bF (fB a₁)) * δ₁ b₁ (bF (fB a₀))) * ph A.0₈
  SW-tab zero       zero       zero       zero       = refl
  SW-tab zero       zero       zero       (suc zero) = refl
  SW-tab zero       zero       (suc zero) zero       = refl
  SW-tab zero       zero       (suc zero) (suc zero) = refl
  SW-tab zero       (suc zero) zero       zero       = refl
  SW-tab zero       (suc zero) zero       (suc zero) = refl
  SW-tab zero       (suc zero) (suc zero) zero       = refl
  SW-tab zero       (suc zero) (suc zero) (suc zero) = refl
  SW-tab (suc zero) zero       zero       zero       = refl
  SW-tab (suc zero) zero       zero       (suc zero) = refl
  SW-tab (suc zero) zero       (suc zero) zero       = refl
  SW-tab (suc zero) zero       (suc zero) (suc zero) = refl
  SW-tab (suc zero) (suc zero) zero       zero       = refl
  SW-tab (suc zero) (suc zero) zero       (suc zero) = refl
  SW-tab (suc zero) (suc zero) (suc zero) zero       = refl
  SW-tab (suc zero) (suc zero) (suc zero) (suc zero) = refl

------------------------------------------------------------------------
-- Letters: ours to theirs

ιg : PGate k → ACR.Gate k
ιg ⌈ ω-gate ⌉  = ACR.ω-gate
ιg ⌈ X-gate ⌉  = ACR.X-gate
ιg ⌈ T-gate ⌉  = ACR.T-gate
ιg ⌈ CX-gate ⌉ = ACR.CNOT-gate
ιg swap        = ACR.SWAP-gate

ι⁻ : Gen n → ACR.Gen n
ι⁻ (gate₀ g) = ACR.gate₀ (ιg g)
ι⁻ (gate₁ g) = ACR.gate₁ (ιg g)
ι⁻ (gate₂ g) = ACR.gate₂ (ιg g)
ι⁻ (g ↥)     = ι⁻ g ACR.↥

------------------------------------------------------------------------
-- Every circuit: no factor 1/√2, and the transposed matrix of their
-- operator

gen-h : (g : Gen n) → proj₁ (Sem.⟦ g ⟧₀) ≡ 0
gen-h (gate₀ ⌈ ω-gate ⌉)  = refl
gen-h (gate₁ ⌈ X-gate ⌉)  = refl
gen-h (gate₁ ⌈ T-gate ⌉)  = refl
gen-h (gate₂ ⌈ CX-gate ⌉) = refl
gen-h (gate₂ swap)        = refl
gen-h (g ↥)               = gen-h g

gen-ok : (g : Gen n) → ix (proj₂ (Sem.⟦ g ⟧₀)) ≐ matT (AI.⟦ ι⁻ g ⟧ᵍ)
gen-ok {n} (gate₀ ⌈ ω-gate ⌉) u v =
  Eq.trans (ix-scalM {n} ω̂ u v)
    (Eq.trans (*-comm ω̂ (δv u v))
      (Eq.cong (_* ω̂) (Eq.trans (δv-sym u v) (Eq.cong (δv v) (Eq.sym (toD-toB u))))))
gen-ok (gate₁ ⌈ X-gate ⌉) (a ∷ u) (b ∷ v) =
  Eq.trans (ix-emb {1} (proj₂ Xᵍ) (a ∷ u) (b ∷ v))
    (tail₁ (ix (proj₂ Xᵍ) (a ∷ []) (b ∷ [])) (δ₁ b (bF (not (fB a)))) A.0₈ u v (X-tab a b))
gen-ok (gate₁ ⌈ T-gate ⌉) (a ∷ u) (b ∷ v) =
  Eq.trans (ix-emb {1} (proj₂ Tᵍ) (a ∷ u) (b ∷ v))
    (tail₁ (ix (proj₂ Tᵍ) (a ∷ []) (b ∷ [])) (δ₁ b (bF (fB a))) (Tph a) u v (T-tab a b))
gen-ok (gate₂ ⌈ CX-gate ⌉) (a₀ ∷ a₁ ∷ u) (b₀ ∷ b₁ ∷ v) =
  Eq.trans (ix-emb {2} (proj₂ CXᵍ) (a₀ ∷ a₁ ∷ u) (b₀ ∷ b₁ ∷ v))
    (tail₂ (ix (proj₂ CXᵍ) (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []))
           (δ₁ b₀ (bF (fB a₁ xor fB a₀))) (δ₁ b₁ (bF (fB a₁))) A.0₈ u v
           (CX-tab a₀ a₁ b₀ b₁))
gen-ok (gate₂ swap) (a₀ ∷ a₁ ∷ u) (b₀ ∷ b₁ ∷ v) =
  Eq.trans (ix-emb {2} (proj₂ SWᵍ) (a₀ ∷ a₁ ∷ u) (b₀ ∷ b₁ ∷ v))
    (tail₂ (ix (proj₂ SWᵍ) (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []))
           (δ₁ b₀ (bF (fB a₁))) (δ₁ b₁ (bF (fB a₀))) A.0₈ u v
           (SW-tab a₀ a₁ b₀ b₁))
gen-ok (g ↥) =
  ≐-trans (ix-up (proj₂ Sem.⟦ g ⟧₀))
    (≐-trans (up-cong (gen-ok g)) (≐-sym (matT-up AI.⟦ ι⁻ g ⟧ᵍ)))

bridge : (w : Circuit n) →
         (proj₁ Sem.⟦ w ⟧ ≡ 0) × (ix (proj₂ Sem.⟦ w ⟧) ≐ matT (AI.⟦ wmap ι⁻ w ⟧))
bridge [ g ]ʷ =
  gen-h g , ≐-trans (gen-ok g) (matT-cong (λ c → Eq.sym (AI.⟦⟧-gen (ι⁻ g) c)))
bridge ε =
  refl , ≐-trans ix-id (≐-trans (≐-sym matT-Id) (matT-cong (λ c → Eq.sym (AI.⟦⟧-ε c))))
bridge (w • w′) =
  Eq.cong₂ _+ℕ_ (proj₁ (bridge w)) (proj₁ (bridge w′)) ,
  ≐-trans (ix-mul (proj₂ Sem.⟦ w′ ⟧) (proj₂ Sem.⟦ w ⟧))
    (≐-trans (⊙-cong (proj₂ (bridge w′)) (proj₂ (bridge w)))
      (≐-trans (≐-sym (matT-⊙ AI.⟦ wmap ι⁻ w ⟧ AI.⟦ wmap ι⁻ w′ ⟧))
               (matT-cong (λ c → Eq.sym (AI.⟦⟧-• (wmap ι⁻ w) (wmap ι⁻ w′) c)))))

------------------------------------------------------------------------
-- matT is injective

matT-inj : (M N : A.Op n) → matT M ≐ matT N → M A.≐ N
matT-inj M N e c = go (VecP.≡-dec FinP._≟_ fM fN)
  where
  fM = toD (proj₁ (M c))
  fN = toD (proj₁ (N c))
  pM = proj₂ (M c)
  pN = proj₂ (N c)

  -- The row of c.
  row : ∀ v → δv v fM * ph pM ≡ δv v fN * ph pN
  row = Eq.subst (λ d → ∀ v → δv v (toD (proj₁ (M d))) * ph (proj₂ (M d)) ≡
                               δv v (toD (proj₁ (N d))) * ph (proj₂ (N d)))
                 (toB-toD c) (e (toD c))

  -- Read at M's column.
  at : ph pM ≡ δv fM fN * ph pN
  at = Eq.trans (Eq.sym (*-identityˡ (ph pM)))
         (Eq.trans (Eq.cong (_* ph pM) (Eq.sym (δv-refl fM))) (row fM))

  go : Dec (fM ≡ fN) → M c ≡ N c
  go (yes same) = Eq.cong₂ _,_ fs (ph-inj pM pN phs)
    where
    fs : proj₁ (M c) ≡ proj₁ (N c)
    fs = Eq.trans (Eq.sym (toB-toD _)) (Eq.trans (Eq.cong toB same) (toB-toD _))

    phs : ph pM ≡ ph pN
    phs = Eq.trans at
            (Eq.trans (Eq.cong (λ d → δv fM d * ph pN) (Eq.sym same))
              (Eq.trans (Eq.cong (_* ph pN) (δv-refl fM)) (*-identityˡ (ph pN))))
  go (no differ) =
    ⊥-elim (ph-nz pM (Eq.trans at (Eq.trans (Eq.cong (_* ph pN) (δv-≢ differ))
                                            (zeroˡ (ph pN)))))

------------------------------------------------------------------------
-- Equal matrices, equal operators

open Circuits Sem.val using (module Exact)

private
  unscale : {hw hv : ℕ} {a b : Q} → hw ≡ 0 → hv ≡ 0 →
            √2 ^ hv * a ≡ (ω̂ ^ 0 * √2 ^ hw) * b → a ≡ b
  unscale {a = a} {b} refl refl e =
    Eq.trans (Eq.sym (*-identityˡ a))
      (Eq.trans e (Eq.trans (Eq.cong (_* b) (*-identityˡ 1#)) (*-identityˡ b)))

same-operator : (w v : Circuit n) → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ →
                AI.⟦ wmap ι⁻ w ⟧ A.≐ AI.⟦ wmap ι⁻ v ⟧
same-operator w v (Exact.phased _ refl agree) =
  matT-inj _ _ λ i j →
    Eq.trans (Eq.sym (proj₂ (bridge w) i j))
      (Eq.trans (unscale (proj₁ (bridge w)) (proj₁ (bridge v)) (agree i j))
                (proj₂ (bridge v) i j))
