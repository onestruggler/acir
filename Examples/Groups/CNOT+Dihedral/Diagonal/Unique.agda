------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical forms of the wire-0 part are unique
--
-- The form T ^ a • F β γ is diagonal, with phase 0 when x₀ = 0 and
--
--     a + Σⱼ xⱼ (2 βⱼ + 4 Σₖ>ⱼ γⱼₖ xₖ)        when x₀ = 1        (DS-E)
--
-- (qF, qC).  Its data are read back from this function one wire at a
-- time: with x₁ = 0 the rest is the form one wire down; with x₁ = 1 and
-- the other wires 0 it is β₁ (doubled, which is injective on ℤ₄); and
-- with x₁ = 1 the rest are the CCZ coefficients γ₁ₖ (E-unique).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.Unique where

open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ ; ∧-identityʳ)
open import Data.Fin.Properties using (all?)
open import Relation.Nullary.Decidable using (toWitness)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sucF)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec ; [] ; _∷_ ; head ; tail ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.CNOT+Dihedral.Semantics
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Interpretation
open import Examples.Groups.CNOT+Dihedral.Evaluation
open import Examples.Groups.CNOT+Dihedral.Affine using (PS ; PS-• ; PS-↑)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Calculus using (toPE)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Gates using (CS ; CCZ ; dCS ; dCCZ ; πL ; πR)
open import Examples.Groups.CNOT+Dihedral.Diagonal.EForm using (Tri ; cz ; C3B ; F)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Decompose using (EData ; E)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Semantics

private
  variable
    n m k : ℕ

------------------------------------------------------------------------
-- Constants and arithmetic

2₈ 4₈ : ℤ₈
2₈ = sucF (sucF 0F)
4₈ = sucF (sucF (sucF (sucF 0F)))

dbl : Fin 4 → ℤ₈
dbl 0F                       = 0₈
dbl (sucF 0F)                = 2₈
dbl (sucF (sucF 0F))         = 4₈
dbl (sucF (sucF (sucF 0F)))  = sucF (sucF (sucF (sucF (sucF (sucF 0F)))))

dbl-injective : (b b' : Fin 4) → dbl b ≡ dbl b' → b ≡ b'
dbl-injective 0F 0F e = Eq.refl
dbl-injective (sucF 0F) (sucF 0F) e = Eq.refl
dbl-injective (sucF (sucF 0F)) (sucF (sucF 0F)) e = Eq.refl
dbl-injective (sucF (sucF (sucF 0F))) (sucF (sucF (sucF 0F))) e = Eq.refl
dbl-injective 0F (sucF 0F) ()
dbl-injective 0F (sucF (sucF 0F)) ()
dbl-injective 0F (sucF (sucF (sucF 0F))) ()
dbl-injective (sucF 0F) 0F ()
dbl-injective (sucF 0F) (sucF (sucF 0F)) ()
dbl-injective (sucF 0F) (sucF (sucF (sucF 0F))) ()
dbl-injective (sucF (sucF 0F)) 0F ()
dbl-injective (sucF (sucF 0F)) (sucF 0F) ()
dbl-injective (sucF (sucF 0F)) (sucF (sucF (sucF 0F))) ()
dbl-injective (sucF (sucF (sucF 0F))) 0F ()
dbl-injective (sucF (sucF (sucF 0F))) (sucF 0F) ()
dbl-injective (sucF (sucF (sucF 0F))) (sucF (sucF 0F)) ()

-- Powers of a constant phase.
powφ-at : ∀ {φ : Bits n → ℤ₈} {x c} → φ x ≡ c → (k : ℕ) → powφ k φ x ≡ powφ k (λ _ → c) x
powφ-at e zero          = Eq.refl
powφ-at e (suc zero)    = e
powφ-at e (suc (suc k)) = Eq.cong₂ _+_ (powφ-at e (suc k)) e

powφ-0 : (k : ℕ) (x : Bits n) → powφ k (λ _ → 0₈) x ≡ 0₈
powφ-0 zero          x = Eq.refl
powφ-0 (suc zero)    x = Eq.refl
powφ-0 (suc (suc k)) x = Eq.trans (+-identityʳ (powφ (suc k) (λ _ → 0₈) x)) (powφ-0 (suc k) x)

powφ-1 : (a : ℤ₈) (x : Bits n) → powφ (toℕ a) (λ _ → 1₈) x ≡ a
powφ-1 0F x = Eq.refl
powφ-1 (sucF 0F) x = Eq.refl
powφ-1 (sucF (sucF 0F)) x = Eq.refl
powφ-1 (sucF (sucF (sucF 0F))) x = Eq.refl
powφ-1 (sucF (sucF (sucF (sucF 0F)))) x = Eq.refl
powφ-1 (sucF (sucF (sucF (sucF (sucF 0F))))) x = Eq.refl
powφ-1 (sucF (sucF (sucF (sucF (sucF (sucF 0F)))))) x = Eq.refl
powφ-1 (sucF (sucF (sucF (sucF (sucF (sucF (sucF 0F))))))) x = Eq.refl

powφ-2 : (b : Fin 4) (x : Bits n) → powφ (toℕ b) (λ _ → 2₈) x ≡ dbl b
powφ-2 0F x = Eq.refl
powφ-2 (sucF 0F) x = Eq.refl
powφ-2 (sucF (sucF 0F)) x = Eq.refl
powφ-2 (sucF (sucF (sucF 0F))) x = Eq.refl

------------------------------------------------------------------------
-- Diagonal operators conjugated by permutations

DS-ext : ∀ {w : Circuit n} {φ ψ} → DS w φ → (∀ x → φ x ≡ ψ x) → DS w ψ
DS-ext d e x = Eq.trans (d x) (Eq.cong (_ ,_) (e x))

DS-conj : ∀ {σ σ' X : Circuit n} {f g φ} → PS σ f → PS σ' g → (∀ x → g (f x) ≡ x) →
          DS X φ → DS (σ' • X • σ) (λ x → φ (f x))
DS-conj {σ = σ} {σ'} {X} {f} {g} {φ} pσ pσ' gf dX x = Eq.cong₂ _,_ fn-eq ph-eq
  where
  fσ : fn σ x ≡ f x
  fσ = Eq.cong proj₁ (pσ x)
  fn-eq : fn (σ' • X • σ) x ≡ x
  fn-eq = Eq.trans (fn-• σ' (X • σ) x)
          (Eq.trans (Eq.cong (fn σ') (fn-• X σ x))
          (Eq.trans (Eq.cong (λ v → fn σ' (fn X v)) fσ)
          (Eq.trans (Eq.cong (λ v → fn σ' (proj₁ v)) (dX (f x)))
          (Eq.trans (Eq.cong proj₁ (pσ' (f x))) (gf x)))))
  ph-eq : ph (σ' • X • σ) x ≡ φ (f x)
  ph-eq = Eq.trans (ph-• σ' (X • σ) x)
          (Eq.trans (Eq.cong₂ _+_
                       (Eq.trans (ph-• X σ x)
                         (Eq.trans (Eq.cong₂ _+_ (Eq.cong proj₂ (pσ x))
                                      (Eq.trans (Eq.cong (ph X) fσ) (Eq.cong proj₂ (dX (f x)))))
                                   (+-identityˡ (φ (f x)))))
                       (Eq.trans (Eq.cong (ph σ') (Eq.trans (fn-• X σ x)
                                    (Eq.trans (Eq.cong (fn X) fσ) (Eq.cong proj₁ (dX (f x))))))
                                 (Eq.cong proj₂ (pσ' (f x)))))
                    (+-identityʳ (φ (f x))))

private
  sw01 : Bits (₂₊ n) → Bits (₂₊ n)
  sw01 v = head (tail v) ∷ head v ∷ tail (tail v)

  PS-SWAP : PS {₂₊ n} SWAP sw01
  PS-SWAP (a ∷ b ∷ y) = ⟦⟧-gen SWAP-gen (a ∷ b ∷ y)

  fR fL : Bits (₃₊ n) → Bits (₃₊ n)
  fR x = sw01 (head x ∷ sw01 (tail x))
  fL x = head (sw01 x) ∷ sw01 (tail (sw01 x))

  PS-πR : PS {₃₊ n} πR fR
  PS-πR = PS-• PS-SWAP (PS-↑ PS-SWAP)

  PS-πL : PS {₃₊ n} πL fL
  PS-πL = PS-• (PS-↑ PS-SWAP) PS-SWAP

  fLR : (x : Bits (₃₊ n)) → fL (fR x) ≡ x
  fLR (a ∷ b ∷ c ∷ y) = Eq.refl

DS-π : ∀ {X : Circuit (₂₊ n)} {φ} → DS X φ →
       DS (πL • X ↑ • πR) (λ x → φ (tail (fR x)))
DS-π d = DS-conj PS-πR PS-πL fLR (DS-↑ d)

------------------------------------------------------------------------
-- The phases of CS and CCZ

private
  φCS : Bits (₂₊ n) → ℤ₈
  φCS = φₑ (toPE dCS)

  φCS-at : (a b : Bool) (y : Bits n) → φCS (a ∷ b ∷ y) ≡ (if a ∧ b then 2₈ else 0₈)
  φCS-at true  true  y = Eq.refl
  φCS-at true  false y = Eq.refl
  φCS-at false true  y = Eq.refl
  φCS-at false false y = Eq.refl

  φCCZ : Bits (₃₊ n) → ℤ₈
  φCCZ = φₑ (toPE dCCZ)

  φCCZ-at : (a b c : Bool) (y : Bits n) → φCCZ (a ∷ b ∷ c ∷ y) ≡ (if a ∧ b ∧ c then 4₈ else 0₈)
  φCCZ-at true  true  true  y = Eq.refl
  φCCZ-at true  true  false y = Eq.refl
  φCCZ-at true  false true  y = Eq.refl
  φCCZ-at true  false false y = Eq.refl
  φCCZ-at false true  true  y = Eq.refl
  φCCZ-at false true  false y = Eq.refl
  φCCZ-at false false true  y = Eq.refl
  φCCZ-at false false false y = Eq.refl

------------------------------------------------------------------------
-- The phases of the forms

-- The CCZ part, with wires 0 and 1 set.
qC : Vec Bool m → Bits m → ℤ₈
qC []       []      = 0₈
qC (c ∷ cs) (x ∷ y) = (if c ∧ x then 4₈ else 0₈) + qC cs y

-- The F part, with wire 0 set.
qF : Vec (Fin 4) k → Tri k → Bits k → ℤ₈
qF []       tt       []       = 0₈
qF (b ∷ bs) (c , cs) (x ∷ y)  = (if x then dbl b + qC c y else 0₈) + qF bs cs y

private
  zero-if : (b : Bool) → 0₈ ≡ (if b then 0₈ else 0₈)
  zero-if true  = Eq.refl
  zero-if false = Eq.refl

  -- A right cancellation and two rearrangements in ℤ₈.
  +-cancelʳ : (a b c : ℤ₈) → a + c ≡ b + c → a ≡ b
  +-cancelʳ a b c e = +-cancelˡ c a b (Eq.trans (+-comm c a) (Eq.trans e (+-comm b c)))

  swap₃ : (p q d : ℤ₈) → (p + q) + d ≡ (d + p) + q
  swap₃ = toWitness {a? = all? λ p → all? λ q → all? λ d → ((p + q) + d) ≟₈ ((d + p) + q)} _

DS-C3B : (cs : Vec Bool m) →
         DS (C3B cs) (λ x → if head x ∧ head (tail x) then qC cs (tail (tail x)) else 0₈)
DS-C3B [] = DS-ext DS-ε λ { (a ∷ b ∷ []) → zero-if (a ∧ b) }
DS-C3B {suc m} (c ∷ cs) =
  DS-ext (DS-• (DS-cz c) (DS-π (DS-C3B cs))) λ { (a ∷ b ∷ d ∷ y) → lemma a b d y }
  where
  DS-cz : (c : Bool) → DS {₃₊ m} (cz c)
          (λ x → if c ∧ head x ∧ head (tail x) ∧ head (tail (tail x)) then 4₈ else 0₈)
  DS-cz true  = DS-ext (DS-D dCCZ) λ { (a ∷ b ∷ d ∷ y) → φCCZ-at a b d y }
  DS-cz false = DS-ext DS-ε λ _ → Eq.refl
  c∧F : 0₈ + (if c ∧ false then 4₈ else 0₈) ≡ 0₈
  c∧F = Eq.cong (λ z → 0₈ + (if z then 4₈ else 0₈)) (∧-zeroʳ c)
  lemma : (a b d : Bool) (y : Bits m) →
          (if a ∧ b then qC cs y else 0₈) + (if c ∧ a ∧ b ∧ d then 4₈ else 0₈) ≡
          (if a ∧ b then (if c ∧ d then 4₈ else 0₈) + qC cs y else 0₈)
  lemma true  true  d y = +-comm (qC cs y) (if c ∧ d then 4₈ else 0₈)
  lemma true  false d y = c∧F
  lemma false b     d y = c∧F

DS-F : (bs : Vec (Fin 4) k) (cs : Tri k) →
       DS (F bs cs) (λ x → if head x then qF bs cs (tail x) else 0₈)
DS-F [] tt = DS-ext DS-ε λ { (a ∷ []) → zero-if a }
DS-F {suc k} (b ∷ bs) (c , cs) =
  DS-ext (DS-• (DS-^ (DS-D dCS) (toℕ b)) (DS-• (DS-swap (DS-F bs cs)) (DS-C3B c)))
    λ { (a ∷ b' ∷ y) →
        Eq.trans (Eq.cong (λ z → ((if a ∧ b' then qC c y else 0₈) + (if a then qF bs cs y else 0₈)) + z)
                          (powφ-at (φCS-at a b' y) (toℕ b)))
                 (lemma a b' y) }
  where
  lemma : (a b' : Bool) (y : Bits k) →
          ((if a ∧ b' then qC c y else 0₈) + (if a then qF bs cs y else 0₈)) +
            powφ (toℕ b) (λ _ → if a ∧ b' then 2₈ else 0₈) (a ∷ b' ∷ y) ≡
          (if a then (if b' then dbl b + qC c y else 0₈) + qF bs cs y else 0₈)
  lemma true true y =
    Eq.trans (Eq.cong ((qC c y + qF bs cs y) +_) (powφ-2 b (true ∷ true ∷ y)))
             (swap₃ (qC c y) (qF bs cs y) (dbl b))
  lemma true false y =
    Eq.trans (Eq.cong ((0₈ + qF bs cs y) +_) (powφ-0 (toℕ b) (true ∷ false ∷ y)))
             (+-identityʳ (0₈ + qF bs cs y))
  lemma false b' y = Eq.cong ((0₈ + 0₈) +_) (powφ-0 (toℕ b) (false ∷ b' ∷ y))

DS-E : (e : EData k) →
       DS (E e) (λ x → if head x then proj₁ e + qF (proj₁ (proj₂ e)) (proj₂ (proj₂ e)) (tail x) else 0₈)
DS-E (a , bs , cs) = DS-ext (DS-• (DS-^ DS-T (toℕ a)) (DS-F bs cs)) λ
  { (true ∷ y) →
      Eq.trans (Eq.cong (qF bs cs y +_) (Eq.trans (powφ-at Eq.refl (toℕ a)) (powφ-1 a (true ∷ y))))
               (+-comm (qF bs cs y) a)
  ; (false ∷ y) →
      Eq.cong (0₈ +_) (Eq.trans (powφ-at Eq.refl (toℕ a)) (powφ-0 (toℕ a) (false ∷ y))) }

------------------------------------------------------------------------
-- Uniqueness

qC-zeros : (cs : Vec Bool m) → qC cs (replicate m false) ≡ 0₈
qC-zeros []       = Eq.refl
qC-zeros (c ∷ cs) =
  Eq.trans (Eq.cong₂ (λ z w → (if z then 4₈ else 0₈) + w) (∧-zeroʳ c) (qC-zeros cs)) Eq.refl

private
  four : (c c' : Bool) → (if c then 4₈ else 0₈) ≡ (if c' then 4₈ else 0₈) → c ≡ c'
  four true  true  e = Eq.refl
  four false false e = Eq.refl
  four true  false ()
  four false true  ()

qC-unique : (cs cs' : Vec Bool m) → (∀ y → qC cs y ≡ qC cs' y) → cs ≡ cs'
qC-unique []       []         e = Eq.refl
qC-unique {suc m} (c ∷ cs) (c' ∷ cs') e = Eq.cong₂ _∷_ hd tl
  where
  tl : cs ≡ cs'
  tl = qC-unique cs cs' λ y →
    +-cancelˡ 0₈ _ _
      (Eq.trans (Eq.cong (λ z → (if z then 4₈ else 0₈) + qC cs y) (Eq.sym (∧-zeroʳ c)))
        (Eq.trans (e (false ∷ y))
          (Eq.cong (λ z → (if z then 4₈ else 0₈) + qC cs' y) (∧-zeroʳ c'))))
  hd : c ≡ c'
  hd = four c c' (+-cancelʳ _ _ 0₈
         (Eq.trans (Eq.cong₂ (λ z w → (if z then 4₈ else 0₈) + w) (Eq.sym (∧-identityʳ c)) (Eq.sym (qC-zeros cs)))
           (Eq.trans (e (true ∷ replicate m false))
             (Eq.cong₂ (λ z w → (if z then 4₈ else 0₈) + w) (∧-identityʳ c') (qC-zeros cs')))))

private
  -- Once the tail and the constant agree, the head.
  head-data : (a : ℤ₈) (b b' : Fin 4) (c c' : Vec Bool k) (K : Bits k → ℤ₈) →
              (∀ y → a + ((dbl b + qC c y) + K y) ≡ a + ((dbl b' + qC c' y) + K y)) →
              b ≡ b' × c ≡ c'
  head-data {k} a b b' c c' K e = bb , cc
    where
    strip : ∀ y → dbl b + qC c y ≡ dbl b' + qC c' y
    strip y = +-cancelʳ _ _ (K y) (+-cancelˡ a _ _ (e y))
    bb : b ≡ b'
    bb = dbl-injective b b'
           (+-cancelʳ _ _ 0₈ (Eq.trans (Eq.cong (dbl b +_) (Eq.sym (qC-zeros c)))
             (Eq.trans (strip (replicate k false)) (Eq.cong (dbl b' +_) (qC-zeros c')))))
    cc : c ≡ c'
    cc = qC-unique c c' λ y →
           +-cancelˡ (dbl b) _ _ (Eq.trans (strip y) (Eq.cong (λ z → dbl z + qC c' y) (Eq.sym bb)))

  next : (a a' : ℤ₈) (b b' : Fin 4) (bs bs' : Vec (Fin 4) k) (c c' : Vec Bool k) (cs cs' : Tri k) →
         a ≡ a' → bs ≡ bs' → cs ≡ cs' →
         (∀ y → a + qF (b ∷ bs) (c , cs) y ≡ a' + qF (b' ∷ bs') (c' , cs') y) →
         b ≡ b' × c ≡ c'
  next a .a b b' bs .bs c c' cs .cs Eq.refl Eq.refl Eq.refl e =
    head-data a b b' c c' (qF bs cs) (λ y → e (true ∷ y))

qF-unique : (a a' : ℤ₈) (bs bs' : Vec (Fin 4) k) (cs cs' : Tri k) →
            (∀ y → a + qF bs cs y ≡ a' + qF bs' cs' y) →
            a ≡ a' × bs ≡ bs' × cs ≡ cs'
qF-unique a a' [] [] tt tt e =
  Eq.trans (Eq.sym (+-identityʳ a)) (Eq.trans (e []) (+-identityʳ a')) , Eq.refl , Eq.refl
qF-unique a a' (b ∷ bs) (b' ∷ bs') (c , cs) (c' , cs') e =
  proj₁ ih , Eq.cong₂ _∷_ (proj₁ hd) (proj₁ (proj₂ ih)) ,
  Eq.cong₂ _,_ (proj₂ hd) (proj₂ (proj₂ ih))
  where
  ih = qF-unique a a' bs bs' cs cs' λ y →
         Eq.trans (Eq.cong (a +_) (Eq.sym (+-identityˡ (qF bs cs y))))
           (Eq.trans (e (false ∷ y)) (Eq.cong (a' +_) (+-identityˡ (qF bs' cs' y))))
  hd = next a a' b b' bs bs' c c' cs cs' (proj₁ ih) (proj₁ (proj₂ ih)) (proj₂ (proj₂ ih)) e

E-unique : (e e' : EData k) → ⟦ E e ⟧ ≐ ⟦ E e' ⟧ → e ≡ e'
E-unique (a , bs , cs) (a' , bs' , cs') eq =
  Eq.cong₂ _,_ (proj₁ u) (Eq.cong₂ _,_ (proj₁ (proj₂ u)) (proj₂ (proj₂ u)))
  where
  u = qF-unique a a' bs bs' cs cs' λ y →
        Eq.cong proj₂ (Eq.trans (Eq.sym (DS-E (a , bs , cs) (true ∷ y)))
                        (Eq.trans (eq (true ∷ y)) (DS-E (a' , bs' , cs') (true ∷ y))))
