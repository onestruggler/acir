------------------------------------------------------------------------
-- Presentations of groups
--
-- Products of Pauli operators, and the existence of normal forms with a
-- given action (Propositions 4.11, 4.12 and 4.15)
--
-- X^a Z^b · X^c Z^d = (−1)^(b c) X^(a+c) Z^(b+d) (_·_).  Two Pauli
-- operators commute or anticommute as their symplectic product ω is
-- false or true, and P · P = ±I, the sign being the parity of the
-- number of letters XZ (ypar; Proposition 2.2).  Circuits preserve ω
-- and ypar (act-ω, act-ypar).
--
-- The decoders of Uniqueness run backwards: an operator Q with Q² = I
-- that is not ±I is QZ L for a Z-circuit L (QZ-surj, Proposition 4.11),
-- and one that moreover anticommutes with Z on the top wire is QX M
-- for an X-circuit M (QX-surj, Proposition 4.12).  Then any images of
-- X and Z on the n wires with the squares and commutations of X and Z
-- (a Frame) are the images under the inverse of an unsigned normal
-- form (realise, Proposition 4.15): L is read off the image of Z₀, M
-- off the image of X₀ after L, and the images of the other generators
-- after M L commute with X₀ and Z₀, so are I on wire 0 and give a frame
-- one wire up.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.PauliAlgebra where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.NormalForm
open import Examples.Groups.Real-Clifford.Pauli
open import Examples.Groups.Real-Clifford.Uniqueness

private
  variable
    k m n : ℕ
    t u : Ty

------------------------------------------------------------------------
-- Boolean identities, checked on all inputs

module BoolCheck where

  _==_ : Bool → Bool → Bool
  a == b = not (a xor b)

  allB : (k : ℕ) → (Vec Bool k → Bool) → Bool
  allB zero    p = p []
  allB (suc k) p = allB k (λ v → p (false ∷ v)) ∧ allB k (λ v → p (true ∷ v))

  private
    ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
    ∧-l {true} _ = refl

    ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
    ∧-r {true} e = e

    ==-sound : (a b : Bool) → a == b ≡ true → a ≡ b
    ==-sound false false _ = refl
    ==-sound true  true  _ = refl

  allB-sound : (k : ℕ) (p : Vec Bool k → Bool) → allB k p ≡ true → ∀ v → p v ≡ true
  allB-sound zero    p e []          = e
  allB-sound (suc k) p e (false ∷ v) = allB-sound k _ (∧-l e) v
  allB-sound (suc k) p e (true ∷ v)  = allB-sound k _ (∧-r {allB k (λ v → p (false ∷ v))} e) v

  bool-id : (k : ℕ) (f g : Vec Bool k → Bool) → allB k (λ v → f v == g v) ≡ true → ∀ v → f v ≡ g v
  bool-id k f g e v = ==-sound (f v) (g v) (allB-sound k (λ v → f v == g v) e v)

open BoolCheck using (bool-id)

private
  xor-false : (a : Bool) → a xor false ≡ a
  xor-false false = refl
  xor-false true  = refl

------------------------------------------------------------------------
-- Products, the symplectic form, and squares

-- X^a Z^b · X^c Z^d = (−1)^(b c) X^(a+c) Z^(b+d).
mulV : Vec Letter n → Vec Letter n → Bool × Vec Letter n
mulV []             []             = false , []
mulV ((a , b) ∷ ps) ((c , d) ∷ qs) =
  (b ∧ c) xor proj₁ (mulV ps qs) , (a xor c , b xor d) ∷ proj₂ (mulV ps qs)

infixl 7 _·_
_·_ : Pauli n → Pauli n → Pauli n
P · Q = (proj₁ P xor proj₁ Q) xor proj₁ (mulV (proj₂ P) (proj₂ Q)) , proj₂ (mulV (proj₂ P) (proj₂ Q))

-- The operator times (−1)^b.
flipIf : Bool → Pauli n → Pauli n
flipIf b P = proj₁ P xor b , proj₂ P

-- P and Q commute or anticommute as ω is false or true.
ωˡ : Letter → Letter → Bool
ωˡ (a , b) (c , d) = (b ∧ c) xor (a ∧ d)

ω : Vec Letter n → Vec Letter n → Bool
ω []       []       = false
ω (p ∷ ps) (q ∷ qs) = ωˡ p q xor ω ps qs

-- The parity of the number of letters XZ: P · P = (−1)^ypar.
ypar : Vec Letter n → Bool
ypar []             = false
ypar ((a , b) ∷ ps) = (a ∧ b) xor ypar ps

private
  sq-sign : (a b r : Bool) → (b ∧ a) xor r ≡ (a ∧ b) xor r
  sq-sign false false r = refl
  sq-sign false true  r = refl
  sq-sign true  false r = refl
  sq-sign true  true  r = refl

  xx-false : (a : Bool) → a xor a ≡ false
  xx-false false = refl
  xx-false true  = refl

mulV-sq : (ps : Vec Letter n) → mulV ps ps ≡ (ypar ps , I^ n)
mulV-sq []             = refl
mulV-sq ((a , b) ∷ ps) = Eq.cong₂ _,_
  (Eq.trans (Eq.cong ((b ∧ a) xor_) (Eq.cong proj₁ (mulV-sq ps))) (sq-sign a b (ypar ps)))
  (Eq.cong₂ (λ l v → l ∷ v) (Eq.cong₂ _,_ (xx-false a) (xx-false b)) (Eq.cong proj₂ (mulV-sq ps)))

-- Proposition 2.2.
·-sq : (P : Pauli n) → P · P ≡ (ypar (proj₂ P) , I^ n)
·-sq (σ , ps) = Eq.cong₂ _,_
  (Eq.trans (Eq.cong₂ _xor_ (xx-false σ) (Eq.cong proj₁ (mulV-sq ps))) refl)
  (Eq.cong proj₂ (mulV-sq ps))

private
  comm-sign : Vec Bool 6 → Bool
  comm-sign (a ∷ b ∷ c ∷ d ∷ r ∷ w ∷ []) = (d ∧ a) xor (r xor w)
  comm-sign' : Vec Bool 6 → Bool
  comm-sign' (a ∷ b ∷ c ∷ d ∷ r ∷ w ∷ []) = ((b ∧ c) xor r) xor (((b ∧ c) xor (a ∧ d)) xor w)

  xor-comm-l : (a c : Bool) → c xor a ≡ a xor c
  xor-comm-l a c = BoolP.xor-comm c a

mulV-comm : (ps qs : Vec Letter n) →
            mulV qs ps ≡ (proj₁ (mulV ps qs) xor ω ps qs , proj₂ (mulV ps qs))
mulV-comm []             []             = refl
mulV-comm ((a , b) ∷ ps) ((c , d) ∷ qs) = Eq.cong₂ _,_
  (Eq.trans (Eq.cong ((d ∧ a) xor_) (Eq.cong proj₁ (mulV-comm ps qs)))
            (bool-id 6 comm-sign comm-sign' refl (a ∷ b ∷ c ∷ d ∷ proj₁ (mulV ps qs) ∷ ω ps qs ∷ [])))
  (Eq.cong₂ (λ l v → l ∷ v) (Eq.cong₂ _,_ (xor-comm-l a c) (xor-comm-l b d))
            (Eq.cong proj₂ (mulV-comm ps qs)))

private
  swap-sign : Vec Bool 4 → Bool
  swap-sign (σ ∷ τ ∷ r ∷ w ∷ []) = (τ xor σ) xor (r xor w)
  swap-sign' : Vec Bool 4 → Bool
  swap-sign' (σ ∷ τ ∷ r ∷ w ∷ []) = ((σ xor τ) xor r) xor w

-- Q P = (−1)^ω P Q.
·-comm : (P Q : Pauli n) → Q · P ≡ flipIf (ω (proj₂ P) (proj₂ Q)) (P · Q)
·-comm (σ , ps) (τ , qs) = Eq.cong₂ _,_
  (Eq.trans (Eq.cong ((τ xor σ) xor_) (Eq.cong proj₁ (mulV-comm ps qs)))
            (bool-id 4 swap-sign swap-sign' refl (σ ∷ τ ∷ proj₁ (mulV ps qs) ∷ ω ps qs ∷ [])))
  (Eq.cong proj₂ (mulV-comm ps qs))

flipIf-inj : (a b : Bool) (P : Pauli n) → flipIf a P ≡ flipIf b P → a ≡ b
flipIf-inj a b (σ , ps) e = go σ a b (Eq.cong proj₁ e)
  where
  go : (σ a b : Bool) → σ xor a ≡ σ xor b → a ≡ b
  go false a b e = e
  go true  false false e = refl
  go true  true  true  e = refl
  go true  false true  ()
  go true  true  false ()

-- ω is symmetric, and vanishes against I.
ω-sym : (ps qs : Vec Letter n) → ω ps qs ≡ ω qs ps
ω-sym []             []             = refl
ω-sym ((a , b) ∷ ps) ((c , d) ∷ qs) = Eq.cong₂ _xor_ (go a b c d) (ω-sym ps qs)
  where
  go : (a b c d : Bool) → (b ∧ c) xor (a ∧ d) ≡ (d ∧ a) xor (c ∧ b)
  go a b c d = Eq.trans (BoolP.xor-comm (b ∧ c) (a ∧ d))
                        (Eq.cong₂ _xor_ (BoolP.∧-comm a d) (BoolP.∧-comm b c))

ω-Iˡ : (qs : Vec Letter n) → ω (I^ n) qs ≡ false
ω-Iˡ []       = refl
ω-Iˡ (q ∷ qs) = ω-Iˡ qs

ω-Iʳ : (ps : Vec Letter n) → ω ps (I^ n) ≡ false
ω-Iʳ ps = Eq.trans (ω-sym ps (I^ _)) (ω-Iˡ ps)

ypar-I : (n : ℕ) → ypar (I^ n) ≡ false
ypar-I zero    = refl
ypar-I (suc n) = ypar-I n

------------------------------------------------------------------------
-- Circuits preserve ω and ypar

private
  cz-ω : Vec Bool 9 → Bool
  cz-ω (a ∷ b ∷ c ∷ d ∷ a' ∷ b' ∷ c' ∷ d' ∷ r ∷ []) =
    ωˡ (a , b xor c) (a' , b' xor c') xor (ωˡ (c , d xor a) (c' , d' xor a') xor r)
  cz-ω' : Vec Bool 9 → Bool
  cz-ω' (a ∷ b ∷ c ∷ d ∷ a' ∷ b' ∷ c' ∷ d' ∷ r ∷ []) =
    ωˡ (a , b) (a' , b') xor (ωˡ (c , d) (c' , d') xor r)

  cz-y : Vec Bool 5 → Bool
  cz-y (a ∷ b ∷ c ∷ d ∷ r ∷ []) = (a ∧ (b xor c)) xor ((c ∧ (d xor a)) xor r)
  cz-y' : Vec Bool 5 → Bool
  cz-y' (a ∷ b ∷ c ∷ d ∷ r ∷ []) = (a ∧ b) xor ((c ∧ d) xor r)

actL-ω : (g : Gen n) (P Q : Pauli n) → ω (proj₂ (actL g P)) (proj₂ (actL g Q)) ≡ ω (proj₂ P) (proj₂ Q)
actL-ω (gate₀ neg-gate) P Q = refl
actL-ω (gate₁ H-gate) (σ , (a , b) ∷ ps) (τ , (c , d) ∷ qs) =
  Eq.cong (_xor ω ps qs) (Eq.trans (BoolP.xor-comm (a ∧ d) (b ∧ c)) refl)
actL-ω (gate₁ Z-gate) (σ , (a , b) ∷ ps) (τ , (c , d) ∷ qs) = refl
actL-ω (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) (τ , (a' , b') ∷ (c' , d') ∷ qs) =
  bool-id 9 cz-ω cz-ω' refl (a ∷ b ∷ c ∷ d ∷ a' ∷ b' ∷ c' ∷ d' ∷ ω ps qs ∷ [])
actL-ω (g ↥) (σ , p ∷ ps) (τ , q ∷ qs) = Eq.cong (ωˡ p q xor_) (actL-ω g (σ , ps) (τ , qs))

actL-ypar : (g : Gen n) (P : Pauli n) → ypar (proj₂ (actL g P)) ≡ ypar (proj₂ P)
actL-ypar (gate₀ neg-gate) P = refl
actL-ypar (gate₁ H-gate) (σ , (a , b) ∷ ps) = Eq.cong (_xor ypar ps) (BoolP.∧-comm b a)
actL-ypar (gate₁ Z-gate) (σ , (a , b) ∷ ps) = refl
actL-ypar (gate₂ CZ-gate) (σ , (a , b) ∷ (c , d) ∷ ps) =
  bool-id 5 cz-y cz-y' refl (a ∷ b ∷ c ∷ d ∷ ypar ps ∷ [])
actL-ypar (g ↥) (σ , (a , b) ∷ ps) = Eq.cong ((a ∧ b) xor_) (actL-ypar g (σ , ps))

act-ω : (w : Circuit n) (P Q : Pauli n) → ω (proj₂ (act w P)) (proj₂ (act w Q)) ≡ ω (proj₂ P) (proj₂ Q)
act-ω [ g ]ʷ  P Q = actL-ω g P Q
act-ω ε       P Q = refl
act-ω (w • v) P Q = Eq.trans (act-ω w (act v P) (act v Q)) (act-ω v P Q)

act-ypar : (w : Circuit n) (P : Pauli n) → ypar (proj₂ (act w P)) ≡ ypar (proj₂ P)
act-ypar [ g ]ʷ  P = actL-ypar g P
act-ypar ε       P = refl
act-ypar (w • v) P = Eq.trans (act-ypar w (act v P)) (act-ypar v P)

------------------------------------------------------------------------
-- The generators X and Z on each wire

single : Letter → Fin n → Vec Letter n
single ℓ zero    = ℓ ∷ I^ _
single ℓ (suc i) = 𝐈 ∷ single ℓ i

Xb Zb : Fin n → Pauli n
Xb i = false , single 𝐗 i
Zb i = false , single 𝐙 i

same : Fin n → Fin n → Bool
same zero    zero    = true
same zero    (suc j) = false
same (suc i) zero    = false
same (suc i) (suc j) = same i j


ypar-X : (i : Fin n) → ypar (single 𝐗 i) ≡ false
ypar-X {suc n} zero    = ypar-I n
ypar-X         (suc i) = ypar-X i

ypar-Z : (i : Fin n) → ypar (single 𝐙 i) ≡ false
ypar-Z {suc n} zero    = ypar-I n
ypar-Z         (suc i) = ypar-Z i

-- X and Z anticommute on the same wire, and commute otherwise.
ω-XX : (i j : Fin n) → ω (single 𝐗 i) (single 𝐗 j) ≡ false
ω-XX {suc n} zero    zero    = ω-Iˡ (I^ n)
ω-XX {suc n} zero    (suc j) = ω-Iˡ (single 𝐗 j)
ω-XX {suc n} (suc i) zero    = ω-Iʳ (single 𝐗 i)
ω-XX         (suc i) (suc j) = ω-XX i j

ω-ZZ : (i j : Fin n) → ω (single 𝐙 i) (single 𝐙 j) ≡ false
ω-ZZ {suc n} zero    zero    = ω-Iˡ (I^ n)
ω-ZZ {suc n} zero    (suc j) = ω-Iˡ (single 𝐙 j)
ω-ZZ {suc n} (suc i) zero    = ω-Iʳ (single 𝐙 i)
ω-ZZ         (suc i) (suc j) = ω-ZZ i j

ω-XZ : (i j : Fin n) → ω (single 𝐗 i) (single 𝐙 j) ≡ same i j
ω-XZ {suc n} zero    zero    = Eq.cong not (ω-Iˡ (I^ n))
ω-XZ {suc n} zero    (suc j) = ω-Iˡ (single 𝐙 j)
ω-XZ {suc n} (suc i) zero    = ω-Iʳ (single 𝐗 i)
ω-XZ         (suc i) (suc j) = ω-XZ i j

------------------------------------------------------------------------
-- Frames: images of the generators with their squares and commutations

record Frame (n : ℕ) : Set where
  field
    x z  : Fin n → Pauli n
    x-sq : ∀ i → ypar (proj₂ (x i)) ≡ false
    z-sq : ∀ i → ypar (proj₂ (z i)) ≡ false
    xx   : ∀ i j → ω (proj₂ (x i)) (proj₂ (x j)) ≡ false
    zz   : ∀ i j → ω (proj₂ (z i)) (proj₂ (z j)) ≡ false
    xz   : ∀ i j → ω (proj₂ (x i)) (proj₂ (z j)) ≡ same i j

standard : Frame n
standard = record
  { x = Xb ; z = Zb ; x-sq = ypar-X ; z-sq = ypar-Z ; xx = ω-XX ; zz = ω-ZZ ; xz = ω-XZ }

------------------------------------------------------------------------
-- Existence of Z-circuits (Proposition 4.11)

private
  ext : (b : BT t u) (l : Lad u (₁₊ m)) {σ : Bool} {rs : Vec Letter m} →
        QL l ≡ (σ , T u ∷ rs) → QL (b ∷ᴮ l) ≡ (σ , T t ∷ ℓB b ∷ rs)
  ext {t = t} b l e = Eq.trans (QL-step b l) (Eq.cong (λ P → proj₁ P , T t ∷ ℓB b ∷ tail (proj₂ P)) e)

  not-not : (a : Bool) → not (not a) ≡ a
  not-not false = refl
  not-not true  = refl

  not-inj : (a b : Bool) → not a ≡ b → a ≡ not b
  not-inj false true  _ = refl
  not-inj true  false _ = refl

QL-surj : (t : Ty) (σ : Bool) (ps : Vec Letter m) → ypar (T t ∷ ps) ≡ false →
          Σ (Lad t (₁₊ m)) λ l → QL l ≡ (σ , T t ∷ ps)
QL-surj sg false [] e = top C₁ , refl
QL-surj sg true  [] e = top C₂ , refl
QL-surj db σ     [] ()
QL-surj sg σ (𝐈 ∷ rs) e = let (l , el) = QL-surj sg σ rs e in B₁ ∷ᴮ l , ext B₁ l el
QL-surj sg σ (𝐗 ∷ rs) e = let (l , el) = QL-surj sg σ rs e in B₂ ∷ᴮ l , ext B₂ l el
QL-surj sg σ (𝐙 ∷ rs) e = let (l , el) = QL-surj sg σ rs e in B₃ ∷ᴮ l , ext B₃ l el
QL-surj sg σ (𝐘 ∷ rs) e = let (l , el) = QL-surj db σ rs e in B₄ ∷ᴮ l , ext B₄ l el
QL-surj db σ (𝐈 ∷ rs) e = let (l , el) = QL-surj db σ rs e in B₅ ∷ᴮ l , ext B₅ l el
QL-surj db σ (𝐗 ∷ rs) e = let (l , el) = QL-surj db σ rs e in B₆ ∷ᴮ l , ext B₆ l el
QL-surj db σ (𝐙 ∷ rs) e = let (l , el) = QL-surj db σ rs e in B₇ ∷ᴮ l , ext B₇ l el
QL-surj db σ (𝐘 ∷ rs) e =
  let (l , el) = QL-surj sg σ rs (Eq.trans (Eq.sym (not-not (ypar rs))) e) in B₈ ∷ᴮ l , ext B₈ l el

-- Every Q with Q² = I other than ±I is QZ L for a Z-circuit L.
QZ-surj : (σ : Bool) (ps : Vec Letter (₁₊ m)) → ypar ps ≡ false → ps ≢ I^ (₁₊ m) →
          Σ (Zc (₁₊ m)) λ L → QZ L ≡ (σ , ps)
QZ-surj {zero}  σ (𝐈 ∷ []) e ne = ⊥-elim (ne refl)
QZ-surj {suc m} σ (𝐈 ∷ ps) e ne =
  let (L , eL) = QZ-surj σ ps e (λ q → ne (Eq.cong (𝐈 ∷_) q))
  in up L , Eq.trans (QZ-up L) (Eq.cong (λ P → proj₁ P , 𝐈 ∷ proj₂ P) eL)
QZ-surj σ (𝐙 ∷ ps) e ne = let (l , el) = QL-surj sg σ ps e in
  at A₁ l , Eq.trans (QZ-at A₁ l) (Eq.cong (λ P → proj₁ P , 𝐙 ∷ tail (proj₂ P)) el)
QZ-surj σ (𝐗 ∷ ps) e ne = let (l , el) = QL-surj sg σ ps e in
  at A₂ l , Eq.trans (QZ-at A₂ l) (Eq.cong (λ P → proj₁ P , 𝐗 ∷ tail (proj₂ P)) el)
QZ-surj σ (𝐘 ∷ ps) e ne = let (l , el) = QL-surj db σ ps e in
  at A₃ l , Eq.trans (QZ-at A₃ l) (Eq.cong (λ P → proj₁ P , 𝐘 ∷ tail (proj₂ P)) el)

------------------------------------------------------------------------
-- Existence of X-circuits (Proposition 4.12)

-- The X bit of the top letter: an operator anticommutes with Z on the
-- top wire exactly when it is set.
topX : Vec Letter (₁₊ m) → Bool
topX {zero}  (p ∷ []) = proj₁ p
topX {suc m} (p ∷ ps) = topX ps

ω-ztop : (ps : Vec Letter (₁₊ m)) → ω ps (ztop m) ≡ topX ps
ω-ztop {zero}  (𝐈 ∷ []) = refl
ω-ztop {zero}  (𝐗 ∷ []) = refl
ω-ztop {zero}  (𝐙 ∷ []) = refl
ω-ztop {zero}  (𝐘 ∷ []) = refl
ω-ztop {suc m} (𝐈 ∷ ps) = ω-ztop ps
ω-ztop {suc m} (𝐗 ∷ ps) = ω-ztop ps
ω-ztop {suc m} (𝐙 ∷ ps) = ω-ztop ps
ω-ztop {suc m} (𝐘 ∷ ps) = ω-ztop ps

-- The letters a D-ladder starting from ℓ on wire 0 can produce.
Good : XY → Vec Letter (₁₊ m) → Set
Good {zero}  ℓ (p ∷ []) = p ≡ xy ℓ
Good {suc m} ℓ (p ∷ ps) = Good (swapD (pickD p) ℓ) ps

private
  ℓD-pickD : (p : Letter) → ℓD (pickD p) ≡ p
  ℓD-pickD 𝐈 = refl
  ℓD-pickD 𝐗 = refl
  ℓD-pickD 𝐙 = refl
  ℓD-pickD 𝐘 = refl

QD-surj : (ℓ : XY) (σ : Bool) (ps : Vec Letter (₁₊ m)) → Good ℓ ps →
          Σ (DL (₁₊ m)) λ dl → QD dl ℓ σ ≡ (σ , ps)
QD-surj {zero}  ℓ σ (p ∷ []) refl = []ᴰ , refl
QD-surj {suc m} ℓ σ (p ∷ ps) g =
  let (dl , e) = QD-surj (swapD (pickD p) ℓ) σ ps g
  in pickD p ∷ᴰ dl , Eq.trans (QD-step (pickD p) dl ℓ σ)
       (Eq.cong₂ _,_ (Eq.cong proj₁ e) (Eq.cong₂ _∷_ (ℓD-pickD p) (Eq.cong proj₂ e)))

yl : XY → Bool
yl xX = false
yl xY = true

good : (ℓ : XY) (ps : Vec Letter (₁₊ m)) → topX ps ≡ true → ypar ps ≡ yl ℓ → Good ℓ ps
good {zero}  xX (𝐗 ∷ []) _ _  = refl
good {zero}  xY (𝐘 ∷ []) _ _  = refl
good {zero}  xX (𝐘 ∷ []) _ ()
good {zero}  xY (𝐗 ∷ []) _ ()
good {zero}  ℓ  (𝐈 ∷ []) () _
good {zero}  ℓ  (𝐙 ∷ []) () _
good {suc m} ℓ  (p ∷ ps) t e = good (swapD (pickD p) ℓ) ps t (step p ℓ e)
  where
  step : (p : Letter) (ℓ : XY) → ypar (p ∷ ps) ≡ yl ℓ → ypar ps ≡ yl (swapD (pickD p) ℓ)
  step 𝐈 ℓ  e = e
  step 𝐗 ℓ  e = e
  step 𝐙 ℓ  e = e
  step 𝐘 xX e = not-inj (ypar ps) false e
  step 𝐘 xY e = not-inj (ypar ps) true e

-- Every Q with Q² = I that anticommutes with Z on the top wire is QX M
-- for an X-circuit M.
QX-surj : (σ : Bool) (ps : Vec Letter (₁₊ m)) → topX ps ≡ true → ypar ps ≡ false →
          Σ (Xc (₁₊ m)) λ M → QX M ≡ (σ , ps)
QX-surj false ps t e = let (dl , q) = QD-surj xX false ps (good xX ps t e) in
  (E₁ ,ˣ dl) , Eq.trans (QX-def E₁ dl) q
QX-surj true  ps t e = let (dl , q) = QD-surj xX true ps (good xX ps t e) in
  (E₂ ,ˣ dl) , Eq.trans (QX-def E₂ dl) q

------------------------------------------------------------------------
-- Operators that commute with X₀ and Z₀

private
  ω-X₀ : (p : Letter) (ps : Vec Letter m) → ω (p ∷ ps) (𝐗 ∷ I^ m) ≡ proj₂ p
  ω-X₀ (a , b) ps = Eq.trans (Eq.cong (ωˡ (a , b) 𝐗 xor_) (ω-Iʳ ps)) (go a b)
    where
    go : (a b : Bool) → ωˡ (a , b) 𝐗 xor false ≡ b
    go false false = refl
    go false true  = refl
    go true  false = refl
    go true  true  = refl

  ω-Z₀ : (p : Letter) (ps : Vec Letter m) → ω (p ∷ ps) (𝐙 ∷ I^ m) ≡ proj₁ p
  ω-Z₀ (a , b) ps = Eq.trans (Eq.cong (ωˡ (a , b) 𝐙 xor_) (ω-Iʳ ps)) (go a b)
    where
    go : (a b : Bool) → ωˡ (a , b) 𝐙 xor false ≡ a
    go false false = refl
    go false true  = refl
    go true  false = refl
    go true  true  = refl

-- Such an operator is I on wire 0.
head-I : (P : Pauli (₁₊ m)) → ω (proj₂ P) (proj₂ (X₀ m)) ≡ false → ω (proj₂ P) (proj₂ (Z₀ m)) ≡ false →
         P ≡ (proj₁ P , 𝐈 ∷ tail (proj₂ P))
head-I (σ , p ∷ ps) ex ez = Eq.cong (λ l → σ , l ∷ ps)
  (Eq.cong₂ _,_ (Eq.trans (Eq.sym (ω-Z₀ p ps)) ez) (Eq.trans (Eq.sym (ω-X₀ p ps)) ex))

-- Dropping wire 0, where it is I.
rest : Pauli (₁₊ m) → Pauli m
rest P = proj₁ P , tail (proj₂ P)

private
  ypar-rest : {P : Pauli (₁₊ m)} → P ≡ (proj₁ P , 𝐈 ∷ tail (proj₂ P)) →
              ypar (proj₂ (rest P)) ≡ ypar (proj₂ P)
  ypar-rest e = Eq.sym (Eq.cong (λ Q → ypar (proj₂ Q)) e)

  ω-rest : {P Q : Pauli (₁₊ m)} → P ≡ (proj₁ P , 𝐈 ∷ tail (proj₂ P)) → Q ≡ (proj₁ Q , 𝐈 ∷ tail (proj₂ Q)) →
           ω (proj₂ (rest P)) (proj₂ (rest Q)) ≡ ω (proj₂ P) (proj₂ Q)
  ω-rest eP eQ = Eq.sym (Eq.cong₂ (λ A B → ω (proj₂ A) (proj₂ B)) eP eQ)

  t≢f : true ≢ false
  t≢f ()

------------------------------------------------------------------------
-- Every frame is realised by an unsigned normal form (Proposition 4.15)

record Realised (F : Frame n) : Set where
  field
    nf   : NF n
    nf-+ : sign nf ≡ false
    on-x : ∀ i → act (inv ⟦ nf ⟧ⁿ) (Xb i) ≡ Frame.x F i
    on-z : ∀ i → act (inv ⟦ nf ⟧ⁿ) (Zb i) ≡ Frame.z F i

realise : (F : Frame n) → Realised F
realise {zero}  F = record { nf = nf₀ false ; nf-+ = refl ; on-x = λ () ; on-z = λ () }
realise {suc m} F = record { nf = nfₛ L M N' ; nf-+ = Realised.nf-+ IH ; on-x = on-x ; on-z = on-z }
  where
  open Frame F
  open Eq.≡-Reasoning

  x₀ z₀ : Pauli (₁₊ m)
  x₀ = x zero
  z₀ = z zero

  -- The image of Z₀ is not ±I, as it anticommutes with that of X₀.
  z₀≢I : proj₂ z₀ ≢ I^ (₁₊ m)
  z₀≢I e = t≢f (begin
    true                              ≡⟨ xz zero zero ⟨
    ω (proj₂ x₀) (proj₂ z₀)           ≡⟨ Eq.cong (ω (proj₂ x₀)) e ⟩
    ω (proj₂ x₀) (I^ (₁₊ m))          ≡⟨ ω-Iʳ (proj₂ x₀) ⟩
    false                             ∎)

  -- L, read off the image of Z₀.
  L : Zc (₁₊ m)
  L = proj₁ (QZ-surj (proj₁ z₀) (proj₂ z₀) (z-sq zero) z₀≢I)
  eL : QZ L ≡ z₀
  eL = proj₂ (QZ-surj (proj₁ z₀) (proj₂ z₀) (z-sq zero) z₀≢I)

  L-z₀ : act ⟦ L ⟧ᶻ z₀ ≡ (false , ztop m)
  L-z₀ = Eq.trans (Eq.cong (act ⟦ L ⟧ᶻ) (Eq.sym eL)) (inv-act ⟦ L ⟧ᶻ (false , ztop m))

  -- M, read off the image of X₀ after L.
  R : Pauli (₁₊ m)
  R = act ⟦ L ⟧ᶻ x₀

  R-top : topX (proj₂ R) ≡ true
  R-top = begin
    topX (proj₂ R)                         ≡⟨ ω-ztop (proj₂ R) ⟨
    ω (proj₂ R) (ztop m)                   ≡⟨ Eq.cong (λ P → ω (proj₂ R) (proj₂ P)) L-z₀ ⟨
    ω (proj₂ R) (proj₂ (act ⟦ L ⟧ᶻ z₀))    ≡⟨ act-ω ⟦ L ⟧ᶻ x₀ z₀ ⟩
    ω (proj₂ x₀) (proj₂ z₀)                ≡⟨ xz zero zero ⟩
    true                                   ∎

  R-sq : ypar (proj₂ R) ≡ false
  R-sq = Eq.trans (act-ypar ⟦ L ⟧ᶻ x₀) (x-sq zero)

  M : Xc (₁₊ m)
  M = proj₁ (QX-surj (proj₁ R) (proj₂ R) R-top R-sq)
  eM : QX M ≡ R
  eM = proj₂ (QX-surj (proj₁ R) (proj₂ R) R-top R-sq)

  -- After M L, the images of X₀ and Z₀ are X₀ and Z₀.
  g : Pauli (₁₊ m) → Pauli (₁₊ m)
  g P = act ⟦ M ⟧ˣ (act ⟦ L ⟧ᶻ P)

  g-x₀ : g x₀ ≡ X₀ m
  g-x₀ = Eq.trans (Eq.cong (act ⟦ M ⟧ˣ) (Eq.sym eM)) (inv-act ⟦ M ⟧ˣ (X₀ m))

  g-z₀ : g z₀ ≡ Z₀ m
  g-z₀ = Eq.trans (Eq.cong (act ⟦ M ⟧ˣ) L-z₀)
    (Eq.trans (Eq.cong (act ⟦ M ⟧ˣ) (Eq.sym (QX-Z M))) (inv-act ⟦ M ⟧ˣ (Z₀ m)))

  g-ω : (P Q : Pauli (₁₊ m)) → ω (proj₂ (g P)) (proj₂ (g Q)) ≡ ω (proj₂ P) (proj₂ Q)
  g-ω P Q = Eq.trans (act-ω ⟦ M ⟧ˣ (act ⟦ L ⟧ᶻ P) (act ⟦ L ⟧ᶻ Q)) (act-ω ⟦ L ⟧ᶻ P Q)

  g-ypar : (P : Pauli (₁₊ m)) → ypar (proj₂ (g P)) ≡ ypar (proj₂ P)
  g-ypar P = Eq.trans (act-ypar ⟦ M ⟧ˣ (act ⟦ L ⟧ᶻ P)) (act-ypar ⟦ L ⟧ᶻ P)

  -- So the images of the generators above commute with X₀ and Z₀, and
  -- are I on wire 0.
  g-head : (P : Pauli (₁₊ m)) → ω (proj₂ P) (proj₂ x₀) ≡ false → ω (proj₂ P) (proj₂ z₀) ≡ false →
           g P ≡ (proj₁ (g P) , 𝐈 ∷ tail (proj₂ (g P)))
  g-head P ex ez = head-I (g P)
    (Eq.trans (Eq.cong (λ Q → ω (proj₂ (g P)) (proj₂ Q)) (Eq.sym g-x₀)) (Eq.trans (g-ω P x₀) ex))
    (Eq.trans (Eq.cong (λ Q → ω (proj₂ (g P)) (proj₂ Q)) (Eq.sym g-z₀)) (Eq.trans (g-ω P z₀) ez))

  hx : (j : Fin m) → g (x (suc j)) ≡ (proj₁ (g (x (suc j))) , 𝐈 ∷ tail (proj₂ (g (x (suc j)))))
  hx j = g-head (x (suc j)) (xx (suc j) zero) (xz (suc j) zero)

  hz : (j : Fin m) → g (z (suc j)) ≡ (proj₁ (g (z (suc j))) , 𝐈 ∷ tail (proj₂ (g (z (suc j)))))
  hz j = g-head (z (suc j)) (Eq.trans (ω-sym (proj₂ (z (suc j))) (proj₂ x₀)) (xz zero (suc j))) (zz (suc j) zero)

  -- The frame one wire up.
  F' : Frame m
  F' = record
    { x    = λ j → rest (g (x (suc j)))
    ; z    = λ j → rest (g (z (suc j)))
    ; x-sq = λ j → Eq.trans (ypar-rest (hx j)) (Eq.trans (g-ypar (x (suc j))) (x-sq (suc j)))
    ; z-sq = λ j → Eq.trans (ypar-rest (hz j)) (Eq.trans (g-ypar (z (suc j))) (z-sq (suc j)))
    ; xx   = λ i j → Eq.trans (ω-rest (hx i) (hx j)) (Eq.trans (g-ω (x (suc i)) (x (suc j))) (xx (suc i) (suc j)))
    ; zz   = λ i j → Eq.trans (ω-rest (hz i) (hz j)) (Eq.trans (g-ω (z (suc i)) (z (suc j))) (zz (suc i) (suc j)))
    ; xz   = λ i j → Eq.trans (ω-rest (hx i) (hz j)) (Eq.trans (g-ω (x (suc i)) (z (suc j))) (xz (suc i) (suc j)))
    }

  IH : Realised F'
  IH = realise F'

  N' : NF m
  N' = Realised.nf IH

  on-x : ∀ i → act (inv ⟦ nfₛ L M N' ⟧ⁿ) (Xb i) ≡ x i
  on-x zero = Eq.trans (Eq.cong (act (inv ⟦ L ⟧ᶻ)) (Eq.trans (nf-X M N') eM)) (act-inv ⟦ L ⟧ᶻ x₀)
  on-x (suc j) = begin
    act (inv ⟦ L ⟧ᶻ) (act (inv ⟦ M ⟧ˣ) (act (inv (⟦ N' ⟧ⁿ ↑)) (false , 𝐈 ∷ single 𝐗 j)))
      ≡⟨ Eq.cong (λ P → act (inv ⟦ L ⟧ᶻ) (act (inv ⟦ M ⟧ˣ) P))
           (Eq.trans (act-inv-↑ ⟦ N' ⟧ⁿ false 𝐈 (single 𝐗 j))
             (Eq.trans (Eq.cong (λ P → proj₁ P , 𝐈 ∷ proj₂ P) (Realised.on-x IH j)) (Eq.sym (hx j)))) ⟩
    act (inv ⟦ L ⟧ᶻ) (act (inv ⟦ M ⟧ˣ) (g (x (suc j))))
      ≡⟨ Eq.cong (act (inv ⟦ L ⟧ᶻ)) (act-inv ⟦ M ⟧ˣ (act ⟦ L ⟧ᶻ (x (suc j)))) ⟩
    act (inv ⟦ L ⟧ᶻ) (act ⟦ L ⟧ᶻ (x (suc j)))
      ≡⟨ act-inv ⟦ L ⟧ᶻ (x (suc j)) ⟩
    x (suc j)
      ∎

  on-z : ∀ i → act (inv ⟦ nfₛ L M N' ⟧ⁿ) (Zb i) ≡ z i
  on-z zero = Eq.trans (nf-Z L M N') eL
  on-z (suc j) = begin
    act (inv ⟦ L ⟧ᶻ) (act (inv ⟦ M ⟧ˣ) (act (inv (⟦ N' ⟧ⁿ ↑)) (false , 𝐈 ∷ single 𝐙 j)))
      ≡⟨ Eq.cong (λ P → act (inv ⟦ L ⟧ᶻ) (act (inv ⟦ M ⟧ˣ) P))
           (Eq.trans (act-inv-↑ ⟦ N' ⟧ⁿ false 𝐈 (single 𝐙 j))
             (Eq.trans (Eq.cong (λ P → proj₁ P , 𝐈 ∷ proj₂ P) (Realised.on-z IH j)) (Eq.sym (hz j)))) ⟩
    act (inv ⟦ L ⟧ᶻ) (act (inv ⟦ M ⟧ˣ) (g (z (suc j))))
      ≡⟨ Eq.cong (act (inv ⟦ L ⟧ᶻ)) (act-inv ⟦ M ⟧ˣ (act ⟦ L ⟧ᶻ (z (suc j)))) ⟩
    act (inv ⟦ L ⟧ᶻ) (act ⟦ L ⟧ᶻ (z (suc j)))
      ≡⟨ act-inv ⟦ L ⟧ᶻ (z (suc j)) ⟩
    z (suc j)
      ∎
