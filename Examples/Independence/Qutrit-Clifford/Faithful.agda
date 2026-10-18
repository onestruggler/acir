------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix of a Paper-V0 circuit determines its interpretation
--
-- If two circuits' matrices are proportional, they conjugate the Weyl
-- operators alike, so by V0Mat.law they have the same symplectic map
-- and the same Pauli part: their interpretations in Pauli ⋊ Sp agree
-- (faithful).  Three facts carry this:
--
-- * every circuit's matrix has a right inverse up to a power of √3, the
--   matrix of the inverse word (H³ for H, S² for S, CZ² for CZ, read
--   backwards), so it can be cancelled on the right (inv-right);
-- * a power of ω times a Weyl operator determines both (D-inj): one
--   wire by evaluation, then wire by wire through the Kronecker
--   product, an entry of D v at its own column 0 being a power of ω;
-- * the symplectic form is nondegenerate (sform-inj).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.Faithful where

open import Data.Bool.Base using (Bool ; T ; _∧_ ; _∨_ ; not ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
open import Data.Nat.Base using (ℕ) renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
import Data.Nat.Base as ℕ
open import Data.Product.Base using (Σ ; ∃ ; _,_ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (tt ; ⊤)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (does ; yes ; no)
import Data.Fin.Properties
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import ForStdlib.Data.Fin.Mod using (ℤ)
import ForStdlib.Data.Fin.Mod as F3

open import Examples.Independence.Semantics.Qutrit
open import Examples.Independence.Qutrit-Clifford.Weyl
open import Examples.Independence.Qutrit-Clifford.V0Mat
import Examples.Independence.Qutrit-Clifford.P3 as P3
open P3 using (ₚ)

import Examples.Groups.ProjectivePauli.Semantics 1 P3.p-prime as PS
open PS using (Pauli1 ; Pauli ; sform1 ; sform ; pIₙ)
open import Examples.Groups.Symplectic.Semantics 1 P3.p-prime using (Symplectic)
open Symplectic using (ap ; ap⁻¹ ; invʳ)

import Examples.Groups.Symplectic.Syntactics.Gates 1 P3.p-prime as Gates
open Gates.Symplectic using (Gen ; gate₁ ; gate₂ ; _↥ ; H-gate ; S-gate ; CZ-gate)

open import Algebra.Bundles using (CommutativeRing)
open CommutativeRing R using (*-assoc ; *-comm ; *-identityˡ ; *-identityʳ ; zeroˡ ; zeroʳ)

private
  variable
    n : ℕ

  open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Powers of ω are units

ω^-inv : (a : ℤ ₚ) → ω^ a * ω^ (F3.- a) ≡ 1#
ω^-inv zero             = refl
ω^-inv (suc zero)       = refl
ω^-inv (suc (suc zero)) = refl

ω^≢0 : (a : ℤ ₚ) → ω^ a ≢ 0#
ω^≢0 zero             ()
ω^≢0 (suc zero)       ()
ω^≢0 (suc (suc zero)) ()

ω^-inj : (a b : ℤ ₚ) → ω^ a ≡ ω^ b → a ≡ b
ω^-inj zero             zero             _ = refl
ω^-inj (suc zero)       (suc zero)       _ = refl
ω^-inj (suc (suc zero)) (suc (suc zero)) _ = refl
ω^-inj zero             (suc zero)       ()
ω^-inj zero             (suc (suc zero)) ()
ω^-inj (suc zero)       zero             ()
ω^-inj (suc zero)       (suc (suc zero)) ()
ω^-inj (suc (suc zero)) zero             ()
ω^-inj (suc (suc zero)) (suc zero)       ()

-- Cancelling a power of ω.
ω^-cancel : (e : ℤ ₚ) {a b : Q} → ω^ e * a ≡ ω^ e * b → a ≡ b
ω^-cancel e {a} {b} h = begin
  a                              ≡⟨ Eq.sym (*-identityˡ a) ⟩
  1# * a                         ≡⟨ Eq.cong (_* a) (Eq.sym (ω^-inv e)) ⟩
  (ω^ e * ω^ (F3.- e)) * a       ≡⟨ Eq.cong (_* a) (*-comm (ω^ e) (ω^ (F3.- e))) ⟩
  (ω^ (F3.- e) * ω^ e) * a       ≡⟨ *-assoc (ω^ (F3.- e)) (ω^ e) a ⟩
  ω^ (F3.- e) * (ω^ e * a)       ≡⟨ Eq.cong (ω^ (F3.- e) *_) h ⟩
  ω^ (F3.- e) * (ω^ e * b)       ≡⟨ Eq.sym (*-assoc (ω^ (F3.- e)) (ω^ e) b) ⟩
  (ω^ (F3.- e) * ω^ e) * b       ≡⟨ Eq.cong (_* b) (*-comm (ω^ (F3.- e)) (ω^ e)) ⟩
  (ω^ e * ω^ (F3.- e)) * b       ≡⟨ Eq.cong (_* b) (ω^-inv e) ⟩
  1# * b                         ≡⟨ *-identityˡ b ⟩
  b                              ∎

------------------------------------------------------------------------
-- Entries of Weyl operators: zero, or a power of ω

private
  δ-cases : (r x : Fin 3) → (δ₁ r x ≡ 1#) ⊎ (δ₁ r x ≡ 0#)
  δ-cases zero             zero             = inj₁ refl
  δ-cases zero             (suc zero)       = inj₂ refl
  δ-cases zero             (suc (suc zero)) = inj₂ refl
  δ-cases (suc zero)       zero             = inj₂ refl
  δ-cases (suc zero)       (suc zero)       = inj₁ refl
  δ-cases (suc zero)       (suc (suc zero)) = inj₂ refl
  δ-cases (suc (suc zero)) zero             = inj₂ refl
  δ-cases (suc (suc zero)) (suc zero)       = inj₂ refl
  δ-cases (suc (suc zero)) (suc (suc zero)) = inj₁ refl

  δ-refl : (r : Fin 3) → δ₁ r r ≡ 1#
  δ-refl zero             = refl
  δ-refl (suc zero)       = refl
  δ-refl (suc (suc zero)) = refl

  0+′ : (a : ℤ ₚ) → zero F3.+ a ≡ a
  0+′ zero             = refl
  0+′ (suc zero)       = refl
  0+′ (suc (suc zero)) = refl

Unit-or-0 : Q → Set
Unit-or-0 q = (Σ (ℤ ₚ) λ j → q ≡ ω^ j) ⊎ (q ≡ 0#)

entry₁ : (p : Pauli1) (r c : Fin 3) → Unit-or-0 (D₁ p (r ∷ []) (c ∷ []))
entry₁ (a , b) r c with δ-cases r (c F3.+ a)
... | inj₁ h = inj₁ (e , Eq.trans (Eq.cong (_* ω^ e) h) (*-identityˡ (ω^ e)))
  where e = (½ F3.* a F3.* b) F3.+ (b F3.* c)
... | inj₂ h = inj₂ (Eq.trans (Eq.cong (_* ω^ e) h) (zeroˡ (ω^ e)))
  where e = (½ F3.* a F3.* b) F3.+ (b F3.* c)

entryD : (v : Pauli n) (rs cs : Digits n) → Unit-or-0 (D v rs cs)
entryD []      []       []       = inj₁ (zero , refl)
entryD (p ∷ v) (r ∷ rs) (c ∷ cs) with entry₁ p r c | entryD v rs cs
... | inj₁ (j , h) | inj₁ (k , g) =
  inj₁ (j F3.+ k , Eq.trans (Eq.cong₂ _*_ h g) (Eq.sym (ω^-+ j k)))
... | inj₂ h       | _            =
  inj₂ (Eq.trans (Eq.cong (_* D v rs cs) h) (zeroˡ (D v rs cs)))
... | inj₁ _       | inj₂ g       =
  inj₂ (Eq.trans (Eq.cong (D₁ p (r ∷ []) (c ∷ []) *_) g) (zeroʳ (D₁ p (r ∷ []) (c ∷ []))))

-- The X part of a label, and the column of zeros.
xs : Pauli n → Digits n
xs []            = []
xs ((a , _) ∷ v) = a ∷ xs v

zeros : Digits n
zeros {ℕ.zero}  = []
zeros {ℕ.suc n} = zero ∷ zeros

-- D v at row xs v of column 0 is a power of ω.
unit₁ : (p : Pauli1) → Σ (ℤ ₚ) λ j → D₁ p (proj₁ p ∷ []) (zero ∷ []) ≡ ω^ j
unit₁ (a , b) = e , Eq.trans (Eq.cong (λ t → δ₁ a t * ω^ e) (0+′ a))
                    (Eq.trans (Eq.cong (_* ω^ e) (δ-refl a)) (*-identityˡ (ω^ e)))
  where e = (½ F3.* a F3.* b) F3.+ (b F3.* zero)

unitD : (v : Pauli n) → Σ (ℤ ₚ) λ j → D v (xs v) zeros ≡ ω^ j
unitD []      = zero , refl
unitD (p ∷ v) with unit₁ p | unitD v
... | j , h | k , g = j F3.+ k , Eq.trans (Eq.cong₂ _*_ h g) (Eq.sym (ω^-+ j k))

------------------------------------------------------------------------
-- One qutrit, by evaluation

private
  eqF : Fin 3 → Fin 3 → Bool
  eqF a b = does (a Data.Fin.Properties.≟ b)

  eqF-sound : (a b : Fin 3) → T (eqF a b) → a ≡ b
  eqF-sound a b t with a Data.Fin.Properties.≟ b
  ... | yes e = e

  dec-sound : (a b : Q) → T (does (a ≟ b)) → a ≡ b
  dec-sound a b t with a ≟ b
  ... | yes e = e

  dec-complete : (a b : Q) → a ≡ b → T (does (a ≟ b))
  dec-complete a b e with a ≟ b
  ... | yes _ = tt
  ... | no ne = ne e

  all3 : (Fin 3 → Bool) → Bool
  all3 = allFin

  same₁ : Pauli1 → Pauli1 → ℤ ₚ → ℤ ₚ → Bool
  same₁ p p' k k' =
    all3 λ r → all3 λ c → does (ω^ k * D₁ p (r ∷ []) (c ∷ []) ≟ ω^ k' * D₁ p' (r ∷ []) (c ∷ []))

  ok₁ : Pauli1 → Pauli1 → ℤ ₚ → ℤ ₚ → Bool
  ok₁ p@(a , b) p'@(a' , b') k k' =
    (eqF a a' ∧ eqF b b' ∧ eqF k k') ∨ not (same₁ p p' k k')

  all-ok₁ : T (allP1 λ p → allP1 λ p' → all3 λ k → all3 λ k' → ok₁ p p' k k')
  all-ok₁ = _

  -- Read back over variables: under core₁'s patterns p@(a , b) the
  -- lambdas are instantiated at pairs, where ok₁ unfolds.
  ok₁-all : ∀ p p' k k' → T (ok₁ p p' k k')
  ok₁-all p p' k k' =
    allFin-sound (ok₁ p p' k)
      (allFin-sound (λ k → all3 λ k' → ok₁ p p' k k')
        (allP1-sound (λ p' → all3 λ k → all3 λ k' → ok₁ p p' k k')
          (allP1-sound (λ p → allP1 λ p' → all3 λ k → all3 λ k' → ok₁ p p' k k') all-ok₁ p) p') k) k'

  ∨-l : ∀ {x y} → T (x ∨ not y) → T y → T x
  ∨-l {true}          _ _ = tt
  ∨-l {false} {true}  () _
  ∨-l {false} {false} _ ()

  ∧₃ : ∀ {x y z} → T (x ∧ y ∧ z) → T x × T y × T z
  ∧₃ {true} {true} {true} _ = tt , tt , tt

core₁ : (p p' : Pauli1) (k k' : ℤ ₚ) →
        (∀ r c → ω^ k * D₁ p (r ∷ []) (c ∷ []) ≡ ω^ k' * D₁ p' (r ∷ []) (c ∷ [])) →
        (p ≡ p') × (k ≡ k')
core₁ p@(a , b) p'@(a' , b') k k' h =
  Eq.cong₂ _,_ (eqF-sound a a' ta) (eqF-sound b b' tb) , eqF-sound k k' tk
  where
  t : T (ok₁ p p' k k')
  t = ok₁-all p p' k k'
  s : T (same₁ p p' k k')
  s = allFin-complete (λ r → all3 λ c → does (ω^ k * D₁ p (r ∷ []) (c ∷ []) ≟ ω^ k' * D₁ p' (r ∷ []) (c ∷ [])))
        λ r → allFin-complete (λ c → does (ω^ k * D₁ p (r ∷ []) (c ∷ []) ≟ ω^ k' * D₁ p' (r ∷ []) (c ∷ [])))
          λ c → dec-complete _ _ (h r c)
  ts = ∧₃ {eqF a a'} {eqF b b'} {eqF k k'} (∨-l {eqF a a' ∧ eqF b b' ∧ eqF k k'} t s)
  ta = proj₁ ts
  tb = proj₁ (proj₂ ts)
  tk = proj₂ (proj₂ ts)


------------------------------------------------------------------------
-- A power of ω times a Weyl operator determines both

private
  -- ω^ k (A ω^ e) = ω^ (k + e) A.
  regroup : (k e : ℤ ₚ) (A : Q) → ω^ k * (A * ω^ e) ≡ ω^ (k F3.+ e) * A
  regroup k e A = begin
    ω^ k * (A * ω^ e)        ≡⟨ Eq.cong (ω^ k *_) (*-comm A (ω^ e)) ⟩
    ω^ k * (ω^ e * A)        ≡⟨ Eq.sym (*-assoc (ω^ k) (ω^ e) A) ⟩
    (ω^ k * ω^ e) * A        ≡⟨ Eq.cong (_* A) (Eq.sym (ω^-+ k e)) ⟩
    ω^ (k F3.+ e) * A        ∎

  -- ω^ k (ω^ u A) = ω^ (k + u) A.
  regroup′ : (k u : ℤ ₚ) (A : Q) → ω^ k * (ω^ u * A) ≡ ω^ (k F3.+ u) * A
  regroup′ k u A = Eq.trans (Eq.sym (*-assoc (ω^ k) (ω^ u) A)) (Eq.cong (_* A) (Eq.sym (ω^-+ k u)))

  eqF-refl : (c : Fin 3) → T (eqF c c)
  eqF-refl zero             = tt
  eqF-refl (suc zero)       = tt
  eqF-refl (suc (suc zero)) = tt

  cancel-ok : ℤ ₚ → ℤ ₚ → ℤ ₚ → Bool
  cancel-ok a b u = eqF a b ∨ not (eqF (a F3.+ u) (b F3.+ u))

  all-cancel : T (all3 λ a → all3 λ b → all3 λ u → cancel-ok a b u)
  all-cancel = _

  +-cancelʳ : (a b u : ℤ ₚ) → a F3.+ u ≡ b F3.+ u → a ≡ b
  +-cancelʳ a b u e =
    eqF-sound a b
      (∨-l {eqF a b} {eqF (a F3.+ u) (b F3.+ u)}
        (allFin-sound (cancel-ok a b)
          (allFin-sound (λ b → all3 λ u → cancel-ok a b u)
            (allFin-sound (λ a → all3 λ b → all3 λ u → cancel-ok a b u) all-cancel a) b) u)
        (Eq.subst (λ t → T (eqF (a F3.+ u) t)) e (eqF-refl (a F3.+ u))))

D-inj : (y y' : Pauli n) (k k' : ℤ ₚ) →
        (∀ rs cs → ω^ k * D y rs cs ≡ ω^ k' * D y' rs cs) → (y ≡ y') × (k ≡ k')
D-inj [] [] k k' h =
  refl , ω^-inj k k' (Eq.trans (Eq.sym (*-identityʳ (ω^ k))) (Eq.trans (h [] []) (*-identityʳ (ω^ k'))))
D-inj (p ∷ v) (p' ∷ v') k k' h with unitD v | entryD v' (xs v) zeros
... | e , ue | inj₂ z = ⊥-elim (ω^≢0 (k F3.+ (j F3.+ e)) contra)
  where
  a = proj₁ p
  j = proj₁ (unit₁ p)
  contra : ω^ (k F3.+ (j F3.+ e)) ≡ 0#
  contra = begin
    ω^ (k F3.+ (j F3.+ e))                            ≡⟨ ω^-+ k (j F3.+ e) ⟩
    ω^ k * ω^ (j F3.+ e)                              ≡⟨ Eq.cong (ω^ k *_) (ω^-+ j e) ⟩
    ω^ k * (ω^ j * ω^ e)                              ≡⟨ Eq.cong₂ (λ s t → ω^ k * (s * t)) (Eq.sym (proj₂ (unit₁ p))) (Eq.sym ue) ⟩
    ω^ k * (D₁ p (a ∷ []) (zero ∷ []) * D v (xs v) zeros)
                                                      ≡⟨ h (a ∷ xs v) (zero ∷ zeros) ⟩
    ω^ k' * (D₁ p' (a ∷ []) (zero ∷ []) * D v' (xs v) zeros)
                                                      ≡⟨ Eq.cong (λ t → ω^ k' * (D₁ p' (a ∷ []) (zero ∷ []) * t)) z ⟩
    ω^ k' * (D₁ p' (a ∷ []) (zero ∷ []) * 0#)         ≡⟨ Eq.cong (ω^ k' *_) (zeroʳ (D₁ p' (a ∷ []) (zero ∷ []))) ⟩
    ω^ k' * 0#                                        ≡⟨ zeroʳ (ω^ k') ⟩
    0#                                                ∎
... | e , ue | inj₁ (j′ , uv′) = go (core₁ p p' (k F3.+ e) (k' F3.+ j′) first)
  where
  first : ∀ r c → ω^ (k F3.+ e) * D₁ p (r ∷ []) (c ∷ []) ≡ ω^ (k' F3.+ j′) * D₁ p' (r ∷ []) (c ∷ [])
  first r c = begin
    ω^ (k F3.+ e) * D₁ p (r ∷ []) (c ∷ [])               ≡⟨ Eq.sym (regroup k e _) ⟩
    ω^ k * (D₁ p (r ∷ []) (c ∷ []) * ω^ e)               ≡⟨ Eq.cong (λ t → ω^ k * (D₁ p (r ∷ []) (c ∷ []) * t)) (Eq.sym ue) ⟩
    ω^ k * (D₁ p (r ∷ []) (c ∷ []) * D v (xs v) zeros)   ≡⟨ h (r ∷ xs v) (c ∷ zeros) ⟩
    ω^ k' * (D₁ p' (r ∷ []) (c ∷ []) * D v' (xs v) zeros) ≡⟨ Eq.cong (λ t → ω^ k' * (D₁ p' (r ∷ []) (c ∷ []) * t)) uv′ ⟩
    ω^ k' * (D₁ p' (r ∷ []) (c ∷ []) * ω^ j′)            ≡⟨ regroup k' j′ _ ⟩
    ω^ (k' F3.+ j′) * D₁ p' (r ∷ []) (c ∷ [])            ∎

  tailOf : p ≡ p' → (v ≡ v') × (k ≡ k')
  tailOf refl with D-inj v v' (k F3.+ u) (k' F3.+ u) rest
    where
    a = proj₁ p
    u = proj₁ (unit₁ p)
    rest : ∀ rs cs → ω^ (k F3.+ u) * D v rs cs ≡ ω^ (k' F3.+ u) * D v' rs cs
    rest rs cs = begin
      ω^ (k F3.+ u) * D v rs cs                         ≡⟨ Eq.sym (regroup′ k u _) ⟩
      ω^ k * (ω^ u * D v rs cs)                         ≡⟨ Eq.cong (λ t → ω^ k * (t * D v rs cs)) (Eq.sym (proj₂ (unit₁ p))) ⟩
      ω^ k * (D₁ p (a ∷ []) (zero ∷ []) * D v rs cs)    ≡⟨ h (a ∷ rs) (zero ∷ cs) ⟩
      ω^ k' * (D₁ p (a ∷ []) (zero ∷ []) * D v' rs cs)  ≡⟨ Eq.cong (λ t → ω^ k' * (t * D v' rs cs)) (proj₂ (unit₁ p)) ⟩
      ω^ k' * (ω^ u * D v' rs cs)                       ≡⟨ regroup′ k' u _ ⟩
      ω^ (k' F3.+ u) * D v' rs cs                       ∎
  ... | vv , ku = vv , +-cancelʳ k k' (proj₁ (unit₁ p)) ku

  go : (p ≡ p') × (k F3.+ e ≡ k' F3.+ j′) → (p ∷ v ≡ p' ∷ v') × (k ≡ k')
  go (pp , _) = Eq.cong₂ _∷_ pp (proj₁ (tailOf pp)) , proj₂ (tailOf pp)

------------------------------------------------------------------------
-- The symplectic form is nondegenerate

private
  sform1-Iʳ : (p : Pauli1) → sform1 p PS.pI ≡ zero
  sform1-Iʳ (zero , zero)                     = refl
  sform1-Iʳ (zero , suc zero)                 = refl
  sform1-Iʳ (zero , suc (suc zero))           = refl
  sform1-Iʳ (suc zero , zero)                 = refl
  sform1-Iʳ (suc zero , suc zero)             = refl
  sform1-Iʳ (suc zero , suc (suc zero))       = refl
  sform1-Iʳ (suc (suc zero) , zero)           = refl
  sform1-Iʳ (suc (suc zero) , suc zero)       = refl
  sform1-Iʳ (suc (suc zero) , suc (suc zero)) = refl

  sform-Iʳ : (P : Pauli n) → sform P pIₙ ≡ zero
  sform-Iʳ []      = refl
  sform-Iʳ (p ∷ P) = Eq.trans (Eq.cong₂ F3._+_ (sform1-Iʳ p) (sform-Iʳ P)) refl

  +0′ : (a : ℤ ₚ) → a F3.+ zero ≡ a
  +0′ zero             = refl
  +0′ (suc zero)       = refl
  +0′ (suc (suc zero)) = refl

  -- One wire, by evaluation.
  form-ok : Pauli1 → Pauli1 → Bool
  form-ok p@(a , b) p'@(a' , b') =
    (eqF a a' ∧ eqF b b') ∨ not (allP1 λ x → eqF (sform1 p x) (sform1 p' x))

  all-form : T (allP1 λ p → allP1 λ p' → form-ok p p')
  all-form = _

  ∧₂ : ∀ {x y} → T (x ∧ y) → T x × T y
  ∧₂ {true} {true} _ = tt , tt

  eqF-complete : (a b : Fin 3) → a ≡ b → T (eqF a b)
  eqF-complete zero             zero             refl = tt
  eqF-complete (suc zero)       (suc zero)       refl = tt
  eqF-complete (suc (suc zero)) (suc (suc zero)) refl = tt

sform1-inj : (p p' : Pauli1) → (∀ x → sform1 p x ≡ sform1 p' x) → p ≡ p'
sform1-inj p@(a , b) p'@(a' , b') h =
  Eq.cong₂ _,_ (eqF-sound a a' (proj₁ t)) (eqF-sound b b' (proj₂ t))
  where
  all-x : T (allP1 λ x → eqF (sform1 p x) (sform1 p' x))
  all-x = allFin-complete (λ c → all3 λ d → eqF (sform1 p (c , d)) (sform1 p' (c , d)))
            λ c → allFin-complete (λ d → eqF (sform1 p (c , d)) (sform1 p' (c , d)))
              λ d → eqF-complete _ _ (h (c , d))
  t = ∧₂ {eqF a a'} {eqF b b'}
        (∨-l {eqF a a' ∧ eqF b b'} {allP1 λ x → eqF (sform1 p x) (sform1 p' x)}
          (allP1-sound (form-ok p) (allP1-sound (λ p → allP1 (form-ok p)) all-form p) p')
          all-x)

sform-inj : (P P' : Pauli n) → (∀ e → sform P e ≡ sform P' e) → P ≡ P'
sform-inj []      []        h = refl
sform-inj (p ∷ P) (p' ∷ P') h = Eq.cong₂ _∷_ head (sform-inj P P' tail)
  where
  head : p ≡ p'
  head = sform1-inj p p' λ x →
    Eq.trans (Eq.sym (Eq.trans (Eq.cong (sform1 p x F3.+_) (sform-Iʳ P)) (+0′ _)))
      (Eq.trans (h (x ∷ pIₙ)) (Eq.trans (Eq.cong (sform1 p' x F3.+_) (sform-Iʳ P')) (+0′ _)))
  tail : ∀ e → sform P e ≡ sform P' e
  tail e = begin
    sform P e                               ≡⟨ Eq.sym (0+′ _) ⟩
    zero F3.+ sform P e                     ≡⟨ Eq.cong (F3._+ sform P e) (Eq.sym (sform1-Iʳ p)) ⟩
    sform1 p PS.pI F3.+ sform P e           ≡⟨ h (PS.pI ∷ e) ⟩
    sform1 p' PS.pI F3.+ sform P' e         ≡⟨ Eq.cong (F3._+ sform P' e) (sform1-Iʳ p') ⟩
    zero F3.+ sform P' e                    ≡⟨ 0+′ _ ⟩
    sform P' e                              ∎

------------------------------------------------------------------------
-- Inverse words: a circuit's matrix has a right inverse up to √3^k

inv₀ : Gen n → Word (Gen n)
inv₀ (gate₁ H-gate)  = [ gate₁ H-gate ]ʷ • ([ gate₁ H-gate ]ʷ • [ gate₁ H-gate ]ʷ)
inv₀ (gate₁ S-gate)  = [ gate₁ S-gate ]ʷ • [ gate₁ S-gate ]ʷ
inv₀ (gate₂ CZ-gate) = [ gate₂ CZ-gate ]ʷ • [ gate₂ CZ-gate ]ʷ
inv₀ (g ↥)           = wmap _↥ (inv₀ g)

inv : Word (Gen n) → Word (Gen n)
inv [ g ]ʷ  = inv₀ g
inv ε       = ε
inv (u • v) = inv v • inv u

infixr 2 _⟨≐⟩_
_⟨≐⟩_ : {m : ℕ} {L M N : Op m} → L ≐ M → M ≐ N → L ≐ N
_⟨≐⟩_ = ≐-trans

private
  ix-M : (u v : Word (Gen n)) → ix (proj₂ (M (u • v))) ≐ (ix (proj₂ (M u)) ⊙ ix (proj₂ (M v)))
  ix-M u v = ix-mul (proj₂ (M u)) (proj₂ (M v))

-- A word one wire up reads as its matrix one wire up.
M-↥ : (w : Word (Gen n)) → ix (proj₂ (M (wmap _↥ w))) ≐ up (ix (proj₂ (M w)))
M-↥ [ g ]ʷ  = ix-up (proj₂ (M₀ g))
M-↥ ε       = ≐-trans ix-id (≐-trans (≐-sym up-Id) (up-cong (≐-sym ix-id)))
M-↥ (u • v) =
  ≐-trans (ix-M (wmap _↥ u) (wmap _↥ v))
    (≐-trans (⊙-cong (M-↥ u) (M-↥ v))
      (≐-trans (up-⊙ (ix (proj₂ (M u))) (ix (proj₂ (M v))))
        (up-cong (≐-sym (ix-M u v)))))

RightInv : Op n → Op n → Set
RightInv A B = Σ ℕ λ k → (A ⊙ B) ≐ scale (√3 ^ k) Idₒ

private
  r^-+ : (a b : ℕ) → √3 ^ (a +ℕ b) ≡ √3 ^ a * √3 ^ b
  r^-+ ℕ.zero    b = Eq.sym (*-identityˡ (√3 ^ b))
  r^-+ (ℕ.suc a) b = Eq.trans (Eq.cong (√3 *_) (r^-+ a b)) (Eq.sym (*-assoc √3 (√3 ^ a) (√3 ^ b)))

  scale-≡ : {m : ℕ} {a b : Q} (N : Op m) → a ≡ b → scale a N ≐ scale b N
  scale-≡ N refl = ≐-refl _

  -- A gate on the bottom wires whose power is a multiple of the identity.
  emb-pow : {k : ℕ} (G : Op k) (c : Q) → (G ⊙ (G ⊙ (G ⊙ G))) ≐ scale c Idₒ →
            (emb {k} {n} G ⊙ (emb G ⊙ (emb G ⊙ emb G))) ≐ scale c Idₒ
  emb-pow {n = n} {k = k} G c e =
    ≐-trans (⊙-cong (≐-refl (emb {k} {n} G)) (⊙-cong (≐-refl (emb {k} {n} G)) (emb-⊙ G G)))
    (≐-trans (⊙-cong (≐-refl (emb {k} {n} G)) (emb-⊙ G (G ⊙ G)))
    (≐-trans (emb-⊙ G (G ⊙ (G ⊙ G)))
    (≐-trans (emb-cong {k = k} {n = n} e)
    (≐-trans (emb-scale {k = k} {n = n} c Idₒ) (scale-cong {c = c} (emb-id {k = k} {n = n}))))))

  emb-pow₃ : {k : ℕ} (G : Op k) (c : Q) → (G ⊙ (G ⊙ G)) ≐ scale c Idₒ →
             (emb {k} {n} G ⊙ (emb G ⊙ emb G)) ≐ scale c Idₒ
  emb-pow₃ {n = n} {k = k} G c e =
    ≐-trans (⊙-cong (≐-refl (emb {k} {n} G)) (emb-⊙ G G))
    (≐-trans (emb-⊙ G (G ⊙ G))
    (≐-trans (emb-cong {k = k} {n = n} e)
    (≐-trans (emb-scale {k = k} {n = n} c Idₒ) (scale-cong {c = c} (emb-id {k = k} {n = n})))))

  -- On their own wires, by evaluation, decided by one boolean (eqWith).
  local-pow : {k : ℕ} (G : Mat k) (c : Q) →
              T (eqWith 1# c (mulM G (mulM G (mulM G G))) idM) →
              (ix G ⊙ (ix G ⊙ (ix G ⊙ ix G))) ≐ scale c Idₒ
  local-pow G c t =
    ≐-trans (⊙-cong (≐-refl (ix G)) (⊙-cong (≐-refl (ix G)) (≐-sym (ix-mul G G))))
    (≐-trans (⊙-cong (≐-refl (ix G)) (≐-sym (ix-mul G (mulM G G))))
    (≐-trans (≐-sym (ix-mul G (mulM G (mulM G G))))
    (≐-trans (≐-sym (scale-1 (ix (mulM G (mulM G (mulM G G))))))
    (≐-trans (eqWith-sound 1# c (mulM G (mulM G (mulM G G))) idM t)
      (scale-cong {c = c} ix-id)))))

  local-pow₃ : {k : ℕ} (G : Mat k) (c : Q) →
               T (eqWith 1# c (mulM G (mulM G G)) idM) →
               (ix G ⊙ (ix G ⊙ ix G)) ≐ scale c Idₒ
  local-pow₃ G c t =
    ≐-trans (⊙-cong (≐-refl (ix G)) (≐-sym (ix-mul G G)))
    (≐-trans (≐-sym (ix-mul G (mulM G G)))
    (≐-trans (≐-sym (scale-1 (ix (mulM G (mulM G G)))))
    (≐-trans (eqWith-sound 1# c (mulM G (mulM G G)) idM t)
      (scale-cong {c = c} ix-id))))

inv-right₀ : (g : Gen n) → RightInv (ix (proj₂ (M₀ g))) (ix (proj₂ (M (inv₀ g))))
inv-right₀ {ℕ.suc n} (gate₁ H-gate) = 4 ,
  ≐-trans (⊙-cong (ix-emb (proj₂ Hᵍ))
            (≐-trans (ix-M [ gate₁ H-gate ]ʷ ([ gate₁ H-gate ]ʷ • [ gate₁ H-gate ]ʷ))
              (⊙-cong (ix-emb (proj₂ Hᵍ))
                (≐-trans (ix-M [ gate₁ H-gate ]ʷ [ gate₁ H-gate ]ʷ)
                  (⊙-cong (ix-emb (proj₂ Hᵍ)) (ix-emb (proj₂ Hᵍ)))))))
    (emb-pow {n = n} {k = 1} (ix (proj₂ Hᵍ)) (√3 ^ 4) (local-pow (proj₂ Hᵍ) (√3 ^ 4) _))
inv-right₀ {ℕ.suc n} (gate₁ S-gate) = 0 ,
  ≐-trans (⊙-cong (ix-emb (proj₂ Sᵍ))
            (≐-trans (ix-M [ gate₁ S-gate ]ʷ [ gate₁ S-gate ]ʷ)
              (⊙-cong (ix-emb (proj₂ Sᵍ)) (ix-emb (proj₂ Sᵍ)))))
    (emb-pow₃ {n = n} {k = 1} (ix (proj₂ Sᵍ)) (√3 ^ 0) (local-pow₃ (proj₂ Sᵍ) (√3 ^ 0) _))
inv-right₀ {ℕ.suc (ℕ.suc n)} (gate₂ CZ-gate) = 0 ,
  ≐-trans (⊙-cong (ix-emb (proj₂ CZᵍ))
            (≐-trans (ix-M [ gate₂ CZ-gate ]ʷ [ gate₂ CZ-gate ]ʷ)
              (⊙-cong (ix-emb (proj₂ CZᵍ)) (ix-emb (proj₂ CZᵍ)))))
    (emb-pow₃ {n = n} {k = 2} (ix (proj₂ CZᵍ)) (√3 ^ 0) (local-pow₃ (proj₂ CZᵍ) (√3 ^ 0) _))
inv-right₀ (g ↥) with inv-right₀ g
... | k , e = k ,
  ≐-trans (⊙-cong (ix-up (proj₂ (M₀ g))) (M-↥ (inv₀ g)))
    (≐-trans (up-⊙ (ix (proj₂ (M₀ g))) (ix (proj₂ (M (inv₀ g)))))
      (≐-trans (up-cong e)
        (≐-trans (up-scale (√3 ^ k) Idₒ) (scale-cong {c = √3 ^ k} up-Id))))

inv-right : (u : Word (Gen n)) → RightInv (ix (proj₂ (M u))) (ix (proj₂ (M (inv u))))
inv-right [ g ]ʷ  = inv-right₀ g
inv-right ε       = 0 ,
  ≐-trans (⊙-cong ix-id ix-id)
    (≐-trans (⊙-identityˡ Idₒ) (≐-sym (scale-1 Idₒ)))
inv-right (u • v) with inv-right u | inv-right v
... | ku , eu | kv , ev = kv +ℕ ku ,
  ( ⊙-cong (ix-M u v) (ix-M (inv v) (inv u))
  ⟨≐⟩ ⊙-assoc A B (B′ ⊙ A′)
  ⟨≐⟩ ⊙-cong (≐-refl A) (≐-sym (⊙-assoc B B′ A′))
  ⟨≐⟩ ⊙-cong (≐-refl A) (⊙-cong ev (≐-refl A′))
  ⟨≐⟩ ⊙-cong (≐-refl A) (scale-⊙ˡ (√3 ^ kv) Idₒ A′)
  ⟨≐⟩ ⊙-cong (≐-refl A) (scale-cong {c = √3 ^ kv} (⊙-identityˡ A′))
  ⟨≐⟩ scale-⊙ʳ (√3 ^ kv) A A′
  ⟨≐⟩ scale-cong {c = √3 ^ kv} eu
  ⟨≐⟩ scale-scale (√3 ^ kv) (√3 ^ ku) Idₒ
  ⟨≐⟩ scale-≡ Idₒ (Eq.sym (r^-+ kv ku)) )
  where
  A  = ix (proj₂ (M u))
  B  = ix (proj₂ (M v))
  A′ = ix (proj₂ (M (inv u)))
  B′ = ix (proj₂ (M (inv v)))

------------------------------------------------------------------------
-- Faithfulness

open Phases (λ _ → ⊤) tt (λ _ _ → tt) (λ _ → tt) public
  using () renaming (_≈_ to _≈ᵖ_ ; phased to phasedᵖ)

private
  cancel-r : (h : ℕ) {m : ℕ} {M N : Op m} → scale (√3 ^ h) M ≐ scale (√3 ^ h) N → M ≐ N
  cancel-r h e i j = r^-cancel h (e i j)

-- Proportional matrices have the same interpretation.
faithful : (u u' : Word (Gen n)) → M u ≈ᵖ M u' →
           (proj₁ ⟦ u ⟧ᵖ ≡ proj₁ ⟦ u' ⟧ᵖ) × (∀ v → ap (proj₂ ⟦ u ⟧ᵖ) v ≡ ap (proj₂ ⟦ u' ⟧ᵖ) v)
faithful {n} u u' (phasedᵖ k _ agree) = P≡ , S≡
  where
  A = ix (proj₂ (M u))
  B = ix (proj₂ (M u'))
  c₁ = √3 ^ proj₁ (M u')
  c₂ = x ^ k * √3 ^ proj₁ (M u)
  P  = proj₁ ⟦ u ⟧ᵖ
  S  = proj₂ ⟦ u ⟧ᵖ
  P′ = proj₁ ⟦ u' ⟧ᵖ
  S′ = proj₂ ⟦ u' ⟧ᵖ
  f f′ : Pauli n → ℤ ₚ
  f v  = sform P (ap S v)
  f′ v = sform P′ (ap S′ v)

  -- Both laws, read on A.
  both : ∀ v → scale (ω^ (f v)) (D (ap S v) ⊙ A) ≐ scale (ω^ (f′ v)) (D (ap S′ v) ⊙ A)
  both v = cancel-r (proj₁ (M u'))
    ( scale-cong {c = c₁} (≐-sym (at (law u) v))
    ⟨≐⟩ ≐-sym (scale-⊙ˡ c₁ A (D v))
    ⟨≐⟩ ⊙-cong agree (≐-refl (D v))
    ⟨≐⟩ scale-⊙ˡ c₂ B (D v)
    ⟨≐⟩ scale-cong {c = c₂} (at (law u') v)
    ⟨≐⟩ scale-scale c₂ (ω^ (f′ v)) (D (ap S′ v) ⊙ B)
    ⟨≐⟩ scale-≡ (D (ap S′ v) ⊙ B) (*-comm c₂ (ω^ (f′ v)))
    ⟨≐⟩ ≐-sym (scale-scale (ω^ (f′ v)) c₂ (D (ap S′ v) ⊙ B))
    ⟨≐⟩ scale-cong {c = ω^ (f′ v)} (≐-sym (scale-⊙ʳ c₂ (D (ap S′ v)) B))
    ⟨≐⟩ scale-cong {c = ω^ (f′ v)} (⊙-cong (≐-refl (D (ap S′ v))) (≐-sym agree))
    ⟨≐⟩ scale-cong {c = ω^ (f′ v)} (scale-⊙ʳ c₁ (D (ap S′ v)) A)
    ⟨≐⟩ scale-scale (ω^ (f′ v)) c₁ (D (ap S′ v) ⊙ A)
    ⟨≐⟩ scale-≡ (D (ap S′ v) ⊙ A) (*-comm (ω^ (f′ v)) c₁)
    ⟨≐⟩ ≐-sym (scale-scale c₁ (ω^ (f′ v)) (D (ap S′ v) ⊙ A)) )

  m = proj₁ (inv-right u)
  A′ = ix (proj₂ (M (inv u)))

  -- Cancel A on the right.
  right : {y : Pauli n} (a : Q) → (scale a (D y ⊙ A) ⊙ A′) ≐ scale (√3 ^ m) (scale a (D y))
  right {y} a =
    scale-⊙ˡ a (D y ⊙ A) A′
    ⟨≐⟩ scale-cong {c = a} (⊙-assoc (D y) A A′)
    ⟨≐⟩ scale-cong {c = a} (⊙-cong (≐-refl (D y)) (proj₂ (inv-right u)))
    ⟨≐⟩ scale-cong {c = a} (scale-⊙ʳ (√3 ^ m) (D y) Idₒ)
    ⟨≐⟩ scale-cong {c = a} (scale-cong {c = √3 ^ m} (⊙-identityʳ (D y)))
    ⟨≐⟩ scale-scale a (√3 ^ m) (D y)
    ⟨≐⟩ scale-≡ (D y) (*-comm a (√3 ^ m))
    ⟨≐⟩ ≐-sym (scale-scale (√3 ^ m) a (D y))

  weyl : ∀ v → (ap S v ≡ ap S′ v) × (f v ≡ f′ v)
  weyl v = D-inj (ap S v) (ap S′ v) (f v) (f′ v)
             (cancel-r m (≐-trans (≐-sym (right {y = ap S v} (ω^ (f v))))
                           (≐-trans (⊙-cong (both v) (≐-refl A′)) (right {y = ap S′ v} (ω^ (f′ v))))))

  S≡ : ∀ v → ap S v ≡ ap S′ v
  S≡ v = proj₁ (weyl v)

  P≡ : P ≡ P′
  P≡ = sform-inj P P′ λ e →
    let v = ap⁻¹ S e in
    begin
      sform P e                 ≡⟨ Eq.cong (sform P) (Eq.sym (invʳ S e)) ⟩
      sform P (ap S v)          ≡⟨ proj₂ (weyl v) ⟩
      sform P′ (ap S′ v)        ≡⟨ Eq.cong (sform P′) (Eq.sym (S≡ v)) ⟩
      sform P′ (ap S v)         ≡⟨ Eq.cong (sform P′) (invʳ S e) ⟩
      sform P′ e                ∎
