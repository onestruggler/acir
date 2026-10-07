------------------------------------------------------------------------
-- Presentations of groups
--
-- The X column: translations, and how linear circuits move them
--
-- Xc b is an X on every wire where b has a 1: the translation
-- x ↦ x ⊕ b.  A linear circuit L sends a translation by v to a
-- translation by its image, L • Xc v ≈ Xc (L v) • L (Xc-pushʷ), so
-- every affine circuit is Xc b • L; and translations add (Xc-xor).
-- Linear circuits and translations permute basis states and carry no
-- phase (PS-⌊⌋, PS-Xc).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Affine where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; head ; tail ; replicate ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.CNOT+Dihedral.Semantics
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Interpretation
open import Examples.Groups.CNOT+Dihedral.Soundness using (sound)
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.LocalX
open import Examples.Groups.CNOT+Dihedral.Linear.Base using (LGen ; cnot ; swap ; _↥ₗ ; ι ; ⌊_⌋)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Translations

Xb : Bool → Circuit (₁₊ n)
Xb true  = X
Xb false = ε

Xc : Bits n → Circuit n
Xc []      = ε
Xc (b ∷ v) = Xb b • Xc v ↑

-- What a linear generator does to a vector.
lmap : LGen n → Bits n → Bits n
lmap cnot   (t ∷ c ∷ v) = (c xor t) ∷ c ∷ v
lmap swap   (a ∷ b ∷ v) = b ∷ a ∷ v
lmap (y ↥ₗ) (a ∷ v)     = a ∷ lmap y v

lmapʷ : Word (LGen n) → Bits n → Bits n
lmapʷ [ y ]ʷ  v = lmap y v
lmapʷ ε       v = v
lmapʷ (w • u) v = lmapʷ w (lmapʷ u v)

------------------------------------------------------------------------
-- Moving translations past linear circuits

private
  Xb-up : (g : Gen n) (b : Bool) → (₁₊ n) ⊢ [ g ↥ ]ʷ • Xb b ≈ Xb b • [ g ↥ ]ʷ
  Xb-up g true      = ax' (comm₁ X-gate g)
  Xb-up {n} g false = Width.slide-ε (₁₊ n)

  -- A gate on the bottom wires past a gadget, the rest two wires up.
  glueX : ∀ {y A B A' B' : Circuit (₂₊ n)} (τ : Circuit n) →
          (₂₊ n) ⊢ y • τ ↑ ↑ ≈ τ ↑ ↑ • y →
          (₂₊ n) ⊢ y • A • B ≈ A' • B' • y →
          (₂₊ n) ⊢ y • A • B • τ ↑ ↑ ≈ (A' • B' • τ ↑ ↑) • y
  glueX {n} {y} {A} {B} {A'} {B'} τ c e = begin
    y • A • B • τ ↑ ↑            ≈⟨ sym assoc ⟩
    (y • A) • B • τ ↑ ↑          ≈⟨ sym assoc ⟩
    ((y • A) • B) • τ ↑ ↑        ≈⟨ front _ assoc ⟩
    (y • A • B) • τ ↑ ↑          ≈⟨ front _ e ⟩
    (A' • B' • y) • τ ↑ ↑        ≈⟨ assoc ⟩
    A' • (B' • y) • τ ↑ ↑        ≈⟨ back A' assoc ⟩
    A' • B' • y • τ ↑ ↑          ≈⟨ back A' (back B' c) ⟩
    A' • B' • τ ↑ ↑ • y          ≈⟨ back A' (sym assoc) ⟩
    A' • (B' • τ ↑ ↑) • y        ≈⟨ sym assoc ⟩
    (A' • B' • τ ↑ ↑) • y        ∎
    where open Width (₂₊ n)

  loc-cnot : (t c : Bool) →
             (₂₊ n) ⊢ CNOT • Xb t • (Xb c) ↑ ≈ Xb (c xor t) • (Xb c) ↑ • CNOT
  loc-cnot {n} false false = by-assoc Eq.refl
    where open Width (₂₊ n)
  loc-cnot {n} true  false = trans (by-assoc Eq.refl) (trans CNOT-X (by-assoc Eq.refl))
    where open Width (₂₊ n)
  loc-cnot {n} false true  = trans (by-assoc Eq.refl) CNOT-X↑
    where open Width (₂₊ n)
  loc-cnot {n} true  true  = trans CNOT-XX↑ (by-assoc Eq.refl)
    where open Width (₂₊ n)

  loc-swap : (a b : Bool) →
             (₂₊ n) ⊢ SWAP • Xb a • (Xb b) ↑ ≈ Xb b • (Xb a) ↑ • SWAP
  loc-swap {n} false false = by-assoc Eq.refl
    where open Width (₂₊ n)
  loc-swap {n} true  false = trans (by-assoc Eq.refl) (trans SWAP-X (by-assoc Eq.refl))
    where open Width (₂₊ n)
  loc-swap {n} false true  = trans (by-assoc Eq.refl) (trans SWAP-X↑ (by-assoc Eq.refl))
    where open Width (₂₊ n)
  loc-swap {n} true  true  = SWAP-XX↑

Xc-push : (y : LGen n) (v : Bits n) → n ⊢ [ ι y ]ʷ • Xc v ≈ Xc (lmap y v) • [ ι y ]ʷ
Xc-push {n} (y ↥ₗ) (a ∷ v) = begin
  [ ι y ↥ ]ʷ • Xb a • Xc v ↑               ≈⟨ sym assoc ⟩
  ([ ι y ↥ ]ʷ • Xb a) • Xc v ↑             ≈⟨ front _ (Xb-up (ι y) a) ⟩
  (Xb a • [ ι y ↥ ]ʷ) • Xc v ↑             ≈⟨ assoc ⟩
  Xb a • ([ ι y ]ʷ • Xc v) ↑               ≈⟨ back _ (lift (Xc-push y v)) ⟩
  Xb a • (Xc (lmap y v) • [ ι y ]ʷ) ↑      ≈⟨ sym assoc ⟩
  (Xb a • Xc (lmap y v) ↑) • [ ι y ↥ ]ʷ    ∎
  where open Width n
Xc-push cnot (t ∷ c ∷ v) =
  glueX (Xc v) (Width.sym (comm-gate₂-w↑↑ CNOT-gate (Xc v))) (loc-cnot t c)
Xc-push swap (a ∷ b ∷ v) =
  glueX (Xc v) (Width.sym (comm-gate₂-w↑↑ SWAP-gate (Xc v))) (loc-swap a b)

Xc-pushʷ : (L : Word (LGen n)) (v : Bits n) → n ⊢ ⌊ L ⌋ • Xc v ≈ Xc (lmapʷ L v) • ⌊ L ⌋
Xc-pushʷ [ y ]ʷ v = Xc-push y v
Xc-pushʷ {n} ε v = trans left-unit (sym right-unit)
  where open Width n
Xc-pushʷ {n} (w • u) v = begin
  (⌊ w ⌋ • ⌊ u ⌋) • Xc v                              ≈⟨ assoc ⟩
  ⌊ w ⌋ • ⌊ u ⌋ • Xc v                                ≈⟨ back _ (Xc-pushʷ u v) ⟩
  ⌊ w ⌋ • Xc (lmapʷ u v) • ⌊ u ⌋                      ≈⟨ sym assoc ⟩
  (⌊ w ⌋ • Xc (lmapʷ u v)) • ⌊ u ⌋                    ≈⟨ front _ (Xc-pushʷ w (lmapʷ u v)) ⟩
  (Xc (lmapʷ w (lmapʷ u v)) • ⌊ w ⌋) • ⌊ u ⌋          ≈⟨ assoc ⟩
  Xc (lmapʷ w (lmapʷ u v)) • ⌊ w ⌋ • ⌊ u ⌋            ∎
  where open Width n

------------------------------------------------------------------------
-- Adding translations

Xb-xor : (a b : Bool) → (₁₊ n) ⊢ Xb a • Xb b ≈ Xb (a xor b)
Xb-xor true  true      = ax R₁
Xb-xor {n} true  false = Width.right-unit
Xb-xor {n} false b     = Width.left-unit

private
  Xb-↑ : (b : Bool) (w : Circuit n) → (₁₊ n) ⊢ w ↑ • Xb b ≈ Xb b • w ↑
  Xb-↑ true  w     = comm-gate₁-w↑ X-gate w
  Xb-↑ {n} false w = Width.slide-ε (₁₊ n)
    where open Width (₁₊ n)

Xc-xor : (u v : Bits n) → n ⊢ Xc u • Xc v ≈ Xc (zipWith _xor_ u v)
Xc-xor {n} [] [] = left-unit
  where open Width n
Xc-xor {n} (a ∷ u) (b ∷ v) = begin
  (Xb a • Xc u ↑) • Xb b • Xc v ↑        ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  Xb a • (Xc u ↑ • Xb b) • Xc v ↑        ≈⟨ back _ (front _ (Xb-↑ b (Xc u))) ⟩
  Xb a • (Xb b • Xc u ↑) • Xc v ↑        ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (Xb a • Xb b) • Xc u ↑ • Xc v ↑        ≈⟨ cong (Xb-xor a b) (lift (Xc-xor u v)) ⟩
  Xb (a xor b) • Xc (zipWith _xor_ u v) ↑ ∎
  where open Width n

Xc-zero : (n : ℕ) → n ⊢ Xc (replicate n false) ≈ ε
Xc-zero zero    = Width.refl
Xc-zero (suc n) = Width.trans Width.left-unit (lift (Xc-zero n))

------------------------------------------------------------------------
-- Permutations of basis states without phase

PS : Circuit n → (Bits n → Bits n) → Set
PS {n} w f = (x : Bits n) → ⟦ w ⟧ x ≡ (f x , 0₈)

PS-ext : ∀ {w : Circuit n} {f g} → PS w f → (∀ x → f x ≡ g x) → PS w g
PS-ext d e x = Eq.trans (d x) (Eq.cong (_, 0₈) (e x))

PS-• : ∀ {a b : Circuit n} {f g} → PS a f → PS b g → PS (a • b) (λ x → f (g x))
PS-• {a = a} {b} {f} {g} da db x =
  Eq.trans (⟦⟧-• a b x)
    (Eq.trans (Eq.cong (λ p → proj₁ (⟦ a ⟧ (proj₁ p)) , proj₂ p + proj₂ (⟦ a ⟧ (proj₁ p))) (db x))
              (Eq.cong (λ p → proj₁ p , 0₈ + proj₂ p) (da (g x))))

PS-ε : PS {n} ε (λ x → x)
PS-ε x = ⟦⟧-ε x

PS-↑ : ∀ {a : Circuit n} {f} → PS a f → PS (a ↑) (λ v → head v ∷ f (tail v))
PS-↑ {a = a} d (b ∷ x) = Eq.trans (up-word a (b ∷ x)) (Eq.cong (λ p → b ∷ proj₁ p , proj₂ p) (d x))

PS-ι : (y : LGen n) → PS [ ι y ]ʷ (lmap y)
PS-ι cnot     (t ∷ c ∷ v) = ⟦⟧-gen CNOT-gen (t ∷ c ∷ v)
PS-ι swap     (a ∷ b ∷ v) = ⟦⟧-gen SWAP-gen (a ∷ b ∷ v)
PS-ι (y ↥ₗ)   (a ∷ v)     = PS-↑ (PS-ι y) (a ∷ v)

PS-⌊⌋ : (L : Word (LGen n)) → PS ⌊ L ⌋ (lmapʷ L)
PS-⌊⌋ [ y ]ʷ  = PS-ι y
PS-⌊⌋ ε       = PS-ε
PS-⌊⌋ (w • u) = PS-• (PS-⌊⌋ w) (PS-⌊⌋ u)

PS-Xb : (b : Bool) → PS {₁₊ n} (Xb b) (λ v → (head v xor b) ∷ tail v)
PS-Xb true  (a ∷ x) = Eq.trans (⟦⟧-gen X-gen (a ∷ x)) (Eq.cong (λ c → c ∷ x , 0₈) (xor-true a))
  where
  xor-true : ∀ a → not a ≡ (a xor true)
  xor-true true  = Eq.refl
  xor-true false = Eq.refl
PS-Xb false (a ∷ x) = Eq.trans (⟦⟧-ε (a ∷ x)) (Eq.cong (λ c → c ∷ x , 0₈) (xor-false a))
  where
  xor-false : ∀ a → a ≡ (a xor false)
  xor-false true  = Eq.refl
  xor-false false = Eq.refl

PS-Xc : (b : Bits n) → PS (Xc b) (λ x → zipWith _xor_ x b)
PS-Xc []      []      = ⟦⟧-ε []
PS-Xc (b ∷ v) (a ∷ x) = PS-• (PS-Xb b) (PS-↑ (PS-Xc v)) (a ∷ x)

-- Linear circuits fix 0.
lmapʷ-zero : (L : Word (LGen n)) → lmapʷ L (replicate n false) ≡ replicate n false
lmapʷ-zero [ y ]ʷ  = lmap-zero y
  where
  lmap-zero : ∀ {n} (y : LGen n) → lmap y (replicate n false) ≡ replicate n false
  lmap-zero cnot     = Eq.refl
  lmap-zero swap     = Eq.refl
  lmap-zero (y ↥ₗ)   = Eq.cong (false ∷_) (lmap-zero y)
lmapʷ-zero ε       = Eq.refl
lmapʷ-zero (w • u) = Eq.trans (Eq.cong (lmapʷ w) (lmapʷ-zero u)) (lmapʷ-zero w)
