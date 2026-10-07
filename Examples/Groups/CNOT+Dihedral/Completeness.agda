------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the CNOT-dihedral relations
--
-- Every circuit is, by the relations, a diagonal part, a translation
-- and a linear part,
--
--     ω ^ s • P ℓ₁ ^ k₁ • … • P ℓⱼ ^ kⱼ • Xc b • L            (decompose)
--
-- (the paper's Lemma 5.1, with the diagonal part spelled in phase
-- gates): a circuit is read one letter at a time, ω moving to the
-- front, an X column through L, a linear gate joining L, and a T,
-- conjugated by L and by the translation, becoming a phase gate
-- (Diagonal.Phase).  Two circuits with the same operator have the
-- same translation (the image of 0), linear parts with the same
-- operator, hence equal (Linear.Completeness), and then diagonal parts
-- with the same operator, hence equal (Diagonal.Complete).  Both use
-- completeness one wire down, so completeness holds at every width by
-- induction, from width 0 where every circuit is a power of ω.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Completeness where

open import Data.Bool using (Bool ; true ; false ; _xor_ ; if_then_else_)
open import Data.Bool.Properties using (xor-same ; xor-identityʳ)
open import Data.Fin using (toℕ)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.Nat using (ℕ ; zero ; suc ; _%_) renaming (_+_ to _+ℕ_)
open import Data.Nat.DivMod using (_mod_ ; m%n<n)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; head ; tail ; replicate ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.CNOT+Dihedral.Semantics
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Interpretation using (⟦_⟧ ; ⟦⟧-•)
open import Examples.Groups.CNOT+Dihedral.Soundness using (sound)
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Powers
open import Examples.Groups.CNOT+Dihedral.Evaluation
open import Examples.Groups.CNOT+Dihedral.Affine
open import Examples.Groups.CNOT+Dihedral.Linear.Base
open import Examples.Groups.CNOT+Dihedral.Linear.Steps using (LNF ; lnf)
open import Examples.Groups.CNOT+Dihedral.Linear.Semantics using (dot)
open import Examples.Groups.CNOT+Dihedral.Linear.Completeness using (linear-complete)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Phase
open import Examples.Groups.CNOT+Dihedral.Diagonal.Calculus
open import Examples.Groups.CNOT+Dihedral.Diagonal.Semantics using (DS ; DS-ₑ ; φₑ ; powφ ; DS-^ ; DS-ω)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Unique using (powφ-1)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Complete using (dpart ; diag-complete)

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- Vectors over F₂

zeros : Bits n
zeros {n} = replicate n false

infixl 6 _⊕_
_⊕_ : Bits n → Bits n → Bits n
_⊕_ = zipWith _xor_

⊕-self : (v : Bits n) → v ⊕ v ≡ zeros
⊕-self []      = Eq.refl
⊕-self (a ∷ v) = Eq.cong₂ _∷_ (xor-same a) (⊕-self v)

zeros-⊕ : (v : Bits n) → zeros ⊕ v ≡ v
zeros-⊕ []      = Eq.refl
zeros-⊕ (a ∷ v) = Eq.cong (a ∷_) (zeros-⊕ v)

⊕-cancelʳ : (u v b : Bits n) → u ⊕ b ≡ v ⊕ b → u ≡ v
⊕-cancelʳ []      []      []      e = Eq.refl
⊕-cancelʳ (a ∷ u) (c ∷ v) (d ∷ b) e =
  Eq.cong₂ _∷_ (xor-cancel a c d (Eq.cong head e)) (⊕-cancelʳ u v b (Eq.cong tail e))
  where
  xor-cancel : ∀ a c d → (a xor d) ≡ (c xor d) → a ≡ c
  xor-cancel true  true  d e = Eq.refl
  xor-cancel false false d e = Eq.refl
  xor-cancel true  false true  ()
  xor-cancel true  false false ()
  xor-cancel false true  true  ()
  xor-cancel false true  false ()

------------------------------------------------------------------------
-- The letters

data Kind : ℕ → Set where
  kω : Kind n
  kX : Bits n → Kind n
  kT : NZ n → Kind n
  kL : LGen n → Kind n

shiftK : Kind n → Kind (₁₊ n)
shiftK kω     = kω
shiftK (kX v) = kX (false ∷ v)
shiftK (kT ℓ) = kT (liftNZ ℓ)
shiftK (kL y) = kL (y ↥ₗ)

classify : Gen n → Kind n
classify (gate₀ ω-gate)    = kω
classify (gate₁ X-gate)    = kX (true ∷ zeros)
classify (gate₁ T-gate)    = kT e₀
classify (gate₂ CNOT-gate) = kL cnot
classify (gate₂ SWAP-gate) = kL swap
classify (g ↥)             = shiftK (classify g)

⟦_⟧ₖ : Kind n → Circuit n
⟦ kω ⟧ₖ   = ω
⟦ kX v ⟧ₖ = Xc v
⟦ kT ℓ ⟧ₖ = Pz ℓ
⟦ kL y ⟧ₖ = [ ι y ]ʷ

private
  shift-sound : (k : Kind n) → (₁₊ n) ⊢ ⟦ k ⟧ₖ ↑ ≈ ⟦ shiftK k ⟧ₖ
  shift-sound kω     = ω↑
  shift-sound {n} (kX v) = Width.sym Width.left-unit
  shift-sound (kT ℓ) = Pz-↑ ℓ
  shift-sound {n} (kL y) = Width.refl

classify-sound : (g : Gen n) → n ⊢ [ g ]ʷ ≈ ⟦ classify g ⟧ₖ
classify-sound (gate₀ ω-gate) = Width.refl
classify-sound {suc n} (gate₁ X-gate) =
  Width.sym (Width.trans (Width.back (₁₊ n) X (lift (Xc-zero n))) Width.right-unit)
classify-sound {suc n} (gate₁ T-gate) = by-assoc Eq.refl
  where open Width (₁₊ n)
classify-sound (gate₂ CNOT-gate) = Width.refl
classify-sound (gate₂ SWAP-gate) = Width.refl
classify-sound (g ↥) = Width.trans (lift (classify-sound g)) (shift-sound (classify g))

------------------------------------------------------------------------
-- A phase gate conjugated by a translation

private
  -- The parity read off a linear representative's image.
  head-lmap : (ℓ : NZ (₁₊ n)) (b : Bits (₁₊ n)) → head (lmapʷ (rL ℓ) b) ≡ dot ℓ b
  head-lmap ℓ b =
    Eq.trans (Eq.cong head (Eq.sym (Eq.cong proj₁ (PS-⌊⌋ (rL ℓ) b))))
      (Eq.trans (Eq.cong (λ w → head (fn w b)) (Eq.sym (r-⌊⌋ ℓ))) (r-head ℓ b))
    where open import Examples.Groups.CNOT+Dihedral.Linear.Semantics using (r-head)

  vec-η : ∀ {A : Set} (v : Vec A (₁₊ n)) → v ≡ head v ∷ tail v
  vec-η (a ∷ v) = Eq.refl

  -- On wire 0: X T X = ω T⁷ (R₁₁).
  core : (c₀ : Bool) (c : Bits n) →
         (₁₊ n) ⊢ Xc (c₀ ∷ c) • T • Xc (c₀ ∷ c) ≈
                  (if c₀ then ω • T ^ 7 else T)
  core {n} c₀ c = begin
    (Xb c₀ • Xc c ↑) • T • Xb c₀ • Xc c ↑
      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □) • □ • □) Eq.refl ⟩
    Xb c₀ • (Xc c ↑ • T) • Xb c₀ • Xc c ↑
      ≈⟨ back _ (front _ (comm-gate₁-w↑ T-gate (Xc c))) ⟩
    Xb c₀ • (T • Xc c ↑) • Xb c₀ • Xc c ↑
      ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
    Xb c₀ • T • (Xc c ↑ • Xb c₀) • Xc c ↑
      ≈⟨ back _ (back _ (front _ (Xb-↑' c₀ (Xc c)))) ⟩
    Xb c₀ • T • (Xb c₀ • Xc c ↑) • Xc c ↑
      ≈⟨ by-passoc (□ • □ • (□ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    Xb c₀ • T • Xb c₀ • (Xc c ↑ • Xc c ↑)
      ≈⟨ back _ (back _ (back _ (lift cc))) ⟩
    Xb c₀ • T • Xb c₀ • ε
      ≈⟨ back _ (back _ right-unit) ⟩
    Xb c₀ • T • Xb c₀
      ≈⟨ XTX c₀ ⟩
    (if c₀ then ω • T ^ 7 else T) ∎
    where
    open Width (₁₊ n)
    cc : n ⊢ Xc c • Xc c ≈ ε
    cc = Width.trans (Xc-xor c c) (Width.trans (refl'' (⊕-self c)) (Xc-zero n))
      where
      refl'' : ∀ {u v : Bits n} → u ≡ v → n ⊢ Xc u ≈ Xc v
      refl'' Eq.refl = Width.refl
    Xb-↑' : (b : Bool) (w : Circuit n) → (₁₊ n) ⊢ w ↑ • Xb b ≈ Xb b • w ↑
    Xb-↑' true  w = comm-gate₁-w↑ X-gate w
    Xb-↑' false w = Width.slide-ε (₁₊ n)
    XTX : (c₀ : Bool) → (₁₊ n) ⊢ Xb c₀ • T • Xb c₀ ≈ (if c₀ then ω • T ^ 7 else T)
    XTX true  = ax R₁₁
    XTX false = Width.trans Width.left-unit Width.right-unit

-- The exponents of a phase gate past a translation.
xs : Bool → ℕ
xs true  = 1
xs false = 0

xe : Bool → ℕ
xe true  = 7
xe false = 1

XP : (b : Bits (₁₊ n)) (ℓ : NZ (₁₊ n)) →
     (₁₊ n) ⊢ Xc b • P ℓ • Xc b ≈ ω ^ xs (dot ℓ b) • P ℓ ^ xe (dot ℓ b)
XP {n} b ℓ = begin
  Xc b • (R ⁻¹ • T • R) • Xc b
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (Xc b • R ⁻¹) • T • (R • Xc b)
    ≈⟨ cong pullR (back T pushR) ⟩
  (R ⁻¹ • Xc c) • T • (Xc c • R)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  R ⁻¹ • (Xc c • T • Xc c) • R
    ≈⟨ back _ (front _ (trans (refl' (Eq.cong (λ v → Xc v • T • Xc v) (vec-η c))) (core (head c) (tail c)))) ⟩
  R ⁻¹ • (if head c then ω • T ^ 7 else T) • R
    ≈⟨ refl' (Eq.cong (λ d → R ⁻¹ • (if d then ω • T ^ 7 else T) • R) (head-lmap ℓ b)) ⟩
  R ⁻¹ • (if dot ℓ b then ω • T ^ 7 else T) • R
    ≈⟨ finish (dot ℓ b) ⟩
  ω ^ xs (dot ℓ b) • P ℓ ^ xe (dot ℓ b) ∎
  where
  open Width (₁₊ n)
  R = r ℓ
  c = lmapʷ (rL ℓ) b
  pushR : (₁₊ n) ⊢ R • Xc b ≈ Xc c • R
  pushR = Eq.subst (λ w → (₁₊ n) ⊢ w • Xc b ≈ Xc c • w) (Eq.sym (r-⌊⌋ ℓ)) (Xc-pushʷ (rL ℓ) b)
  pullR : (₁₊ n) ⊢ Xc b • R ⁻¹ ≈ R ⁻¹ • Xc c
  pullR = begin
    Xc b • R ⁻¹                     ≈⟨ sym left-unit ⟩
    ε • Xc b • R ⁻¹                 ≈⟨ front _ (sym (Inv.inverseˡ (₁₊ n))) ⟩
    (R ⁻¹ • R) • Xc b • R ⁻¹        ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    R ⁻¹ • (R • Xc b) • R ⁻¹        ≈⟨ back _ (front _ pushR) ⟩
    R ⁻¹ • (Xc c • R) • R ⁻¹        ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    R ⁻¹ • Xc c • R • R ⁻¹          ≈⟨ back _ (back _ (Inv.inverseʳ (₁₊ n))) ⟩
    R ⁻¹ • Xc c • ε                 ≈⟨ back _ right-unit ⟩
    R ⁻¹ • Xc c                     ∎
  finish : (d : Bool) → (₁₊ n) ⊢ R ⁻¹ • (if d then ω • T ^ 7 else T) • R ≈ ω ^ xs d • P ℓ ^ xe d
  finish true = begin
    R ⁻¹ • (ω • T ^ 7) • R          ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (R ⁻¹ • ω) • T ^ 7 • R          ≈⟨ front _ (comm-gate₀-w ω-gate (R ⁻¹)) ⟩
    (ω • R ⁻¹) • T ^ 7 • R          ≈⟨ assoc ⟩
    ω • R ⁻¹ • T ^ 7 • R            ≈⟨ back ω (sym (Pow.pow-conj (₁₊ n) R T 7)) ⟩
    ω • P ℓ ^ 7                     ∎
  finish false = sym left-unit

------------------------------------------------------------------------
-- Decomposing a circuit

record Dec (n : ℕ) : Set where
  constructor dec
  field
    sc  : ℕ
    pe  : PE n
    tr  : Bits n
    lin : Word (LGen n)

⌜_⌝ᵈ : Dec n → Circuit n
⌜ dec s pe b L ⌝ᵈ = dpart s pe • Xc b • ⌊ L ⌋

-- The row of T conjugated by a linear circuit.
rowT : NZ (₁₊ n) → Word (LGen (₁₊ n)) → NZ (₁₊ n)
rowT ℓ L = LNF.row (lnf (rL ℓ • revL L))

step : Dec n → Kind n → Dec n
step (dec s pe b L) kω     = dec (suc s) pe b L
step (dec s pe b L) (kX v) = dec s pe (b ⊕ lmapʷ L v) L
step (dec s pe b L) (kL y) = dec s pe b (L • [ y ]ʷ)
step {suc n} (dec s pe b L) (kT ℓ) =
  dec (s +ℕ xs (dot (rowT ℓ L) b)) (pe ++ (rowT ℓ L , xe (dot (rowT ℓ L) b)) ∷ []) b L

private
  -- A linear circuit carries a phase gate across.
  L-conj : (ℓ : NZ (₁₊ n)) (L : Word (LGen (₁₊ n))) →
           (₁₊ n) ⊢ ⌊ L ⌋ • P ℓ ≈ P (rowT ℓ L) • ⌊ L ⌋
  L-conj {n} ℓ L = sym (begin
    P (rowT ℓ L) • ⌊ L ⌋
      ≈⟨ front _ (sym (phase-conj M)) ⟩
    (⌊ M ⌋ ⁻¹ • T • ⌊ M ⌋) • ⌊ L ⌋
      ≈⟨ front _ (cong M⁻¹≈ (back T M≈)) ⟩
    ((⌊ L ⌋ • r ℓ ⁻¹) • T • (r ℓ • ⌊ L ⌋ ⁻¹)) • ⌊ L ⌋
      ≈⟨ by-passoc (((□ • □) • □ • (□ • □)) • □) (□ • (□ • □ • □) • (□ • □)) Eq.refl ⟩
    ⌊ L ⌋ • (r ℓ ⁻¹ • T • r ℓ) • (⌊ L ⌋ ⁻¹ • ⌊ L ⌋)
      ≈⟨ back _ (trans (back _ (Inv.inverseˡ (₁₊ n))) right-unit) ⟩
    ⌊ L ⌋ • P ℓ ∎)
    where
    open Width (₁₊ n)
    M = rL ℓ • revL L
    M≈ : (₁₊ n) ⊢ ⌊ M ⌋ ≈ r ℓ • ⌊ L ⌋ ⁻¹
    M≈ = cong (refl' (Eq.sym (r-⌊⌋ ℓ))) (rev-⁻¹ L)
    M⁻¹≈ : (₁₊ n) ⊢ ⌊ M ⌋ ⁻¹ ≈ ⌊ L ⌋ • r ℓ ⁻¹
    M⁻¹≈ = trans (Inv.⁻¹-cong (₁₊ n) M≈) (front _ (Inv.⁻¹-involutive (₁₊ n)))

  -- The diagonal part absorbs a scalar and a phase gate.
  absorb : (s c : ℕ) (pe : PE n) (ℓ : NZ n) (k : ℕ) →
           n ⊢ dpart s pe • (ω ^ c • Pz ℓ ^ k) ≈ dpart (s +ℕ c) (pe ++ (ℓ , k) ∷ [])
  absorb {n} s c pe ℓ k = begin
    (ω ^ s • prod pe) • ω ^ c • Pz ℓ ^ k
      ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    ω ^ s • (prod pe • ω ^ c) • Pz ℓ ^ k
      ≈⟨ back _ (front _ (sym (ωᵏ-comm c (prod pe)))) ⟩
    ω ^ s • (ω ^ c • prod pe) • Pz ℓ ^ k
      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (ω ^ s • ω ^ c) • prod pe • Pz ℓ ^ k
      ≈⟨ cong (sym (Pow.pow-+ n ω s c))
              (sym (trans (prod-++ pe ((ℓ , k) ∷ [])) (back _ right-unit))) ⟩
    ω ^ (s +ℕ c) • prod (pe ++ (ℓ , k) ∷ []) ∎
    where open Width n

  Xc² : (b : Bits n) → n ⊢ Xc b • Xc b ≈ ε
  Xc² {n} b = Width.trans (Xc-xor b b) (Width.trans (eqXc (⊕-self b)) (Xc-zero n))
    where
    eqXc : ∀ {u v : Bits n} → u ≡ v → n ⊢ Xc u ≈ Xc v
    eqXc Eq.refl = Width.refl

step-sound : (D : Dec n) (k : Kind n) → n ⊢ ⌜ D ⌝ᵈ • ⟦ k ⟧ₖ ≈ ⌜ step D k ⌝ᵈ
step-sound {n} (dec s pe b L) kω = begin
  (dpart s pe • Xc b • ⌊ L ⌋) • ω
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • (□ • □) • □) Eq.refl ⟩
  dpart s pe • (Xc b • ⌊ L ⌋) • ω
    ≈⟨ back _ (comm-gate₀-w ω-gate (Xc b • ⌊ L ⌋)) ⟩
  dpart s pe • ω • Xc b • ⌊ L ⌋
    ≈⟨ sym assoc ⟩
  (dpart s pe • ω) • Xc b • ⌊ L ⌋
    ≈⟨ front _ ωstep ⟩
  dpart (suc s) pe • Xc b • ⌊ L ⌋ ∎
  where
  open Width n
  ωstep : n ⊢ dpart s pe • ω ≈ dpart (suc s) pe
  ωstep = begin
    (ω ^ s • prod pe) • ω            ≈⟨ assoc ⟩
    ω ^ s • prod pe • ω              ≈⟨ back _ (sym (ω-comm (prod pe))) ⟩
    ω ^ s • ω • prod pe              ≈⟨ sym assoc ⟩
    (ω ^ s • ω) • prod pe            ≈⟨ front _ (trans (Pow.pow-comm n s refl) (sym (Pow.pow-suc n ω s))) ⟩
    ω ^ suc s • prod pe              ∎
step-sound {n} (dec s pe b L) (kX v) = begin
  (dpart s pe • Xc b • ⌊ L ⌋) • Xc v
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  dpart s pe • Xc b • ⌊ L ⌋ • Xc v
    ≈⟨ back _ (back _ (Xc-pushʷ L v)) ⟩
  dpart s pe • Xc b • Xc (lmapʷ L v) • ⌊ L ⌋
    ≈⟨ back _ (trans (sym assoc) (front _ (Xc-xor b (lmapʷ L v)))) ⟩
  dpart s pe • Xc (b ⊕ lmapʷ L v) • ⌊ L ⌋ ∎
  where open Width n
step-sound {n} (dec s pe b L) (kL y) =
  by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl
  where open Width n
step-sound {suc n} (dec s pe b L) (kT ℓ) = begin
  (dpart s pe • Xc b • ⌊ L ⌋) • P ℓ
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  dpart s pe • Xc b • ⌊ L ⌋ • P ℓ
    ≈⟨ back _ (back _ (L-conj ℓ L)) ⟩
  dpart s pe • Xc b • P ℓ' • ⌊ L ⌋
    ≈⟨ back _ (back _ (back _ (sym (trans (front _ (Xc² b)) left-unit)))) ⟩
  dpart s pe • Xc b • P ℓ' • (Xc b • Xc b) • ⌊ L ⌋
    ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □) ((□ • (□ • □ • □)) • □ • □) Eq.refl ⟩
  (dpart s pe • (Xc b • P ℓ' • Xc b)) • Xc b • ⌊ L ⌋
    ≈⟨ front _ (back _ (XP b ℓ')) ⟩
  (dpart s pe • (ω ^ xs (dot ℓ' b) • P ℓ' ^ xe (dot ℓ' b))) • Xc b • ⌊ L ⌋
    ≈⟨ front _ (absorb s (xs (dot ℓ' b)) pe ℓ' (xe (dot ℓ' b))) ⟩
  dpart (s +ℕ xs (dot ℓ' b)) (pe ++ (ℓ' , xe (dot ℓ' b)) ∷ []) • Xc b • ⌊ L ⌋ ∎
  where
  open Width (suc n)
  ℓ' = rowT ℓ L

run-dec : Dec n → Circuit n → Dec n
run-dec D [ g ]ʷ  = step D (classify g)
run-dec D ε       = D
run-dec D (w • v) = run-dec (run-dec D w) v

run-dec-sound : (D : Dec n) (w : Circuit n) → n ⊢ ⌜ D ⌝ᵈ • w ≈ ⌜ run-dec D w ⌝ᵈ
run-dec-sound {n} D [ g ]ʷ = trans (back _ (classify-sound g)) (step-sound D (classify g))
  where open Width n
run-dec-sound {n} D ε = right-unit
  where open Width n
run-dec-sound {n} D (w • v) =
  trans (sym assoc) (trans (front _ (run-dec-sound D w)) (run-dec-sound (run-dec D w) v))
  where open Width n

D₀ : Dec n
D₀ = dec 0 [] zeros ε

decompose : (w : Circuit n) → n ⊢ w ≈ ⌜ run-dec D₀ w ⌝ᵈ
decompose {n} w = begin
  w                        ≈⟨ sym left-unit ⟩
  ε • w                    ≈⟨ front _ (sym D₀-ε) ⟩
  ⌜ D₀ ⌝ᵈ • w              ≈⟨ run-dec-sound D₀ w ⟩
  ⌜ run-dec D₀ w ⌝ᵈ        ∎
  where
  open Width n
  D₀-ε : n ⊢ ⌜ D₀ {n} ⌝ᵈ ≈ ε
  D₀-ε = trans (front _ left-unit) (trans (back _ right-unit) (trans (back _ (Xc-zero n)) left-unit))

------------------------------------------------------------------------
-- Comparing decompositions

private
  shape : (s : ℕ) (pe : PE n) (b : Bits n) (L : Word (LGen n)) (x : Bits n) →
          ⟦ ⌜ dec s pe b L ⌝ᵈ ⟧ x ≡ (lmapʷ L x ⊕ b , φₑ (s , pe) (lmapʷ L x ⊕ b))
  shape s pe b L x =
    Eq.trans (⟦⟧-• (dpart s pe) (Xc b • ⌊ L ⌋) x)
      (Eq.trans (Eq.cong (λ p → proj₁ (⟦ dpart s pe ⟧ (proj₁ p)) , proj₂ p + proj₂ (⟦ dpart s pe ⟧ (proj₁ p)))
                         (PS-• (PS-Xc b) (PS-⌊⌋ L) x))
        (Eq.trans (Eq.cong (λ p → proj₁ p , 0₈ + proj₂ p) (DS-ₑ (s , pe) (lmapʷ L x ⊕ b)))
                  (Eq.cong (lmapʷ L x ⊕ b ,_) (+-identityˡ (φₑ (s , pe) (lmapʷ L x ⊕ b))))))

  same-b : (s s' : ℕ) (pe pe' : PE n) (b b' : Bits n) (L L' : Word (LGen n)) →
           ⟦ ⌜ dec s pe b L ⌝ᵈ ⟧ ≐ ⟦ ⌜ dec s' pe' b' L' ⌝ᵈ ⟧ → b ≡ b'
  same-b {n} s s' pe pe' b b' L L' e =
    Eq.trans (Eq.sym (at0 L b))
      (Eq.trans (Eq.cong proj₁ (Eq.trans (Eq.sym (shape s pe b L zeros))
                   (Eq.trans (e zeros) (shape s' pe' b' L' zeros))))
                (at0 L' b'))
    where
    at0 : (L : Word (LGen n)) (b : Bits n) → lmapʷ L zeros ⊕ b ≡ b
    at0 L b = Eq.trans (Eq.cong (_⊕ b) (lmapʷ-zero L)) (zeros-⊕ b)

  cmp' : Complete m → (s s' : ℕ) (pe pe' : PE (₁₊ m)) (b b' : Bits (₁₊ m)) (L L' : Word (LGen (₁₊ m))) →
         b ≡ b' → ⟦ ⌜ dec s pe b L ⌝ᵈ ⟧ ≐ ⟦ ⌜ dec s' pe' b' L' ⌝ᵈ ⟧ →
         (₁₊ m) ⊢ ⌜ dec s pe b L ⌝ᵈ ≈ ⌜ dec s' pe' b' L' ⌝ᵈ
  cmp' {m} IH s s' pe pe' b .b L L' Eq.refl e =
    trans (back _ (back _ LL')) (front _ DD')
    where
    open Width (₁₊ m)
    lin-eq : ⟦ ⌊ L ⌋ ⟧ ≐ ⟦ ⌊ L' ⌋ ⟧
    lin-eq x = Eq.trans (PS-⌊⌋ L x) (Eq.trans (Eq.cong (_, 0₈) same) (Eq.sym (PS-⌊⌋ L' x)))
      where
      same : lmapʷ L x ≡ lmapʷ L' x
      same = ⊕-cancelʳ _ _ b (Eq.cong proj₁ (Eq.trans (Eq.sym (shape s pe b L x))
                                (Eq.trans (e x) (shape s' pe' b L' x))))
    LL' : (₁₊ m) ⊢ ⌊ L ⌋ ≈ ⌊ L' ⌋
    LL' = linear-complete IH L L' lin-eq
    DD' : (₁₊ m) ⊢ dpart s pe ≈ dpart s' pe'
    DD' = diag-complete IH s s' pe pe'
            (cancelʳ-⟦⟧ (dpart s pe) (dpart s' pe') (Xc b • ⌊ L' ⌋)
              (≐-trans (sound (back _ (back _ (sym LL')))) e))

cmp : Complete m → (D D' : Dec (₁₊ m)) → ⟦ ⌜ D ⌝ᵈ ⟧ ≐ ⟦ ⌜ D' ⌝ᵈ ⟧ →
      (₁₊ m) ⊢ ⌜ D ⌝ᵈ ≈ ⌜ D' ⌝ᵈ
cmp IH (dec s pe b L) (dec s' pe' b' L') e =
  cmp' IH s s' pe pe' b b' L L' (same-b s s' pe pe' b b' L L' e) e

------------------------------------------------------------------------
-- Width 0: powers of ω

private
  prod₀ : (pe : PE 0) → 0 ⊢ prod pe ≈ ε
  prod₀ [] = Width.refl

  lin₀ : (L : Word (LGen 0)) → 0 ⊢ ⌊ L ⌋ ≈ ε
  lin₀ ε       = Width.refl
  lin₀ (w • v) = Width.trans (Width.cong (lin₀ w) (lin₀ v)) Width.left-unit

  -- A circuit on no wires is a power of ω.
  as-ω : (D : Dec 0) → 0 ⊢ ⌜ D ⌝ᵈ ≈ ω ^ toℕ (Dec.sc D mod 8)
  as-ω (dec s pe [] L) = begin
    (ω ^ s • prod pe) • ε • ⌊ L ⌋     ≈⟨ cong (back _ (prod₀ pe)) (back _ (lin₀ L)) ⟩
    (ω ^ s • ε) • ε • ε               ≈⟨ trans (back _ left-unit) right-unit ⟩
    ω ^ s • ε                         ≈⟨ right-unit ⟩
    ω ^ s                             ≈⟨ ωᵏ-mod s ⟩
    ω ^ (s % 8)                       ≈⟨ refl' (Eq.cong (ω ^_) (Eq.sym (toℕ-fromℕ< (m%n<n s 8)))) ⟩
    ω ^ toℕ (s mod 8)                 ∎
    where open Width 0

  ωᵃ-ph : (a : ℤ₈) → ph (ω {0} ^ toℕ a) [] ≡ a
  ωᵃ-ph a = Eq.trans (Eq.cong proj₂ (DS-^ DS-ω (toℕ a) [])) (powφ-1 a [])

complete₀ : Complete 0
complete₀ {w} {v} e =
  trans (decompose w) (trans (as-ω Dw) (trans (refl' (Eq.cong (λ a → ω ^ toℕ a) same))
    (trans (sym (as-ω Dv)) (sym (decompose v)))))
  where
  open Width 0
  Dw = run-dec D₀ w
  Dv = run-dec D₀ v
  same : Dec.sc Dw mod 8 ≡ Dec.sc Dv mod 8
  same = Eq.trans (Eq.sym (ωᵃ-ph _))
           (Eq.trans (ph-≈ (sym (trans (decompose w) (as-ω Dw))) [])
             (Eq.trans (Eq.cong proj₂ (e []))
               (Eq.trans (ph-≈ (trans (decompose v) (as-ω Dv)) []) (ωᵃ-ph _))))

------------------------------------------------------------------------
-- Every width

complete-step : Complete m → Complete (₁₊ m)
complete-step {m} IH {w} {v} e =
  trans (decompose w)
    (trans (cmp IH (run-dec D₀ w) (run-dec D₀ v)
              (≐-trans (sound (sym (decompose w))) (≐-trans e (sound (decompose v)))))
           (sym (decompose v)))
  where open Width (₁₊ m)

completeness : (n : ℕ) → Complete n
completeness zero    = complete₀
completeness (suc m) = complete-step (completeness m)

-- The theorem: circuits with the same operator are equal.
complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≐ ⟦ v ⟧ → n ⊢ w ≈ v
complete {n} = completeness n
