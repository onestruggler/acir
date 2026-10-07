------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled circuits
--
-- At level 3 the phase of a diagonal circuit, read along wire 0, is
--
--     t (x₀ choose 3) + (x₀ choose 2) f(x') + x₀ g(x')
--
-- with f of degree 1 and g of degree 2 in the other labels x'.  The
-- parts x₀ g and (x₀ choose 2) f are circuits of a lower level,
-- controlled: a circuit w of level lv' ≤ 2 on n wires becomes a circuit
-- ctrl* w of level 3 on ₁₊ n wires, wire 0 the control, whose phase is
-- κ(x₀) times that of w, κ x₀ = x₀ or (x₀ choose 2).  The affine
-- generators go one wire up, and the phases to controlled phases:
--
--     ω ↦ Ωg       Z ↦ Zg       S ↦ Sg       g ↥ ↦ SWAP • ctrl g ↑ • SWAP
--
-- (Ωg, Zg, Sg = Z, CZ, SC for κ x₀ = x₀, and S, CS for its square).
-- Every rule of level lv' then holds of the images (ctrl-cong), given
-- the images of its rules involving phases; so is every equation, and
-- equal circuits of level lv' stay equal controlled.  The structural
-- rules hold because each generator's image is either one wire up or
-- diagonal (cls).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Control
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

open import Data.Empty using (⊥ ; ⊥-elim-irr)
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Examples.Groups.Qupit-Phase-Affine.Syntactics as Syntactics′
import Examples.Groups.Qupit-Phase-Affine.Interpretation as Interpretation′
import Examples.Groups.Qupit-Phase-Affine.Powers as Powers′
import Examples.Groups.Qupit-Phase-Affine.Linear.Base as Linear′
import Examples.Groups.Qupit-Phase-Affine.Basic as Basic′

open import Notations using (₁₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; _+_ ; _*_ ; -_ ; -1* ; binom2 ; Labels ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime lv
  using (DiagC ; •-at ; at-≡ ; ↑-at ; SWAP-at)
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv using (↑-pow)
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Commute p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv using (LGen ; cx ; sw ; mul ; _↥ₗ ; ι ; ⌊_⌋)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Two p-2 p-prime lv using (σ ; σ⁻ ; σσ⁻ ; σ⁻σ ; two-σ ; t2 ; swap-gate₁)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Diag p-2 p-prime lv h gt3
  using (Diag₃ ; diag₃∥ ; Diag₃-↑ ; Diag₃-SWAP)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Tools

module _ {m : ℕ} where

  open Width m

  -- Commuting words stay commuting conjugated.
  conj∥ : {s s' a b : Circuit m} → m ⊢ s' • s ≈ ε → m ⊢ a ∥ b → m ⊢ (s • a • s') ∥ (s • b • s')
  conj∥ {s} {s'} {a} {b} e ab = begin
    (s • a • s') • s • b • s'      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    s • a • (s' • s) • b • s'      ≈⟨ back _ (back _ (trans (front _ e) left-unit)) ⟩
    s • a • b • s'                 ≈⟨ back _ (trans (sym assoc) (trans (front _ ab) assoc)) ⟩
    s • b • a • s'                 ≈⟨ back _ (back _ (trans (sym left-unit) (front _ (sym e)))) ⟩
    s • b • (s' • s) • a • s'      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl ⟩
    (s • b • s') • s • a • s'      ∎

  ∥-≈ˡ : {a a' b : Circuit m} → m ⊢ a ≈ a' → m ⊢ a' ∥ b → m ⊢ a ∥ b
  ∥-≈ˡ e ab = trans (front _ e) (trans ab (back _ (sym e)))

  ∥-≈ʳ : {a b b' : Circuit m} → m ⊢ b ≈ b' → m ⊢ a ∥ b' → m ⊢ a ∥ b
  ∥-≈ʳ e ab = trans (back _ e) (trans ab (front _ (sym e)))

-- A word two wires up passes SWAP.
c↑ : (w : Circuit n) → (₂₊ n) ⊢ SWAP • w ↑ ↑ • SWAP ≈ w ↑ ↑
c↑ {n} w = begin
  SWAP • w ↑ ↑ • SWAP      ≈⟨ trans (sym assoc) (front _ (sym (comm-gate₂-w↑↑ SWAP-gate w))) ⟩
  (w ↑ ↑ • SWAP) • SWAP    ≈⟨ trans assoc (cancel-at (ax swap-order) _) ⟩
  w ↑ ↑                    ∎
  where open Width (₂₊ n)

up^ : (w : Circuit n) (m : ℕ) → (₁₊ n) ⊢ (w ↑) ^ m ≈ (w ^ m) ↑
up^ {n} w m = Width.refl' (₁₊ n) (Eq.sym (↑-pow w m))

-- The controlled product of three gates: the image of CZ.
W : (G : ∀ {m} → Circuit (₂₊ m)) → Circuit (₃₊ n)
W G = G ^ᶠ (- 1F) • (SWAP • G ↑ • SWAP) ^ᶠ (- 1F) • (CX ↑) ^ᶠ (- 1F) • G • CX ↑

------------------------------------------------------------------------
-- The functor

module Functor
  (lv' : ℕ) (no3 : 3 ≤ lv' → ⊥) (κ : F → F)
  (Ωg : ∀ {n} → Circuit (₁₊ n))
  (Zg : ∀ {n} → Circuit (₂₊ n))
  (Sg : ∀ {n} → .(2 ≤ lv') → Circuit (₂₊ n))
  -- The images are diagonal; Ω is on wire 0, Zg and Sg on wires 0, 1.
  (Ω-D    : ∀ {n} → Diag₃ (₁₊ n) Ωg)
  (Z-D    : ∀ {n} → Diag₃ (₂₊ n) Zg)
  (S-D    : ∀ {n} .(h' : 2 ≤ lv') → Diag₃ (₂₊ n) (Sg h'))
  (Ω-up   : ∀ {n} (w : Circuit n) → (₁₊ n) ⊢ Ωg ∥ (w ↑))
  (Z-two  : ∀ {n} (w : Circuit n) → (₂₊ n) ⊢ Zg ∥ (w ↑ ↑))
  (S-two  : ∀ {n} .(h' : 2 ≤ lv') (w : Circuit n) → (₂₊ n) ⊢ Sg h' ∥ (w ↑ ↑))
  -- The images of the rules with phases.
  (Ω-sw   : ∀ {n} → (₂₊ n) ⊢ SWAP • Ωg ↑ • SWAP ≈ Ωg)
  (Z-sw   : ∀ {n} → (₃₊ n) ⊢ Zg • SWAP ↑ ≈ SWAP ↑ • SWAP • Zg ↑ • SWAP)
  (S-sw   : ∀ {n} .(h' : 2 ≤ lv') → (₃₊ n) ⊢ Sg h' • SWAP ↑ ≈ SWAP ↑ • SWAP • Sg h' ↑ • SWAP)
  (Ω-ord  : ∀ {n} → (₁₊ n) ⊢ Ωg ^ p ≈ ε)
  (Z-ord  : ∀ {n} → (₂₊ n) ⊢ Zg ^ p ≈ ε)
  (Z-CX   : ∀ {n} → (₃₊ n) ⊢ CX ↑ • Zg • SWAP • Zg ↑ • SWAP ≈ Zg • CX ↑)
  (Z-M    : ∀ {n} (x : F*) → (₂₊ n) ⊢ Zg • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ • Zg ^ toℕ (proj₁ x))
  (Z-X    : ∀ {n} → (₂₊ n) ⊢ Zg • X ↑ ≈ Ωg • X ↑ • Zg)
  (S-ord  : ∀ {n} .(h' : 2 ≤ lv') → (₂₊ n) ⊢ Sg h' ^ p ≈ ε)
  (S-X    : ∀ {n} .(h' : 2 ≤ lv') → (₂₊ n) ⊢ Sg h' • X ↑ ≈ X ↑ • Zg • Sg h')
  (S-M    : ∀ {n} .(h' : 2 ≤ lv') (x : F*) → (₂₊ n) ⊢ Sg h' • M⟨ x ⟩ ↑ ≈
              M⟨ x ⟩ ↑ • Zg ^ toℕ (binom2 (proj₁ x)) • Sg h' ^ toℕ (proj₁ x * proj₁ x))
  (S-CX   : ∀ {n} .(h' : 2 ≤ lv') → (₃₊ n) ⊢ CX ↑ • SWAP • Sg h' ↑ • SWAP ≈ (SWAP • Sg h' ↑ • SWAP) • CX ↑)
  (W-M    : ∀ {n} .(h' : 2 ≤ lv') → (₃₊ n) ⊢ (SWAP • M⟨ -1* ⟩ ↑ ↑ • SWAP) • W (Sg h') ^ toℕ (- 1F) • SWAP • M⟨ -1* ⟩ ↑ ↑ • SWAP ≈ W (Sg h'))
  (W-CX   : ∀ {n} .(h' : 2 ≤ lv') → (₄₊ n) ⊢ W (Sg h') • SWAP • CX ↑ ↑ • SWAP ≈
              (SWAP • CX ↑ ↑ • SWAP) • W (Sg h') • (SWAP • SWAP ↑ ↑ • SWAP) • W (Sg h') • SWAP • SWAP ↑ ↑ • SWAP)
  -- Their phases.
  (Ω-sem  : ∀ {n} → DiagC {₁₊ n} Ωg (λ y → κ (head y)))
  (Z-sem  : ∀ {n} → DiagC {₂₊ n} Zg (λ y → κ (head y) * head (tail y)))
  (S-sem  : ∀ {n} .(h' : 2 ≤ lv') → DiagC {₂₊ n} (Sg h') (λ y → κ (head y) * binom2 (head (tail y))))
  where

  private
    module Src = Syntactics′ p-2 p-prime lv'
    module SI = Interpretation′ p-2 p-prime lv'
    module SP = Powers′ p-2 p-prime lv'
    module SL = Linear′ p-2 p-prime lv'
    module SB = Basic′ p-2 p-prime lv'

  ----------------------------------------------------------------------
  -- The map

  ctrl : Src.Gen n → Circuit (₁₊ n)
  ctrl (Src.gate₀ (Src.ω-gate _))     = Ωg
  ctrl (Src.gate₁ Src.X-gate)         = X ↑
  ctrl (Src.gate₁ (Src.M-gate a nz))  = M a nz ↑
  ctrl (Src.gate₁ (Src.Z-gate _))     = Zg
  ctrl (Src.gate₁ (Src.S-gate h'))    = Sg h'
  ctrl (Src.gate₁ (Src.T-gate h'))    = ⊥-elim-irr (no3 h')
  ctrl (Src.gate₂ Src.CX-gate)        = CX ↑
  ctrl (Src.gate₂ Src.SWAP-gate)      = SWAP ↑
  ctrl (g Src.↥)                      = SWAP • ctrl g ↑ • SWAP

  ctrl* : Src.Circuit n → Circuit (₁₊ n)
  ctrl* [ g ]ʷ   = ctrl g
  ctrl* ε        = ε
  ctrl* (u • v)  = ctrl* u • ctrl* v

  ctrl*-^ : (w : Src.Circuit n) (m : ℕ) → ctrl* (w ^ m) ≡ ctrl* w ^ m
  ctrl*-^ w zero          = Eq.refl
  ctrl*-^ w (suc zero)    = Eq.refl
  ctrl*-^ w (suc (suc m)) = Eq.cong (ctrl* w •_) (ctrl*-^ w (suc m))

  pw : (w : Src.Circuit n) (m : ℕ) → (₁₊ n) ⊢ ctrl* (w ^ m) ≈ ctrl* w ^ m
  pw {n} w m = Width.refl' (₁₊ n) (ctrl*-^ w m)

  ctrl*-↑ : (w : Src.Circuit n) → (₂₊ n) ⊢ ctrl* (w Src.↑) ≈ SWAP • ctrl* w ↑ • SWAP
  ctrl*-↑ {n} [ g ]ʷ  = Width.refl
  ctrl*-↑ {n} ε       = Width.sym (Width.trans (Width.back (₂₊ n) _ Width.left-unit) (ax swap-order))
  ctrl*-↑ {n} (u • v) = begin
    ctrl* (u Src.↑) • ctrl* (v Src.↑)
      ≈⟨ cong (ctrl*-↑ u) (ctrl*-↑ v) ⟩
    (SWAP • ctrl* u ↑ • SWAP) • SWAP • ctrl* v ↑ • SWAP
      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    SWAP • ctrl* u ↑ • (SWAP • SWAP) • ctrl* v ↑ • SWAP
      ≈⟨ back _ (back _ (trans (front _ (ax swap-order)) left-unit)) ⟩
    SWAP • ctrl* u ↑ • ctrl* v ↑ • SWAP
      ≈⟨ back _ (sym assoc) ⟩
    SWAP • (ctrl* u • ctrl* v) ↑ • SWAP ∎
    where open Width (₂₊ n)

  -- The image of CZ.
  ctrl-CZ : .(h' : 2 ≤ lv') → ctrl* (Src.CZ {n} h') ≡ W (Sg h')
  ctrl-CZ {n} h' = Eq.cong₂ _•_ (ctrl*-^ _ (toℕ (- 1F)))
                     (Eq.cong₂ _•_ (Eq.trans (Eq.cong ctrl* (SP.↑-pow (Src.S h') (toℕ (- 1F)))) (ctrl*-^ _ (toℕ (- 1F))))
                       (Eq.cong (_• (Sg h' • CX ↑)) (ctrl*-^ _ (toℕ (- 1F)))))

  ----------------------------------------------------------------------
  -- Affine or diagonal

  -- The inclusion of the lower level.
  trG : {k : ℕ} → Src.Gate k → Gate k
  trG (Src.ω-gate _)    = ω-gate (lin₃ h)
  trG Src.X-gate        = X-gate
  trG (Src.M-gate a nz) = M-gate a nz
  trG (Src.Z-gate _)    = Z-gate (lin₃ h)
  trG (Src.S-gate _)    = S-gate (quad₃ h)
  trG (Src.T-gate _)    = T-gate h
  trG Src.CX-gate       = CX-gate
  trG Src.SWAP-gate     = SWAP-gate

  tr : Src.Gen n → Gen n
  tr (Src.gate₀ g) = gate₀ (trG g)
  tr (Src.gate₁ g) = gate₁ (trG g)
  tr (Src.gate₂ g) = gate₂ (trG g)
  tr (g Src.↥)     = tr g ↥

  data Cls (g : Src.Gen n) : Set where
    aff : (₁₊ n) ⊢ ctrl g ≈ [ tr g ]ʷ ↑ → Cls g
    dia : Diag₃ (₁₊ n) (ctrl g) → Cls g

  cls : (g : Src.Gen n) → Cls g
  cls (Src.gate₀ (Src.ω-gate _))     = dia Ω-D
  cls (Src.gate₁ Src.X-gate)         = aff Width.refl
  cls (Src.gate₁ (Src.M-gate a nz))  = aff Width.refl
  cls (Src.gate₁ (Src.Z-gate _))     = dia Z-D
  cls (Src.gate₁ (Src.S-gate h'))    = dia (S-D h')
  cls (Src.gate₁ (Src.T-gate h'))    = ⊥-elim-irr (no3 h')
  cls (Src.gate₂ Src.CX-gate)        = aff Width.refl
  cls (Src.gate₂ Src.SWAP-gate)      = aff Width.refl
  cls {suc n} (g Src.↥) with cls g
  ... | aff e = aff (Width.trans (Width.mid (₂₊ n) SWAP SWAP (lift e)) (c↑ [ tr g ]ʷ))
  ... | dia d = dia (Diag₃-SWAP (Diag₃-↑ d))

  ----------------------------------------------------------------------
  -- The structural rules

  -- Ω passes every image.
  Ω∥ : (g : Src.Gen n) → (₁₊ n) ⊢ Ωg ∥ ctrl g
  Ω∥ (Src.gate₀ (Src.ω-gate _))     = Width.refl
  Ω∥ (Src.gate₁ Src.X-gate)         = Ω-up X
  Ω∥ (Src.gate₁ (Src.M-gate a nz))  = Ω-up (M a nz)
  Ω∥ (Src.gate₁ (Src.Z-gate _))     = diag₃∥ Ω-D Z-D
  Ω∥ (Src.gate₁ (Src.S-gate h'))    = diag₃∥ Ω-D (S-D h')
  Ω∥ (Src.gate₁ (Src.T-gate h'))    = ⊥-elim-irr (no3 h')
  Ω∥ (Src.gate₂ Src.CX-gate)        = Ω-up CX
  Ω∥ (Src.gate₂ Src.SWAP-gate)      = Ω-up SWAP
  Ω∥ {suc n} (g Src.↥) = ∥-≈ˡ (Width.sym Ω-sw) (conj∥ (ax swap-order) (lift (Ω∥ g)))

  -- A two-wire diagonal on wires 0, 1 passes the image of a gate
  -- further up.
  two-cls : {G : Circuit (₂₊ n)} → Diag₃ (₂₊ n) G → (∀ (w : Circuit n) → (₂₊ n) ⊢ G ∥ (w ↑ ↑)) →
            (g : Src.Gen n) → (₂₊ n) ⊢ G ∥ (SWAP • ctrl g ↑ • SWAP)
  two-cls {n} dG tG g with cls g
  ... | aff e = ∥-≈ʳ (Width.trans (Width.mid (₂₊ n) SWAP SWAP (lift e)) (c↑ [ tr g ]ʷ)) (tG [ tr g ]ʷ)
  ... | dia d = diag₃∥ dG (Diag₃-SWAP (Diag₃-↑ d))

  -- A gate on wire 1 passes the image of a gate further up.
  gate1∥ : (h₀ : Gate 1) (c : Circuit (₁₊ n)) → (₂₊ n) ⊢ (SWAP • c ↑ • SWAP) ∥ [ gate₁ h₀ ↥ ]ʷ
  gate1∥ {n} h₀ c = ∥-≈ʳ (Width.sym s1) (conj∥ (ax swap-order) (comm-gate₁-w↑ h₀ c))
    where
    open Width (₂₊ n)
    s1 : (₂₊ n) ⊢ SWAP • [ gate₁ h₀ ]ʷ • SWAP ≈ [ gate₁ h₀ ↥ ]ʷ
    s1 = trans (sym assoc) (trans (front _ (swap-gate₁ h₀)) (trans assoc (cancel-at (ax swap-order) _)))

  -- The image of a gate two wires up is a conjugate by σ.
  σ-up : (g : Src.Gen n) → (₃₊ n) ⊢ ctrl (g Src.↥ Src.↥) ≈ σ • ctrl g ↑ ↑ • σ⁻
  σ-up {n} g = by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl
    where open Width (₃₊ n)

  σ-gate₂ : (g : Gate 2) → (₃₊ n) ⊢ [ gate₂ g ]ʷ ↑ ≈ σ • [ gate₂ g ]ʷ • σ⁻
  σ-gate₂ {n} g = sym (trans (sym assoc) (trans (front _ (two-σ (t2 g))) (trans assoc (cancel-at σσ⁻ _))))
    where open Width (₃₊ n)

  comm2 : (h₀ : Gate 2) (g : Src.Gen n) → (₃₊ n) ⊢ ctrl (g Src.↥ Src.↥) ∥ ([ gate₂ h₀ ]ʷ ↑)
  comm2 h₀ g = ∥-≈ˡ (σ-up g) (∥-≈ʳ (σ-gate₂ h₀) (conj∥ σ⁻σ (comm-gate₂-w↑↑ h₀ (ctrl g))))

  ----------------------------------------------------------------------
  -- The rules hold of the images

  private
    gp : (g : Src.Gen n) (g' : Gen n) → ctrl g ≡ [ g' ]ʷ ↑ → (m : ℕ) → (₁₊ n) ⊢ ctrl* ([ g ]ʷ ^ m) ≈ ([ g' ]ʷ ^ m) ↑
    gp {n} g g' e m = Width.trans (pw [ g ]ʷ m) (Width.trans (Width.refl' (₁₊ n) (Eq.cong (_^ m) e)) (up^ [ g' ]ʷ m))

    gX : (m : ℕ) → (₂₊ n) ⊢ ctrl* (Src.X ^ m) ≈ (X ^ m) ↑
    gX = gp (Src.gate₁ Src.X-gate) (gate₁ X-gate) Eq.refl

    gCX : (m : ℕ) → (₃₊ n) ⊢ ctrl* (Src.CX ^ m) ≈ (CX ^ m) ↑
    gCX = gp (Src.gate₂ Src.CX-gate) (gate₂ CX-gate) Eq.refl

  ctrl-srel : {w v : Src.Circuit n} → n Src.SRel, w === v → (₁₊ n) ⊢ ctrl* w ≈ ctrl* v
  ctrl-srel Src.ax1 = lift (ax ax1)
  ctrl-srel (Src.ax2 x y) = lift (ax (ax2 x y))
  ctrl-srel {₁₊ n} (Src.ax3 x) =
    trans (cong (gX (toℕ (proj₁ x))) (back _ (gX (toℕ (- 1F))))) (lift (ax (ax3 x)))
    where open Width (₂₊ n)
  ctrl-srel {₂₊ n} (Src.ax4 x) =
    trans (back _ (c↑ M⟨ x ⟩)) (trans (lift (ax (ax4 x))) (cong (sym (c↑ M⟨ x ⟩)) (sym (gCX (toℕ (proj₁ x))))))
    where open Width (₃₊ n)
  ctrl-srel {₂₊ n} (Src.ax5 x) = trans (front _ (gCX (toℕ (- proj₁ x)))) (lift (ax (ax5 x)))
    where open Width (₃₊ n)
  ctrl-srel {₂₊ n} Src.ax6 =
    trans (back _ (c↑ X)) (trans (lift (ax ax6)) (back _ (front _ (sym (c↑ X)))))
    where open Width (₃₊ n)
  ctrl-srel {₂₊ n} Src.ax7 =
    trans (lift (ax ax7))
      (sym (cong (c↑ M⟨ -1* ⟩) (cong (back _ (front _ (gCX (toℕ (- 1F)))))
                                      (back _ (back _ (front _ (gCX (toℕ (- 1F)))))))))
    where open Width (₃₊ n)
  ctrl-srel {₃₊ n} Src.ax8 =
    trans (cong (c↑ CX) (back _ (cong (c↑ SWAP) (back _ (c↑ SWAP)))))
      (trans (lift (ax ax8)) (back _ (sym (c↑ CX))))
    where open Width (₄₊ n)
  ctrl-srel Src.swap-order = lift (ax swap-order)
  ctrl-srel {₃₊ n} Src.swap-braid =
    trans (back _ (front _ (c↑ SWAP)))
      (trans (lift (ax swap-braid)) (sym (cong (c↑ SWAP) (back _ (c↑ SWAP)))))
    where open Width (₄₊ n)
  ctrl-srel {₂₊ n} Src.swap-X = trans (lift (ax swap-X)) (back _ (sym (c↑ X)))
    where open Width (₃₊ n)
  ctrl-srel {₂₊ n} (Src.swap-M a nz) = trans (lift (ax (swap-M a nz))) (back _ (sym (c↑ (M a nz))))
    where open Width (₃₊ n)
  ctrl-srel (Src.swap-Z _) = Z-sw
  ctrl-srel (Src.swap-S h') = S-sw h'
  ctrl-srel (Src.swap-T h') = ⊥-elim-irr (no3 h')
  ctrl-srel {₃₊ n} Src.swap-CX =
    trans (back _ (front _ (c↑ SWAP)))
      (trans (lift (ax swap-CX)) (sym (cong (c↑ SWAP) (back _ (c↑ CX)))))
    where open Width (₄₊ n)
  ctrl-srel (Src.ax19 h') = Width.trans (pw (Src.ω h') p) Ω-ord
  ctrl-srel (Src.ax20 h') = Width.trans (pw (Src.Z h') p) Z-ord
  ctrl-srel (Src.ax21 _) = Z-CX
  ctrl-srel {₁₊ n} (Src.ax22 h' x) = trans (Z-M x) (back _ (sym (pw (Src.Z h') (toℕ (proj₁ x)))))
    where open Width (₂₊ n)
  ctrl-srel (Src.ax23 _) = Z-X
  ctrl-srel (Src.ax24 h') = Width.trans (pw (Src.S h') p) (S-ord h')
  ctrl-srel (Src.ax25 h') = S-X h'
  ctrl-srel (Src.ax26 h') = diag₃∥ (S-D h') Z-D
  ctrl-srel {₁₊ n} (Src.ax27 h' x) =
    trans (S-M h' x)
      (back _ (sym (cong (pw (Src.Z (Src.lin₂ h')) (toℕ (binom2 (proj₁ x))))
                         (pw (Src.S h') (toℕ (proj₁ x * proj₁ x))))))
    where open Width (₂₊ n)
  ctrl-srel {₂₊ n} (Src.ax28 h') =
    trans (back _ (front _ (trans (pw (Src.CZ h') (toℕ (- 1F))) (refl' (Eq.cong (_^ toℕ (- 1F)) (ctrl-CZ h'))))))
      (trans (W-M h') (refl' (Eq.sym (ctrl-CZ h'))))
    where open Width (₃₊ n)
  ctrl-srel (Src.ax29 h') = S-CX h'
  ctrl-srel {₃₊ n} (Src.ax30 h') =
    trans (refl' (Eq.cong (_• (SWAP • CX ↑ ↑ • SWAP)) (ctrl-CZ h')))
      (trans (W-CX h')
        (refl' (Eq.cong (λ q → (SWAP • CX ↑ ↑ • SWAP) • q • (SWAP • SWAP ↑ ↑ • SWAP) • q • SWAP • SWAP ↑ ↑ • SWAP)
                        (Eq.sym (ctrl-CZ h')))))
    where open Width (₄₊ n)
  ctrl-srel (Src.ax31 h')   = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax32 h' _) = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax33 h')   = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax34 h')   = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax35 h' _) = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax36 h')   = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax37 h' _) = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax38 h')   = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax39 h')   = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax40 h' _) = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax41 h')   = ⊥-elim-irr (no3 h')
  ctrl-srel (Src.ax42 h')   = ⊥-elim-irr (no3 h')

  ctrl-ax : {w v : Src.Circuit n} → n Src.VRel, w === v → (₁₊ n) ⊢ ctrl* w ≈ ctrl* v
  ctrl-ax (Src.srel r) = ctrl-srel r
  ctrl-ax {suc n} (Src.cong↑ {w = w} {v = v} r) =
    Width.trans (ctrl*-↑ w) (Width.trans (Width.mid (₂₊ n) SWAP SWAP (lift (ctrl-ax r))) (Width.sym (ctrl*-↑ v)))
  ctrl-ax (Src.comm₀ (Src.ω-gate _) g)     = Width.sym (Ω∥ g)
  ctrl-ax (Src.comm₁ Src.X-gate g)         = gate1∥ X-gate (ctrl g)
  ctrl-ax (Src.comm₁ (Src.M-gate a nz) g)  = gate1∥ (M-gate a nz) (ctrl g)
  ctrl-ax (Src.comm₁ (Src.Z-gate _) g)     = Width.sym (two-cls Z-D Z-two g)
  ctrl-ax (Src.comm₁ (Src.S-gate h') g)    = Width.sym (two-cls (S-D h') (S-two h') g)
  ctrl-ax (Src.comm₁ (Src.T-gate h') g)    = ⊥-elim-irr (no3 h')
  ctrl-ax (Src.comm₂ Src.CX-gate g)        = comm2 CX-gate g
  ctrl-ax (Src.comm₂ Src.SWAP-gate g)      = comm2 SWAP-gate g
  ctrl-ax (Src.ω↑=ω (Src.ω-gate _))        = Ω-sw

  -- Equal circuits of the lower level, controlled, are equal.
  ctrl-cong : {w v : Src.Circuit n} → n Src.⊢ w ≈ v → (₁₊ n) ⊢ ctrl* w ≈ ctrl* v
  ctrl-cong PB.refl         = Width.refl
  ctrl-cong (PB.sym e)      = Width.sym (ctrl-cong e)
  ctrl-cong (PB.trans e f)  = Width.trans (ctrl-cong e) (ctrl-cong f)
  ctrl-cong (PB.cong e f)   = Width.cong (ctrl-cong e) (ctrl-cong f)
  ctrl-cong PB.assoc        = Width.assoc
  ctrl-cong PB.left-unit    = Width.left-unit
  ctrl-cong PB.right-unit   = Width.right-unit
  ctrl-cong (PB.axiom r)    = ctrl-ax r

  ----------------------------------------------------------------------
  -- Inverses and linear words

  ctrl-⁻¹ : (w : Src.Circuit n) → (₁₊ n) ⊢ ctrl* (w SB.⁻¹) ≈ (ctrl* w) ⁻¹
  ctrl-⁻¹ {n} w = Inv.inverseˡ-unique (₁₊ n) {ctrl* w} (ctrl-cong (SB.Inv.inverseˡ n {w}))

  -- The linear generators of the lower level.
  trL : LGen n → SL.LGen n
  trL cx       = SL.cx
  trL sw       = SL.sw
  trL (mul a)  = SL.mul a
  trL (y ↥ₗ)   = trL y SL.↥ₗ

  trL* : Word (LGen n) → Word (SL.LGen n)
  trL* [ y ]ʷ   = [ trL y ]ʷ
  trL* ε        = ε
  trL* (u • v)  = trL* u • trL* v

  ctrl-ι : (y : LGen n) → (₁₊ n) ⊢ ctrl (SL.ι (trL y)) ≈ [ ι y ]ʷ ↑
  ctrl-ι cx            = Width.refl
  ctrl-ι sw            = Width.refl
  ctrl-ι (mul a)       = Width.refl
  ctrl-ι {suc n} (y ↥ₗ) = Width.trans (Width.mid (₂₊ n) SWAP SWAP (lift (ctrl-ι y))) (c↑ [ ι y ]ʷ)

  -- A linear word of the lower level, controlled, is the word one wire up.
  ctrl-lin : (L : Word (LGen n)) → (₁₊ n) ⊢ ctrl* SL.⌊ trL* L ⌋ ≈ ⌊ L ⌋ ↑
  ctrl-lin [ y ]ʷ  = ctrl-ι y
  ctrl-lin ε       = Width.refl
  ctrl-lin (u • v) = Width.cong (ctrl-lin u) (ctrl-lin v)

  ----------------------------------------------------------------------
  -- The phase of a controlled circuit: κ x₀ times the phase

  private
    κ0 : (a : F) → 0F ≡ κ a * 0F
    κ0 a = Eq.sym (FR.zeroʳ (κ a))

    ctrl-gen : (g : Src.Gen n) (x0 : F) (x : Labels n) →
               ⟦ ctrl g ⟧ (x0 ∷ x) ≡ (x0 ∷ proj₁ (SI.⟦ g ⟧ᵍ x) , κ x0 * proj₂ (SI.⟦ g ⟧ᵍ x))
    ctrl-gen (Src.gate₀ (Src.ω-gate _)) x0 x =
      at-≡ (Ω-sem (x0 ∷ x)) Eq.refl (Eq.sym (FR.*-identityʳ (κ x0)))
    ctrl-gen (Src.gate₁ Src.X-gate) x0 (a ∷ x) =
      at-≡ (⟦⟧-gen (gate₁ X-gate ↥) (x0 ∷ a ∷ x)) Eq.refl (κ0 x0)
    ctrl-gen (Src.gate₁ (Src.M-gate c nz)) x0 (a ∷ x) =
      at-≡ (⟦⟧-gen (gate₁ (M-gate c nz) ↥) (x0 ∷ a ∷ x)) Eq.refl (κ0 x0)
    ctrl-gen (Src.gate₁ (Src.Z-gate _)) x0 (a ∷ x) = Z-sem (x0 ∷ a ∷ x)
    ctrl-gen (Src.gate₁ (Src.S-gate h')) x0 (a ∷ x) = S-sem h' (x0 ∷ a ∷ x)
    ctrl-gen (Src.gate₁ (Src.T-gate h')) x0 x = ⊥-elim-irr (no3 h')
    ctrl-gen (Src.gate₂ Src.CX-gate) x0 (a ∷ b ∷ x) =
      at-≡ (⟦⟧-gen (gate₂ CX-gate ↥) (x0 ∷ a ∷ b ∷ x)) Eq.refl (κ0 x0)
    ctrl-gen (Src.gate₂ Src.SWAP-gate) x0 (a ∷ b ∷ x) =
      at-≡ (⟦⟧-gen (gate₂ SWAP-gate ↥) (x0 ∷ a ∷ b ∷ x)) Eq.refl (κ0 x0)
    ctrl-gen (g Src.↥) x0 (a ∷ x) =
      at-≡ (•-at (•-at (SWAP-at x0 a x) (↑-at (ctrl-gen g x0 x))) (SWAP-at a x0 _)) Eq.refl
           (Eq.trans (FR.+-identityʳ _) (FR.+-identityˡ _))

  ctrl-sem : (w : Src.Circuit n) (x0 : F) (x : Labels n) →
             ⟦ ctrl* w ⟧ (x0 ∷ x) ≡ (x0 ∷ proj₁ (SI.⟦ w ⟧ x) , κ x0 * proj₂ (SI.⟦ w ⟧ x))
  ctrl-sem [ g ]ʷ x0 x =
    Eq.trans (ctrl-gen g x0 x) (Eq.cong (λ q → x0 ∷ proj₁ q , κ x0 * proj₂ q) (Eq.sym (SI.⟦⟧-gen g x)))
  ctrl-sem ε x0 x =
    Eq.trans (⟦⟧-ε (x0 ∷ x))
      (Eq.trans (Eq.cong (x0 ∷ x ,_) (κ0 x0)) (Eq.cong (λ q → x0 ∷ proj₁ q , κ x0 * proj₂ q) (Eq.sym (SI.⟦⟧-ε x))))
  ctrl-sem (u • v) x0 x =
    Eq.trans (at-≡ (•-at (ctrl-sem v x0 x) (ctrl-sem u x0 (proj₁ (SI.⟦ v ⟧ x)))) Eq.refl
                   (Eq.sym (FR.distribˡ (κ x0) _ _)))
      (Eq.cong (λ q → x0 ∷ proj₁ q , κ x0 * proj₂ q) (Eq.sym (SI.⟦⟧-• u v x)))
