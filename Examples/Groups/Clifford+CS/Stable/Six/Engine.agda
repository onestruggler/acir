------------------------------------------------------------------------
-- Presentations of groups
--
-- Six-wire derivations over placed gates: windows, transport along a
-- network, and chains of segment replacements
--
-- On six wires no borrowed-wire switch of an S-box leaves a wire idle,
-- so its derivation (the joint paper's b6.py) is written over small
-- gates placed by swap networks: a gate `gk ρ c` is the k-wire circuit
-- c placed by the network ρ (`LocalPlace.pl`), and a line is a list of
-- them.  A step replaces a segment of a line, either
--
--   * by a window (`Window.win`): every gate of the segment and of its
--     replacement avoids one wire w; the network τ carries w to the top,
--     each gate is placed again under τ by a network on the other five
--     wires (`Frame`, from `LocalPlace.place-eq`, whose hypotheses are
--     equations between concrete permutations, `Eq.refl`), and the two
--     five-wire circuits so obtained are compared by one evaluation,
--     with completeness on five wires as a module parameter; or
--   * by transport (`transport`): an equation between two lines,
--     conjugated by a network, is the equation between the lines placed
--     again — so a lemma proved at one placement holds at every other.
--
-- `run` assembles a chain of such steps, each typed by the line it is
-- applied to (Four.Chain, after Real-Clifford+CH's Eq80); the networks
-- and the derivations are written by scratchpad/stable/gen6.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Six.Engine where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.TopWeakening using (σ ; σ⁻¹ ; σσ⁻¹ ; nat)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Same ; same-sem)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; perm ; revS ; net-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-• ; pl-pl ; place-eq)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Weakening using (top-congᵧ)
open import Examples.Groups.Clifford+CS.Stable.Nets7 using (sw₆ ; ns₆) public
open import Examples.Groups.Clifford+CS.Soundness using (sound)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (λ¹-sem ; ⟦•⟧ ; ⟦ε⟧)
open import Examples.Groups.Clifford+CS.Semantics.Control using (ctrl ; ctrl-~)
open import Examples.Groups.Clifford+CS.Semantics using (~-trans ; ~-sym ; ~-refl ; ∙-cong ; ∙-identityʳ ; ε∙ ; _∙_)
open import Examples.Groups.Clifford+CS.Stable.CtrlSem using (conj-ctrl ; ctrl-• ; ctrl-ε′)

------------------------------------------------------------------------
-- Networks on five wires

sw₅ : ℕ → Word (S.Gen 5)
sw₅ 0 = [ S.gate₂ S.σ-gate ]ʷ
sw₅ 1 = [ S.gate₂ S.σ-gate S.↥ ]ʷ
sw₅ 2 = [ S.gate₂ S.σ-gate S.↥ S.↥ ]ʷ
sw₅ 3 = [ S.gate₂ S.σ-gate S.↥ S.↥ S.↥ ]ʷ
sw₅ _ = ε

ns₅ : List ℕ → Word (S.Gen 5)
ns₅ []       = ε
ns₅ (p ∷ ps) = sw₅ p • ns₅ ps

sw₄ : ℕ → Word (S.Gen 4)
sw₄ 0 = [ S.gate₂ S.σ-gate ]ʷ
sw₄ 1 = [ S.gate₂ S.σ-gate S.↥ ]ʷ
sw₄ 2 = [ S.gate₂ S.σ-gate S.↥ S.↥ ]ʷ
sw₄ _ = ε

ns₄ : List ℕ → Word (S.Gen 4)
ns₄ []       = ε
ns₄ (p ∷ ps) = sw₄ p • ns₄ ps

------------------------------------------------------------------------
-- Placed gates and lines

data PG : Set where
  g1 : List ℕ → Circuit 1 → PG
  g2 : List ℕ → Circuit 2 → PG
  g3 : List ℕ → Circuit 3 → PG
  g4 : List ℕ → Circuit 4 → PG
  g5 : List ℕ → Circuit 5 → PG

-- On six wires, and (networks on the bottom five wires) on five.
⟦_⟧₆ : PG → Circuit 6
⟦ g1 ρ c ⟧₆ = pl (ns₆ ρ) (c ↓ᵏ 5)
⟦ g2 ρ c ⟧₆ = pl (ns₆ ρ) (c ↓ᵏ 4)
⟦ g3 ρ c ⟧₆ = pl (ns₆ ρ) (c ↓ᵏ 3)
⟦ g4 ρ c ⟧₆ = pl (ns₆ ρ) (c ↓ᵏ 2)
⟦ g5 ρ c ⟧₆ = pl (ns₆ ρ) (c ↓ᵏ 1)

⟦_⟧₅ : PG → Circuit 5
⟦ g1 ρ c ⟧₅ = pl (ns₅ ρ) (c ↓ᵏ 4)
⟦ g2 ρ c ⟧₅ = pl (ns₅ ρ) (c ↓ᵏ 3)
⟦ g3 ρ c ⟧₅ = pl (ns₅ ρ) (c ↓ᵏ 2)
⟦ g4 ρ c ⟧₅ = pl (ns₅ ρ) (c ↓ᵏ 1)
⟦ g5 ρ c ⟧₅ = pl (ns₅ ρ) c

⟪_⟫₆ : List PG → Circuit 6
⟪ [] ⟫₆           = ε
⟪ x ∷ [] ⟫₆       = ⟦ x ⟧₆
⟪ x ∷ (y ∷ ys) ⟫₆ = ⟦ x ⟧₆ • ⟪ y ∷ ys ⟫₆

⟪_⟫₅ : List PG → Circuit 5
⟪ [] ⟫₅           = ε
⟪ x ∷ [] ⟫₅       = ⟦ x ⟧₅
⟪ x ∷ (y ∷ ys) ⟫₅ = ⟦ x ⟧₅ • ⟪ y ∷ ys ⟫₅

private
  refl≡ᵧ : ∀ {n} {a b : Circuit n} → a ≡ b → n ⊢ᵧ a ≈ b
  refl≡ᵧ Eq.refl = PB.refl

  -- Placing is a congruence.
  plᵧ : (σ : Word (S.Gen 6)) {g g′ : Circuit 6} → 6 ⊢ᵧ g ≈ g′ → 6 ⊢ᵧ pl σ g ≈ pl σ g′
  plᵧ σ e = PB.cong PB.refl (PB.cong e PB.refl)

  pl-ε : (σ : Word (S.Gen 6)) → 6 ⊢ᵧ pl σ ε ≈ ε
  pl-ε σ = PB.trans (PB.cong PB.refl PB.left-unit) (embed (net-inv σ))

------------------------------------------------------------------------
-- Frames: a gate placed again under a network

-- A record, so that the gates are read off its type.
record Frame (τ : List ℕ) (x x′ : PG) : Set where
  constructor frame
  field
    eq : 6 ⊢ᵧ ⟦ x ⟧₆ ≈ pl (ns₆ τ) ⟦ x′ ⟧₆

-- The agreement of the two placements on the j-th wire of the gate.
Ag : List ℕ → List ℕ → List ℕ → Fin 6 → Set
Ag τ ρ ρ′ j = perm (ns₆ τ • ns₆ ρ′) ⟨$⟩ʳ (perm (revS (ns₆ ρ)) ⟨$⟩ʳ j) ≡ j

private
  -- From place-eq and pl-pl.
  framed : ∀ {k r} (c : Circuit k) (σ σ′ τ : Word (S.Gen (k + r))) →
           (k + r) ⊢ pl σ (c ↓ᵏ r) ≈ pl (τ • σ′) (c ↓ᵏ r) →
           (k + r) ⊢ᵧ pl σ (c ↓ᵏ r) ≈ pl τ (pl σ′ (c ↓ᵏ r))
  framed c σ σ′ τ e = PB.trans (embed e) (PB.sym (embed (pl-pl τ σ′ (c ↓ᵏ _))))

fr1 : ∀ τ ρ ρ′ (c : Circuit 1) → Ag τ ρ ρ′ 0F → Frame τ (g1 ρ c) (g1 ρ′ c)
fr1 τ ρ ρ′ c e0 = frame (framed c (ns₆ ρ) (ns₆ ρ′) (ns₆ τ) (place-eq c (ns₆ ρ) (ns₆ τ • ns₆ ρ′) agree))
  where
  agree : ∀ (j : Fin 6) → toℕ j < 1 → Ag τ ρ ρ′ j
  agree 0F      _ = e0
  agree (sF j) (s≤s ())

fr2 : ∀ τ ρ ρ′ (c : Circuit 2) → Ag τ ρ ρ′ 0F → Ag τ ρ ρ′ (sF 0F) → Frame τ (g2 ρ c) (g2 ρ′ c)
fr2 τ ρ ρ′ c e0 e1 = frame (framed c (ns₆ ρ) (ns₆ ρ′) (ns₆ τ) (place-eq c (ns₆ ρ) (ns₆ τ • ns₆ ρ′) agree))
  where
  agree : ∀ (j : Fin 6) → toℕ j < 2 → Ag τ ρ ρ′ j
  agree 0F           _ = e0
  agree (sF 0F)      _ = e1
  agree (sF (sF j)) (s≤s (s≤s ()))

fr3 : ∀ τ ρ ρ′ (c : Circuit 3) → Ag τ ρ ρ′ 0F → Ag τ ρ ρ′ (sF 0F) → Ag τ ρ ρ′ (sF (sF 0F)) →
      Frame τ (g3 ρ c) (g3 ρ′ c)
fr3 τ ρ ρ′ c e0 e1 e2 = frame (framed c (ns₆ ρ) (ns₆ ρ′) (ns₆ τ) (place-eq c (ns₆ ρ) (ns₆ τ • ns₆ ρ′) agree))
  where
  agree : ∀ (j : Fin 6) → toℕ j < 3 → Ag τ ρ ρ′ j
  agree 0F                _ = e0
  agree (sF 0F)           _ = e1
  agree (sF (sF 0F))      _ = e2
  agree (sF (sF (sF j))) (s≤s (s≤s (s≤s ())))

fr4 : ∀ τ ρ ρ′ (c : Circuit 4) → Ag τ ρ ρ′ 0F → Ag τ ρ ρ′ (sF 0F) → Ag τ ρ ρ′ (sF (sF 0F)) →
      Ag τ ρ ρ′ (sF (sF (sF 0F))) → Frame τ (g4 ρ c) (g4 ρ′ c)
fr4 τ ρ ρ′ c e0 e1 e2 e3 = frame (framed c (ns₆ ρ) (ns₆ ρ′) (ns₆ τ) (place-eq c (ns₆ ρ) (ns₆ τ • ns₆ ρ′) agree))
  where
  agree : ∀ (j : Fin 6) → toℕ j < 4 → Ag τ ρ ρ′ j
  agree 0F                     _ = e0
  agree (sF 0F)                _ = e1
  agree (sF (sF 0F))           _ = e2
  agree (sF (sF (sF 0F)))      _ = e3
  agree (sF (sF (sF (sF j)))) (s≤s (s≤s (s≤s (s≤s ()))))

fr5 : ∀ τ ρ ρ′ (c : Circuit 5) → Ag τ ρ ρ′ 0F → Ag τ ρ ρ′ (sF 0F) → Ag τ ρ ρ′ (sF (sF 0F)) →
      Ag τ ρ ρ′ (sF (sF (sF 0F))) → Ag τ ρ ρ′ (sF (sF (sF (sF 0F)))) → Frame τ (g5 ρ c) (g5 ρ′ c)
fr5 τ ρ ρ′ c e0 e1 e2 e3 e4 = frame (framed c (ns₆ ρ) (ns₆ ρ′) (ns₆ τ) (place-eq c (ns₆ ρ) (ns₆ τ • ns₆ ρ′) agree))
  where
  agree : ∀ (j : Fin 6) → toℕ j < 5 → Ag τ ρ ρ′ j
  agree 0F                          _ = e0
  agree (sF 0F)                     _ = e1
  agree (sF (sF 0F))                _ = e2
  agree (sF (sF (sF 0F)))           _ = e3
  agree (sF (sF (sF (sF 0F))))      _ = e4
  agree (sF (sF (sF (sF (sF j))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

infixr 5 _∷_
data Frames (τ : List ℕ) : List PG → List PG → Set where
  []  : Frames τ [] []
  _∷_ : ∀ {x x′ xs xs′} → Frame τ x x′ → Frames τ xs xs′ → Frames τ (x ∷ xs) (x′ ∷ xs′)

frames : ∀ {τ xs xs′} → Frames τ xs xs′ → 6 ⊢ᵧ ⟪ xs ⟫₆ ≈ pl (ns₆ τ) ⟪ xs′ ⟫₆
frames {τ} []             = PB.sym (pl-ε (ns₆ τ))
frames     (f ∷ [])       = Frame.eq f
frames {τ} (_∷_ {x′ = x′} f (_∷_ {x′ = y′} {xs′ = ys′} g fs)) =
  PB.trans (PB.cong (Frame.eq f) (frames (g ∷ fs)))
           (PB.sym (embed (pl-• (ns₆ τ) ⟦ x′ ⟧₆ ⟪ y′ ∷ ys′ ⟫₆)))

------------------------------------------------------------------------
-- Transport and windows

-- An equation between two lines holds between the lines placed again.
transport : ∀ τ {xs xs′ ys ys′} → Frames τ xs xs′ → Frames τ ys ys′ →
            6 ⊢ᵧ ⟪ xs′ ⟫₆ ≈ ⟪ ys′ ⟫₆ → 6 ⊢ᵧ ⟪ xs ⟫₆ ≈ ⟪ ys ⟫₆
transport τ fx fy e = PB.trans (frames fx) (PB.trans (plᵧ (ns₆ τ) e) (PB.sym (frames fy)))

-- A five-wire gate as two.
split5 : ∀ ρ (a b : Circuit 5) → 6 ⊢ᵧ ⟪ g5 ρ (a • b) ∷ [] ⟫₆ ≈ ⟪ g5 ρ a ∷ g5 ρ b ∷ [] ⟫₆
split5 ρ a b = embed (pl-• (ns₆ ρ) (a ↓ᵏ 1) (b ↓ᵏ 1))

-- Controlled lines: the five-wire reading of a gate denotes the
-- controlled operator of a four-wire circuit (top wire the control), by
-- a λ¹-image placed below the control (`sbox`) or by evaluating a small
-- gate against one (`small`); a line of them, the controlled product.
record CF (x : PG) (d : Circuit 4) : Set where
  constructor cf
  field
    sem : ⟦ ⟦ x ⟧₅ ⟧ ~ ctrl ⟦ d ⟧

sbox : ∀ ρ (g : Gen 4) →
       pl (ns₅ ρ) (λ¹ g) ≡ top (net (ns₄ ρ)) • (λ¹ g • top (net (revS (ns₄ ρ)))) →
       CF (g5 ρ (λ¹ g)) (pl (ns₄ ρ) [ g ]ʷ)
sbox ρ g e = cf (Eq.subst (λ w → ⟦ w ⟧ ~ ctrl ⟦ pl (ns₄ ρ) [ g ]ʷ ⟧) (Eq.sym e)
  (conj-ctrl (net (ns₄ ρ)) (net (revS (ns₄ ρ))) [ g ]ʷ (λ¹ g) (sound (net-inv (ns₄ ρ))) (λ¹-sem [ g ]ʷ)))

small : ∀ (x : PG) (g : Gen 4) → Same ⟦ x ⟧₅ (λ¹ g) → CF x [ g ]ʷ
small x g s = cf (~-trans {s = ⟦ ⟦ x ⟧₅ ⟧} {t = ⟦ λ¹ g ⟧} {u = ctrl ⟦ [ g ]ʷ ⟧}
                     (same-sem ⟦ x ⟧₅ (λ¹ g) s) (λ¹-sem [ g ]ʷ))

infixr 5 _∷ᶜ_
data CtrlLine : List PG → Circuit 4 → Set where
  []ᶜ  : CtrlLine [] ε
  _∷ᶜ_ : ∀ {x xs d ds} → CF x d → CtrlLine xs ds → CtrlLine (x ∷ xs) (d • ds)

ctrl-line : ∀ {xs ds} → CtrlLine xs ds → ⟦ ⟪ xs ⟫₅ ⟧ ~ ctrl ⟦ ds ⟧
ctrl-line []ᶜ = ctrl-ε′
ctrl-line (_∷ᶜ_ {x} {d = d} c []ᶜ) =
  ~-trans {s = ⟦ ⟦ x ⟧₅ ⟧} {t = ctrl ⟦ d ⟧} {u = ctrl ⟦ d • ε ⟧} (CF.sem c)
    (ctrl-~ {s = ⟦ d ⟧} {⟦ d • ε ⟧}
      (~-sym {s = ⟦ d • ε ⟧} {t = ⟦ d ⟧}
        (~-trans {s = ⟦ d • ε ⟧} {t = ⟦ d ⟧ ∙ ⟦ ε ⟧} {u = ⟦ d ⟧} (⟦•⟧ d ε)
          (~-trans {s = ⟦ d ⟧ ∙ ⟦ ε ⟧} {t = ⟦ d ⟧ ∙ ε∙} {u = ⟦ d ⟧}
            (∙-cong {s = ⟦ d ⟧} {⟦ d ⟧} {⟦ ε ⟧} {ε∙} (~-refl ⟦ d ⟧) ⟦ε⟧) (∙-identityʳ ⟦ d ⟧)))))
ctrl-line (_∷ᶜ_ {x} {y ∷ ys} {d} {ds} c cs@(_ ∷ᶜ _)) =
  ~-trans {s = ⟦ ⟦ x ⟧₅ • ⟪ y ∷ ys ⟫₅ ⟧} {t = ⟦ ⟦ x ⟧₅ ⟧ ∙ ⟦ ⟪ y ∷ ys ⟫₅ ⟧} {u = ctrl ⟦ d • ds ⟧}
    (⟦•⟧ ⟦ x ⟧₅ ⟪ y ∷ ys ⟫₅)
    (~-trans {s = ⟦ ⟦ x ⟧₅ ⟧ ∙ ⟦ ⟪ y ∷ ys ⟫₅ ⟧} {t = ctrl ⟦ d ⟧ ∙ ctrl ⟦ ds ⟧} {u = ctrl ⟦ d • ds ⟧}
      (∙-cong {s = ⟦ ⟦ x ⟧₅ ⟧} {ctrl ⟦ d ⟧} {⟦ ⟪ y ∷ ys ⟫₅ ⟧} {ctrl ⟦ ds ⟧} (CF.sem c) (ctrl-line cs))
      (ctrl-• d ds))

module Window (c₅ : ∀ {u v : Circuit 5} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ᵧ u ≈ v) where

  -- Lines that avoid the top wire are five-wire lines; compare them by
  -- an evaluation, or by a five-wire derivation.
  win′ : ∀ τ {xs xs′ ys ys′} → Frames τ xs xs′ → Frames τ ys ys′ →
         ⟪ xs′ ⟫₆ ≡ top ⟪ xs′ ⟫₅ → ⟪ ys′ ⟫₆ ≡ top ⟪ ys′ ⟫₅ →
         5 ⊢ᵧ ⟪ xs′ ⟫₅ ≈ ⟪ ys′ ⟫₅ → 6 ⊢ᵧ ⟪ xs ⟫₆ ≈ ⟪ ys ⟫₆
  win′ τ fx fy ex ey e =
    transport τ fx fy (PB.trans (refl≡ᵧ ex) (PB.trans (top-congᵧ e) (refl≡ᵧ (Eq.sym ey))))

  win : ∀ τ {xs xs′ ys ys′} → Frames τ xs xs′ → Frames τ ys ys′ →
        ⟪ xs′ ⟫₆ ≡ top ⟪ xs′ ⟫₅ → ⟪ ys′ ⟫₆ ≡ top ⟪ ys′ ⟫₅ →
        Same ⟪ xs′ ⟫₅ ⟪ ys′ ⟫₅ → 6 ⊢ᵧ ⟪ xs ⟫₆ ≈ ⟪ ys ⟫₆
  win τ {xs′ = xs′} {ys′ = ys′} fx fy ex ey s =
    win′ τ fx fy ex ey (c₅ (same-sem ⟪ xs′ ⟫₅ ⟪ ys′ ⟫₅ s))

  -- Controlled lines: compare the domain words instead.
  winC : ∀ τ {xs xs′ ys ys′ ds es} → Frames τ xs xs′ → Frames τ ys ys′ →
         ⟪ xs′ ⟫₆ ≡ top ⟪ xs′ ⟫₅ → ⟪ ys′ ⟫₆ ≡ top ⟪ ys′ ⟫₅ →
         CtrlLine xs′ ds → CtrlLine ys′ es → Same ds es → 6 ⊢ᵧ ⟪ xs ⟫₆ ≈ ⟪ ys ⟫₆
  winC τ {xs′ = xs′} {ys′ = ys′} {ds} {es} fx fy ex ey cx cy s =
    win′ τ fx fy ex ey (c₅
      (~-trans {s = ⟦ ⟪ xs′ ⟫₅ ⟧} {t = ctrl ⟦ ds ⟧} {u = ⟦ ⟪ ys′ ⟫₅ ⟧} (ctrl-line cx)
        (~-trans {s = ctrl ⟦ ds ⟧} {t = ctrl ⟦ es ⟧} {u = ⟦ ⟪ ys′ ⟫₅ ⟧}
          (ctrl-~ {s = ⟦ ds ⟧} {⟦ es ⟧} (same-sem ds es s))
          (~-sym {s = ⟦ ⟪ ys′ ⟫₅ ⟧} {t = ctrl ⟦ es ⟧} (ctrl-line cy)))))

------------------------------------------------------------------------
-- The ends of a derivation

-- Re-bracketing on six wires, in the old theory.
module T₆ = Tools (6 VRel,_===_)

-- A circuit one wire up is the circuit with an idle wire on top, carried
-- down by the cycle σ.
↑≈ : ∀ {n} (w : Circuit n) → (suc n) ⊢ w ↑ ≈ σ n • top w • σ⁻¹ n
↑≈ {n} w = begin
  w ↑                         ≈⟨ sym right-unit ⟩
  w ↑ • ε                     ≈⟨ back _ (sym (σσ⁻¹ n)) ⟩
  w ↑ • σ n • σ⁻¹ n           ≈⟨ sym assoc ⟩
  (w ↑ • σ n) • σ⁻¹ n         ≈⟨ front _ (nat w) ⟩
  (σ n • top w) • σ⁻¹ n       ≈⟨ assoc ⟩
  σ n • top w • σ⁻¹ n ∎
  where open Tools ((suc n) VRel,_===_)

------------------------------------------------------------------------
-- Chains of segment replacements

open Tools (6 YVRel,_===_) using (front ; back) public

private
  ⟪⟫-∷ : ∀ x xs → 6 ⊢ᵧ ⟪ x ∷ xs ⟫₆ ≈ ⟦ x ⟧₆ • ⟪ xs ⟫₆
  ⟪⟫-∷ x []       = PB.sym PB.right-unit
  ⟪⟫-∷ x (y ∷ ys) = PB.refl

  ⟪⟫-++ : ∀ xs ys → 6 ⊢ᵧ ⟪ xs ++ ys ⟫₆ ≈ ⟪ xs ⟫₆ • ⟪ ys ⟫₆
  ⟪⟫-++ []       ys = PB.sym PB.left-unit
  ⟪⟫-++ (x ∷ xs) ys =
    PB.trans (⟪⟫-∷ x (xs ++ ys))
    (PB.trans (back ⟦ x ⟧₆ (⟪⟫-++ xs ys))
    (PB.trans (PB.sym PB.assoc) (front ⟪ ys ⟫₆ (PB.sym (⟪⟫-∷ x xs)))))

  seg : ∀ p x y s → 6 ⊢ᵧ ⟪ x ⟫₆ ≈ ⟪ y ⟫₆ → 6 ⊢ᵧ ⟪ p ++ x ++ s ⟫₆ ≈ ⟪ p ++ y ++ s ⟫₆
  seg p x y s e =
    PB.trans (⟪⟫-++ p (x ++ s))
    (PB.trans (back ⟪ p ⟫₆ (PB.trans (⟪⟫-++ x s) (PB.trans (front ⟪ s ⟫₆ e) (PB.sym (⟪⟫-++ y s)))))
              (PB.sym (⟪⟫-++ p (y ++ s))))

  drop-drop : ∀ (k n : ℕ) (xs : List PG) → drop n (drop k xs) ≡ drop (k + n) xs
  drop-drop zero    n xs       = Eq.refl
  drop-drop (suc k) zero    [] = Eq.refl
  drop-drop (suc k) (suc n) [] = Eq.refl
  drop-drop (suc k) n (x ∷ xs) = drop-drop k n xs

-- Replacing the n gates from position k.
step : ∀ (k n : ℕ) (xs ys : List PG) → 6 ⊢ᵧ ⟪ take n (drop k xs) ⟫₆ ≈ ⟪ ys ⟫₆ →
       6 ⊢ᵧ ⟪ xs ⟫₆ ≈ ⟪ take k xs ++ ys ++ drop (k + n) xs ⟫₆
step k n xs ys e =
  PB.trans (refl≡ᵧ (Eq.cong ⟪_⟫₆ split))
  (PB.trans (seg (take k xs) (take n (drop k xs)) ys (drop n (drop k xs)) e)
            (refl≡ᵧ (Eq.cong (λ r → ⟪ take k xs ++ ys ++ r ⟫₆) (drop-drop k n xs))))
  where
  split : xs ≡ take k xs ++ (take n (drop k xs) ++ drop n (drop k xs))
  split = Eq.trans (Eq.sym (take++drop≡id k xs))
                   (Eq.cong (take k xs ++_) (Eq.sym (take++drop≡id n (drop k xs))))

record Step (xs : List PG) : Set where
  constructor at
  field
    k n : ℕ
    ys  : List PG
    e   : 6 ⊢ᵧ ⟪ take n (drop k xs) ⟫₆ ≈ ⟪ ys ⟫₆

next : ∀ {xs : List PG} → Step xs → List PG
next {xs} (at k n ys _) = take k xs ++ ys ++ drop (k + n) xs

infixr 4 _▸_
data Chain : List PG → List PG → Set where
  done : ∀ {xs : List PG} → Chain xs xs
  _▸_  : ∀ {xs zs : List PG} (s : Step xs) → Chain (next s) zs → Chain xs zs

run : ∀ {xs zs : List PG} → Chain xs zs → 6 ⊢ᵧ ⟪ xs ⟫₆ ≈ ⟪ zs ⟫₆
run done                   = PB.refl
run {xs} (at k n ys e ▸ c) = PB.trans (step k n xs ys e) (run c)
