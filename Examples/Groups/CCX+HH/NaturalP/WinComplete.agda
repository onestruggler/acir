------------------------------------------------------------------------
-- Presentations of groups
--
-- Products of window gates in a common frame are complete.
--
-- On 4 + k + c wires a window gate `gate (wg A Y)` is
-- ⌈ inv A ⌉ • Λw k (Λw c Y) • ⌈ A ⌉ (WinGate).  Given an affine word B
-- that sends the frame of every gate of two products into the window
-- of the top 4 + c wires (`AllGood B`), conjugating by B turns each
-- product into Λw k of a circuit on those wires (`into-window`), and
-- two such circuits with the same matrix are equal, given completeness
-- on 4 + c wires: Λw k is injective on matrices (`Λw-inj`, through
-- AtCalc.Λ-at and a vector extending a restricted one, `ext`), and
-- respects derivations.  So two products of window gates in a common
-- frame with the same matrix are equal (`win-complete`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_ ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Notations using (₄₊)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S

module Examples.Groups.CCX+HH.NaturalP.WinComplete
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  (k c : ℕ)
  (complete-top : ∀ {u v : P.Circuit (₄₊ (c + 0))} → interpret u ≡ interpret v →
     (₄₊ (c + 0)) S.⊢ u ≈ v)
  where

open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FP
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using (Vec ; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using (refl ; sym ; trans ; cong)
open import Relation.Nullary using (Dec ; yes ; no)
open import Data.Empty using (⊥-elim)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Instances using (0#)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι ; injective)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_ ; vec-ext ; restrict ; restrict-!)
import Examples.Groups.CCX+HH.Semantics as Q
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum)
open import Examples.Groups.CCX+HH.GeneralN.ActionSemantics using (action⇒matrix ; matrix⇒action)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.SchemaSound using (sound)
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (Λw ; whites)
open import Examples.Groups.CCX+HH.NaturalP.LambdaLaws complete≤ using (Λ-cong ; Λ-• ; Λ-ε)
import Data.Nat.Properties as ℕP₃
open import Examples.Groups.CCX+HH.NaturalP.Affine (λ p → complete≤ (ℕP₃.≤-trans p (ℕP₃.m≤m+n 3 5))) using (AGen ; ⌈_⌉ ; inv ; inv-r ; inv-l)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (A⟦_⟧)
open import Examples.Groups.CCX+HH.NaturalP.Window using (low)
open import Examples.Groups.CCX+HH.NaturalP.AtCalc using (At ; on ; ιW ; Λ-at ; image?)
open import Examples.Groups.CCX+HH.NaturalP.WinGate complete≤ using (ι₄ ; conj-gate)

W : ℕ
W = ₄₊ (k + (c + 0))

------------------------------------------------------------------------
-- Window gates

record WG : Set where
  constructor wg
  field
    A : Word (AGen W)
    Y : Circuit 4

gate : WG → Circuit W
gate (wg A Y) = ⌈ inv A ⌉ • (Λw k (Λw c Y) • ⌈ A ⌉)

gates : Word WG → Circuit W
gates = gate ʷ

-- B sends the frame of the gate into the window of the top 4 + c wires.
Good : Word (AGen W) → WG → Set
Good B (wg A Y) = ∀ h → low k (A⟦ B ⟧ (A⟦ inv A ⟧ (ι₄ k c h))) ≈s zeros

AllGood : Word (AGen W) → Word WG → Set
AllGood B [ g ]ʷ  = Good B g
AllGood B ε       = ⊤
AllGood B (u • v) = AllGood B u × AllGood B v

------------------------------------------------------------------------
-- Into the window

into-window : (B : Word (AGen W)) (u : Word WG) → AllGood B u →
  Σ (Circuit (₄₊ (c + 0))) λ X → W ⊢ ⌈ B ⌉ • (gates u • ⌈ inv B ⌉) ≈ Λw k X
into-window B [ wg A Y ]ʷ good    = conj-gate k c A B Y good
into-window B ε           _       =
  ε , PB.trans (PB.cong PB.refl PB.left-unit) (PB.trans (inv-r B) (PB.sym (Λ-ε (whites k))))
into-window B (u • v)     (gu , gv) = (proj₁ U • proj₁ V) , chain
  where
  U = into-window B u gu
  V = into-window B v gv
  b = ⌈ B ⌉
  ib = ⌈ inv B ⌉
  split : W ⊢ b • ((gates u • gates v) • ib) ≈ (b • (gates u • ib)) • (b • (gates v • ib))
  split =
    PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.left-unit)))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong (PB.sym (inv-l B)) PB.refl)))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.assoc))
    (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
      (PB.sym PB.assoc)))))
  chain : W ⊢ b • ((gates u • gates v) • ib) ≈ Λw k (proj₁ U • proj₁ V)
  chain = PB.trans split (PB.trans (PB.cong (proj₂ U) (proj₂ V))
    (PB.sym (Λ-• (whites k) (proj₁ U) (proj₁ V))))

------------------------------------------------------------------------
-- Λw is injective on matrices

-- A vector with given entries on the image of an embedding.
pick : ∀ {m n} (e : Emb m n) (u : Vec D m) (x : Fin n) → Dec (∃ λ y → ι e y ≡ x) → D
pick e u x (yes (y , _)) = u ! y
pick e u x (no _)        = 0#

ext : ∀ {m n} → Emb m n → Vec D m → Vec D n
ext e u = tabulate λ x → pick e u x (image? e x)

restrict-ext : ∀ {m n} (e : Emb m n) (u : Vec D m) → restrict e (ext e u) ≡ u
restrict-ext e u = vec-ext λ y →
  trans (restrict-! e (ext e u) y)
    (trans (lookup∘tabulate (λ x → pick e u x (image? e x)) (ι e y)) (at y (image? e (ι e y))))
  where
  same : ∀ {y z} → ι e z ≡ ι e y → z ≡ y
  same {y} {z} eq with z FP.≟ y
  ... | yes p = p
  ... | no ne = ⊥-elim (injective e ne eq)
  at : ∀ y (d : Dec (∃ λ z → ι e z ≡ ι e y)) → pick e u (ι e y) d ≡ u ! y
  at y (yes (z , eq)) = cong (u !_) (same eq)
  at y (no ¬i)        = ⊥-elim (¬i (y , refl))

Λw-inj : ∀ {c′} (X X′ : Circuit (₄₊ c′)) → interpret (Λw k X) ≡ interpret (Λw k X′) →
  interpret X ≡ interpret X′
Λw-inj {c′} X X′ eq = action⇒matrix {u = τ X} {v = τ X′} λ u →
  trans (sym (cong (quantum (τ X)) (restrict-ext e u)))
  (trans (sym (on (Λ-at k X) (ext e u)))
  (trans (cong (restrict e) (matrix⇒action {u = τ (Λw k X)} {v = τ (Λw k X′)} eq (ext e u)))
  (trans (on (Λ-at k X′) (ext e u)) (cong (quantum (τ X′)) (restrict-ext e u)))))
  where
  e = ιW k c′

------------------------------------------------------------------------
-- Completeness in a common frame

private
  unconj : (B : Word (AGen W)) (w : Circuit W) → W ⊢ w ≈ ⌈ inv B ⌉ • ((⌈ B ⌉ • (w • ⌈ inv B ⌉)) • ⌈ B ⌉)
  unconj B w = PB.sym
    (PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (inv-l B) PB.refl)
    (PB.trans PB.left-unit
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (inv-l B)) PB.right-unit))))))

win-complete : (B : Word (AGen W)) (u v : Word WG) → AllGood B u → AllGood B v →
  interpret (gates u) ≡ interpret (gates v) → W ⊢ gates u ≈ gates v
win-complete B u v gu gv eq =
  PB.trans (unconj B (gates u))
  (PB.trans (PB.cong PB.refl (PB.cong (PB.trans (proj₂ U) (PB.trans (Λ-cong (whites k) tops)
                                         (PB.sym (proj₂ V)))) PB.refl))
    (PB.sym (unconj B (gates v))))
  where
  U = into-window B u gu
  V = into-window B v gv
  conj-same : interpret (⌈ B ⌉ • (gates u • ⌈ inv B ⌉)) ≡ interpret (⌈ B ⌉ • (gates v • ⌈ inv B ⌉))
  conj-same = action⇒matrix {u = τ (⌈ B ⌉ • (gates u • ⌈ inv B ⌉))} {v = τ (⌈ B ⌉ • (gates v • ⌈ inv B ⌉))}
    λ x → cong (quantum (τ ⌈ B ⌉))
      (matrix⇒action {u = τ (gates u)} {v = τ (gates v)} eq (quantum (τ ⌈ inv B ⌉) x))
  sem : interpret (Λw k (proj₁ U)) ≡ interpret (Λw k (proj₁ V))
  sem = trans (sym (sound (proj₂ U))) (trans conj-same (sound (proj₂ V)))
  tops : (₄₊ (c + 0)) ⊢ proj₁ U ≈ proj₁ V
  tops = complete-top (Λw-inj (proj₁ U) (proj₁ V) sem)
