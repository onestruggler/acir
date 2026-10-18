------------------------------------------------------------------------
-- Presentations of groups
--
-- Decoded atoms in a common frame are complete.
--
-- A decoded atom (AtomCases) is a window gate (WinComplete): `toWG`.
-- A frame for a list of states xs is an affine word B that sends their
-- span into the window of the top 4 + c wires, when xs also spans the
-- unit vectors of the bottom four wires (`Frame`).  Then every decoded
-- atom whose indices lie in the span of xs has its frame sent there as
-- well (`good-atoms`, through Routed.back and AtomCases.pts-in), and
-- two words of decoded atoms with the same matrix are equal
-- (`atoms-complete`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_ ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Notations using (₄₊)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S

module Examples.Groups.CCX+HH.NaturalP.AtomWin
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  (k c : ℕ)
  (complete-top : ∀ {u v : P.Circuit (₄₊ (c + 0))} → interpret u ≡ interpret v →
     (₄₊ (c + 0)) S.⊢ u ≈ v)
  where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using (Vec ; tabulate ; lookup ; _++_)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using (refl ; sym ; cong₂ ; subst ; subst₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.CCX+HH.GeneralN.DecodingPlans using (Atom)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (bits)
open import Examples.Groups.CCX+HH.NaturalP.Schema using (Circuit ; _⊢_≈_)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (A⟦_⟧)
open import Examples.Groups.CCX+HH.NaturalP.Window using (low)
open import Examples.Groups.CCX+HH.NaturalP.Span using (InSpan ; E4 ; e4)
open import Examples.Groups.CCX+HH.NaturalP.SpanEmb using (lookup-++-all)
open import Examples.Groups.CCX+HH.NaturalP.RouteTo using (span-trans)
open import Examples.Groups.CCX+HH.NaturalP.WinComplete complete≤ k c complete-top
  using (WG ; wg ; gate ; gates ; AllGood ; win-complete)
open import Examples.Groups.CCX+HH.NaturalP.AtomDecoder k c
  using (W ; N ; Routed ; Decoded ; trivial ; routed ; decode ; c₄)
open import Examples.Groups.CCX+HH.NaturalP.AtomCases k c
  using (classify ; atom ; ArgsIn ; PtsIn ; pts-in)

private
  variable
    r : ℕ

------------------------------------------------------------------------
-- Decoded atoms are window gates

toWG : {p : Atom N} → Decoded p → Word WG
toWG (trivial _) = ε
toWG (routed r)  = [ wg (Routed.K r) (c₄ (Routed.q r)) ]ʷ

decode-gates : {p : Atom N} (d : Decoded p) → decode d ≡ gates (toWG d)
decode-gates (trivial _) = refl
decode-gates (routed r)  = refl

dw : Atom N → Word WG
dw p = toWG (classify p)

dws : Word (Atom N) → Word WG
dws = dw ʷ

atoms-gates : (w : Word (Atom N)) → (atom ʷ) w ≡ gates (dws w)
atoms-gates [ p ]ʷ  = decode-gates (classify p)
atoms-gates ε       = refl
atoms-gates (u • v) = cong₂ _•_ (atoms-gates u) (atoms-gates v)

------------------------------------------------------------------------
-- Frames

record Frame (B : Word (AGen W)) (xs : Vec (State W) r) : Set where
  field
    into  : ∀ {y} → InSpan xs y → low k (A⟦ B ⟧ y) ≈s zeros
    e4-in : ∀ t → InSpan xs (e4 t)

private
  lookup-E4 : ∀ t → lookup (E4 {k + (c + 0)}) t ≡ e4 t
  lookup-E4 zero                   = refl
  lookup-E4 (suc zero)             = refl
  lookup-E4 (suc (suc zero))       = refl
  lookup-E4 (suc (suc (suc zero))) = refl

good-decoded : ∀ {B} {xs : Vec (State W) r} → Frame B xs → {p : Atom N} (d : Decoded p) →
  PtsIn xs d → AllGood B (toWG d)
good-decoded fr (trivial _) _   = tt
good-decoded {xs = xs} fr (routed r) pin h =
  Frame.into fr (span-trans xs (pl ++ E4) each (Routed.back r h))
  where
  pl = tabulate (λ y → bits W (Routed.pts r y))
  each : ∀ i → InSpan xs (lookup (pl ++ E4) i)
  each = lookup-++-all (InSpan xs) pl E4
    (λ t → subst (InSpan xs) (sym (lookup∘tabulate (λ y → bits W (Routed.pts r y)) t)) (pin t))
    (λ t → subst (InSpan xs) (sym (lookup-E4 t)) (Frame.e4-in fr t))

AllArgsIn : Vec (State W) r → Word (Atom N) → Set
AllArgsIn xs [ p ]ʷ  = ArgsIn xs p
AllArgsIn xs ε       = ⊤
AllArgsIn xs (u • v) = AllArgsIn xs u × AllArgsIn xs v

good-atoms : ∀ {B} {xs : Vec (State W) r} → Frame B xs → (w : Word (Atom N)) →
  AllArgsIn xs w → AllGood B (dws w)
good-atoms {xs = xs} fr [ p ]ʷ  a         = good-decoded fr (classify p) (pts-in xs p a)
good-atoms           fr ε       _         = tt
good-atoms           fr (u • v) (au , av) = good-atoms fr u au , good-atoms fr v av

------------------------------------------------------------------------
-- Completeness in a frame

atoms-complete : ∀ {B} {xs : Vec (State W) r} → Frame B xs → (u v : Word (Atom N)) →
  AllArgsIn xs u → AllArgsIn xs v → interpret ((atom ʷ) u) ≡ interpret ((atom ʷ) v) →
  W ⊢ (atom ʷ) u ≈ (atom ʷ) v
atoms-complete {B = B} fr u v au av eq =
  subst₂ (λ x y → W ⊢ x ≈ y) (sym (atoms-gates u)) (sym (atoms-gates v))
    (win-complete B (dws u) (dws v) (good-atoms fr u au) (good-atoms fr v av)
      (subst₂ (λ x y → interpret x ≡ interpret y) (atoms-gates u) (atoms-gates v) eq))
