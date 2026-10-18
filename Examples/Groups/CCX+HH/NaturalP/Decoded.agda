------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoded auxiliary relations, derived.
--
-- On 4 + k + c wires (c at least 8), an auxiliary edge is decoded as
-- the word of decoded atoms of its plan (`dE`, `D`), which acts on
-- vectors as the edge (`D-act`).  Every relation of the auxiliary
-- presentation (Subgroup/PresentationAt) — a round trip, or a relation
-- of Table 1 translated at a coset — decodes to an equation between
-- two words of decoded atoms whose indices lie among at most eight
-- indices and the indices below 16 (AxIdx, PlanArgs).  That frame is
-- moved into the window of the top 4 + c wires by one affine word
-- (RouteTo.frame), and the equation is derived by AtomWin's
-- completeness in a common frame (`decoded`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_ ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Notations using (₄₊)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S

module Examples.Groups.CCX+HH.NaturalP.Decoded
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  (k c : ℕ) (big : 8 ≤ c)
  (complete-top : ∀ {u v : P.Circuit (₄₊ (c + 0))} → interpret u ≡ interpret v →
     (₄₊ (c + 0)) S.⊢ u ≈ v)
  where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; fromℕ<)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (zero ; suc ; z≤n ; s≤s ; _^_ ; _<_)
import Data.Nat.Properties as NP
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; map ; _++_)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
  using (refl ; sym ; trans ; cong ; cong₂ ; subst ; subst₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; _ᵗ)
import Presentation.Base as PB

import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
open T using (M-gen ; X-gen ; K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as TS
open TS using (actVʷ ; same-action)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red
open import Examples.Groups.CCX+HH.Subgroup.Action using (Coset ; c00 ; c10 ; c11 ; c01 ; dyadic-step)
import Examples.Groups.CCX+HH-TwoLevel.Derived as TD
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum)
open import Examples.Groups.CCX+HH.GeneralN.ActionSemantics using (action⇒matrix)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (bits)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State)
import Examples.Groups.CCX+HH.GeneralN.DecodingPlans as Plan
open Plan using (Atom ; MM ; XX ; J ; read ; plan)
import Examples.Groups.CCX+HH.CircuitTranslation as CT
open import Examples.Groups.CCX+HH.NaturalP.Schema using (_⊢_≈_)
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen)
open import Examples.Groups.CCX+HH.NaturalP.Span using (InSpan ; E4)
open import Examples.Groups.CCX+HH.NaturalP.SpanEmb using (elem-span ; span-++ˡ ; span-++ʳ ; e4-span)
open import Examples.Groups.CCX+HH.NaturalP.RouteTo using (frame ; module Framed)
open import Examples.Groups.CCX+HH.NaturalP.SmallIdx using (small-span)
open import Examples.Groups.CCX+HH.NaturalP.PlanArgs using (AllW ; GenQ ; AtomQ ; Small ; plan-args)
open import Examples.Groups.CCX+HH.NaturalP.AxIdx using (AxIdx ; ax-in)
open import Examples.Groups.CCX+HH.NaturalP.AtomDecoder k c using (W ; N ; decode-act)
open import Examples.Groups.CCX+HH.NaturalP.AtomCases k c using (atom ; classify)
open import Examples.Groups.CCX+HH.NaturalP.AtomWin complete≤ k c complete-top
  using (Frame ; AllArgsIn ; atoms-complete)

module Aux = CT.Auxiliary (k + (c + 0))

private
  enough : 6 ≤ N
  enough = NP.≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
    (NP.^-monoʳ-≤ 2 {4} {₄₊ (k + (c + 0))} (s≤s (s≤s (s≤s (s≤s z≤n)))))

------------------------------------------------------------------------
-- The decoder of edges

dE : Aux.Edge → P.Circuit W
dE g = (atom ʷ) (plan N enough g)

D : Word Aux.Edge → P.Circuit W
D = dE ʷ

private
  D-atoms : ∀ u → D u ≡ (atom ʷ) ((plan N enough ʷ) u)
  D-atoms [ g ]ʷ  = refl
  D-atoms ε       = refl
  D-atoms (u • v) = cong₂ _•_ (D-atoms u) (D-atoms v)

  atoms-act : ∀ w v → quantum (τ ((atom ʷ) w)) v ≡ actVʷ (read w) v
  atoms-act [ p ]ʷ  v = decode-act (classify p) v
  atoms-act ε       v = refl
  atoms-act (u • w) v = trans (cong (quantum (τ ((atom ʷ) u))) (atoms-act w v)) (atoms-act u _)

edge-act : ∀ g v → quantum (τ (dE g)) v ≡ actVʷ (Aux.e g) v
edge-act g v = trans (atoms-act (plan N enough g) v)
  (same-action (read (plan N enough g)) (Aux.e g)
    (Red.sound-act (PB.sym (Plan.correct N enough g)) TS.𝕀) v)

D-act : ∀ u v → quantum (τ (D u)) v ≡ actVʷ (Aux.encode u) v
D-act [ g ]ʷ  v = edge-act g v
D-act ε       v = refl
D-act (u • w) v = trans (cong (quantum (τ (D u))) (D-act w v)) (D-act u _)

------------------------------------------------------------------------
-- Frames of at most eight indices

private
  P : Fin N → State W
  P = bits W

  frameList : ∀ {r} → Vec (Fin N) r → Vec (State W) (r + 4)
  frameList ix = map P ix ++ E4

  len-ok : ∀ {r} → r ≤ 8 → r + 4 ≤ ₄₊ (c + 0)
  len-ok {r} le = NP.≤-trans (NP.+-monoˡ-≤ 4 (NP.≤-trans le (NP.≤-trans big (NP.≤-reflexive (sym (NP.+-identityʳ c))))))
    (NP.≤-reflexive (NP.+-comm (c + 0) 4))

  mkFrame : ∀ {r} (ix : Vec (Fin N) r) → r ≤ 8 → Σ (Word (AGen W)) λ B → Frame B (frameList ix)
  mkFrame ix le = Framed.B fr , record { into = Framed.into fr ; e4-in = e4-span (map P ix) }
    where
    fr = frame k (c + 0) (frameList ix) (len-ok le)

  -- The property of an index: its state is in the span of the frame.
  Q : ∀ {r} → Vec (Fin N) r → Fin N → Set
  Q ix z = InSpan (frameList ix) (P z)

  small : ∀ {r} (ix : Vec (Fin N) r) → Small (Q ix)
  small ix z lt = span-++ʳ (map P ix) (small-span (k + (c + 0)) z lt)

  in-ix : ∀ {r} (ix : Vec (Fin N) r) i → Q ix (lookup ix i)
  in-ix ix i = span-++ˡ {xs = map P ix} E4
    (subst (InSpan (map P ix)) (VecP.lookup-map i P ix) (elem-span (map P ix) i))

  -- Indices of edges, through the walk and the plans.
  walk-all : ∀ (R : Fin N → Set) c w → AllW (GenQ R) w →
    AllW (λ g → GenQ R (proj₂ g)) (proj₁ ((Aux.Theory.h ᵗ) c w))
  walk-all R c [ y ]ʷ  q = q
  walk-all R c ε       q = tt
  walk-all R c (w • u) (qw , qu) with (Aux.Theory.h ᵗ) c w | walk-all R c w qw
  ... | (w′ , c′) | iw with (Aux.Theory.h ᵗ) c′ u | walk-all R c′ u qu
  ...   | (u′ , c″) | iu = iw , iu

  edges-atoms : ∀ (R : Fin N → Set) → Small R → (u : Word Aux.Edge) →
    AllW (λ g → GenQ R (proj₂ g)) u → AllW (AtomQ R) ((plan N enough ʷ) u)
  edges-atoms R sm [ g ]ʷ  q         = plan-args N enough R sm g q
  edges-atoms R sm ε       q         = tt
  edges-atoms R sm (u • v) (qu , qv) = edges-atoms R sm u qu , edges-atoms R sm v qv

  to-args : ∀ {r} (ix : Vec (Fin N) r) (w : Word (Atom N)) → AllW (AtomQ (Q ix)) w → AllArgsIn (frameList ix) w
  to-args ix [ MM a b ]ʷ          q         = q
  to-args ix [ XX a b x y _ _ ]ʷ  q         = q
  to-args ix [ J a b x y _ _ _ ]ʷ q         = q
  to-args ix ε                    q         = tt
  to-args ix (u • v)              (qu , qv) = to-args ix u qu , to-args ix v qv

  -- Two edge words whose letters' indices lie in a frame, and which act
  -- alike, decode to equal circuits.
  in-frame : ∀ {r} (ix : Vec (Fin N) r) → r ≤ 8 → (u v : Word Aux.Edge) →
    AllW (λ g → GenQ (Q ix) (proj₂ g)) u → AllW (λ g → GenQ (Q ix) (proj₂ g)) v →
    TS.⟦ Aux.encode u ⟧ᵐ ≡ TS.⟦ Aux.encode v ⟧ᵐ → W ⊢ D u ≈ D v
  in-frame ix le u v qu qv eq =
    subst₂ (λ x y → W ⊢ x ≈ y) (sym (D-atoms u)) (sym (D-atoms v))
      (atoms-complete (proj₂ (mkFrame ix le)) ((plan N enough ʷ) u) ((plan N enough ʷ) v)
        (to-args ix ((plan N enough ʷ) u) (edges-atoms (Q ix) (small ix) u qu))
        (to-args ix ((plan N enough ʷ) v) (edges-atoms (Q ix) (small ix) v qv))
        (subst₂ (λ x y → interpret x ≡ interpret y) (D-atoms u) (D-atoms v)
          (action⇒matrix {u = τ (D u)} {v = τ (D v)} λ x →
            trans (D-act u x) (trans (same-action (Aux.encode u) (Aux.encode v) eq x) (sym (D-act v x))))))

------------------------------------------------------------------------
-- The relations

private
  -- The coset representatives use the indices 0 and 1.
  a-small : ∀ {R : Fin N → Set} → Small R → R (fromℕ< (NP.m^n>0 2 (₄₊ (k + (c + 0)))))
  a-small sm = sm _ (subst (_< 16) (sym (FP.toℕ-fromℕ< (NP.m^n>0 2 (₄₊ (k + (c + 0)))))) (s≤s z≤n))

  p₁ : 1 < N
  p₁ = NP.^-monoʳ-≤ 2 {1} {₄₊ (k + (c + 0))} (s≤s z≤n)

  b-small : ∀ {R : Fin N → Set} → Small R → R (fromℕ< p₁)
  b-small sm = sm _ (subst (_< 16) (sym (FP.toℕ-fromℕ< p₁)) (s≤s (s≤s z≤n)))

  rep-all : ∀ {R : Fin N → Set} → Small R → ∀ c′ → AllW (GenQ R) (Aux.rep c′)
  rep-all sm c00 = tt
  rep-all sm c10 = a-small sm
  rep-all sm c11 = a-small sm , b-small sm
  rep-all sm c01 = a-small sm , (a-small sm , b-small sm)

  inv-all : ∀ {R : Fin N → Set} → Small R → ∀ c′ → AllW (GenQ R) (TD._⁻¹ (Aux.rep c′))
  inv-all sm c00 = tt
  inv-all sm c10 = a-small sm
  inv-all sm c11 = a-small sm , b-small sm
  inv-all sm c01 = (a-small sm , b-small sm) , a-small sm

  e-all : ∀ {R : Fin N → Set} → Small R → ∀ g → GenQ R (proj₂ g) → AllW (GenQ R) (Aux.e g)
  e-all sm (c′ , y) gy = (rep-all sm c′ , gy) , inv-all sm (dyadic-step c′ y)

  -- The indices of a generator, padded to four.
  genIdx : T.Gen N → Vec (Fin N) 4
  genIdx (M-gen a)             = a ∷ a ∷ a ∷ a ∷ []
  genIdx (X-gen a b _)         = a ∷ b ∷ a ∷ a ∷ []
  genIdx (K-gen a b c d _ _ _) = a ∷ b ∷ c ∷ d ∷ []

  gen-in : ∀ (R : Fin N → Set) y → (∀ i → R (lookup (genIdx y) i)) → GenQ R y
  gen-in R (M-gen a)             q = q zero
  gen-in R (X-gen a b _)         q = q zero , q (suc zero)
  gen-in R (K-gen a b c d _ _ _) q = q zero , q (suc zero) , q (suc (suc zero)) , q (suc (suc (suc zero)))

-- Every relation of the auxiliary presentation, decoded, is derived.
decoded : ∀ {u v} → u Aux.=== v → W ⊢ D u ≈ D v
decoded (Aux.roundtrip g) =
  in-frame ix (s≤s (s≤s (s≤s (s≤s z≤n)))) [ g ]ʷ (Aux.decode c00 (Aux.e g)) qg
    (walk-all (Q ix) c00 (Aux.e g) (e-all (small ix) g qg))
    (Aux.soundness (PB.axiom (Aux.roundtrip g)))
  where
  ix = genIdx (proj₂ g)
  qg = gen-in (Q ix) (proj₂ g) (in-ix ix)
decoded (Aux.translated c′ {u} {v} ax) =
  in-frame ix NP.≤-refl (Aux.decode c′ u) (Aux.decode c′ v)
    (walk-all (Q ix) c′ u (proj₁ both)) (walk-all (Q ix) c′ v (proj₂ both))
    (Aux.soundness (PB.axiom (Aux.translated c′ ax)))
  where
  ix = AxIdx ax
  both = ax-in ax (Q ix) (in-ix ix)
