------------------------------------------------------------------------
-- Presentations of groups
--
-- Each piece of a gate is a decoded auxiliary word.
--
-- A piece of a gate x (Merge.recover-win) is a window gate whose frame
-- is sixteen states listed in increasing order (GatePieces.emb).  The
-- Table 1 encoding of its circuit on four wires, moved along that
-- embedding, is a word with the same matrix (both act at the sixteen
-- states as the four-wire circuit: AtCalc, as in AtomDecoder), so it is
-- closed at the coset 00, and its auxiliary decoding `piece-word`
-- decodes to the piece: the letters lie in the piece's frame of five
-- states, so AtomWin's completeness in a common frame applies
-- (`piece-decoded`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_ ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Notations using (₄₊)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)
import Examples.Groups.CCX+HH.NaturalP.Schema as S

module Examples.Groups.CCX+HH.NaturalP.GateDecoded
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  (k c : ℕ) (big : 8 ≤ c)
  (complete-top : ∀ {u v : P.Circuit (₄₊ (c + 0))} → interpret u ≡ interpret v →
     (₄₊ (c + 0)) S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
  using (refl ; sym ; trans ; cong ; subst ; subst₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ ; wmap)

import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
open T using (M-gen ; X-gen ; K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as TS
open TS using (actVʷ ; same-action ; same-matrix)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι ; word ; gen)
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Semantics as Q
open import Examples.Groups.CCX+HH.Subgroup.Action using (c00)
open import Examples.Groups.CCX+HH.Subgroup.CircuitCharge using (image-closed)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics using (quantum ; encoding-action)
open import Examples.Groups.CCX+HH.GeneralN.ActionSemantics using (action⇒matrix)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (idx ; bits ; idx-cong ; idx-bits ; bits-idx)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.NaturalP.Schema using (Circuit ; Gen ; _⊢_≈_)
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (Λw)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; ⌈_⌉ ; inv)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute using (A⟦_⟧ ; A-cong ; A-inv)
open import Examples.Groups.CCX+HH.NaturalP.Span using (InSpan ; E4)
open import Examples.Groups.CCX+HH.NaturalP.SpanEmb using (span-++ʳ ; e4-span)
open import Examples.Groups.CCX+HH.NaturalP.RouteTo using (frame ; Framed ; module Framed)
open import Examples.Groups.CCX+HH.NaturalP.SmallIdx using (small-span)
open import Examples.Groups.CCX+HH.NaturalP.PlanArgs using (AllW ; GenQ ; Small)
open import Examples.Groups.CCX+HH.NaturalP.AtCalc
  using (AtI ; at→I ; atI-ext ; atI-cong ; atI-∘ ; ιW ; Λ-at ; at-word ; at-perm)
open import Examples.Groups.CCX+HH.NaturalP.Route4 using (stack-ιW)
open import Examples.Groups.CCX+HH.NaturalP.Transport using (placed)
open import Examples.Groups.CCX+HH.NaturalP.WinGate complete≤ using (A-inv′)
open import Examples.Groups.CCX+HH.NaturalP.Merge complete≤ using (gate′ ; trW)
open import Examples.Groups.CCX+HH.NaturalP.GatePieces complete≤ using (module Piece)
open import Examples.Groups.CCX+HH.NaturalP.AtomDecoder k c using (W ; N ; perm-aff)
open import Examples.Groups.CCX+HH.NaturalP.WinComplete complete≤ k c complete-top
  using (wg ; gates ; win-complete)
open import Examples.Groups.CCX+HH.NaturalP.AtomWin complete≤ k c complete-top
  using (Frame ; dws ; atoms-gates ; good-atoms)
open import Examples.Groups.CCX+HH.NaturalP.AtomCases k c using (atom)
open import Examples.Groups.CCX+HH.NaturalP.Decoded complete≤ k c big complete-top
  using (module Aux ; D ; D-act ; D-atoms ; enough ; walk-all ; edges-atoms ; to-args′)
open import Examples.Groups.CCX+HH.GeneralN.DecodingPlans using (plan)

module _ (x : Gen W) (s₁ : Vec Bool k) (s₂ : Vec Bool c) where

  open Piece k c x s₁ s₂ using (A′ ; F ; pts ; emb ; dirs ; frameP ; F-span)

  x₄ : Circuit 4
  x₄ = proj₁ (proj₂ (placed k c x))

  -- The piece's Table 1 word, and its auxiliary word.
  tword : Word (T.Gen N)
  tword = word emb (E.encode (τ x₄))

  piece-word : Word Aux.Edge
  piece-word = Aux.decode c00 tword

  private
    -- The piece acts at its sixteen states as its circuit.
    cond : ∀ y → ι (ιW k (c + 0)) (ι (ιW c 0) y) ≡ idx W (A⟦ A′ ⟧ (bits W (pts y)))
    cond y =
      trans (cong (λ z → ι (ιW k (c + 0)) (ι (ιW c 0) z)) (sym (idx-bits 4 y)))
      (trans (stack-ιW k c (bits 4 y))
        (idx-cong W (λ i → sym (trans (A-cong A′ (bits-idx W (F (bits 4 y))) i)
                                       (A-inv′ A′ _ i)))))

    piece-act : ∀ v → quantum (τ (gate′ k c A′ x₄)) v ≡ actVʷ tword v
    piece-act v = atI-ext conj tbl (λ u → refl) v
      where
      win = atI-∘ (at→I (Λ-at k (Λw c x₄))) (at→I (Λ-at c x₄))
      conj = at-perm (quantum (τ ⌈ A′ ⌉)) (quantum (τ ⌈ inv A′ ⌉)) A⟦ A′ ⟧ A⟦ inv A′ ⟧
        (perm-aff A′) (perm-aff (inv A′)) (A-inv A′) (A-cong (inv A′)) win pts cond
      tbl : AtI pts (quantum (τ x₄)) (actVʷ tword)
      tbl = atI-cong (at→I (at-word emb (E.encode (τ x₄)))) (λ u → encoding-action (τ x₄) u) (λ u → refl)

    closed : Aux.state c00 tword ≡ c00
    closed = trans (Aux.state-semantic c00 {u = tword} {v = E.encode (τ (gate′ k c A′ x₄))}
        (same-matrix tword (E.encode (τ (gate′ k c A′ x₄)))
          (λ u → trans (sym (piece-act u)) (sym (encoding-action (τ (gate′ k c A′ x₄)) u)))))
      (image-closed {n = k + (c + 0)} c00 (τ (gate′ k c A′ x₄)))

    word-act : ∀ v → quantum (τ (D piece-word)) v ≡ quantum (τ (gate′ k c A′ x₄)) v
    word-act v = trans (D-act piece-word v)
      (trans (same-action (Aux.encode piece-word) tword (Red.sound-act (Aux.decode-loop {tword} closed) TS.𝕀) v)
        (sym (piece-act v)))

    -- The frame.
    nine : 9 ≤ ₄₊ (c + 0)
    nine = s≤s (s≤s (s≤s (s≤s (NP.≤-trans (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
      (NP.≤-trans big (NP.≤-reflexive (sym (NP.+-identityʳ c))))))))
    -- Opaque: its basis search is never worth unfolding.
    opaque
      fr : Framed k (c + 0) frameP
      fr = frame k (c + 0) frameP nine
    FrameP : Frame (Framed.B fr) frameP
    FrameP = record { into = Framed.into fr ; e4-in = e4-span (F zeros ∷ dirs) }

    Qp : Fin N → Set
    Qp z = InSpan frameP (bits W z)

    smallP : Small Qp
    smallP z lt = span-++ʳ (F zeros ∷ dirs) (small-span (k + (c + 0)) z lt)

    pt-in : ∀ y → Qp (pts y)
    pt-in y = proj₁ (F-span (bits 4 y)) , λ i →
      trans (proj₂ (F-span (bits 4 y)) i) (sym (bits-idx W (F (bits 4 y)) i))

    letters-in : ∀ (w : Word (T.Gen 16)) → AllW (GenQ Qp) (word emb w)
    letters-in [ M-gen a ]ʷ             = pt-in a
    letters-in [ X-gen a b _ ]ʷ         = pt-in a , pt-in b
    letters-in [ K-gen a b c′ d _ _ _ ]ʷ = pt-in a , pt-in b , pt-in c′ , pt-in d
    letters-in ε                        = _
    letters-in (u • v)                  = letters-in u , letters-in v

  piece-decoded : W ⊢ gate′ k c A′ x₄ ≈ D piece-word
  piece-decoded =
    subst (λ z → W ⊢ gate′ k c A′ x₄ ≈ z)
      (trans (sym (atoms-gates ((plan N enough ʷ) piece-word))) (sym (D-atoms piece-word)))
      (win-complete (Framed.B fr) [ wg A′ x₄ ]ʷ (dws ((plan N enough ʷ) piece-word))
        (λ h → Framed.into fr (F-span h))
        (good-atoms FrameP ((plan N enough ʷ) piece-word)
          (to-args′ frameP ((plan N enough ʷ) piece-word)
            (edges-atoms Qp smallP piece-word (walk-all Qp c00 tword (letters-in (E.encode (τ x₄)))))))
        (subst (λ z → interpret (gate′ k c A′ x₄) ≡ interpret z)
          (trans (D-atoms piece-word) (atoms-gates ((plan N enough ʷ) piece-word)))
          (action⇒matrix {u = τ (gate′ k c A′ x₄)} {v = τ (D piece-word)} λ v → sym (word-act v))))
