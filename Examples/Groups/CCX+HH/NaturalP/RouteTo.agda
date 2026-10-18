------------------------------------------------------------------------
-- Presentations of groups
--
-- Routing a frame into the window.
--
-- `To E F`: for two injective linear maps E, F from 𝔽₂ᵈ, the affine
-- word B = inv (route F) • route E sends E(s) to F(s) (`B-ok`) and is
-- linear (`B-lin`): route E carries E's images to unit vectors, and
-- the reverse of route F carries those to F's.  `greedy` extracts from
-- any list of vectors an independent list with the same span, and
-- `frame` puts that span into the window of 4 + k + c wires, the states
-- whose bottom k wires are 0: B sends the basis to unit vectors of the
-- top 4 + c wires (`win`, through `pad`).  So any frame list of at most
-- 4 + c vectors is moved into the window by one linear affine word
-- (`Framed`), and so is everything in its span (`into`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.RouteTo where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties using (≤-trans ; m≤n+m ; m≤n⇒m≤1+n)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup ; tabulate ; replicate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; _•_)
open import Notations using (₄₊)

import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; inv)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute
  using (A⟦_⟧ ; A-cong ; A-inv ; _⊕_ ; unit ; Lin ; Emb ; word-lin ; lin-ext ; lin-∘
        ; route ; route-zero ; route-ok)
open import Examples.Groups.CCX+HH.NaturalP.Span
  using (comb ; Indep ; InSpan ; span? ; indep-extend ; span-grow ; comb-zero ; comb-mix ; cmix)
open import Examples.Groups.CCX+HH.NaturalP.SpanEmb using (embL ; indep₀)
open import Examples.Groups.CCX+HH.NaturalP.Window
  using (low ; high ; join ; low-join ; high-join ; join-⊕ ; join-resp ; low-resp ; high-resp)

private
  variable
    n m d : ℕ

------------------------------------------------------------------------
-- One injective linear image onto another

module To {d m : ℕ} (le : d ≤ m) (E F : Emb d m) where

  B : Word (AGen m)
  B = inv (route le F) • route le E

  private
    inv-zero : (w : Word (AGen m)) → A⟦ w ⟧ zeros ≈s zeros → A⟦ inv w ⟧ zeros ≈s zeros
    inv-zero w z i = trans (A-cong (inv w) (λ j → sym (z j)) i) (A-inv w zeros i)

  B-zero : A⟦ B ⟧ zeros ≈s zeros
  B-zero i = trans (A-cong (inv (route le F)) (route-zero le E) i)
    (inv-zero (route le F) (route-zero le F) i)

  B-lin : Lin A⟦ B ⟧
  B-lin = word-lin B B-zero

  B-unit : ∀ i → A⟦ B ⟧ (Emb.f E (unit i)) ≈s Emb.f F (unit i)
  B-unit i x =
    trans (A-cong (inv (route le F)) (λ y → trans (route-ok le E i y) (sym (route-ok le F i y))) x)
      (A-inv (route le F) (Emb.f F (unit i)) x)

  B-ok : ∀ s → A⟦ B ⟧ (Emb.f E s) ≈s Emb.f F s
  B-ok = lin-ext (λ s → A⟦ B ⟧ (Emb.f E s)) (Emb.f F) (lin-∘ B-lin (Emb.lin E)) (Emb.lin F) B-unit

------------------------------------------------------------------------
-- Into the window

pad : d ≤ m → State d → State m
pad z≤n      s = zeros
pad (s≤s le) s = cons (s zero) (pad le (lower s))

private
  pad-add : (le : d ≤ m) (s t : State d) → pad le (s ⊕ t) ≈s pad le s ⊕ pad le t
  pad-add z≤n      s t i       = refl
  pad-add (s≤s le) s t zero    = refl
  pad-add (s≤s le) s t (suc i) = pad-add le (lower s) (lower t) i

  pad-resp : (le : d ≤ m) {s t : State d} → s ≈s t → pad le s ≈s pad le t
  pad-resp z≤n      e i       = refl
  pad-resp (s≤s le) e zero    = e zero
  pad-resp (s≤s le) e (suc i) = pad-resp le (λ j → e (suc j)) i

  pad-inj : (le : d ≤ m) (s : State d) → pad le s ≈s zeros → s ≈s zeros
  pad-inj (s≤s le) s z zero    = z zero
  pad-inj (s≤s le) s z (suc i) = pad-inj le (lower s) (λ j → z (suc j)) i

  high-zeros : ∀ k {c} → high {c} k zeros ≈s zeros
  high-zeros zero    i = refl
  high-zeros (suc k) i = high-zeros k i

-- 𝔽₂ᵈ onto the bottom of the block above k controls.
win : ∀ k {c} → d ≤ ₄₊ c → Emb d (₄₊ (k + c))
win k {c} le = record
  { f   = λ s → join k zeros (pad le s)
  ; lin = record
      { add  = λ s t i → trans (join-resp k (λ _ → refl) (pad-add le s t) i)
                           (join-⊕ k zeros zeros (pad le s) (pad le t) i)
      ; resp = λ e → join-resp k (λ _ → refl) (pad-resp le e) }
  ; inj = λ s z → pad-inj le s λ i →
      trans (sym (high-join k zeros (pad le s) i)) (trans (high-resp k z i) (high-zeros k i)) }

------------------------------------------------------------------------
-- A basis of the span of a list

record Basis {m} (xs : Vec (State n) m) : Set where
  constructor basis
  field
    dim   : ℕ
    ys    : Vec (State n) dim
    ind   : Indep ys
    le    : dim ≤ m
    spans : ∀ i → InSpan ys (lookup xs i)

private
  self-span : (x : State n) (ys : Vec (State n) d) → InSpan (x ∷ ys) x
  self-span {d = d} x ys = (true ∷ replicate d false) ,
    λ i → trans (cong (x i xor_) (comb-zero ys i)) (xor-identityʳ (x i))

greedy : (xs : Vec (State n) m) → Basis xs
greedy []       = basis 0 [] indep₀ z≤n (λ ())
greedy (x ∷ xs) = go (greedy xs)
  where
  step : (b : Basis xs) → Dec (InSpan (Basis.ys b) x) → Basis (x ∷ xs)
  step (basis d ys ind le sp) (yes s) = basis d ys ind (m≤n⇒m≤1+n le)
    λ { zero → s ; (suc i) → sp i }
  step (basis d ys ind le sp) (no o) = basis (suc d) (x ∷ ys) (indep-extend ind o) (s≤s le)
    λ { zero → self-span x ys ; (suc i) → span-grow (x ∷ []) (sp i) }
  go : Basis xs → Basis (x ∷ xs)
  go b = step b (span? (Basis.ys b) x)

-- What a list spans, a list spanning it spans.
span-trans : (ys : Vec (State n) d) (xs : Vec (State n) m) → (∀ i → InSpan ys (lookup xs i)) →
  ∀ {y} → InSpan xs y → InSpan ys y
span-trans ys xs sp (as , e) = cmix cs as , λ i → trans (sym (comb-mix ys xs cs ok as i)) (e i)
  where
  cs = tabulate (λ i → proj₁ (sp i))
  ok : ∀ i → comb ys (lookup cs i) ≈s lookup xs i
  ok i j = trans (cong (λ c → comb ys c j) (VecP.lookup∘tabulate (λ i → proj₁ (sp i)) i))
    (proj₂ (sp i) j)

------------------------------------------------------------------------
-- A frame moved into the window

record Framed (k c : ℕ) {m} (xs : Vec (State (₄₊ (k + c))) m) : Set where
  field
    B     : Word (AGen (₄₊ (k + c)))
    B-lin : Lin A⟦ B ⟧
    into  : ∀ {y} → InSpan xs y → low k (A⟦ B ⟧ y) ≈s zeros

frame : ∀ k c {m} (xs : Vec (State (₄₊ (k + c))) m) → m ≤ ₄₊ c → Framed k c xs
frame k c xs le = record { B = T.B ; B-lin = T.B-lin ; into = into }
  where
  bs = greedy xs
  open Basis bs using (ys ; ind ; spans)
  dle : Basis.dim bs ≤ ₄₊ c
  dle = ≤-trans (Basis.le bs) le
  up : ₄₊ c ≤ ₄₊ (k + c)
  up = s≤s (s≤s (s≤s (s≤s (m≤n+m c k))))
  E = embL ys ind
  module T = To (≤-trans dle up) E (win k dle)
  into : ∀ {y} → InSpan xs y → low k (A⟦ T.B ⟧ y) ≈s zeros
  into {y} sp i = trans (low-resp k (λ j → trans (A-cong T.B (λ z → sym (onE z)) j) (T.B-ok s j)) i)
    (low-join k zeros (pad dle s) i)
    where
    cy = span-trans ys xs spans sp
    s = lookup (proj₁ cy)
    onE : Emb.f E s ≈s y
    onE z = trans (cong (λ c → comb ys c z) (VecP.tabulate∘lookup (proj₁ cy))) (proj₂ cy z)
