------------------------------------------------------------------------
-- Presentations of groups
--
-- Known states, on which the letters of a route act as Step does.
--
-- Fix a numerator W and m local indices ι 0, …, ι (m - 1) ≤ p.  A
-- matrix N is known with local vector e when its column p is W with e
-- put at the local indices, at scale k, and N is the identity beyond p
-- (Known).  The word of the letter H i j is Hs (ι i) (ι j), which is
-- X H X on (ι j, ι i) when ι j < ι i; that of X i j is Xs (ι i) (ι j);
-- each acts on known states as Step does on e (known-step).
--
-- count-emb: when W is even away from the local indices, the odd
-- entries of the column are its odd local entries.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Embed {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.Product.Base using (∃ ; _,_)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Data.Unit.Base using (⊤)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-cong ; count-drop ; count-false)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; √2ᶻ ; oddᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (Beyond)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (upd₁ ; upd₂ ; upd₂-i ; upd₂-j ; upd₂-o ; module Emb)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (Hs ; HsT ; Xs ; XsT)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

------------------------------------------------------------------------
-- Counting odd entries of an embedding

count-emb : ∀ {m} (ι : Fin m → Fin n) (inj : ∀ {i j} → ι i ≡ ι j → i ≡ j) (e : Vec Z m) (V : Vec Z n) →
            (∀ x → oddᶻ (V ! x) ≡ false) → nodd (Emb.emb ι inj e V) ≡ noddV e
count-emb {zero} ι inj [] V ev =
  ≡.trans (count-cong (λ x → oddᶻ (Emb.emb ι inj [] V ! x)) (λ x → oddᶻ (V ! x))
                      (λ x → ≡.cong oddᶻ (Emb.emb-o ι inj [] V {x} (λ ()))))
          (count-false (λ x → oddᶻ (V ! x)) ev)
count-emb {suc m} ι inj (x₀ ∷ e) V ev = by (oddᶻ x₀) ≡.refl
  where
  ι′ : Fin m → Fin n
  ι′ = ι ∘ suc
  inj′ : ∀ {i j} → ι′ i ≡ ι′ j → i ≡ j
  inj′ eq = FinP.suc-injective (inj eq)
  a = ι zero
  U = Emb.emb ι′ inj′ e V
  out′ : ∀ i → ι′ i ≢ a
  out′ i eq with inj eq
  ... | ()
  Ua : U ! a ≡ V ! a
  Ua = Emb.emb-o ι′ inj′ e V out′
  -- The embedding is U with x₀ put at a.
  E≡ : ∀ y → y ≢ a → Emb.emb ι inj (x₀ ∷ e) V ! y ≡ U ! y
  E≡ y y≢a = at (Emb.where? ι inj y)
    where
    at : _ → Emb.emb ι inj (x₀ ∷ e) V ! y ≡ U ! y
    at (inj₁ (zero , eq)) = ⊥-elim (y≢a (≡.sym eq))
    at (inj₁ (suc i , ≡.refl)) = ≡.trans (Emb.emb-ι ι inj (x₀ ∷ e) V (suc i)) (≡.sym (Emb.emb-ι ι′ inj′ e V i))
    at (inj₂ out) = ≡.trans (Emb.emb-o ι inj (x₀ ∷ e) V out) (≡.sym (Emb.emb-o ι′ inj′ e V (out ∘ suc)))
  Ea : Emb.emb ι inj (x₀ ∷ e) V ! a ≡ x₀
  Ea = Emb.emb-ι ι inj (x₀ ∷ e) V zero
  P Q : Fin n → Bool
  P y = oddᶻ (Emb.emb ι inj (x₀ ∷ e) V ! y)
  Q y = oddᶻ (U ! y)
  agree : ∀ y → y ≢ a → P y ≡ Q y
  agree y y≢a = ≡.cong oddᶻ (E≡ y y≢a)
  rest : count Q ≡ noddV e
  rest = count-emb ι′ inj′ e V ev
  by : ∀ b → oddᶻ x₀ ≡ b → count P ≡ (if oddᶻ x₀ then 1 else 0) ℕ.+ noddV e
  by true o = ≡.trans (count-drop P Q a (≡.trans (≡.cong oddᶻ Ea) o) (≡.trans (≡.cong oddᶻ Ua) (ev a)) agree)
                      (≡.trans (≡.cong suc rest) (≡.cong (ℕ._+ noddV e) (≡.cong (λ b → if b then 1 else 0) (≡.sym o))))
  by false o = ≡.trans (count-cong P Q λ y → at y (y FinP.≟ a))
                       (≡.trans rest (≡.cong (ℕ._+ noddV e) (≡.cong (λ b → if b then 1 else 0) (≡.sym o))))
    where
    at : ∀ y → Dec (y ≡ a) → P y ≡ Q y
    at y (yes ≡.refl) = ≡.trans (≡.cong oddᶻ Ea) (≡.trans o (≡.sym (≡.trans (≡.cong oddᶻ Ua) (ev a))))
    at y (no y≢a) = agree y y≢a

------------------------------------------------------------------------
-- Known states

module Known-at (p : Fin n) (k : ℕ) {m : ℕ} (ι : Fin m → Fin n) (inj : ∀ {i j} → ι i ≡ ι j → i ≡ j)
                (ι≤p : ∀ i → ι i ≤ p) (W₀ : Vec Z n) where

  open Emb ι inj using (emb ; H-emb ; X-emb ; Z-emb)

  record Known (N : Matrix n n D) (e : Vec Z m) : Set where
    constructor known
    field
      colK : col N p ≡ scV k (emb e W₀)
      beK  : Beyond p N

  open Known public

  -- The words of the letters.
  open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Placed ι public using (wordL ; wordR)

  private
    ι≢ : ∀ {i j} → i ≢ j → ι i ≢ ι j
    ι≢ i≢j e = i≢j (inj e)

  -- Swapping the entries at j and i, then updating them, is updating them.
  swap-upd : ∀ (i j : Fin m) (α β : Z) (e : Vec Z m) → i ≢ j →
             upd₂ j i β α (upd₂ j i α β (upd₂ j i (e ! i) (e ! j) e)) ≡ upd₂ i j α β e
  swap-upd i j α β e i≢j = vec-ext λ l → at l (l FinP.≟ i) (l FinP.≟ j)
    where
    j≢i = sym≢ i≢j
    e₁ = upd₂ j i (e ! i) (e ! j) e
    e₂ = upd₂ j i α β e₁
    at : ∀ l → Dec (l ≡ i) → Dec (l ≡ j) → upd₂ j i β α e₂ ! l ≡ upd₂ i j α β e ! l
    at l (yes ≡.refl) _ = ≡.trans (upd₂-j j l β α e₂ j≢i) (≡.sym (upd₂-i l j α β e))
    at l (no l≢i) (yes ≡.refl) = ≡.trans (upd₂-i l i β α e₂) (≡.sym (upd₂-j i l α β e i≢j))
    at l (no l≢i) (no l≢j) =
      ≡.trans (upd₂-o j i β α e₂ l≢j l≢i)
        (≡.trans (upd₂-o j i α β e₁ l≢j l≢i)
          (≡.trans (upd₂-o j i (e ! i) (e ! j) e l≢j l≢i) (≡.sym (upd₂-o i j α β e l≢i l≢j))))

  swap-sym : ∀ (i j : Fin m) (e : Vec Z m) → i ≢ j → upd₂ j i (e ! i) (e ! j) e ≡ upd₂ i j (e ! j) (e ! i) e
  swap-sym i j e i≢j = vec-ext λ l → at l (l FinP.≟ i) (l FinP.≟ j)
    where
    at : ∀ l → Dec (l ≡ i) → Dec (l ≡ j) → upd₂ j i (e ! i) (e ! j) e ! l ≡ upd₂ i j (e ! j) (e ! i) e ! l
    at l (yes ≡.refl) _ = ≡.trans (upd₂-j j l (e ! l) (e ! j) e (sym≢ i≢j)) (≡.sym (upd₂-i l j (e ! j) (e ! l) e))
    at l (no l≢i) (yes ≡.refl) = ≡.trans (upd₂-i l i (e ! i) (e ! l) e) (≡.sym (upd₂-j i l (e ! l) (e ! i) e i≢j))
    at l (no l≢i) (no l≢j) = ≡.trans (upd₂-o j i _ _ e l≢j l≢i) (≡.sym (upd₂-o i j _ _ e l≢i l≢j))

  -- The intermediate states of H i j with ι j < ι i.
  module Rev {i j : Fin m} (gt : ι j < ι i) where
    X₁ = X-gen (ι j) (ι i) gt
    H₁ = H-gen (ι j) (ι i) gt

    swapK : ∀ {N e} → Known N e → Known (actM X₁ N) (upd₂ j i (e ! i) (e ! j) e)
    swapK {N} {e} (known cK bK) =
      known (≡.trans (col-actM X₁ N p) (≡.trans (≡.cong (actV X₁) cK) (X-emb j i gt k e W₀)))
            (Beyond-actM X₁ {p} {N} (ι≤p i) bK)

  -- Single generators on local indices a, b with ι a < ι b.
  known-Hgen : ∀ {N e} (a b : Fin m) (lt : ι a < ι b) (α β : Z) → e ! a ZR.+ e ! b ≡ √2ᶻ ZR.* α →
               e ! a ZR.- e ! b ≡ √2ᶻ ZR.* β → Known N e → Known (actM (H-gen (ι a) (ι b) lt) N) (upd₂ a b α β e)
  known-Hgen {N} {e} a b lt α β sum dif (known cK bK) =
    known (≡.trans (col-actM (H-gen (ι a) (ι b) lt) N p) (≡.trans (≡.cong (actV (H-gen (ι a) (ι b) lt)) cK) (H-emb a b lt k e W₀ α β sum dif)))
          (Beyond-actM (H-gen (ι a) (ι b) lt) {p} {N} (ι≤p b) bK)

  known-Xgen : ∀ {N e} (a b : Fin m) (lt : ι a < ι b) → Known N e →
               Known (actM (X-gen (ι a) (ι b) lt) N) (upd₂ a b (e ! b) (e ! a) e)
  known-Xgen {N} {e} a b lt (known cK bK) =
    known (≡.trans (col-actM (X-gen (ι a) (ι b) lt) N p) (≡.trans (≡.cong (actV (X-gen (ι a) (ι b) lt)) cK) (X-emb a b lt k e W₀)))
          (Beyond-actM (X-gen (ι a) (ι b) lt) {p} {N} (ι≤p b) bK)

  known-H : ∀ {N e} (i j : Fin m) → i ≢ j → (α β : Z) → e ! i ZR.+ e ! j ≡ √2ᶻ ZR.* α →
            e ! i ZR.- e ! j ≡ √2ᶻ ZR.* β → Known N e → Known (actMʷ (Hs (ι i) (ι j)) N) (upd₂ i j α β e)
  known-H {N} {e} i j i≢j α β sum dif K = at (FinP.<-cmp (ι i) (ι j)) K
    where
    at : (t : Tri (ι i < ι j) (ι i ≡ ι j) (ι j < ι i)) → Known N e → Known (actMʷ (HsT (ι i) (ι j) t) N) (upd₂ i j α β e)
    at (tri< lt _ _) (known cK bK) =
      known (≡.trans (col-actM (H-gen (ι i) (ι j) lt) N p) (≡.trans (≡.cong (actV (H-gen (ι i) (ι j) lt)) cK) (H-emb i j lt k e W₀ α β sum dif)))
            (Beyond-actM (H-gen (ι i) (ι j) lt) {p} {N} (ι≤p j) bK)
    at (tri≈ _ eq _) _ = ⊥-elim (ι≢ i≢j eq)
    at (tri> _ _ gt) K₀ = K₃
      where
      open Rev {i} {j} gt
      j≢i = sym≢ i≢j
      e₁ = upd₂ j i (e ! i) (e ! j) e
      K₁ = swapK K₀
      sum₁ : e₁ ! j ZR.+ e₁ ! i ≡ √2ᶻ ZR.* α
      sum₁ = ≡.trans (≡.cong₂ ZR._+_ (upd₂-i j i (e ! i) (e ! j) e) (upd₂-j j i (e ! i) (e ! j) e j≢i)) sum
      dif₁ : e₁ ! j ZR.- e₁ ! i ≡ √2ᶻ ZR.* β
      dif₁ = ≡.trans (≡.cong₂ ZR._-_ (upd₂-i j i (e ! i) (e ! j) e) (upd₂-j j i (e ! i) (e ! j) e j≢i)) dif
      e₂ = upd₂ j i α β e₁
      K₂ : Known (actM H₁ (actM X₁ N)) e₂
      K₂ = known (≡.trans (col-actM H₁ (actM X₁ N) p)
                   (≡.trans (≡.cong (actV H₁) (colK K₁)) (H-emb j i gt k e₁ W₀ α β sum₁ dif₁)))
                 (Beyond-actM H₁ {p} {actM X₁ N} (ι≤p i) (beK K₁))
      K₃′ : Known (actM X₁ (actM H₁ (actM X₁ N))) (upd₂ j i (e₂ ! i) (e₂ ! j) e₂)
      K₃′ = swapK K₂
      e₃≡ : upd₂ j i (e₂ ! i) (e₂ ! j) e₂ ≡ upd₂ i j α β e
      e₃≡ = ≡.trans (≡.cong₂ (λ s t → upd₂ j i s t e₂) (upd₂-j j i α β e₁ j≢i) (upd₂-i j i α β e₁))
                    (swap-upd i j α β e i≢j)
      K₃ = ≡.subst (Known (actM X₁ (actM H₁ (actM X₁ N)))) e₃≡ K₃′

  known-X : ∀ {N e} (i j : Fin m) → i ≢ j → Known N e → Known (actMʷ (Xs (ι i) (ι j)) N) (upd₂ i j (e ! j) (e ! i) e)
  known-X {N} {e} i j i≢j K = at (FinP.<-cmp (ι i) (ι j)) K
    where
    at : (t : Tri (ι i < ι j) (ι i ≡ ι j) (ι j < ι i)) → Known N e → Known (actMʷ (XsT (ι i) (ι j) t) N) (upd₂ i j (e ! j) (e ! i) e)
    at (tri< lt _ _) (known cK bK) =
      known (≡.trans (col-actM (X-gen (ι i) (ι j) lt) N p) (≡.trans (≡.cong (actV (X-gen (ι i) (ι j) lt)) cK) (X-emb i j lt k e W₀)))
            (Beyond-actM (X-gen (ι i) (ι j) lt) {p} {N} (ι≤p j) bK)
    at (tri≈ _ eq _) _ = ⊥-elim (ι≢ i≢j eq)
    at (tri> _ _ gt) K₀ = ≡.subst (Known (actM (X-gen (ι j) (ι i) gt) N)) (swap-sym i j e i≢j) (Rev.swapK {i} {j} gt K₀)

  known-Z : ∀ {N e} (i : Fin m) → Known N e → Known (actMʷ (Zʷ (ι i)) N) (upd₁ i (ZR.- (e ! i)) e)
  known-Z {N} {e} i (known cK bK) =
    known (≡.trans (col-actM (Z-gen (ι i)) N p) (≡.trans (≡.cong (actV (Z-gen (ι i))) cK) (Z-emb i k e W₀)))
          (Beyond-actM (Z-gen (ι i)) {p} {N} (ι≤p i) bK)

  -- A step on the local vector is a step on known states.
  known-step : ∀ {N e e′} (g : Let m) → Distinct g → Step g e e′ → Known N e → Known (actMʷ (wordL g) N) e′
  known-step (Hˡ i j) d (stepH α β sum dif) K = known-H i j d α β sum dif K
  known-step (Xˡ i j) d stepX K = known-X i j d K
  known-step (Zˡ i) d stepZ K = known-Z i K
