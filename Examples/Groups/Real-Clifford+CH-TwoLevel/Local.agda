------------------------------------------------------------------------
-- Presentations of groups
--
-- Columns that differ from a given numerator W only at four indices
-- ι 0 < ι 1 < ι 2 < ι 3: emb e W puts the local vector e ∈ ℤ[√2]⁴ at
-- those indices.  The generators on these indices act on e, so the
-- column computations of the four-entry diamond are computations on
-- literal 4-vectors, which evaluate.
--
-- * actV-H-same: H_[a,b] at the same scale, when √2 divides the sum
--   and the difference of the two entries;
-- * H-emb, X-emb, Z-emb: the generators on an embedded vector;
-- * nodd-emb: an even local entry where W is odd lowers the number of
--   odd entries.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing ; maybe′)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true ; dec-false)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; √2ᶻ ; oddᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; Odd ; Even)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Zᶻ ; Xᶻ ; Hᶻ ; actV-H ; actV-X ; actV-Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (scV-δmap)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (first ; first-just ; first-none ; first-char ; count-lt)

------------------------------------------------------------------------
-- H at the same scale

actV-H-same : (a b : Fin n) .(ab : a < b) (k : ℕ) (w : Vec Z n) (α β : Z) →
              w ! a ZR.+ w ! b ≡ √2ᶻ ZR.* α → w ! a ZR.- w ! b ≡ √2ᶻ ZR.* β →
              actV (H-gen a b ab) (scV k w) ≡ scV k (set₂ a b α β w)
actV-H-same a b ab k w α β sum dif =
  ≡.trans (actV-H a b ab k w) (≡.trans (≡.cong (scV (suc k)) H≡) (scV-δmap k (set₂ a b α β w)))
  where
  a≢b : a ≢ b
  a≢b = <⇒≢ ab
  δm : Vec Z n → Vec Z n
  δm = Vec.map (√2ᶻ ZR.*_)
  w′ = set₂ a b α β w
  at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Hᶻ a b w ! x ≡ δm w′ ! x
  at x (yes ≡.refl) _ =
    ≡.trans (set₂-a x b _ _ _) (≡.trans sum (≡.trans (≡.cong (√2ᶻ ZR.*_) (≡.sym (set₂-a x b α β w)))
                                                   (≡.sym (VecP.lookup-map x (√2ᶻ ZR.*_) w′))))
  at x (no x≢a) (yes ≡.refl) =
    ≡.trans (set₂-b a x _ _ _ a≢b) (≡.trans dif (≡.trans (≡.cong (√2ᶻ ZR.*_) (≡.sym (set₂-b a x α β w a≢b)))
                                                       (≡.sym (VecP.lookup-map x (√2ᶻ ZR.*_) w′))))
  at x (no x≢a) (no x≢b) =
    ≡.trans (set₂-≢ a b _ _ _ x≢a x≢b)
      (≡.trans (VecP.lookup-map x (√2ᶻ ZR.*_) w)
        (≡.trans (≡.cong (√2ᶻ ZR.*_) (≡.sym (set₂-≢ a b α β w x≢a x≢b))) (≡.sym (VecP.lookup-map x (√2ᶻ ZR.*_) w′))))
  H≡ : Hᶻ a b w ≡ δm w′
  H≡ = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b)

------------------------------------------------------------------------
-- Local vectors, and their updates (transparent: they evaluate on
-- literal vectors and indices)

upd₁ : Fin 4 → Z → Vec Z 4 → Vec Z 4
upd₁ i α e = tabulate (λ m → if does (m FinP.≟ i) then α else e ! m)

upd₂ : Fin 4 → Fin 4 → Z → Z → Vec Z 4 → Vec Z 4
upd₂ i j α β e = tabulate (λ m → if does (m FinP.≟ i) then α else if does (m FinP.≟ j) then β else e ! m)

private
  if-true : ∀ {A : Set} {d : Bool} (x y : A) → d ≡ true → (if d then x else y) ≡ x
  if-true x y ≡.refl = ≡.refl

  if-false : ∀ {A : Set} {d : Bool} (x y : A) → d ≡ false → (if d then x else y) ≡ y
  if-false x y ≡.refl = ≡.refl

upd₁-i : ∀ i α e → upd₁ i α e ! i ≡ α
upd₁-i i α e = ≡.trans (VecP.lookup∘tabulate (λ m → if does (m FinP.≟ i) then α else e ! m) i) (if-true α (e ! i) (dec-true (i FinP.≟ i) ≡.refl))

upd₁-o : ∀ i α e {m} → m ≢ i → upd₁ i α e ! m ≡ e ! m
upd₁-o i α e {m} m≢i = ≡.trans (VecP.lookup∘tabulate (λ m → if does (m FinP.≟ i) then α else e ! m) m) (if-false α (e ! m) (dec-false (m FinP.≟ i) m≢i))

upd₂-i : ∀ i j α β e → upd₂ i j α β e ! i ≡ α
upd₂-i i j α β e = ≡.trans (VecP.lookup∘tabulate (λ m → if does (m FinP.≟ i) then α else if does (m FinP.≟ j) then β else e ! m) i) (if-true α _ (dec-true (i FinP.≟ i) ≡.refl))

upd₂-j : ∀ i j α β e → i ≢ j → upd₂ i j α β e ! j ≡ β
upd₂-j i j α β e i≢j =
  ≡.trans (VecP.lookup∘tabulate (λ m → if does (m FinP.≟ i) then α else if does (m FinP.≟ j) then β else e ! m) j)
    (≡.trans (if-false α _ (dec-false (j FinP.≟ i) (λ e → i≢j (≡.sym e))))
             (if-true β (e ! j) (dec-true (j FinP.≟ j) ≡.refl)))

upd₂-o : ∀ i j α β e {m} → m ≢ i → m ≢ j → upd₂ i j α β e ! m ≡ e ! m
upd₂-o i j α β e {m} m≢i m≢j =
  ≡.trans (VecP.lookup∘tabulate (λ m → if does (m FinP.≟ i) then α else if does (m FinP.≟ j) then β else e ! m) m)
    (≡.trans (if-false α _ (dec-false (m FinP.≟ i) m≢i)) (if-false β (e ! m) (dec-false (m FinP.≟ j) m≢j)))

------------------------------------------------------------------------
-- Embedding a local vector at four indices

module Emb (ι : Fin 4 → Fin n) (inj : ∀ {i j} → ι i ≡ ι j → i ≡ j) where

  pre : Fin n → Maybe (Fin 4)
  pre x = first (λ m → does (ι m FinP.≟ x))

  emb : Vec Z 4 → Vec Z n → Vec Z n
  emb e W = tabulate (λ x → maybe′ (e !_) (W ! x) (pre x))

  private
    ι≢ : ∀ {i j} → i ≢ j → ι i ≢ ι j
    ι≢ i≢j e = i≢j (inj e)

  pre-ι : ∀ i → pre (ι i) ≡ just i
  pre-ι i = first-char (λ m → does (ι m FinP.≟ ι i)) (dec-true (ι i FinP.≟ ι i) ≡.refl)
              (λ m m<i → dec-false (ι m FinP.≟ ι i) (ι≢ (λ e → FinP.<-irrefl e m<i)))

  pre-just : ∀ {x m} → pre x ≡ just m → ι m ≡ x
  pre-just {x} {m} eq = from (ι m FinP.≟ x) (proj₁ (first-just (λ m → does (ι m FinP.≟ x)) eq))
    where
    from : (d : Dec (ι m ≡ x)) → does d ≡ true → ι m ≡ x
    from (yes e) _ = e
    from (no _) ()

  pre-o : ∀ {x} → (∀ m → ι m ≢ x) → pre x ≡ nothing
  pre-o {x} out = first-none (λ m → does (ι m FinP.≟ x)) (λ m → dec-false (ι m FinP.≟ x) (out m))

  emb-ι : ∀ e W i → emb e W ! ι i ≡ e ! i
  emb-ι e W i = ≡.trans (VecP.lookup∘tabulate (λ x → maybe′ (e !_) (W ! x) (pre x)) (ι i)) (≡.cong (maybe′ (e !_) (W ! ι i)) (pre-ι i))

  emb-o : ∀ e W {x} → (∀ m → ι m ≢ x) → emb e W ! x ≡ W ! x
  emb-o e W {x} out = ≡.trans (VecP.lookup∘tabulate (λ x → maybe′ (e !_) (W ! x) (pre x)) x) (≡.cong (maybe′ (e !_) (W ! x)) (pre-o out))

  -- Every index is in the image or out of it.
  where? : ∀ x → (∃ λ m → ι m ≡ x) ⊎ (∀ m → ι m ≢ x)
  where? x = at (pre x) ≡.refl
    where
    at : (r : Maybe (Fin 4)) → pre x ≡ r → (∃ λ m → ι m ≡ x) ⊎ (∀ m → ι m ≢ x)
    at (just m) e = inj₁ (m , pre-just e)
    at nothing e = inj₂ λ m eq → nothing≢just (≡.trans (≡.sym e) (≡.trans (≡.cong pre (≡.sym eq)) (pre-ι m)))
      where
      nothing≢just : ∀ {j : Fin 4} → nothing ≢ just j
      nothing≢just ()

  -- Pointwise equality of embeddings.
  emb-ext : ∀ {e e′ W W′} → (∀ m → e ! m ≡ e′ ! m) → (∀ x → (∀ m → ι m ≢ x) → W ! x ≡ W′ ! x) →
            emb e W ≡ emb e′ W′
  emb-ext {e} {e′} {W} {W′} loc out = vec-ext λ x → at x (where? x)
    where
    at : ∀ x → (∃ λ m → ι m ≡ x) ⊎ (∀ m → ι m ≢ x) → emb e W ! x ≡ emb e′ W′ ! x
    at x (inj₁ (m , ≡.refl)) = ≡.trans (emb-ι e W m) (≡.trans (loc m) (≡.sym (emb-ι e′ W′ m)))
    at x (inj₂ o) = ≡.trans (emb-o e W o) (≡.trans (out x o) (≡.sym (emb-o e′ W′ o)))

  -- W is the embedding of its own entries.
  loc : Vec Z n → Vec Z 4
  loc W = tabulate (λ m → W ! ι m)

  emb-self : ∀ W → emb (loc W) W ≡ W
  emb-self W = vec-ext λ x → at x (where? x)
    where
    at : ∀ x → (∃ λ m → ι m ≡ x) ⊎ (∀ m → ι m ≢ x) → emb (loc W) W ! x ≡ W ! x
    at x (inj₁ (m , ≡.refl)) = ≡.trans (emb-ι (loc W) W m) (VecP.lookup∘tabulate (λ m → W ! ι m) m)
    at x (inj₂ o) = emb-o (loc W) W o

  -- Updating two embedded entries.
  set₂-emb : ∀ i j α β e W → i ≢ j → set₂ (ι i) (ι j) α β (emb e W) ≡ emb (upd₂ i j α β e) W
  set₂-emb i j α β e W i≢j = vec-ext λ x → at x (where? x)
    where
    e′ = upd₂ i j α β e
    at : ∀ x → (∃ λ m → ι m ≡ x) ⊎ (∀ m → ι m ≢ x) → set₂ (ι i) (ι j) α β (emb e W) ! x ≡ emb e′ W ! x
    at x (inj₁ (m , ≡.refl)) = by (m FinP.≟ i) (m FinP.≟ j)
      where
      by : Dec (m ≡ i) → Dec (m ≡ j) → set₂ (ι i) (ι j) α β (emb e W) ! ι m ≡ emb e′ W ! ι m
      by (yes ≡.refl) _ = ≡.trans (set₂-a (ι m) (ι j) α β _) (≡.trans (≡.sym (upd₂-i m j α β e)) (≡.sym (emb-ι e′ W m)))
      by (no m≢i) (yes ≡.refl) =
        ≡.trans (set₂-b (ι i) (ι m) α β _ (ι≢ i≢j)) (≡.trans (≡.sym (upd₂-j i m α β e i≢j)) (≡.sym (emb-ι e′ W m)))
      by (no m≢i) (no m≢j) =
        ≡.trans (set₂-≢ (ι i) (ι j) α β _ (ι≢ m≢i) (ι≢ m≢j))
          (≡.trans (emb-ι e W m) (≡.trans (≡.sym (upd₂-o i j α β e m≢i m≢j)) (≡.sym (emb-ι e′ W m))))
    at x (inj₂ o) =
      ≡.trans (set₂-≢ (ι i) (ι j) α β _ (λ e → o i (≡.sym e)) (λ e → o j (≡.sym e)))
        (≡.trans (emb-o e W o) (≡.sym (emb-o e′ W o)))

  set₁-emb : ∀ i α e W → set₁ (ι i) α (emb e W) ≡ emb (upd₁ i α e) W
  set₁-emb i α e W = vec-ext λ x → at x (where? x)
    where
    e′ = upd₁ i α e
    at : ∀ x → (∃ λ m → ι m ≡ x) ⊎ (∀ m → ι m ≢ x) → set₁ (ι i) α (emb e W) ! x ≡ emb e′ W ! x
    at x (inj₁ (m , ≡.refl)) = by (m FinP.≟ i)
      where
      by : Dec (m ≡ i) → set₁ (ι i) α (emb e W) ! ι m ≡ emb e′ W ! ι m
      by (yes ≡.refl) = ≡.trans (set₁-a (ι m) α _) (≡.trans (≡.sym (upd₁-i m α e)) (≡.sym (emb-ι e′ W m)))
      by (no m≢i) =
        ≡.trans (set₁-≢ (ι i) α _ (ι≢ m≢i)) (≡.trans (emb-ι e W m) (≡.trans (≡.sym (upd₁-o i α e m≢i)) (≡.sym (emb-ι e′ W m))))
    at x (inj₂ o) =
      ≡.trans (set₁-≢ (ι i) α _ (λ e → o i (≡.sym e))) (≡.trans (emb-o e W o) (≡.sym (emb-o e′ W o)))

  ----------------------------------------------------------------------
  -- The generators on embedded vectors

  H-emb : ∀ (i j : Fin 4) .(ij : ι i < ι j) k e W (α β : Z) →
          e ! i ZR.+ e ! j ≡ √2ᶻ ZR.* α → e ! i ZR.- e ! j ≡ √2ᶻ ZR.* β →
          actV (H-gen (ι i) (ι j) ij) (scV k (emb e W)) ≡ scV k (emb (upd₂ i j α β e) W)
  H-emb i j ij k e W α β sum dif =
    ≡.trans (actV-H-same (ι i) (ι j) ij k (emb e W) α β
               (≡.trans (≡.cong₂ ZR._+_ (emb-ι e W i) (emb-ι e W j)) sum)
               (≡.trans (≡.cong₂ ZR._-_ (emb-ι e W i) (emb-ι e W j)) dif))
            (≡.cong (scV k) (set₂-emb i j α β e W i≢j))
    where
    i≢j : i ≢ j
    i≢j e = <⇒≢ ij (≡.cong ι e)

  X-emb : ∀ (i j : Fin 4) .(ij : ι i < ι j) k e W →
          actV (X-gen (ι i) (ι j) ij) (scV k (emb e W)) ≡ scV k (emb (upd₂ i j (e ! j) (e ! i) e) W)
  X-emb i j ij k e W =
    ≡.trans (actV-X (ι i) (ι j) ij k (emb e W))
      (≡.cong (scV k) (≡.trans (≡.cong₂ (λ s t → set₂ (ι i) (ι j) s t (emb e W)) (emb-ι e W j) (emb-ι e W i))
                                (set₂-emb i j (e ! j) (e ! i) e W i≢j)))
    where
    i≢j : i ≢ j
    i≢j e = <⇒≢ ij (≡.cong ι e)

  Z-emb : ∀ (i : Fin 4) k e W → actV (Z-gen (ι i)) (scV k (emb e W)) ≡ scV k (emb (upd₁ i (ZR.- (e ! i)) e) W)
  Z-emb i k e W =
    ≡.trans (actV-Z (ι i) k (emb e W))
      (≡.cong (scV k) (≡.trans (≡.cong (λ s → set₁ (ι i) (ZR.- s) (emb e W)) (emb-ι e W i)) (set₁-emb i _ e W)))

  ----------------------------------------------------------------------
  -- Fewer odd entries

  nodd-emb : ∀ e W → (∀ m → Odd (W ! ι m)) → (m : Fin 4) → Even (e ! m) → nodd (emb e W) ℕ.< nodd W
  nodd-emb e W odd m ev =
    count-lt (λ x → oddᶻ (W ! x)) (λ x → oddᶻ (emb e W ! x)) (ι m) imp (odd m) (≡.trans (≡.cong oddᶻ (emb-ι e W m)) ev)
    where
    imp : ∀ x → oddᶻ (emb e W ! x) ≡ true → oddᶻ (W ! x) ≡ true
    imp x ox = at (where? x)
      where
      at : (∃ λ m → ι m ≡ x) ⊎ (∀ m → ι m ≢ x) → oddᶻ (W ! x) ≡ true
      at (inj₁ (m′ , ≡.refl)) = odd m′
      at (inj₂ o) = ≡.trans (≡.cong oddᶻ (≡.sym (emb-o e W o))) ox
