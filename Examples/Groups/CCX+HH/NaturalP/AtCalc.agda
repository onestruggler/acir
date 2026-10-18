------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators that act on the coordinates of an embedding.
--
-- `At e G F`: on the coordinates that the increasing embedding e picks
-- out, F acts as G, and every other coordinate F leaves alone.  Two such
-- operators with the same G are equal (`at-ext`); a Table 1 word moved
-- along e is one (`at-word`, from CCX+HH-TwoLevel/EmbedAction); they
-- compose along composed embeddings (`at-∘`) and are conjugated by
-- permutations of the coordinates (`at-perm`).  A circuit under k white
-- controls acts at the window embedding `ιW k c` (`Λ-at`), and an affine
-- word permutes the coordinates as its classical action permutes the
-- basis states (`perm-!`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.AtCalc where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (any? ; _≟_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _^_)
open import Data.Product.Base using (∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Word.Base using (Word ; wmap)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring hiding (ι)
open import Instances using (_*_ ; 0# ; 1#)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι ; mono ; word)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
  using (_!_ ; vec-ext ; restrict ; restrict-! ; actVʷ ; emb-actVʷ-restrict ; emb-actVʷ-out
        ; actVʷ≡ ; colmat ; ent ; ent-·*· ; sum-single ; δ ; δ-refl ; δ-≢ ; ⟦_⟧ᵐ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (Partition ; left ; right ; locate ; cover ; parallel ; parallel-left ; parallel-right)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
  using (quantum ; encoding-action ; physical-column ; ket)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis
  using (idx ; bits ; bits-idx ; idx-bits ; idx-cong ; idx-injective)
open import Examples.Groups.CCX+HH.GeneralN.BasisVectors using (basis-!)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (act-injective)
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (whites ; Λw)
open import Examples.Groups.CCX+HH.NaturalP.LambdaSem using (opΛ ; Λ-sem)

open IsCommutativeRing isCommutativeRing-D using (zeroˡ ; *-identityˡ)

private
  variable
    m n p c : ℕ

------------------------------------------------------------------------
-- Operators at an embedding

Op : ℕ → Set
Op n = Vec D n → Vec D n

record At (e : Emb m n) (G : Op m) (F : Op n) : Set where
  field
    on  : ∀ v → restrict e (F v) ≡ G (restrict e v)
    off : ∀ v x → (∀ y → x ≢ ι e y) → F v ! x ≡ v ! x
open At public

image? : (e : Emb m n) (x : Fin n) → Dec (∃ λ y → ι e y ≡ x)
image? e x = any? (λ y → ι e y ≟ x)

at-ext : {e : Emb m n} {G G′ : Op m} {F F′ : Op n} → At e G F → At e G′ F′ →
  (∀ u → G u ≡ G′ u) → ∀ v → F v ≡ F′ v
at-ext {e = e} {G} {G′} {F} {F′} a a′ gg v = vec-ext λ x → by x (image? e x)
  where
  by : ∀ x → Dec (∃ λ y → ι e y ≡ x) → F v ! x ≡ F′ v ! x
  by x (yes (y , refl)) =
    trans (sym (restrict-! e (F v) y))
    (trans (cong (_! y) (on a v))
    (trans (cong (_! y) (gg (restrict e v)))
    (trans (cong (_! y) (sym (on a′ v))) (restrict-! e (F′ v) y))))
  by x (no ¬i) =
    trans (off a v x (λ y eq → ¬i (y , sym eq)))
      (sym (off a′ v x (λ y eq → ¬i (y , sym eq))))

at-cong : {e : Emb m n} {G : Op m} {F F′ : Op n} → At e G F → (∀ v → F v ≡ F′ v) → At e G F′
at-cong {e = e} a eq = record
  { on  = λ v → trans (cong (restrict e) (sym (eq v))) (on a v)
  ; off = λ v x h → trans (sym (cong (_! x) (eq v))) (off a v x h) }

at-congG : {e : Emb m n} {G G′ : Op m} {F : Op n} → At e G F → (∀ u → G u ≡ G′ u) → At e G′ F
at-congG {e = e} a eq = record
  { on  = λ v → trans (on a v) (eq (restrict e v))
  ; off = off a }

-- A Table 1 word moved along an increasing embedding.
at-word : (e : Emb m n) (w : Word (Gen m)) → At e (actVʷ w) (actVʷ (word e w))
at-word e w = record { on = emb-actVʷ-restrict e w ; off = emb-actVʷ-out e w }

------------------------------------------------------------------------
-- Composition

idₑ : Emb n n
idₑ = record { ι = λ y → y ; mono = λ lt → lt }

infixr 9 _∘ₑ_
_∘ₑ_ : Emb n p → Emb m n → Emb m p
e₁ ∘ₑ e₂ = record { ι = λ y → ι e₁ (ι e₂ y) ; mono = λ lt → mono e₁ (mono e₂ lt) }

private
  restrict-id : (v : Vec D n) → restrict idₑ v ≡ v
  restrict-id v = vec-ext (restrict-! idₑ v)

  restrict-∘ : (e₁ : Emb n p) (e₂ : Emb m n) (v : Vec D p) →
    restrict (e₁ ∘ₑ e₂) v ≡ restrict e₂ (restrict e₁ v)
  restrict-∘ e₁ e₂ v = vec-ext λ y →
    trans (restrict-! (e₁ ∘ₑ e₂) v y)
      (trans (sym (restrict-! e₁ v (ι e₂ y))) (sym (restrict-! e₂ (restrict e₁ v) y)))

at-id : {G : Op n} → At idₑ G G
at-id {G = G} = record
  { on  = λ v → trans (restrict-id (G v)) (cong G (sym (restrict-id v)))
  ; off = λ v x h → ⊥-elim (h x refl) }

at-∘ : {e₁ : Emb n p} {e₂ : Emb m n} {H : Op m} {G : Op n} {F : Op p} →
  At e₁ G F → At e₂ H G → At (e₁ ∘ₑ e₂) H F
at-∘ {e₁ = e₁} {e₂} {H} {G} {F} a b = record
  { on  = λ v →
      trans (restrict-∘ e₁ e₂ (F v))
      (trans (cong (restrict e₂) (on a v))
      (trans (on b (restrict e₁ v)) (cong H (sym (restrict-∘ e₁ e₂ v)))))
  ; off = λ v x h → by v x h (image? e₁ x) }
  where
  by : ∀ v x → (∀ y → x ≢ ι e₁ (ι e₂ y)) → Dec (∃ λ y → ι e₁ y ≡ x) → F v ! x ≡ v ! x
  by v x h (yes (y , refl)) =
    trans (sym (restrict-! e₁ (F v) y))
    (trans (cong (_! y) (on a v))
    (trans (off b (restrict e₁ v) y (λ z eq → h z (cong (ι e₁) eq)))
      (restrict-! e₁ v y)))
  by v x h (no ¬i) = off a v x (λ y eq → ¬i (y , sym eq))

------------------------------------------------------------------------
-- The window

private
  off-left : (P : Partition m n) (G : Op m) (v : Vec D n) (x : Fin n) →
    (∀ y → x ≢ ι (left P) y) → parallel P G (λ x → x) v ! x ≡ v ! x
  off-left P G v x h with locate P x | cover P x
  ... | inj₁ y | eq   = ⊥-elim (h y (sym eq))
  ... | inj₂ y | refl =
    trans (sym (restrict-! (right P) (parallel P G (λ x → x) v) y))
      (trans (cong (_! y) (parallel-right P G (λ x → x) v)) (restrict-! (right P) v y))

-- A direct sum with the identity on the second half acts at the first.
at-left : (P : Partition m n) {G : Op m} → At (left P) G (parallel P G (λ x → x))
at-left P {G} = record { on = parallel-left P G (λ x → x) ; off = off-left P G }

-- The states whose bottom k wires are 0.
ιW : ∀ k c → Emb (2 ^ ₄₊ c) (2 ^ ₄₊ (k + c))
ιW zero    c = idₑ
ιW (suc k) c = left (alternating (2 ^ ₄₊ (k + c))) ∘ₑ ιW k c

opΛ-at : ∀ k c (G : Op (2 ^ ₄₊ c)) → At (ιW k c) G (opΛ (whites k) c G)
opΛ-at zero    c G = at-id
opΛ-at (suc k) c G = at-∘ (at-left (alternating (2 ^ ₄₊ (k + c)))) (opΛ-at k c G)

-- A circuit under k white controls.
Λ-at : ∀ k (X : P.Circuit (₄₊ c)) → At (ιW k c) (quantum (τ X)) (quantum (τ (Λw k X)))
Λ-at {c} k X = at-cong (opΛ-at k c (quantum (τ X))) (λ v → sym (Λ-sem (whites k) X v))

------------------------------------------------------------------------
-- Permutations of the coordinates

-- A classical circuit permutes the coordinates as it permutes the basis.
perm-! : (w : C.Circuit n) (v : Vec D (2 ^ n)) (s : C.State n) →
  quantum (C.physical w) v ! idx n (C.act w s) ≡ v ! idx n s
perm-! {n} w v s =
  trans (cong (_! r) (sym (encoding-action (C.physical w) v)))
  (trans (cong (_! r) (actVʷ≡ (E.encode (C.physical w)) v))
  (trans (ent-·*· M (colmat v) r zero)
  (trans (sum-single _ (idx n s) zero-off)
  (trans (cong (_* (v ! idx n s))
            (trans (entry (idx n s)) (trans (cong (δ r) π-s) (δ-refl r))))
    (*-identityˡ (v ! idx n s))))))
  where
  r = idx n (C.act w s)
  M = ⟦ E.encode (C.physical w) ⟧ᵐ
  π : Fin (2 ^ n) → Fin (2 ^ n)
  π x = idx n (C.act w (bits n x))
  entry : ∀ x → ent M r x ≡ δ r (π x)
  entry x =
    trans (cong (λ N → ent N r x) (Q.encoding-correct (C.physical w)))
    (trans (cong (_! r) (physical-column w x)) (basis-! (π x) r))
  π-s : π (idx n s) ≡ r
  π-s = idx-cong n (C.act-cong w (bits-idx n s))
  zero-off : ∀ x → x ≢ idx n s → ent M r x * ent (colmat v) x zero ≡ _
  zero-off x x≢ = trans (cong (_* ent (colmat v) x zero) (trans (entry x) (δ-≢ ne))) (zeroˡ _)
    where
    ne : r ≢ π x
    ne eq = x≢ (sym (trans (idx-cong n (act-injective w (idx-injective n eq))) (idx-bits n x)))

-- Conjugating an operator at e by a permutation of the coordinates.
at-perm : (Q Q⁻ : Op (2 ^ n)) (f f⁻ : C.State n → C.State n) →
  (∀ v s → Q v ! idx n (f s) ≡ v ! idx n s) →
  (∀ v s → Q⁻ v ! idx n (f⁻ s) ≡ v ! idx n s) →
  (∀ s → f⁻ (f s) C.≈s s) → (∀ {s t} → s C.≈s t → f⁻ s C.≈s f⁻ t) →
  {e : Emb m (2 ^ n)} {G : Op m} {F : Op (2 ^ n)} → At e G F →
  (e′ : Emb m (2 ^ n)) → (∀ y → ι e y ≡ idx n (f (bits n (ι e′ y)))) →
  At e′ G (λ v → Q⁻ (F (Q v)))
at-perm {n} Q Q⁻ f f⁻ Qf Q⁻f f⁻f f⁻-cong {e} {G} {F} a e′ ee′ = record
  { on  = λ v → vec-ext λ y →
      trans (restrict-! e′ (Q⁻ (F (Q v))) y)
      (trans (back (F (Q v)) (ι e′ y))
      (trans (cong (F (Q v) !_) (sym (ee′ y)))
      (trans (sym (restrict-! e (F (Q v)) y))
      (cong (_! y) (trans (on a (Q v)) (cong G (restrict-Q v)))))))
  ; off = λ v x h →
      trans (back (F (Q v)) x)
      (trans (off a (Q v) (idx n (f (bits n x))) (not-image x h))
      (trans (Qf v (bits n x)) (cong (v !_) (idx-bits n x))))
  }
  where
  -- Q⁻ read at any coordinate.
  back : ∀ u x → Q⁻ u ! x ≡ u ! idx n (f (bits n x))
  back u x =
    trans (cong (Q⁻ u !_) (sym (trans (idx-cong n (f⁻f (bits n x))) (idx-bits n x))))
      (Q⁻f u (f (bits n x)))
  restrict-Q : ∀ v → restrict e (Q v) ≡ restrict e′ v
  restrict-Q v = vec-ext λ y →
    trans (restrict-! e (Q v) y)
    (trans (cong (Q v !_) (ee′ y))
    (trans (Qf v (bits n (ι e′ y)))
    (trans (cong (v !_) (idx-bits n (ι e′ y))) (sym (restrict-! e′ v y)))))
  not-image : ∀ x → (∀ y → x ≢ ι e′ y) → ∀ y → idx n (f (bits n x)) ≢ ι e y
  not-image x h y eq = h y
    (trans (sym (idx-bits n x))
      (trans (idx-cong n (λ j → trans (sym (f⁻f (bits n x) j))
                          (trans (f⁻-cong (idx-injective n (trans eq (ee′ y))) j)
                                 (f⁻f (bits n (ι e′ y)) j))))
        (idx-bits n (ι e′ y))))
