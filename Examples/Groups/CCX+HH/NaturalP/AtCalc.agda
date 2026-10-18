------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators that act on the coordinates of an embedding.
--
-- `At e G F`: on the coordinates that the increasing embedding e picks
-- out, F acts as G, and every other coordinate F leaves alone.  Two such
-- operators with the same G are equal (`at-ext`); a Table 1 word moved
-- along e is one (`at-word`, from CCX+HH-TwoLevel/EmbedAction); they
-- compose along composed embeddings (`at-∘`).  `AtI` is the same at any
-- injection of the coordinates, not necessarily increasing: a generator
-- acts there as its pull-back (`atI-M`, `atI-X`, `atI-K`), and a
-- permutation of the coordinates carries one injection to another
-- (`at-perm`).  A circuit under k white controls acts at the window
-- embedding `ιW k c` (`Λ-at`), and an affine word permutes the
-- coordinates as its classical action permutes the basis states
-- (`perm-!`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.AtCalc where

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Bool.Base using (false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Fin.Properties using (any? ; _≟_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _^_)
open import Data.Product.Base using (∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; tabulate)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Word.Base using (Word ; wmap)
open import Notations using (₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring hiding (ι)
open import Instances using (_*_ ; -_ ; 0# ; 1#)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι ; mono ; word)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen ; M-gen ; X-gen ; K-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
  using (_!_ ; vec-ext ; restrict ; restrict-! ; actVʷ ; emb-actVʷ-restrict ; emb-actVʷ-out
        ; actVʷ≡ ; colmat ; ent ; ent-·*· ; sum-single ; δ ; δ-refl ; δ-≢ ; ⟦_⟧ᵐ
        ; !-tabulate ; actV ; actV-Ma ; actV-M≢ ; actV-Xa ; actV-Xb ; actV-X≢
        ; actV-Ka ; actV-Kb ; actV-Kc ; actV-Kd ; actV-K≢ ; rowA ; rowB ; rowC ; rowD)
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
-- Operators at an injection

-- The restriction along any map of indices; along an increasing
-- embedding it is `restrict`, definitionally.
restrictI : (Fin m → Fin n) → Vec D n → Vec D m
restrictI ι′ v = tabulate (λ y → v ! ι′ y)

restrictI-! : (ι′ : Fin m → Fin n) (v : Vec D n) (y : Fin m) → restrictI ι′ v ! y ≡ v ! ι′ y
restrictI-! ι′ v y = !-tabulate (λ y → v ! ι′ y) y

-- `AtI ι′ G F`: F acts as G on the coordinates ι′ picks out, in the
-- order ι′ lists them, and leaves every other coordinate alone.
record AtI (ι′ : Fin m → Fin n) (G : Op m) (F : Op n) : Set where
  field
    onI  : ∀ v → restrictI ι′ (F v) ≡ G (restrictI ι′ v)
    offI : ∀ v x → (∀ y → x ≢ ι′ y) → F v ! x ≡ v ! x
open AtI public

at→I : {e : Emb m n} {G : Op m} {F : Op n} → At e G F → AtI (ι e) G F
at→I a = record { onI = on a ; offI = off a }

Inj : (Fin m → Fin n) → Set
Inj ι′ = ∀ {x y} → ι′ x ≡ ι′ y → x ≡ y

atI-ext : {ι′ : Fin m → Fin n} {G G′ : Op m} {F F′ : Op n} → AtI ι′ G F → AtI ι′ G′ F′ →
  (∀ u → G u ≡ G′ u) → ∀ v → F v ≡ F′ v
atI-ext {ι′ = ι′} {G} {G′} {F} {F′} a a′ gg v = vec-ext λ x → by x (any? (λ y → ι′ y ≟ x))
  where
  by : ∀ x → Dec (∃ λ y → ι′ y ≡ x) → F v ! x ≡ F′ v ! x
  by x (yes (y , refl)) =
    trans (sym (restrictI-! ι′ (F v) y))
    (trans (cong (_! y) (onI a v))
    (trans (cong (_! y) (gg (restrictI ι′ v)))
    (trans (cong (_! y) (sym (onI a′ v))) (restrictI-! ι′ (F′ v) y))))
  by x (no ¬i) =
    trans (offI a v x (λ y eq → ¬i (y , sym eq)))
      (sym (offI a′ v x (λ y eq → ¬i (y , sym eq))))

atI-cong : {ι′ : Fin m → Fin n} {G G′ : Op m} {F F′ : Op n} → AtI ι′ G F →
  (∀ u → G u ≡ G′ u) → (∀ v → F v ≡ F′ v) → AtI ι′ G′ F′
atI-cong {ι′ = ι′} {G} {G′} {F} {F′} a gg ff = record
  { onI  = λ v → trans (cong (restrictI ι′) (sym (ff v))) (trans (onI a v) (gg (restrictI ι′ v)))
  ; offI = λ v x h → trans (sym (cong (_! x) (ff v))) (offI a v x h) }

atI-id : {ι′ : Fin m → Fin n} → AtI ι′ (λ u → u) (λ v → v)
atI-id = record { onI = λ v → refl ; offI = λ v x h → refl }

-- Products at the same injection.
atI-• : {ι′ : Fin m → Fin n} {G₁ G₂ : Op m} {F₁ F₂ : Op n} →
  AtI ι′ G₁ F₁ → AtI ι′ G₂ F₂ → AtI ι′ (λ u → G₁ (G₂ u)) (λ v → F₁ (F₂ v))
atI-• {G₁ = G₁} {F₂ = F₂} a b = record
  { onI  = λ v → trans (onI a (F₂ v)) (cong G₁ (onI b v))
  ; offI = λ v x h → trans (offI a (F₂ v) x h) (offI b v x h) }

-- Composed injections.
atI-∘ : {ι₁ : Fin n → Fin p} {ι₂ : Fin m → Fin n} {H : Op m} {G : Op n} {F : Op p} →
  AtI ι₁ G F → AtI ι₂ H G → AtI (λ y → ι₁ (ι₂ y)) H F
atI-∘ {ι₁ = ι₁} {ι₂} {H} {G} {F} a b = record
  { onI  = λ v →
      trans (∘-restrict (F v))
      (trans (cong (restrictI ι₂) (onI a v))
      (trans (onI b (restrictI ι₁ v)) (cong H (sym (∘-restrict v)))))
  ; offI = λ v x h → by v x h (any? (λ y → ι₁ y ≟ x)) }
  where
  ∘-restrict : (v : Vec D _) → restrictI (λ y → ι₁ (ι₂ y)) v ≡ restrictI ι₂ (restrictI ι₁ v)
  ∘-restrict v = vec-ext λ y →
    trans (restrictI-! (λ y → ι₁ (ι₂ y)) v y)
      (trans (sym (restrictI-! ι₁ v (ι₂ y))) (sym (restrictI-! ι₂ (restrictI ι₁ v) y)))
  by : ∀ v x → (∀ y → x ≢ ι₁ (ι₂ y)) → Dec (∃ λ y → ι₁ y ≡ x) → F v ! x ≡ v ! x
  by v x h (yes (y , refl)) =
    trans (sym (restrictI-! ι₁ (F v) y))
    (trans (cong (_! y) (onI a v))
    (trans (offI b (restrictI ι₁ v) y (λ z eq → h z (cong ι₁ eq)))
      (restrictI-! ι₁ v y)))
  by v x h (no ¬i) = offI a v x (λ y eq → ¬i (y , sym eq))

------------------------------------------------------------------------
-- The generators at an injection

private
  ne-ι : {ι′ : Fin m → Fin n} → Inj ι′ → ∀ {x y} → x ≢ y → ι′ x ≢ ι′ y
  ne-ι inj ne eq = ne (inj eq)

  cong₄ : ∀ {A B : Set} (f : A → A → A → A → B) {x x′ y y′ z z′ t t′} →
    x ≡ x′ → y ≡ y′ → z ≡ z′ → t ≡ t′ → f x y z t ≡ f x′ y′ z′ t′
  cong₄ f refl refl refl refl = refl

atI-M : (ι′ : Fin m → Fin n) → Inj ι′ → (i : Fin m) →
  AtI ι′ (actV (M-gen i)) (actV (M-gen (ι′ i)))
atI-M ι′ inj i = record
  { onI  = λ v → vec-ext λ y →
      trans (restrictI-! ι′ (actV (M-gen (ι′ i)) v) y) (by v y (y ≟ i))
  ; offI = λ v x h → actV-M≢ (ι′ i) v (h i) }
  where
  by : ∀ v y → Dec (y ≡ i) → actV (M-gen (ι′ i)) v ! ι′ y ≡ actV (M-gen i) (restrictI ι′ v) ! y
  by v y (yes refl) =
    trans (actV-Ma (ι′ y) v)
      (sym (trans (actV-Ma y (restrictI ι′ v)) (cong -_ (restrictI-! ι′ v y))))
  by v y (no ne) =
    trans (actV-M≢ (ι′ i) v (ne-ι inj ne))
      (sym (trans (actV-M≢ i (restrictI ι′ v) ne) (restrictI-! ι′ v y)))

atI-X : (ι′ : Fin m → Fin n) → Inj ι′ → (i k : Fin m) .(q : i < k) .(p : ι′ i < ι′ k) →
  AtI ι′ (actV (X-gen i k q)) (actV (X-gen (ι′ i) (ι′ k) p))
atI-X ι′ inj i k q p = record
  { onI  = λ v → vec-ext λ y →
      trans (restrictI-! ι′ (actV (X-gen (ι′ i) (ι′ k) p) v) y) (by v y (y ≟ i) (y ≟ k))
  ; offI = λ v x h → actV-X≢ p v (h i) (h k) }
  where
  by : ∀ v y → Dec (y ≡ i) → Dec (y ≡ k) →
    actV (X-gen (ι′ i) (ι′ k) p) v ! ι′ y ≡ actV (X-gen i k q) (restrictI ι′ v) ! y
  by v y (yes refl) _ =
    trans (actV-Xa p v) (sym (trans (actV-Xa q (restrictI ι′ v)) (restrictI-! ι′ v k)))
  by v y (no _) (yes refl) =
    trans (actV-Xb p v) (sym (trans (actV-Xb q (restrictI ι′ v)) (restrictI-! ι′ v i)))
  by v y (no ni) (no nk) =
    trans (actV-X≢ p v (ne-ι inj ni) (ne-ι inj nk))
      (sym (trans (actV-X≢ q (restrictI ι′ v) ni nk) (restrictI-! ι′ v y)))

atI-K : (ι′ : Fin m → Fin n) → Inj ι′ → (a b c d : Fin m) .(p : a < b) .(q : b < c) .(r : c < d)
  .(p′ : ι′ a < ι′ b) .(q′ : ι′ b < ι′ c) .(r′ : ι′ c < ι′ d) →
  AtI ι′ (actV (K-gen a b c d p q r)) (actV (K-gen (ι′ a) (ι′ b) (ι′ c) (ι′ d) p′ q′ r′))
atI-K ι′ inj a b c d p q r p′ q′ r′ = record
  { onI  = λ v → vec-ext λ y →
      trans (restrictI-! ι′ (actV (K-gen (ι′ a) (ι′ b) (ι′ c) (ι′ d) p′ q′ r′) v) y)
        (by v y (y ≟ a) (y ≟ b) (y ≟ c) (y ≟ d))
  ; offI = λ v x h → actV-K≢ p′ q′ r′ v (h a) (h b) (h c) (h d) }
  where
  rows : (f : D → D → D → D → D) (v : Vec D _) →
    f (v ! ι′ a) (v ! ι′ b) (v ! ι′ c) (v ! ι′ d)
      ≡ f (restrictI ι′ v ! a) (restrictI ι′ v ! b) (restrictI ι′ v ! c) (restrictI ι′ v ! d)
  rows f v = sym (cong₄ f (restrictI-! ι′ v a) (restrictI-! ι′ v b)
                          (restrictI-! ι′ v c) (restrictI-! ι′ v d))
  by : ∀ v y → Dec (y ≡ a) → Dec (y ≡ b) → Dec (y ≡ c) → Dec (y ≡ d) →
    actV (K-gen (ι′ a) (ι′ b) (ι′ c) (ι′ d) p′ q′ r′) v ! ι′ y
      ≡ actV (K-gen a b c d p q r) (restrictI ι′ v) ! y
  by v y (yes refl) _ _ _ =
    trans (actV-Ka p′ q′ r′ v) (trans (rows rowA v) (sym (actV-Ka p q r (restrictI ι′ v))))
  by v y (no _) (yes refl) _ _ =
    trans (actV-Kb p′ q′ r′ v) (trans (rows rowB v) (sym (actV-Kb p q r (restrictI ι′ v))))
  by v y (no _) (no _) (yes refl) _ =
    trans (actV-Kc p′ q′ r′ v) (trans (rows rowC v) (sym (actV-Kc p q r (restrictI ι′ v))))
  by v y (no _) (no _) (no _) (yes refl) =
    trans (actV-Kd p′ q′ r′ v) (trans (rows rowD v) (sym (actV-Kd p q r (restrictI ι′ v))))
  by v y (no na) (no nb) (no nc) (no nd) =
    trans (actV-K≢ p′ q′ r′ v (ne-ι inj na) (ne-ι inj nb) (ne-ι inj nc) (ne-ι inj nd))
      (sym (trans (actV-K≢ p q r (restrictI ι′ v) na nb nc nd) (restrictI-! ι′ v y)))

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

-- Conjugating an operator at ι₁ by a permutation of the coordinates:
-- the result acts at ι₂, the coordinates that the permutation carries
-- onto those of ι₁.
at-perm : (Q Q⁻ : Op (2 ^ n)) (f f⁻ : C.State n → C.State n) →
  (∀ v s → Q v ! idx n (f s) ≡ v ! idx n s) →
  (∀ v s → Q⁻ v ! idx n (f⁻ s) ≡ v ! idx n s) →
  (∀ s → f⁻ (f s) C.≈s s) → (∀ {s t} → s C.≈s t → f⁻ s C.≈s f⁻ t) →
  {ι₁ : Fin m → Fin (2 ^ n)} {G : Op m} {F : Op (2 ^ n)} → AtI ι₁ G F →
  (ι₂ : Fin m → Fin (2 ^ n)) → (∀ y → ι₁ y ≡ idx n (f (bits n (ι₂ y)))) →
  AtI ι₂ G (λ v → Q⁻ (F (Q v)))
at-perm {n} Q Q⁻ f f⁻ Qf Q⁻f f⁻f f⁻-cong {ι₁} {G} {F} a ι₂ eq₁₂ = record
  { onI  = λ v → vec-ext λ y →
      trans (restrictI-! ι₂ (Q⁻ (F (Q v))) y)
      (trans (back (F (Q v)) (ι₂ y))
      (trans (cong (F (Q v) !_) (sym (eq₁₂ y)))
      (trans (sym (restrictI-! ι₁ (F (Q v)) y))
      (cong (_! y) (trans (onI a (Q v)) (cong G (restrict-Q v)))))))
  ; offI = λ v x h →
      trans (back (F (Q v)) x)
      (trans (offI a (Q v) (idx n (f (bits n x))) (not-image x h))
      (trans (Qf v (bits n x)) (cong (v !_) (idx-bits n x))))
  }
  where
  -- Q⁻ read at any coordinate.
  back : ∀ u x → Q⁻ u ! x ≡ u ! idx n (f (bits n x))
  back u x =
    trans (cong (Q⁻ u !_) (sym (trans (idx-cong n (f⁻f (bits n x))) (idx-bits n x))))
      (Q⁻f u (f (bits n x)))
  restrict-Q : ∀ v → restrictI ι₁ (Q v) ≡ restrictI ι₂ v
  restrict-Q v = vec-ext λ y →
    trans (restrictI-! ι₁ (Q v) y)
    (trans (cong (Q v !_) (eq₁₂ y))
    (trans (Qf v (bits n (ι₂ y)))
    (trans (cong (v !_) (idx-bits n (ι₂ y))) (sym (restrictI-! ι₂ v y)))))
  not-image : ∀ x → (∀ y → x ≢ ι₂ y) → ∀ y → idx n (f (bits n x)) ≢ ι₁ y
  not-image x h y eq = h y
    (trans (sym (idx-bits n x))
      (trans (idx-cong n (λ j → trans (sym (f⁻f (bits n x) j))
                          (trans (f⁻-cong (idx-injective n (trans eq (eq₁₂ y))) j)
                                 (f⁻f (bits n (ι₂ y)) j))))
        (idx-bits n (ι₂ y))))
