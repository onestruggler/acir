------------------------------------------------------------------------
-- Presentations of groups
--
-- A quartic invariant under every signed permutation of eight levels.
-- A single evaluation vector separates the 135 finite circuit cosets.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.QuarticInvariant where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (s≤s)
open import Data.Integer.Base using (+_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (recompute)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix')
open import Notations
open import Word.Base using (Word ; ε ; _•_)
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red
open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; ι ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; module DS)
open S using (actV ; set₁ ; set₂)
open DS using (_:+_ ; _:*_ ; :-_ ; _:=_)

fourth : D → D
fourth x = (x *ᴰ x) *ᴰ (x *ᴰ x)

fourth-neg : ∀ x → fourth (-ᴰ x) ≡ fourth x
fourth-neg = DS.solve 1
  (λ x → ((:- x) :* (:- x)) :* ((:- x) :* (:- x)) := (x :* x) :* (x :* x)) refl

quartic : Vec D 8 → D
quartic (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
  fourth a +ᴰ (fourth b +ᴰ (fourth c +ᴰ (fourth d +ᴰ
  (fourth e +ᴰ (fourth f +ᴰ (fourth g +ᴰ fourth h))))))

data Signed : Word (T.Gen 8) → Set where
  minus : ∀ a → Signed (T.M a)
  exchange : ∀ a b .(p : a < b) → Signed (T.X a b p)
  empty : Signed ε
  product : ∀ {u v} → Signed u → Signed v → Signed (u • v)

opaque
  unfolding actV set₁ set₂

  minus-invariant : ∀ a v → quartic (S.actVʷ (T.M a) v) ≡ quartic v
  minus-invariant ₀ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) rewrite fourth-neg a = refl
  minus-invariant ₁ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) rewrite fourth-neg b = refl
  minus-invariant ₂ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) rewrite fourth-neg c = refl
  minus-invariant ₃ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) rewrite fourth-neg d = refl
  minus-invariant ₄ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) rewrite fourth-neg e = refl
  minus-invariant ₅ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) rewrite fourth-neg f = refl
  minus-invariant ₆ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) rewrite fourth-neg g = refl
  minus-invariant ₇ (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) rewrite fourth-neg h = refl

  exchange-invariant : ∀ a b (p : a < b) v → quartic (S.actVʷ (T.X a b p) v) ≡ quartic v
  exchange-invariant ₀ ₀ () v
  exchange-invariant ₁ ₀ () v
  exchange-invariant ₁ ₁ (s≤s ()) v
  exchange-invariant ₂ ₀ () v
  exchange-invariant ₂ ₁ (s≤s ()) v
  exchange-invariant ₂ ₂ (s≤s (s≤s ())) v
  exchange-invariant ₃ ₀ () v
  exchange-invariant ₃ ₁ (s≤s ()) v
  exchange-invariant ₃ ₂ (s≤s (s≤s ())) v
  exchange-invariant ₃ ₃ (s≤s (s≤s (s≤s ()))) v
  exchange-invariant ₄ ₀ () v
  exchange-invariant ₄ ₁ (s≤s ()) v
  exchange-invariant ₄ ₂ (s≤s (s≤s ())) v
  exchange-invariant ₄ ₃ (s≤s (s≤s (s≤s ()))) v
  exchange-invariant ₄ ₄ (s≤s (s≤s (s≤s (s≤s ())))) v
  exchange-invariant ₅ ₀ () v
  exchange-invariant ₅ ₁ (s≤s ()) v
  exchange-invariant ₅ ₂ (s≤s (s≤s ())) v
  exchange-invariant ₅ ₃ (s≤s (s≤s (s≤s ()))) v
  exchange-invariant ₅ ₄ (s≤s (s≤s (s≤s (s≤s ())))) v
  exchange-invariant ₅ ₅ (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) v
  exchange-invariant ₆ ₀ () v
  exchange-invariant ₆ ₁ (s≤s ()) v
  exchange-invariant ₆ ₂ (s≤s (s≤s ())) v
  exchange-invariant ₆ ₃ (s≤s (s≤s (s≤s ()))) v
  exchange-invariant ₆ ₄ (s≤s (s≤s (s≤s (s≤s ())))) v
  exchange-invariant ₆ ₅ (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) v
  exchange-invariant ₆ ₆ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))) v
  exchange-invariant ₇ ₀ () v
  exchange-invariant ₇ ₁ (s≤s ()) v
  exchange-invariant ₇ ₂ (s≤s (s≤s ())) v
  exchange-invariant ₇ ₃ (s≤s (s≤s (s≤s ()))) v
  exchange-invariant ₇ ₄ (s≤s (s≤s (s≤s (s≤s ())))) v
  exchange-invariant ₇ ₅ (s≤s (s≤s (s≤s (s≤s (s≤s ()))))) v
  exchange-invariant ₇ ₆ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))) v
  exchange-invariant ₇ ₇ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))) v
  exchange-invariant ₀ ₁ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → b :+ (a :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₀ ₂ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → c :+ (b :+ (a :+ (d :+ (e :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₀ ₃ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → d :+ (b :+ (c :+ (a :+ (e :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₀ ₄ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → e :+ (b :+ (c :+ (d :+ (a :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₀ ₅ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → f :+ (b :+ (c :+ (d :+ (e :+ (a :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₀ ₆ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → g :+ (b :+ (c :+ (d :+ (e :+ (f :+ (a :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₀ ₇ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → h :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (a))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₁ ₂ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (c :+ (b :+ (d :+ (e :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₁ ₃ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (d :+ (c :+ (b :+ (e :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₁ ₄ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (e :+ (c :+ (d :+ (b :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₁ ₅ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (f :+ (c :+ (d :+ (e :+ (b :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₁ ₆ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (g :+ (c :+ (d :+ (e :+ (f :+ (b :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₁ ₇ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (h :+ (c :+ (d :+ (e :+ (f :+ (g :+ (b))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₂ ₃ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (d :+ (c :+ (e :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₂ ₄ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (e :+ (d :+ (c :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₂ ₅ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (f :+ (d :+ (e :+ (c :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₂ ₆ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (g :+ (d :+ (e :+ (f :+ (c :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₂ ₇ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (h :+ (d :+ (e :+ (f :+ (g :+ (c))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₃ ₄ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (e :+ (d :+ (f :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₃ ₅ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (f :+ (e :+ (d :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₃ ₆ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (g :+ (e :+ (f :+ (d :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₃ ₇ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (h :+ (e :+ (f :+ (g :+ (d))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₄ ₅ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (d :+ (f :+ (e :+ (g :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₄ ₆ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (d :+ (g :+ (f :+ (e :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₄ ₇ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (d :+ (h :+ (f :+ (g :+ (e))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₅ ₆ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (d :+ (e :+ (g :+ (f :+ (h))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₅ ₇ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (d :+ (e :+ (h :+ (g :+ (f))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)
  exchange-invariant ₆ ₇ p (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) =
    DS.solve 8 (λ a b c d e f g h → a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (h :+ (g))))))) := a :+ (b :+ (c :+ (d :+ (e :+ (f :+ (g :+ (h))))))))
      refl (fourth a) (fourth b) (fourth c) (fourth d) (fourth e) (fourth f) (fourth g) (fourth h)

invariant : ∀ {w} → Signed w → ∀ v → quartic (S.actVʷ w v) ≡ quartic v
invariant (minus a) v = minus-invariant a v
invariant (exchange a b p) v = exchange-invariant a b (recompute (a FP.<? b) p) v
invariant empty v = refl
invariant (product {u} {w} p q) v =
  Eq.trans (invariant p (S.actVʷ w v)) (invariant q v)

-- Four times a small integer evaluation vector makes every one of the
-- 135 representative evaluations integral.
probe : Vec D 8
probe = ι (+ 4) ∷ ι (+ 8) ∷ ι (+ 12) ∷ ι (+ 20) ∷
        ι (+ 28) ∷ ι (+ 44) ∷ ι (+ 52) ∷ ι (+ 68) ∷ []

signature : Word (T.Gen 8) → D
signature w = quartic (S.actVʷ w probe)

prefix-invariant : ∀ {u} → Signed u → ∀ v → signature (u • v) ≡ signature v
prefix-invariant p v = invariant p (S.actVʷ v probe)

private
  columns : Vec D 8 → Matrix 8 8 D
  columns v = Matrix' (v ∷ v ∷ v ∷ v ∷ v ∷ v ∷ v ∷ v ∷ [])

actV-cong : ∀ {u v} → PB._≈_ (T._===_ {8}) u v →
  ∀ w → S.actVʷ u w ≡ S.actVʷ v w
actV-cong {u} {v} p w =
  Eq.trans (Eq.sym (S.col-actMʷ u (columns w) ₀))
    (Eq.trans (Eq.cong (λ m → S.col m ₀) (Red.sound-act p (columns w)))
              (S.col-actMʷ v (columns w) ₀))

signature-cong : ∀ {u v} → PB._≈_ (T._===_ {8}) u v → signature u ≡ signature v
signature-cong p = Eq.cong quartic (actV-cong p probe)

