------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine words as circuits
--
-- On 4 + m wires X on wire a is X placed by a network bringing a to
-- wire 0, and CX from u onto v is CX₁₀ placed by one bringing v to wire
-- 0 and u to wire 1 (`⟪_⟫`).  Every relation of Affine.Theory holds of
-- the circuits (`⟪⟫-cong`): its wires are brought to the bottom by one
-- network σ (a frame), each letter is σ composed with a small fixed
-- network ρ placing it at its position among those wires (`T-frame`,
-- `X-frame`: a placement depends only on where the network sends the
-- significant wires, LocalPlace.place-eq), and the relation is then one
-- equation of closed circuits on two, three or four wires, decided by
-- evaluation with completeness there (four only for two CX on disjoint
-- wires, from the module parameter).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)

module Examples.Groups.Clifford+CS.Affine.Circuits (m : ℕ) (c4 : Complete 4) where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (zero ; suc ; _<_ ; s≤s ; z≤n)
open import Data.Product using (proj₁ ; proj₂ ; _,_)
import Data.Empty.Irrelevant as Irr
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Completeness using (complete₁ ; complete₂ ; complete₃)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.PermCalc using (perm ; revS ; perm-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-cong ; pl-• ; pl-ε ; pl-pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (bring₁ ; bring₂ ; bring₃ ; bring₄)

import Examples.Groups.Clifford+CS.Affine.Theory (₃₊ m) as A
open A using (Lt ; xL ; tL ; Wire)

private
  W : ℕ
  W = ₄₊ m

  module S₂ = Below 2 complete₂
  module S₃ = Below 3 complete₃
  module S₄ = Below 4 c4

open Tools (W VRel,_===_)

------------------------------------------------------------------------
-- The interpretation

-- A distinctness proof made relevant (the same term for every proof).
ne : ∀ {a b : Wire} → .(a ≢ b) → a ≢ b
ne p e = Irr.⊥-elim (p e)

⟪_⟫ : Lt → Circuit W
⟪ xL a ⟫     = pl (proj₁ (bring₁ a)) X
⟪ tL u v p ⟫ = pl (proj₁ (bring₂ v u (ne p))) CX₁₀

⟪_⟫ʷ : Word Lt → Circuit W
⟪_⟫ʷ = ⟪_⟫ ʷ

------------------------------------------------------------------------
-- Small networks: ρ i j brings position i to wire 0 and j to wire 1

module _ {k : ℕ} where
  s0 : Word (S.Gen (₂₊ k))
  s0 = S.σ

  s1 : Word (S.Gen (₃₊ k))
  s1 = S.σ S.↑

  s2 : Word (S.Gen (₄₊ k))
  s2 = S.σ S.↑ S.↑

-- CX and X placed by a network.
cx : ∀ {k} → Word (S.Gen (₂₊ k)) → Circuit (₂₊ k)
cx ρ = pl ρ CX₁₀

xx : ∀ {k} → Word (S.Gen (₁₊ k)) → Circuit (₁₊ k)
xx ρ = pl ρ X

------------------------------------------------------------------------
-- A letter in a frame

private
  back-to : ∀ (σ : Word (S.Gen W)) {a : Wire} {i : Fin W} → perm σ ⟨$⟩ʳ a ≡ i → perm (revS σ) ⟨$⟩ʳ i ≡ a
  back-to σ {a} e = Eq.subst (λ x → perm (revS σ) ⟨$⟩ʳ x ≡ a) e (perm-inv σ a)

T-frame : ∀ {u v : Wire} .(p : u ≢ v) (σ ρ : Word (S.Gen W)) →
          perm ρ ⟨$⟩ʳ (perm σ ⟨$⟩ʳ v) ≡ 0F → perm ρ ⟨$⟩ʳ (perm σ ⟨$⟩ʳ u) ≡ sF 0F →
          ⟪ tL u v p ⟫ ≈ pl σ (cx ρ)
T-frame {u} {v} p σ ρ ev eu =
  trans (place-eq {k = 2} CX₁₀ b (σ • ρ) agree) (sym (pl-pl σ ρ CX₁₀))
  where
  B = bring₂ v u (ne p)
  b = proj₁ B
  agree : ∀ (j : Fin W) → toℕ j < 2 → perm (σ • ρ) ⟨$⟩ʳ (perm (revS b) ⟨$⟩ʳ j) ≡ j
  agree 0F          _                 = Eq.trans (Eq.cong (λ x → perm (σ • ρ) ⟨$⟩ʳ x) (back-to b (proj₁ (proj₂ B)))) ev
  agree (sF 0F)     _                 = Eq.trans (Eq.cong (λ x → perm (σ • ρ) ⟨$⟩ʳ x) (back-to b (proj₂ (proj₂ B)))) eu
  agree (sF (sF j)) (s≤s (s≤s ()))

X-frame : ∀ {a : Wire} (σ ρ : Word (S.Gen W)) → perm ρ ⟨$⟩ʳ (perm σ ⟨$⟩ʳ a) ≡ 0F → ⟪ xL a ⟫ ≈ pl σ (xx ρ)
X-frame {a} σ ρ ea =
  trans (place-eq {k = 1} X b (σ • ρ) agree) (sym (pl-pl σ ρ X))
  where
  B = bring₁ a
  b = proj₁ B
  agree : ∀ (j : Fin W) → toℕ j < 1 → perm (σ • ρ) ⟨$⟩ʳ (perm (revS b) ⟨$⟩ʳ j) ≡ j
  agree 0F      _          = Eq.trans (Eq.cong (λ x → perm (σ • ρ) ⟨$⟩ʳ x) (back-to b (proj₂ B))) ea
  agree (sF j)  (s≤s ())

private
  at : ∀ (ρ σ : Word (S.Gen W)) {a : Wire} {i : Fin W} → perm σ ⟨$⟩ʳ a ≡ i →
       perm ρ ⟨$⟩ʳ (perm σ ⟨$⟩ʳ a) ≡ perm ρ ⟨$⟩ʳ i
  at ρ σ e = Eq.cong (perm ρ ⟨$⟩ʳ_) e

  rel : ∀ {a b : Wire} → .(a ≢ b) → b ≢ a
  rel p e = Irr.⊥-elim (p (Eq.sym e))

  pl₂ : ∀ (σ : Word (S.Gen W)) (a b : Circuit W) → pl σ a • pl σ b ≈ pl σ (a • b)
  pl₂ σ a b = sym (pl-• σ a b)

  pl₃ : ∀ (σ : Word (S.Gen W)) (a b c : Circuit W) → pl σ a • pl σ b • pl σ c ≈ pl σ (a • b • c)
  pl₃ σ a b c = trans (cong refl (pl₂ σ b c)) (pl₂ σ a (b • c))

  pl₄ : ∀ (σ : Word (S.Gen W)) (a b c d : Circuit W) → pl σ a • pl σ b • pl σ c • pl σ d ≈ pl σ (a • b • c • d)
  pl₄ σ a b c d = trans (cong refl (pl₃ σ b c d)) (pl₂ σ a (b • c • d))

  pl₅ : ∀ (σ : Word (S.Gen W)) (a b c d e : Circuit W) →
        pl σ a • pl σ b • pl σ c • pl σ d • pl σ e ≈ pl σ (a • b • c • d • e)
  pl₅ σ a b c d e = trans (cong refl (pl₄ σ b c d e)) (pl₂ σ a (b • c • d • e))

------------------------------------------------------------------------
-- The relations hold

⟪⟫-sound : ∀ {l r : Word Lt} → l A.=== r → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
⟪⟫-sound (A.t-sq {u} {v} {p}) = begin
  pl b CX₁₀ • pl b CX₁₀     ≈⟨ pl₂ b CX₁₀ CX₁₀ ⟩
  pl b (CX₁₀ • CX₁₀)        ≈⟨ pl-cong b (S₂.by-sem (CX₁₀ • CX₁₀) ε Eq.refl) ⟩
  pl b ε                    ≈⟨ pl-ε b ⟩
  ε ∎
  where b = proj₁ (bring₂ v u (ne p))
⟪⟫-sound (A.t-sw {u} {v} {p} {q}) = begin
  ⟪ tL u v p ⟫ • ⟪ tL v u q ⟫ • ⟪ tL u v p ⟫
    ≈⟨ cong (T-frame p σ ε ev eu) (cong (T-frame q σ s0 (at s0 σ eu) (at s0 σ ev)) (T-frame p σ ε ev eu)) ⟩
  pl σ (cx ε) • pl σ (cx s0) • pl σ (cx ε)
    ≈⟨ pl₃ σ _ _ _ ⟩
  pl σ (cx ε • cx s0 • cx ε)
    ≈⟨ pl-cong σ (S₂.by-sem (cx ε • cx s0 • cx ε) (cx s0 • cx ε • cx s0) Eq.refl) ⟩
  pl σ (cx s0 • cx ε • cx s0)
    ≈⟨ sym (pl₃ σ _ _ _) ⟩
  pl σ (cx s0) • pl σ (cx ε) • pl σ (cx s0)
    ≈⟨ sym (cong (T-frame q σ s0 (at s0 σ eu) (at s0 σ ev)) (cong (T-frame p σ ε ev eu) (T-frame q σ s0 (at s0 σ eu) (at s0 σ ev)))) ⟩
  ⟪ tL v u q ⟫ • ⟪ tL u v p ⟫ • ⟪ tL v u q ⟫ ∎
  where
  B = bring₂ v u (ne p)
  σ = proj₁ B
  ev = proj₁ (proj₂ B)
  eu = proj₂ (proj₂ B)
⟪⟫-sound (A.t-cc {u} {v} {w} {p} {q} vw) = begin
  ⟪ tL u v p ⟫ • ⟪ tL u w q ⟫
    ≈⟨ cong (T-frame p σ s0 (at s0 σ ev) (at s0 σ eu)) (T-frame q σ ρ20 (at ρ20 σ ew) (at ρ20 σ eu)) ⟩
  pl σ (cx s0) • pl σ (cx ρ20)
    ≈⟨ pl₂ σ _ _ ⟩
  pl σ (cx s0 • cx ρ20)
    ≈⟨ pl-cong σ (S₃.by-sem (cx s0 • cx (s1 • s0)) (cx (s1 • s0) • cx s0) Eq.refl) ⟩
  pl σ (cx ρ20 • cx s0)
    ≈⟨ sym (pl₂ σ _ _) ⟩
  pl σ (cx ρ20) • pl σ (cx s0)
    ≈⟨ sym (cong (T-frame q σ ρ20 (at ρ20 σ ew) (at ρ20 σ eu)) (T-frame p σ s0 (at s0 σ ev) (at s0 σ eu))) ⟩
  ⟪ tL u w q ⟫ • ⟪ tL u v p ⟫ ∎
  where
  ρ20 = s1 • s0
  B = bring₃ u v w (rel p) (rel q) (rel vw)
  σ = proj₁ B
  eu = proj₁ (proj₂ B)
  ev = proj₁ (proj₂ (proj₂ B))
  ew = proj₂ (proj₂ (proj₂ B))
⟪⟫-sound (A.t-tt {u} {v} {w} {p} {q} uv) = begin
  ⟪ tL u w p ⟫ • ⟪ tL v w q ⟫
    ≈⟨ cong (T-frame p σ ε ew eu) (T-frame q σ s1 (at s1 σ ew) (at s1 σ ev)) ⟩
  pl σ (cx ε) • pl σ (cx s1)
    ≈⟨ pl₂ σ _ _ ⟩
  pl σ (cx ε • cx s1)
    ≈⟨ pl-cong σ (S₃.by-sem (cx ε • cx s1) (cx s1 • cx ε) Eq.refl) ⟩
  pl σ (cx s1 • cx ε)
    ≈⟨ sym (pl₂ σ _ _) ⟩
  pl σ (cx s1) • pl σ (cx ε)
    ≈⟨ sym (cong (T-frame q σ s1 (at s1 σ ew) (at s1 σ ev)) (T-frame p σ ε ew eu)) ⟩
  ⟪ tL v w q ⟫ • ⟪ tL u w p ⟫ ∎
  where
  B = bring₃ w u v (ne p) (ne q) (rel uv)
  σ = proj₁ B
  ew = proj₁ (proj₂ B)
  eu = proj₁ (proj₂ (proj₂ B))
  ev = proj₂ (proj₂ (proj₂ B))
⟪⟫-sound (A.t-dd {a} {b} {c} {d} {p} {q} ac ad bc bd) = begin
  ⟪ tL a b p ⟫ • ⟪ tL c d q ⟫
    ≈⟨ cong (T-frame p σ ε eb ea) (T-frame q σ ρ23 (at ρ23 σ ed) (at ρ23 σ ec)) ⟩
  pl σ (cx ε) • pl σ (cx ρ23)
    ≈⟨ pl₂ σ _ _ ⟩
  pl σ (cx ε • cx ρ23)
    ≈⟨ pl-cong σ (S₄.by-sem (cx ε • cx (s1 • s0 • s2 • s1)) (cx (s1 • s0 • s2 • s1) • cx ε) Eq.refl) ⟩
  pl σ (cx ρ23 • cx ε)
    ≈⟨ sym (pl₂ σ _ _) ⟩
  pl σ (cx ρ23) • pl σ (cx ε)
    ≈⟨ sym (cong (T-frame q σ ρ23 (at ρ23 σ ed) (at ρ23 σ ec)) (T-frame p σ ε eb ea)) ⟩
  ⟪ tL c d q ⟫ • ⟪ tL a b p ⟫ ∎
  where
  ρ23 = s1 • s0 • s2 • s1
  B = bring₄ b a d c (ne p) (rel bd) (rel ad) (rel bc) (rel ac) (ne q)
  σ = proj₁ B
  eb = proj₁ (proj₂ B)
  ea = proj₁ (proj₂ (proj₂ B))
  ed = proj₁ (proj₂ (proj₂ (proj₂ B)))
  ec = proj₂ (proj₂ (proj₂ (proj₂ B)))
⟪⟫-sound (A.t-ts {x} {y} {z} {p} {q} {r}) = begin
  ⟪ tL x y p ⟫ • ⟪ tL y z q ⟫ • ⟪ tL x y p ⟫
    ≈⟨ cong Txy (cong Tyz Txy) ⟩
  pl σ (cx s0) • pl σ (cx ρ21) • pl σ (cx s0)
    ≈⟨ pl₃ σ _ _ _ ⟩
  pl σ (cx s0 • cx ρ21 • cx s0)
    ≈⟨ pl-cong σ (S₃.by-sem (cx s0 • cx (s1 • s0 • s1) • cx s0) (cx (s1 • s0 • s1) • cx (s1 • s0)) Eq.refl) ⟩
  pl σ (cx ρ21 • cx ρ20)
    ≈⟨ sym (pl₂ σ _ _) ⟩
  pl σ (cx ρ21) • pl σ (cx ρ20)
    ≈⟨ sym (cong Tyz Txz) ⟩
  ⟪ tL y z q ⟫ • ⟪ tL x z r ⟫ ∎
  where
  ρ21 = s1 • s0 • s1
  ρ20 = s1 • s0
  B = bring₃ x y z (rel p) (rel r) (rel q)
  σ = proj₁ B
  ex = proj₁ (proj₂ B)
  ey = proj₁ (proj₂ (proj₂ B))
  ez = proj₂ (proj₂ (proj₂ B))
  Txy = T-frame p σ s0 (at s0 σ ey) (at s0 σ ex)
  Tyz = T-frame q σ ρ21 (at ρ21 σ ez) (at ρ21 σ ey)
  Txz = T-frame r σ ρ20 (at ρ20 σ ez) (at ρ20 σ ex)
⟪⟫-sound (A.t-st {x} {y} {z} {p} {q} {r}) = begin
  ⟪ tL y z q ⟫ • ⟪ tL x y p ⟫ • ⟪ tL y z q ⟫
    ≈⟨ cong Tyz (cong Txy Tyz) ⟩
  pl σ (cx ρ21) • pl σ (cx s0) • pl σ (cx ρ21)
    ≈⟨ pl₃ σ _ _ _ ⟩
  pl σ (cx ρ21 • cx s0 • cx ρ21)
    ≈⟨ pl-cong σ (S₃.by-sem (cx (s1 • s0 • s1) • cx s0 • cx (s1 • s0 • s1)) (cx s0 • cx (s1 • s0)) Eq.refl) ⟩
  pl σ (cx s0 • cx ρ20)
    ≈⟨ sym (pl₂ σ _ _) ⟩
  pl σ (cx s0) • pl σ (cx ρ20)
    ≈⟨ sym (cong Txy Txz) ⟩
  ⟪ tL x y p ⟫ • ⟪ tL x z r ⟫ ∎
  where
  ρ21 = s1 • s0 • s1
  ρ20 = s1 • s0
  B = bring₃ x y z (rel p) (rel r) (rel q)
  σ = proj₁ B
  ex = proj₁ (proj₂ B)
  ey = proj₁ (proj₂ (proj₂ B))
  ez = proj₂ (proj₂ (proj₂ B))
  Txy = T-frame p σ s0 (at s0 σ ey) (at s0 σ ex)
  Tyz = T-frame q σ ρ21 (at ρ21 σ ez) (at ρ21 σ ey)
  Txz = T-frame r σ ρ20 (at ρ20 σ ez) (at ρ20 σ ex)
⟪⟫-sound (A.t-pv {o} {u} {j} {a} {b} {c} {d} {e}) = begin
  ⟪ tL j o a ⟫ • ⟪ tL u o b ⟫ • ⟪ tL o u c ⟫ • ⟪ tL o j d ⟫
    ≈⟨ cong Tjo (cong Tuo (cong Tou Toj)) ⟩
  pl σ (cx s1) • pl σ (cx ε) • pl σ (cx s0) • pl σ (cx ρ20)
    ≈⟨ pl₄ σ _ _ _ _ ⟩
  pl σ (cx s1 • cx ε • cx s0 • cx ρ20)
    ≈⟨ pl-cong σ (S₃.by-sem (cx s1 • cx ε • cx s0 • cx (s1 • s0))
                            (cx s0 • cx (s1 • s0) • (cx (s1 • s0 • s1) • cx (s0 • s1) • cx (s1 • s0 • s1)) • cx ε • cx s1)
                            Eq.refl) ⟩
  pl σ (cx s0 • cx ρ20 • (cx ρ21 • cx ρ12 • cx ρ21) • cx ε • cx s1)
    ≈⟨ trans (pl-• σ _ _) (cong refl (trans (pl-• σ _ _) (cong refl (trans (pl-• σ _ _)
         (cong (trans (pl-• σ _ _) (cong refl (pl-• σ _ _))) (pl-• σ _ _)))))) ⟩
  pl σ (cx s0) • pl σ (cx ρ20) • (pl σ (cx ρ21) • pl σ (cx ρ12) • pl σ (cx ρ21)) • pl σ (cx ε) • pl σ (cx s1)
    ≈⟨ sym (cong Tou (cong Toj (cong (cong Tuj (cong Tju Tuj)) (cong Tuo Tjo)))) ⟩
  ⟪ tL o u c ⟫ • ⟪ tL o j d ⟫ • (⟪ tL u j e ⟫ • ⟪ tL j u (λ x → e (Eq.sym x)) ⟫ • ⟪ tL u j e ⟫) •
    ⟪ tL u o b ⟫ • ⟪ tL j o a ⟫ ∎
  where
  ρ20 = s1 • s0
  ρ21 = s1 • s0 • s1
  ρ12 = s0 • s1
  B = bring₃ o u j (rel c) (rel d) (rel e)
  σ = proj₁ B
  eo = proj₁ (proj₂ B)
  eu = proj₁ (proj₂ (proj₂ B))
  ej = proj₂ (proj₂ (proj₂ B))
  Tjo = T-frame a σ s1 (at s1 σ eo) (at s1 σ ej)
  Tuo = T-frame b σ ε eo eu
  Tou = T-frame c σ s0 (at s0 σ eu) (at s0 σ eo)
  Toj = T-frame d σ ρ20 (at ρ20 σ ej) (at ρ20 σ eo)
  Tuj = T-frame e σ ρ21 (at ρ21 σ ej) (at ρ21 σ eu)
  Tju = T-frame (λ x → e (Eq.sym x)) σ ρ12 (at ρ12 σ eu) (at ρ12 σ ej)
⟪⟫-sound (A.x-sq {v}) = begin
  pl b X • pl b X     ≈⟨ pl₂ b X X ⟩
  pl b (X • X)        ≈⟨ pl-cong b (S₁.by-sem (X • X) ε Eq.refl) ⟩
  pl b ε              ≈⟨ pl-ε b ⟩
  ε ∎
  where
  b = proj₁ (bring₁ v)
  module S₁ = Below 1 complete₁
⟪⟫-sound (A.x-xx {v} {w}) with v ≟ w
... | yes Eq.refl = refl
... | no vw = begin
  ⟪ xL v ⟫ • ⟪ xL w ⟫
    ≈⟨ cong (X-frame σ ε ev) (X-frame σ s0 (at s0 σ ew)) ⟩
  pl σ (xx ε) • pl σ (xx s0)
    ≈⟨ pl₂ σ _ _ ⟩
  pl σ (xx ε • xx s0)
    ≈⟨ pl-cong σ (S₂.by-sem (xx ε • xx s0) (xx s0 • xx ε) Eq.refl) ⟩
  pl σ (xx s0 • xx ε)
    ≈⟨ sym (pl₂ σ _ _) ⟩
  pl σ (xx s0) • pl σ (xx ε)
    ≈⟨ sym (cong (X-frame σ s0 (at s0 σ ew)) (X-frame σ ε ev)) ⟩
  ⟪ xL w ⟫ • ⟪ xL v ⟫ ∎
  where
  B = bring₂ v w (λ e → vw (Eq.sym e))
  σ = proj₁ B
  ev = proj₁ (proj₂ B)
  ew = proj₂ (proj₂ B)
⟪⟫-sound (A.x-ctl {u} {v} {p}) = begin
  ⟪ tL u v p ⟫ • ⟪ xL u ⟫
    ≈⟨ cong Tuv Xu ⟩
  pl σ (cx ε) • pl σ (xx s0)
    ≈⟨ pl₂ σ _ _ ⟩
  pl σ (cx ε • xx s0)
    ≈⟨ pl-cong σ (S₂.by-sem (cx ε • xx s0) (xx s0 • xx ε • cx ε) Eq.refl) ⟩
  pl σ (xx s0 • xx ε • cx ε)
    ≈⟨ sym (pl₃ σ _ _ _) ⟩
  pl σ (xx s0) • pl σ (xx ε) • pl σ (cx ε)
    ≈⟨ sym (cong Xu (cong Xv Tuv)) ⟩
  ⟪ xL u ⟫ • ⟪ xL v ⟫ • ⟪ tL u v p ⟫ ∎
  where
  B = bring₂ v u (ne p)
  σ = proj₁ B
  ev = proj₁ (proj₂ B)
  eu = proj₂ (proj₂ B)
  Tuv = T-frame p σ ε ev eu
  Xu = X-frame σ s0 (at s0 σ eu)
  Xv = X-frame σ ε ev
⟪⟫-sound (A.x-tgt {u} {v} {p}) = begin
  ⟪ tL u v p ⟫ • ⟪ xL v ⟫
    ≈⟨ cong Tuv Xv ⟩
  pl σ (cx ε) • pl σ (xx ε)
    ≈⟨ pl₂ σ _ _ ⟩
  pl σ (cx ε • xx ε)
    ≈⟨ pl-cong σ (S₂.by-sem (cx ε • xx ε) (xx ε • cx ε) Eq.refl) ⟩
  pl σ (xx ε • cx ε)
    ≈⟨ sym (pl₂ σ _ _) ⟩
  pl σ (xx ε) • pl σ (cx ε)
    ≈⟨ sym (cong Xv Tuv) ⟩
  ⟪ xL v ⟫ • ⟪ tL u v p ⟫ ∎
  where
  B = bring₂ v u (ne p)
  σ = proj₁ B
  ev = proj₁ (proj₂ B)
  eu = proj₂ (proj₂ B)
  Tuv = T-frame p σ ε ev eu
  Xv = X-frame σ ε ev
⟪⟫-sound (A.x-far {u} {v} {w} {p} wu wv) = begin
  ⟪ tL u v p ⟫ • ⟪ xL w ⟫
    ≈⟨ cong Tuv Xw ⟩
  pl σ (cx ε) • pl σ (xx ρ20)
    ≈⟨ pl₂ σ _ _ ⟩
  pl σ (cx ε • xx ρ20)
    ≈⟨ pl-cong σ (S₃.by-sem (cx ε • xx (s1 • s0)) (xx (s1 • s0) • cx ε) Eq.refl) ⟩
  pl σ (xx ρ20 • cx ε)
    ≈⟨ sym (pl₂ σ _ _) ⟩
  pl σ (xx ρ20) • pl σ (cx ε)
    ≈⟨ sym (cong Xw Tuv) ⟩
  ⟪ xL w ⟫ • ⟪ tL u v p ⟫ ∎
  where
  ρ20 = s1 • s0
  B = bring₃ v u w (ne p) (ne wv) (ne wu)
  σ = proj₁ B
  ev = proj₁ (proj₂ B)
  eu = proj₁ (proj₂ (proj₂ B))
  ew = proj₂ (proj₂ (proj₂ B))
  Tuv = T-frame p σ ε ev eu
  Xw = X-frame σ ρ20 (at ρ20 σ ew)

-- The congruence.
⟪⟫-cong : ∀ {l r : Word Lt} → l A.≈ r → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
⟪⟫-cong PB.refl          = refl
⟪⟫-cong (PB.sym e)       = sym (⟪⟫-cong e)
⟪⟫-cong (PB.trans e e′)  = trans (⟪⟫-cong e) (⟪⟫-cong e′)
⟪⟫-cong (PB.cong e e′)   = cong (⟪⟫-cong e) (⟪⟫-cong e′)
⟪⟫-cong PB.assoc         = assoc
⟪⟫-cong PB.left-unit     = left-unit
⟪⟫-cong PB.right-unit    = right-unit
⟪⟫-cong (PB.axiom a)     = ⟪⟫-sound a
