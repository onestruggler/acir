------------------------------------------------------------------------
-- Presentations of groups
--
-- The two halves of the five-wire Gray numbering
--
-- The indices 0 … 15 of five wires read as the four-wire Gray codes with
-- wire 4 at 0 (`cod-lo`), and 16 + a as the four-wire code of a with
-- wire 3 flipped and wire 4 at 1 (`cod-hi`): the binary-reflected Gray
-- code reflects the lower half onto the upper.  Both embeddings keep the
-- order of the indices, so the letters of P′ stay letters.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Gray5 where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; zero ; suc ; _<_ ; inject+ ; raise)
open import Data.Fin.Properties using (toℕ-↑ˡ ; toℕ-↑ʳ)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
open import Data.Vec using (Vec ; [] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Examples.Groups.Clifford+CS.Five.Sem.TL using (F ; T)
open import Examples.Groups.Clifford+CS.Five.Sem.Build using (_⊕ᵥ_)
import Examples.Groups.Clifford+CS.Numbering 5 as N5
import Examples.Groups.Clifford+CS.Numbering 4 as N4

-- The two embeddings.
lo hi : Fin 16 → Fin 32
lo a = inject+ 16 a
hi a = raise 16 a

-- Wire 3.
e₃ : Vec Bool 4
e₃ = false ∷ false ∷ false ∷ true ∷ []

cod-lo : ∀ (a : Fin 16) → N5.cod (lo a) ≡ N4.cod a ++ F
cod-lo zero = refl
cod-lo (suc zero) = refl
cod-lo (suc (suc zero)) = refl
cod-lo (suc (suc (suc zero))) = refl
cod-lo (suc (suc (suc (suc zero)))) = refl
cod-lo (suc (suc (suc (suc (suc zero))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc zero)))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = refl
cod-lo (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = refl

cod-hi : ∀ (a : Fin 16) → N5.cod (hi a) ≡ (N4.cod a ⊕ᵥ e₃) ++ T
cod-hi zero = refl
cod-hi (suc zero) = refl
cod-hi (suc (suc zero)) = refl
cod-hi (suc (suc (suc zero))) = refl
cod-hi (suc (suc (suc (suc zero)))) = refl
cod-hi (suc (suc (suc (suc (suc zero))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc zero)))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) = refl
cod-hi (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))) = refl

lo-mono : ∀ {a b : Fin 16} → a < b → lo a < lo b
lo-mono {a} {b} lt = Eq.subst₂ ℕ._<_ (Eq.sym (toℕ-↑ˡ a 16)) (Eq.sym (toℕ-↑ˡ b 16)) lt

hi-mono : ∀ {a b : Fin 16} → a < b → hi a < hi b
hi-mono {a} {b} lt =
  Eq.subst₂ ℕ._<_ (Eq.sym (toℕ-↑ʳ 16 a)) (Eq.sym (toℕ-↑ʳ 16 b)) (ℕP.+-monoʳ-< 16 lt)
