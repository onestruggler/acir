------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-wire gadgets, as the record the five-wire modules take
--
-- Five.Facts4 filled from the evaluations of Five.Gadgets and
-- Five.Sem.G4.  The facade's lemmas are used through the unapplied
-- module, so that their types and the record's name the gadgets alike.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)

module Examples.Groups.Clifford+CS.Five.Facts4Inst (c4 : Complete 4) where

open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; kpp ; krot ; kki)
open import Examples.Groups.Clifford+CS.Five.Sem.G4 using (g4-pp ; g4-rot ; g4-ki)
open import Examples.Groups.Clifford+CS.Five.Gadgets.Words using (G-pp ; G-rot ; G-ki)
import Examples.Groups.Clifford+CS.Five.Gadgets as GD

facts4 : Facts4
facts4 = record
  { G       = λ { kpp → G-pp ; krot → G-rot ; kki → G-ki }
  ; G⁻      = λ { kpp → GD.G-pp⁻ c4 ; krot → GD.G-rot⁻ c4 ; kki → GD.G-ki⁻ c4 }
  ; inv     = λ { kpp → GD.pp-inv c4 ; krot → GD.rot-inv c4 ; kki → GD.ki-inv c4 }
  ; inv′    = λ { kpp → GD.pp-inv′ c4 ; krot → GD.rot-inv′ c4 ; kki → GD.ki-inv′ c4 }
  ; sem     = λ { kpp → g4-pp ; krot → g4-rot ; kki → g4-ki }
  ; cx₀     = λ { kpp → GD.pp-cx₀ c4 ; krot → GD.rot-cx₀ c4 ; kki → GD.ki-cx₀ c4 }
  ; cx₁     = λ { kpp → GD.pp-cx₁ c4 ; krot → GD.rot-cx₁ c4 ; kki → GD.ki-cx₁ c4 }
  ; cx₂     = λ { kpp → GD.pp-cx₂ c4 ; krot → GD.rot-cx₂ c4 ; kki → GD.ki-cx₂ c4 }
  ; sw₁     = λ { kpp → GD.pp-sw₁ c4 ; krot → GD.rot-sw₁ c4 ; kki → GD.ki-sw₁ c4 }
  ; sw₂     = λ { kpp → GD.pp-sw₂ c4 ; krot → GD.rot-sw₂ c4 ; kki → GD.ki-sw₂ c4 }
  ; s₁-rot  = GD.rot-s₁ c4
  ; s₁-ki   = GD.ki-s₁ c4
  ; cs-rot  = GD.rot-cs c4
  ; cs-ki   = GD.ki-cs c4
  ; dec-pp⁻ = GD.dec-pp⁻ c4
  ; dec-ki⁻ = GD.dec-ki⁻ c4
  ; dec-rot = GD.dec-rot c4
  }
