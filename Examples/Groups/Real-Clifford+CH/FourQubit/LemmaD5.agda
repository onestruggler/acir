------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma D.5 of Clément's paper: the ninety-nine auxiliary equations on
-- four qubits, Equations (150)–(248), from completeness on two and three
-- qubits.  Typechecking this module checks all of Appendix D.3.
--
-- An equation with several instances carries a suffix: eq228₁/eq228₀ and
-- eq239₁/eq239₀ by the colour of a control, a prime for the mirrored or
-- inverse statement.  The families with parametrised colours, (240)–(245)
-- and (248), are stated over Bool, black being true.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.LemmaD5
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃ public
  using (eq150 ; eq151 ; eq152 ; eq153)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃ public
  using (eq154 ; eq155 ; eq156 ; eq157 ; eq158 ; eq159 ; eq160 ; eq161 ; eq162 ; eq163
       ; eq165 ; eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃ public
  using (eq164 ; eq167 ; eq168 ; eq169 ; eq170 ; eq170′ ; eq171 ; eq171′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃ public
  using (eq172 ; eq173 ; eq174 ; eq175 ; eq176 ; eq177 ; eq178)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ public
  using (eq179 ; eq180)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃ public
  using (eq181)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃ public
  using (eq182 ; eq183 ; eq184 ; eq185 ; eq186 ; eq187 ; eq188 ; eq189 ; eq190)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃ public
  using (eq191 ; eq192 ; eq193 ; eq194 ; eq195 ; eq196 ; eq197 ; eq198 ; eq199 ; eq200)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃ public
  using (eq201 ; eq202)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃ public
  using (eq203 ; eq204 ; eq205 ; eq206 ; eq207)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ public
  using (eq208 ; eq208′ ; eq209 ; eq210 ; eq211 ; eq212 ; eq213 ; eq214 ; eq214′ ; eq215 ; eq215′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃ public
  using (eq216 ; eq217 ; eq218)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃ public
  using (eq219 ; eq220 ; eq221 ; eq221′ ; eq222 ; eq223 ; eq223′ ; eq224 ; eq225 ; eq226)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PConjugates complete₂ complete₃ public
  using (eq227 ; eq228₁ ; eq228₀)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations4 complete₂ complete₃ public
  using (eq229 ; eq229′ ; eq230 ; eq231 ; eq232 ; eq233)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations5 complete₂ complete₃ public
  using (eq234 ; eq235 ; eq236 ; eq237 ; eq238)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families complete₂ complete₃ public
  using (eq239₁ ; eq239₁′ ; eq239₀ ; eq239₀′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃ public
  using (eq240)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃ public
  using (eq241)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies242 complete₂ complete₃ public
  using (eq242)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies243 complete₂ complete₃ public
  using (eq243)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies244 complete₂ complete₃ public
  using (eq244)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies245 complete₂ complete₃ public
  using (eq245)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃ public
  using (eq246)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies247 complete₂ complete₃ public
  using (eq247 ; eq248)
