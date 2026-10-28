/-
Copyright (c) 2026 QCert contributors. All rights reserved.


# Appendices D.2–D.4: the fixed-width equations on wider circuits

`eqNNN m ih`: the equation `(NNN)` of `SmallDefs` on `K` wires, on the
bottom `K` wires of `m + K` wires, given completeness on fewer wires: by
Lemma 5.1 when `m ≥ 1` (`small_of`), by the derivation `dNNN` at width `K`
when `m = 0`.  The derivations are `W3` (package (i), D.2), `W4` (package
(ii), D.3) and `W5` (package (iii), D.4) of `PLAN.md`.
-/
import QCert.RealCliffordCH.Sec8.D.W3
import QCert.RealCliffordCH.Sec8.D.W4
import QCert.RealCliffordCH.Sec8.D.W5

namespace QCert.RealCliffordCH.Sec8.D

open Circuit

/-- (117) on the bottom 3 wires of `m + 3`. -/
theorem eq117 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l117)) (Circuit.pad m (r117)) :=
  small_of (sem_of_derivable (d117 (ih.mono (by omega)))) (d117) m ih

/-- (118) on the bottom 3 wires of `m + 3`. -/
theorem eq118 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l118)) (Circuit.pad m (r118)) :=
  small_of (sem_of_derivable (d118 (ih.mono (by omega)))) (d118) m ih

/-- (119) on the bottom 3 wires of `m + 3`. -/
theorem eq119 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l119)) (Circuit.pad m (r119)) :=
  small_of (sem_of_derivable (d119 (ih.mono (by omega)))) (d119) m ih

/-- (120) on the bottom 3 wires of `m + 3`. -/
theorem eq120 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l120)) (Circuit.pad m (r120)) :=
  small_of (sem_of_derivable (d120 (ih.mono (by omega)))) (d120) m ih

/-- (121) on the bottom 3 wires of `m + 3`. -/
theorem eq121 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l121)) (Circuit.pad m (r121)) :=
  small_of (sem_of_derivable (d121 (ih.mono (by omega)))) (d121) m ih

/-- (122) on the bottom 3 wires of `m + 3`. -/
theorem eq122 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l122)) (Circuit.pad m (r122)) :=
  small_of (sem_of_derivable (d122 (ih.mono (by omega)))) (d122) m ih

/-- (123) on the bottom 3 wires of `m + 3`. -/
theorem eq123 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l123)) (Circuit.pad m (r123)) :=
  small_of (sem_of_derivable (d123 (ih.mono (by omega)))) (d123) m ih

/-- (124) on the bottom 3 wires of `m + 3`. -/
theorem eq124 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l124)) (Circuit.pad m (r124)) :=
  small_of (sem_of_derivable (d124 (ih.mono (by omega)))) (d124) m ih

/-- (125) on the bottom 3 wires of `m + 3`. -/
theorem eq125 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l125)) (Circuit.pad m (r125)) :=
  small_of (sem_of_derivable (d125 (ih.mono (by omega)))) (d125) m ih

/-- (126) on the bottom 3 wires of `m + 3`. -/
theorem eq126 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l126)) (Circuit.pad m (r126)) :=
  small_of (sem_of_derivable (d126 (ih.mono (by omega)))) (d126) m ih

/-- (127) on the bottom 3 wires of `m + 3`. -/
theorem eq127 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l127)) (Circuit.pad m (r127)) :=
  small_of (sem_of_derivable (d127 (ih.mono (by omega)))) (d127) m ih

/-- (128) on the bottom 3 wires of `m + 3`. -/
theorem eq128 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l128)) (Circuit.pad m (r128)) :=
  small_of (sem_of_derivable (d128 (ih.mono (by omega)))) (d128) m ih

/-- (129) on the bottom 3 wires of `m + 3`. -/
theorem eq129 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l129)) (Circuit.pad m (r129)) :=
  small_of (sem_of_derivable (d129 (ih.mono (by omega)))) (d129) m ih

/-- (130) on the bottom 3 wires of `m + 3`. -/
theorem eq130 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l130)) (Circuit.pad m (r130)) :=
  small_of (sem_of_derivable (d130 (ih.mono (by omega)))) (d130) m ih

/-- (131) on the bottom 3 wires of `m + 3`. -/
theorem eq131 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l131)) (Circuit.pad m (r131)) :=
  small_of (sem_of_derivable (d131 (ih.mono (by omega)))) (d131) m ih

/-- (132) on the bottom 3 wires of `m + 3`. -/
theorem eq132 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l132)) (Circuit.pad m (r132)) :=
  small_of (sem_of_derivable (d132 (ih.mono (by omega)))) (d132) m ih

/-- (133) on the bottom 3 wires of `m + 3`. -/
theorem eq133 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l133)) (Circuit.pad m (r133)) :=
  small_of (sem_of_derivable (d133 (ih.mono (by omega)))) (d133) m ih

/-- (134) on the bottom 3 wires of `m + 3`. -/
theorem eq134 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l134)) (Circuit.pad m (r134)) :=
  small_of (sem_of_derivable (d134 (ih.mono (by omega)))) (d134) m ih

/-- (135) on the bottom 3 wires of `m + 3`. -/
theorem eq135 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l135)) (Circuit.pad m (r135)) :=
  small_of (sem_of_derivable (d135 (ih.mono (by omega)))) (d135) m ih

/-- (136) on the bottom 3 wires of `m + 3`. -/
theorem eq136 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l136)) (Circuit.pad m (r136)) :=
  small_of (sem_of_derivable (d136 (ih.mono (by omega)))) (d136) m ih

/-- (137) on the bottom 3 wires of `m + 3`. -/
theorem eq137 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l137)) (Circuit.pad m (r137)) :=
  small_of (sem_of_derivable (d137 (ih.mono (by omega)))) (d137) m ih

/-- (138) on the bottom 3 wires of `m + 3`. -/
theorem eq138 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l138)) (Circuit.pad m (r138)) :=
  small_of (sem_of_derivable (d138 (ih.mono (by omega)))) (d138) m ih

/-- (139) on the bottom 3 wires of `m + 3`. -/
theorem eq139 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l139)) (Circuit.pad m (r139)) :=
  small_of (sem_of_derivable (d139 (ih.mono (by omega)))) (d139) m ih

/-- (140) on the bottom 3 wires of `m + 3`. -/
theorem eq140 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l140)) (Circuit.pad m (r140)) :=
  small_of (sem_of_derivable (d140 (ih.mono (by omega)))) (d140) m ih

/-- (141) on the bottom 3 wires of `m + 3`. -/
theorem eq141 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l141)) (Circuit.pad m (r141)) :=
  small_of (sem_of_derivable (d141 (ih.mono (by omega)))) (d141) m ih

/-- (142) on the bottom 3 wires of `m + 3`. -/
theorem eq142 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l142)) (Circuit.pad m (r142)) :=
  small_of (sem_of_derivable (d142 (ih.mono (by omega)))) (d142) m ih

/-- (143) on the bottom 3 wires of `m + 3`. -/
theorem eq143 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l143)) (Circuit.pad m (r143)) :=
  small_of (sem_of_derivable (d143 (ih.mono (by omega)))) (d143) m ih

/-- (144) on the bottom 3 wires of `m + 3`. -/
theorem eq144 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l144)) (Circuit.pad m (r144)) :=
  small_of (sem_of_derivable (d144 (ih.mono (by omega)))) (d144) m ih

/-- (145) on the bottom 3 wires of `m + 3`. -/
theorem eq145 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l145)) (Circuit.pad m (r145)) :=
  small_of (sem_of_derivable (d145 (ih.mono (by omega)))) (d145) m ih

/-- (146) on the bottom 3 wires of `m + 3`. -/
theorem eq146 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l146)) (Circuit.pad m (r146)) :=
  small_of (sem_of_derivable (d146 (ih.mono (by omega)))) (d146) m ih

/-- (147) on the bottom 3 wires of `m + 3`. -/
theorem eq147 (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l147)) (Circuit.pad m (r147)) :=
  small_of (sem_of_derivable (d147 (ih.mono (by omega)))) (d147) m ih

/-- (148a) on the bottom 3 wires of `m + 3`. -/
theorem eq148a (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l148a)) (Circuit.pad m (r148a)) :=
  small_of (sem_of_derivable (d148a (ih.mono (by omega)))) (d148a) m ih

/-- (148b) on the bottom 3 wires of `m + 3`. -/
theorem eq148b (m : ℕ) (ih : IH (m + 3)) :
    Derivable (theory (m + 3)) (Circuit.pad m (l148b)) (Circuit.pad m (r148b)) :=
  small_of (sem_of_derivable (d148b (ih.mono (by omega)))) (d148b) m ih

/-- (157) on the bottom 4 wires of `m + 4`. -/
theorem eq157 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l157)) (Circuit.pad m (r157)) :=
  small_of (sem_of_derivable (d157 (ih.mono (by omega)))) (d157) m ih

/-- (160) on the bottom 4 wires of `m + 4`. -/
theorem eq160 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l160)) (Circuit.pad m (r160)) :=
  small_of (sem_of_derivable (d160 (ih.mono (by omega)))) (d160) m ih

/-- (168) on the bottom 4 wires of `m + 4`. -/
theorem eq168 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l168)) (Circuit.pad m (r168)) :=
  small_of (sem_of_derivable (d168 (ih.mono (by omega)))) (d168) m ih

/-- (172) on the bottom 4 wires of `m + 4`. -/
theorem eq172 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l172)) (Circuit.pad m (r172)) :=
  small_of (sem_of_derivable (d172 (ih.mono (by omega)))) (d172) m ih

/-- (173) on the bottom 4 wires of `m + 4`. -/
theorem eq173 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l173)) (Circuit.pad m (r173)) :=
  small_of (sem_of_derivable (d173 (ih.mono (by omega)))) (d173) m ih

/-- (174) on the bottom 4 wires of `m + 4`. -/
theorem eq174 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l174)) (Circuit.pad m (r174)) :=
  small_of (sem_of_derivable (d174 (ih.mono (by omega)))) (d174) m ih

/-- (209) on the bottom 4 wires of `m + 4`. -/
theorem eq209 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l209)) (Circuit.pad m (r209)) :=
  small_of (sem_of_derivable (d209 (ih.mono (by omega)))) (d209) m ih

/-- (214) on the bottom 4 wires of `m + 4`. -/
theorem eq214 (a : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l214 a)) (Circuit.pad m (r214 a)) :=
  small_of (sem_of_derivable (d214 a (ih.mono (by omega)))) (d214 a) m ih

/-- (215) on the bottom 4 wires of `m + 4`. -/
theorem eq215 (a : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l215 a)) (Circuit.pad m (r215 a)) :=
  small_of (sem_of_derivable (d215 a (ih.mono (by omega)))) (d215 a) m ih

/-- (216) on the bottom 4 wires of `m + 4`. -/
theorem eq216 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l216)) (Circuit.pad m (r216)) :=
  small_of (sem_of_derivable (d216 (ih.mono (by omega)))) (d216) m ih

/-- (217) on the bottom 4 wires of `m + 4`. -/
theorem eq217 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l217)) (Circuit.pad m (r217)) :=
  small_of (sem_of_derivable (d217 (ih.mono (by omega)))) (d217) m ih

/-- (218) on the bottom 4 wires of `m + 4`. -/
theorem eq218 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l218)) (Circuit.pad m (r218)) :=
  small_of (sem_of_derivable (d218 (ih.mono (by omega)))) (d218) m ih

/-- (219) on the bottom 4 wires of `m + 4`. -/
theorem eq219 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l219)) (Circuit.pad m (r219)) :=
  small_of (sem_of_derivable (d219 (ih.mono (by omega)))) (d219) m ih

/-- (220) on the bottom 4 wires of `m + 4`. -/
theorem eq220 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l220)) (Circuit.pad m (r220)) :=
  small_of (sem_of_derivable (d220 (ih.mono (by omega)))) (d220) m ih

/-- (221) on the bottom 4 wires of `m + 4`. -/
theorem eq221 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l221)) (Circuit.pad m (r221)) :=
  small_of (sem_of_derivable (d221 (ih.mono (by omega)))) (d221) m ih

/-- (222) on the bottom 4 wires of `m + 4`. -/
theorem eq222 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l222)) (Circuit.pad m (r222)) :=
  small_of (sem_of_derivable (d222 (ih.mono (by omega)))) (d222) m ih

/-- (223) on the bottom 4 wires of `m + 4`. -/
theorem eq223 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l223)) (Circuit.pad m (r223)) :=
  small_of (sem_of_derivable (d223 (ih.mono (by omega)))) (d223) m ih

/-- (224) on the bottom 4 wires of `m + 4`. -/
theorem eq224 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l224)) (Circuit.pad m (r224)) :=
  small_of (sem_of_derivable (d224 (ih.mono (by omega)))) (d224) m ih

/-- (225) on the bottom 4 wires of `m + 4`. -/
theorem eq225 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l225)) (Circuit.pad m (r225)) :=
  small_of (sem_of_derivable (d225 (ih.mono (by omega)))) (d225) m ih

/-- (226) on the bottom 4 wires of `m + 4`. -/
theorem eq226 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l226)) (Circuit.pad m (r226)) :=
  small_of (sem_of_derivable (d226 (ih.mono (by omega)))) (d226) m ih

/-- (227) on the bottom 4 wires of `m + 4`. -/
theorem eq227 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l227)) (Circuit.pad m (r227)) :=
  small_of (sem_of_derivable (d227 (ih.mono (by omega)))) (d227) m ih

/-- (228) on the bottom 4 wires of `m + 4`. -/
theorem eq228 (β : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l228 β)) (Circuit.pad m (r228 β)) :=
  small_of (sem_of_derivable (d228 β (ih.mono (by omega)))) (d228 β) m ih

/-- (229) on the bottom 4 wires of `m + 4`. -/
theorem eq229 (a : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l229 a)) (Circuit.pad m (r229 a)) :=
  small_of (sem_of_derivable (d229 a (ih.mono (by omega)))) (d229 a) m ih

/-- (230) on the bottom 4 wires of `m + 4`. -/
theorem eq230 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l230)) (Circuit.pad m (r230)) :=
  small_of (sem_of_derivable (d230 (ih.mono (by omega)))) (d230) m ih

/-- (231) on the bottom 4 wires of `m + 4`. -/
theorem eq231 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l231)) (Circuit.pad m (r231)) :=
  small_of (sem_of_derivable (d231 (ih.mono (by omega)))) (d231) m ih

/-- (232) on the bottom 4 wires of `m + 4`. -/
theorem eq232 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l232)) (Circuit.pad m (r232)) :=
  small_of (sem_of_derivable (d232 (ih.mono (by omega)))) (d232) m ih

/-- (233) on the bottom 4 wires of `m + 4`. -/
theorem eq233 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l233)) (Circuit.pad m (r233)) :=
  small_of (sem_of_derivable (d233 (ih.mono (by omega)))) (d233) m ih

/-- (234) on the bottom 4 wires of `m + 4`. -/
theorem eq234 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l234)) (Circuit.pad m (r234)) :=
  small_of (sem_of_derivable (d234 (ih.mono (by omega)))) (d234) m ih

/-- (235) on the bottom 4 wires of `m + 4`. -/
theorem eq235 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l235)) (Circuit.pad m (r235)) :=
  small_of (sem_of_derivable (d235 (ih.mono (by omega)))) (d235) m ih

/-- (236) on the bottom 4 wires of `m + 4`. -/
theorem eq236 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l236)) (Circuit.pad m (r236)) :=
  small_of (sem_of_derivable (d236 (ih.mono (by omega)))) (d236) m ih

/-- (237) on the bottom 4 wires of `m + 4`. -/
theorem eq237 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l237)) (Circuit.pad m (r237)) :=
  small_of (sem_of_derivable (d237 (ih.mono (by omega)))) (d237) m ih

/-- (238) on the bottom 4 wires of `m + 4`. -/
theorem eq238 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l238)) (Circuit.pad m (r238)) :=
  small_of (sem_of_derivable (d238 (ih.mono (by omega)))) (d238) m ih

/-- (239) on the bottom 4 wires of `m + 4`. -/
theorem eq239 (a : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l239 a γ)) (Circuit.pad m (r239 a γ)) :=
  small_of (sem_of_derivable (d239 a γ (ih.mono (by omega)))) (d239 a γ) m ih

/-- (240) on the bottom 4 wires of `m + 4`. -/
theorem eq240 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (δ : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l240 a α b β δ γ)) (Circuit.pad m (r240 a α b β δ γ)) :=
  small_of (sem_of_derivable (d240 a α b β δ γ (ih.mono (by omega)))) (d240 a α b β δ γ) m ih

/-- (241) on the bottom 4 wires of `m + 4`. -/
theorem eq241 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (δ : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l241 a α b β δ γ)) (Circuit.pad m (r241 a α b β δ γ)) :=
  small_of (sem_of_derivable (d241 a α b β δ γ (ih.mono (by omega)))) (d241 a α b β δ γ) m ih

/-- (242) on the bottom 4 wires of `m + 4`. -/
theorem eq242 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (δ : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l242 a α b β δ γ)) (Circuit.pad m (r242 a α b β δ γ)) :=
  small_of (sem_of_derivable (d242 a α b β δ γ (ih.mono (by omega)))) (d242 a α b β δ γ) m ih

/-- (243) on the bottom 4 wires of `m + 4`. -/
theorem eq243 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (δ : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l243 a α b β δ γ)) (Circuit.pad m (r243 a α b β δ γ)) :=
  small_of (sem_of_derivable (d243 a α b β δ γ (ih.mono (by omega)))) (d243 a α b β δ γ) m ih

/-- (244) on the bottom 4 wires of `m + 4`. -/
theorem eq244 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l244 a α b β)) (Circuit.pad m (r244 a α b β)) :=
  small_of (sem_of_derivable (d244 a α b β (ih.mono (by omega)))) (d244 a α b β) m ih

/-- (245) on the bottom 4 wires of `m + 4`. -/
theorem eq245 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l245 a α b β)) (Circuit.pad m (r245 a α b β)) :=
  small_of (sem_of_derivable (d245 a α b β (ih.mono (by omega)))) (d245 a α b β) m ih

/-- (246) on the bottom 4 wires of `m + 4`. -/
theorem eq246 (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l246)) (Circuit.pad m (r246)) :=
  small_of (sem_of_derivable (d246 (ih.mono (by omega)))) (d246) m ih

/-- (247) on the bottom 4 wires of `m + 4`. -/
theorem eq247 (a : Bool) (α : Bool) (β : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l247 a α β γ)) (Circuit.pad m (r247 a α β γ)) :=
  small_of (sem_of_derivable (d247 a α β γ (ih.mono (by omega)))) (d247 a α β γ) m ih

/-- (248) on the bottom 4 wires of `m + 4`. -/
theorem eq248 (a : Bool) (α : Bool) (β : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 4)) :
    Derivable (theory (m + 4)) (Circuit.pad m (l248 a α β γ)) (Circuit.pad m (r248 a α β γ)) :=
  small_of (sem_of_derivable (d248 a α β γ (ih.mono (by omega)))) (d248 a α β γ) m ih

/-- (267) on the bottom 5 wires of `m + 5`. -/
theorem eq267 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (Circuit.pad m (l267 a α b β γ)) (Circuit.pad m (r267 a α b β γ)) :=
  small_of (sem_of_derivable (d267 a α b β γ (ih.mono (by omega)))) (d267 a α b β γ) m ih

/-- (268) on the bottom 5 wires of `m + 5`. -/
theorem eq268 (a : Bool) (α : Bool) (b : Bool) (β : Bool) (γ : Bool) (m : ℕ) (ih : IH (m + 5)) :
    Derivable (theory (m + 5)) (Circuit.pad m (l268 a α b β γ)) (Circuit.pad m (r268 a α b β γ)) :=
  small_of (sem_of_derivable (d268 a α b β γ (ih.mono (by omega)))) (d268 a α b β γ) m ih

end QCert.RealCliffordCH.Sec8.D
