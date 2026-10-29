/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: Lemma 8.8

The decoding maps each rule of Figure 8 to a derivable equation (Appendix
E.5), rule by rule (`E/Cheap`, `E/Rules1`, `E/Rule22`, `E/Rule24`, `E/Rule32`, `E/Rule38`,
`E/Rule39`, `E/Rule40`, `E/Rule31`, `E/Rule43`, `E/Rule44`, `E/Rule3637`).
Still open: (45), (46).
-/
import QCert.RealCliffordCH.Sec8.Statement
import QCert.RealCliffordCH.Sec8.E.Rule38
import QCert.RealCliffordCH.Sec8.E.Rule31
import QCert.RealCliffordCH.Sec8.E.Rule43
import QCert.RealCliffordCH.Sec8.E.Rule3637
import QCert.RealCliffordCH.Sec8.E.Rule45

namespace QCert.RealCliffordCH.Sec8

/-- Lemma 8.8 (Appendix E.5, with Appendix D).  The rules (45) and (46) are
not yet proved. -/
theorem lemma_8_8 (n : ℕ) (hn : 3 ≤ n) : Lemma88 n := by
  intro ih u v h
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 3 := ⟨n - 3, by omega⟩
  have ih' : IH (M + 3) := ih
  cases h with
  | r20 a ha => rw [E.dec20 a ha]
  | r21 a b ha hb => rw [E.dec21 a b ha hb]
  | r22 a b c ha hb hc => exact E.dec22 ih' a b c ha hb hc
  | r23 a ha => exact E.dec23 ih' a ha
  | r24 a ha => exact E.dec24 ih' a ha
  | r25 a c hac hc hodd => rw [E.dec25 a c hac hc hodd]
  | r26 a c hac hc hodd => rw [E.dec26 a c hac hc hodd]
  | r27 a c hac hc heven => rw [E.dec27 a c hac hc heven]
  | r28 a c hac hc heven => rw [E.dec28 a c hac hc heven]
  | r29 a ha => exact E.dec29 ih' a ha
  | r30 a b c hb ha hc hab hca hcb => rw [E.dec30 a b c hb ha hc hab hca hcb]
  | r31 a c ha hc hca hca1 => exact E.dec31 ih' a c ha hc hca hca1
  | r32 a b hab hb => exact E.dec32 ih' a b hab hb
  | r33 a b ha hb hab => rw [E.dec33 a b ha hb hab]
  | r34 a b c d ha hb hc hd hab hcd => rw [E.dec34 a b c d ha hb hc hd hab hcd]
  | r35 a b c d ha hb hc hd hd4 hp => rw [E.dec35 hn a b c d ha hb hc hd hd4 hp]
  | r36 a b c d u w ha hb hc hd hd4 hp => exact E.dec36 ih' a b c d u w ha hb hc hd hd4 hp
  | r37 a b c d u w ha hb hc hd hd4 hp => exact E.dec37 ih' a b c d u w ha hb hc hd hd4 hp
  | r38 a h4 ha => exact E.dec38 ih' a h4 ha
  | r39 => exact E.dec39 ih'
  | r40 => exact E.dec40 ih'
  | r41 => exact E.dec41 ih'
  | r42 a b c d ha hb hc hd hab hcd h3 => rw [E.dec42 hn a b c d ha hb hc hd hab hcd h3]
  | r43 => exact E.dec43 ih'
  | r44 => exact E.dec44 ih'
  | r45 => exact E.dec45_of sorry -- `E.Core45 M`: (146) with white controls above
  | r46 => sorry

end QCert.RealCliffordCH.Sec8
