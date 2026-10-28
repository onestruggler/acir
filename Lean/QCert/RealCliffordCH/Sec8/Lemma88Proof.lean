/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Section 8: Lemma 8.8

The decoding maps each rule of Figure 8 to a derivable equation (Appendix
E.5), rule by rule (`E/Cheap`, `E/Rules1`, `E/Rule22`, `E/Rule24`, `E/Rule32`).
Still open: (31), (36)–(40), (43)–(46).
-/
import QCert.RealCliffordCH.Sec8.Statement
import QCert.RealCliffordCH.Sec8.E.Rule24

namespace QCert.RealCliffordCH.Sec8

/-- Lemma 8.8 (Appendix E.5, with Appendix D).  The rules (31), (36)–(40)
and (43)–(46) are not yet proved. -/
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
  | r31 a c ha hc hca hca1 => sorry
  | r32 a b hab hb => exact E.dec32 ih' a b hab hb
  | r33 a b ha hb hab => rw [E.dec33 a b ha hb hab]
  | r34 a b c d ha hb hc hd hab hcd => rw [E.dec34 a b c d ha hb hc hd hab hcd]
  | r35 a b c d ha hb hc hd hd4 hp => rw [E.dec35 hn a b c d ha hb hc hd hd4 hp]
  | r36 a b c d u w ha hb hc hd hd4 hp => sorry
  | r37 a b c d u w ha hb hc hd hd4 hp => sorry
  | r38 a h4 ha => sorry
  | r39 => sorry
  | r40 => sorry
  | r41 => exact E.dec41 ih'
  | r42 a b c d ha hb hc hd hab hcd h3 => rw [E.dec42 hn a b c d ha hb hc hd hab hcd h3]
  | r43 => sorry
  | r44 => sorry
  | r45 => sorry
  | r46 => sorry

end QCert.RealCliffordCH.Sec8
