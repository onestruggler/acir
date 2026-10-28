/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E: moving equations of multi-controlled gates to any wires

The equations of Appendix D are stated at a canonical position (box wire
`0`, …).  The paper uses them on any wires, the network being irrelevant
in a PROP; here a swap network `μ` conjugates (`Net.placedBy N μ`) every
multi-controlled gate into another one (`placedBy_mc`), its wire `q` going
to `pos μ.reverse q`, so an equation between products of such gates moves
along any network (`placedBy_drawn`, `placedBy_cong`).

* `McSwapAll N`: naturality of `mc` for one swap, at any wires.  `Net.mc_swap`
  is the case where the two wires are not both controls; the other case
  needs (307), (313), (353) and is supplied by package (v).  Every lemma
  that moves gates across controls takes it as a hypothesis.
* `frame`: with `μ` the network of `placeG` for the wires `ps` and
  `π = pos μ.reverse` (so `π i = ps[i]`), `placedBy μ (mc K tg (c ∘ π))` is
  `mc K (tg.map π) c`: the canonical statement at the colouring `c ∘ π`
  gives the statement on the wires `ps`.
* `recolour`: `X` on several control wires on both sides exchanges their
  colours (Equation (81), iterated).
-/
import QCert.RealCliffordCH.Sec8.E.TransportCore
import QCert.RealCliffordCH.Sec8.D.N15

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-- Naturality of `mc` for one swap at any wires, from completeness below `N`
and the symmetries (307), (313), (353) of the canonical gates (Net's
`mc_swap_sym`; at a width below `N` they are the same equations there). -/
theorem mcSwapAll {N : ℕ} (ih : IH N) : McSwapAll N :=
  mcSwapOf ih fun k hk h3 a j hj1 hj2 => D.eq353 (k + 1) h3 (ih.mono hk) a j hj1 hj2

end QCert.RealCliffordCH.Sec8.E
