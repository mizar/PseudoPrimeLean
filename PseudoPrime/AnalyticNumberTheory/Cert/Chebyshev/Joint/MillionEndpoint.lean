/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.CheckedCell
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.AdvanceSound

/-! # Closing the right endpoint of the joint finite estimate -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The terminal cursor and its four integer bounds before consuming one million. -/
def millionEdge : Edge :=
  ⟨1000000, 999586518104918955, 999593238652839812, 1102422326452684, 1102435268224133⟩

/-- Validity of the outgoing state gives both endpoint estimates. One million has
two distinct prime divisors, so consuming it leaves the prefix unchanged. -/
theorem million_endpoint (hs : Valid millionEdge) :
    |Chebyshev.psi 1000000 - 1000000| ≤ (4 / 5 : ℝ) * Real.sqrt 1000000 ∧
      |Chebyshev.theta 1000000 - 1000000| ≤ (97 / 50 : ℝ) * Real.sqrt 1000000 := by
  have hprev :
    Prefix 999999 millionEdge.psiLo millionEdge.psiHi millionEdge.powerLo millionEdge.powerHi :=
    hs.2
  have hn : ¬IsPrimePow (999999 + 1 : ℕ) := by decide +kernel
  have hp := prefix_other hprev hn (fun h ↦ hn h.isPrimePow)
  have hg :
    cellCheck 1000000 1000001 4 5 millionEdge.psiLo (millionEdge.psiLo - millionEdge.powerLo)
        millionEdge.psiHi millionEdge.powerHi =
      true := by
    decide +kernel
  have hb :=
    cellCheck_sound (a := 1000000) (b := 1000001) (x := 1000000) hp hp (by decide)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) hg
  exact ⟨hb.1, hb.2 (by decide) le_rfl⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
