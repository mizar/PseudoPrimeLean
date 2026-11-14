/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100BlockSums
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Block01
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Block02
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Block03
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Block04
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Block05
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Block06
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Block07
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Block08
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Correction

/-! # Combined finite approximation at the fourth lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The rotated rational finite approximation at `31155/1024` exceeds `9311/100000000`.
Eight independently checked blocks and the correction are added using their exact decomposition. -/
theorem endpoint004_finite_lower :
    (9311 / 100000000 : ℚ) ≤ (endpointRotatedFinite (31155 / 1024)).1 := by
  have h1 := endpoint004_block01.1
  have h2 := endpoint004_block02.1
  have h3 := endpoint004_block03.1
  have h4 := endpoint004_block04.1
  have h5 := endpoint004_block05.1
  have h6 := endpoint004_block06.1
  have h7 := endpoint004_block07.1
  have h8 := endpoint004_block08.1
  have h9 := endpoint004_correction.1
  rw [endpointRotatedFinite, endpoint_finite_blocks]
  simp only [endpoint_rotated_add]
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
