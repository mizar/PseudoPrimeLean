/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100BlockSums
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Block01
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Block02
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Block03
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Block04
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Block05
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Block06
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Block07
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Block08
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Correction

/-! # Combined finite approximation at the twenty-ninth lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The rotated rational finite approximation at `101203/1024` is below `-49036/100000000`.
Eight independently checked blocks and the correction are added using their exact decomposition. -/
theorem endpoint029_finite_upper :
    (endpointRotatedFinite (101203 / 1024)).1 < (-49036 / 100000000 : ℚ) := by
  have h1 := endpoint029_block01.2
  have h2 := endpoint029_block02.2
  have h3 := endpoint029_block03.2
  have h4 := endpoint029_block04.2
  have h5 := endpoint029_block05.2
  have h6 := endpoint029_block06.2
  have h7 := endpoint029_block07.2
  have h8 := endpoint029_block08.2
  have h9 := endpoint029_correction.2
  rw [endpointRotatedFinite, endpoint_finite_blocks]
  simp only [endpoint_rotated_add]
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
