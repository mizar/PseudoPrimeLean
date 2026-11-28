/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSignedBoundary570
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiPrefix632

/-! # Signed principal boundary bounds for the five comparisons through logarithm 632 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed principal boundary lower bound on the radius interval [313, 1568 / 5]. -/
theorem quarter_psi_boundary_3136 {r : ℝ} (hl : 313 ≤ r) (hu : r ≤ 1568 / 5) :
    4 * 0.09105 * (-28.592) / (313) ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  exact
    cutoff_boundary_neg_570 (by norm_num only) hl (by norm_num only) (quarter_psi_signed_3136 hl hu)

/-- The signed principal boundary lower bound on the radius interval [1568 / 5, 314]. -/
theorem quarter_psi_boundary_314 {r : ℝ} (hl : 1568 / 5 ≤ r) (hu : r ≤ 314) :
    4 * 0.09105 * (-20.120) / (1568 / 5) ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  exact
    cutoff_boundary_neg_570 (by norm_num only) hl (by norm_num only) (quarter_psi_signed_314 hl hu)

/-- The signed principal boundary lower bound on the radius interval [314, 6289 / 20]. -/
theorem quarter_psi_boundary_31445 {r : ℝ} (hl : 314 ≤ r) (hu : r ≤ 6289 / 20) :
    4 * 0.09105 * (-23.6745) / (314) ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  exact
    cutoff_boundary_neg_570 (by norm_num only) hl (by norm_num only)
      (quarter_psi_signed_31445 hl hu)

/-- The signed principal boundary lower bound on the radius interval [6289 / 20, 315]. -/
theorem quarter_psi_boundary_315 {r : ℝ} (hl : 6289 / 20 ≤ r) (hu : r ≤ 315) :
    4 * 0.09105 * (-9.170) / (6289 / 20) ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  exact
    cutoff_boundary_neg_570 (by norm_num only) hl (by norm_num only) (quarter_psi_signed_315 hl hu)

/-- The signed principal boundary lower bound on the radius interval [315, 316]. -/
theorem quarter_psi_boundary_316 {r : ℝ} (hl : 315 ≤ r) (hu : r ≤ 316) :
    4 * 0.09104 * (10.585) / (316) ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  exact
    cutoff_boundary_pos_570 (by linarith only [hl]) hu (by norm_num only)
      (quarter_psi_signed_316 hl hu)

end PseudoPrime.PrimeTestBounds.MillerRabin
