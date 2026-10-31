/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPoleKernel
public import PseudoPrime.Analysis.RationalPoleMajorant

/-! # Fixed-node majorant for the LLS fourth-order rational-pole kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The fourth-order candidate at a=13/25 has exact critical-line norm
rho^3/(rho^2+t^2)^2, rho=25/26. Normalize the general norm formula by rational
algebra. The exponential shift does not affect this whole-height identity. -/
theorem norm_rationalPole_four (c t : ℝ) :
    ‖Analysis.rationalPoleFunction 2 (13 / 25) c (Complex.I * t)‖ =
      (25 / 26 : ℝ) ^ 3 / ((25 / 26 : ℝ) ^ 2 + t ^ 2) ^ 2 := by
  rw [Analysis.norm_rationalPoleFunction 2 (by norm_num only : (0 : ℝ) < 13 / 25)]
  have h : (25 / 26 : ℝ) ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t))
  have hd : 1 + (2 * (13 / 25 : ℝ) * t) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg _))
  apply (div_eq_div_iff (pow_ne_zero 2 hd) (pow_ne_zero 2 h)).mpr
  ring

/-- The left Poisson distance 1237/1300 is rho-1/100, with rho=25/26.
It exceeds one half and is smaller than the right distance. This fixed rational
node is shared by the height majorant and the actual zero-series consumer. -/
noncomputable abbrev poleFourAlpha : ℝ :=
  1237 / 1300

/-- The right Poisson distance 1578581/1625000 is the perturbed companion to alpha.
The two rational distances meet the sum-of-squares and product constraints needed
for the fourth-order majorant. No parameter search is used in the formal certificate. -/
noncomputable abbrev poleFourBeta : ℝ :=
  1578581 / 1625000

/-- The positive coefficient of the left Poisson profile, rho^3/(alpha(beta^2-alpha^2)).
Together with poleFourLowerWeight it represents the product majorant exactly and
retains cancellation between the two Euler evaluations. -/
noncomputable def poleFourUpperWeight : ℝ :=
  (25 / 26 : ℝ) ^ 3 / (poleFourAlpha * (poleFourBeta ^ 2 - poleFourAlpha ^ 2))

/-- The magnitude of the negative right-node coefficient,
rho^3/(beta(beta^2-alpha^2)). It is positive and less than the upper weight.
The zero-mass consumer subtracts this node rather than estimating its absolute value. -/
noncomputable def poleFourLowerWeight : ℝ :=
  (25 / 26 : ℝ) ^ 3 / (poleFourBeta * (poleFourBeta ^ 2 - poleFourAlpha ^ 2))

/-- The fixed two nodes are right of one half and ordered, with nonnegative lower
weight at most the upper weight. Exact rational normalization proves all conditions.
These are the sign and evaluation-domain inputs to the paired Euler API. -/
theorem poleFour_node_data :
    1 / 2 < poleFourAlpha ∧
      poleFourAlpha < poleFourBeta ∧
      0 ≤ poleFourLowerWeight ∧ poleFourLowerWeight ≤ poleFourUpperWeight := by
  norm_num only [poleFourAlpha, poleFourBeta, poleFourUpperWeight, poleFourLowerWeight, and_self]

/-- For every shift c and real height t, the fourth-order norm is bounded by the
fixed signed Poisson difference. The rational node certificate covers all heights.
This is the actual analytic majorant, independent of Mellin admissibility. -/
theorem norm_poleFour_le_poisson (c t : ℝ) :
    ‖Analysis.rationalPoleFunction 2 (13 / 25) c (Complex.I * t)‖ ≤
      Analysis.poissonDifferenceWeight poleFourAlpha poleFourBeta poleFourUpperWeight
        poleFourLowerWeight t := by
  rw [norm_rationalPole_four, poleFourUpperWeight, poleFourLowerWeight, ←
    Analysis.pole_product_eq_poisson_difference (ρ := (25 / 26 : ℝ))
      (by norm_num only : 0 < poleFourAlpha) poleFour_node_data.2.1]
  exact
    Analysis.pole_four_product_majorant (by norm_num only) (by norm_num only) poleFour_node_data.2.1
      (by norm_num only [poleFourAlpha, poleFourBeta])
      (by norm_num only [poleFourAlpha, poleFourBeta])

/-- The conductor coefficient in the two-node zero bound is exactly the stated
rational number, slightly larger than 1/4. Normalize the difference of node weights.
This concerns the majorant coefficient, not yet the actual Mellin mass. -/
theorem poleFour_majorant_coefficient :
    (poleFourUpperWeight - poleFourLowerWeight) / 2 =
      (1525878906250000 / 6101872171031207 : ℝ) := by
  norm_num only [poleFourUpperWeight, poleFourLowerWeight, poleFourAlpha, poleFourBeta]

end PseudoPrime.LLS.PaperStatements
