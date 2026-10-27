/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointChordTransfer
public import PseudoPrime.LLS.OddEndpointTwoCostPolynomial

/-! # Two-sided logarithmic windows for odd-prime endpoint certificates -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The window polynomial retains a lower logarithm z in the full endpoint
polynomial and an upper logarithm u in both odd-prime costs. Inputs L,P,y,c
are the conductor level, pi bound, radius and nonnegative reciprocal cost.
Its positivity will certify the actual endpoint whenever z<=log y<=u. -/
noncomputable def oddEndpointLogWindowPolynomial (L P y z u c : ℝ) : ℝ :=
  fullEndpointPolynomial L P y z - (2 * y + 2 * u + 2) * c * y ^ 2 - (y - 1) ^ 2 * (2 * u ^ 2)

/-- For y>=1, L<=3y/2, P>=0 and c>=0, a nonnegative logarithmic window
z<=log y<=u gives a lower bound for the odd-prime endpoint polynomial with
logarithmic cost 2(log y)^2. Use monotonicity of the full polynomial and
bound the two arithmetic costs separately. This supports affine certificates. -/
theorem oddEndpointLogWindowPolynomial_le {L P y z u c : ℝ} (hy : 1 ≤ y) (hL : L ≤ (3 / 2 : ℝ) * y)
    (hP : 0 ≤ P) (hc : 0 ≤ c) (hz : 0 ≤ z) (hzlog : z ≤ Real.log y) (hlogu : Real.log y ≤ u) :
    oddEndpointLogWindowPolynomial L P y z u c ≤
      oddEndpointTwoCostPolynomial L P y (Real.log y) c (2 * (Real.log y) ^ 2) := by
  have hp := fullEndpointPolynomial_mono_log_of_level_bound hy hL hP hz hzlog
  have hlog : 0 ≤ Real.log y := hz.trans hzlog
  have hsq : (Real.log y) ^ 2 ≤ u ^ 2 := by nlinarith only [hlog, hlogu]
  have hcost := mul_nonneg (sub_nonneg.mpr hlogu) (mul_nonneg hc (sq_nonneg y))
  have hdefect := mul_nonneg (sq_nonneg (y - 1)) (sub_nonneg.mpr hsq)
  dsimp only [oddEndpointLogWindowPolynomial, oddEndpointTwoCostPolynomial]
  nlinarith only [hp, hcost, hdefect]

end PseudoPrime.LLS.PaperStatements
