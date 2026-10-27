/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapFullEndpoint

/-! # Uniform conductor comparison for full-prime endpoint separation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive h,x>=1,Y>=64 and 0<q<=N, the full-prime scalar separation
at conductor q is at most the same expression at N. The reciprocal mass cap
is monotone in log q, and the endpoint-budget coefficients are nonnegative.
This replaces a condition over all possible conductors by one original-level test. -/
theorem reciprocalGapFullEndpointSeparation_mono_level {h x Y : ℝ} (hh : 0 < h) (hx : 1 ≤ x)
    (hY : 64 ≤ Y) {q N : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    reciprocalGapFullEndpointSeparation h q x Y ≤ reciprocalGapFullEndpointSeparation h N x Y := by
  have hy0 : 0 < Y := by linarith only [hY]
  have hy1 : 1 ≤ Y := by linarith only [hY]
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / Y) :=
    mul_nonneg (by norm_num only) (sub_nonneg.mpr ((div_le_one hy0).mpr hy1))
  have hl := Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqN)
  have hm :
    reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ)) ≤
      reciprocalGapReciprocalMassCap N Y (Real.log Y - (31551 / 20000 : ℝ)) := by
    unfold reciprocalGapReciprocalMassCap
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact
      sub_le_sub_right
        (sub_le_sub_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hl (Real.log Real.pi)) hcoef)
          (1 / 4))
        _
  have hD := reciprocalGapLogQuotient_nonneg hh hx
  have hc : 0 ≤ (reciprocalGapLogQuotient h x + 2) / (1 + 2 * h) :=
    div_nonneg (by linarith only [hD]) (by linarith only [hh])
  have hb :
    reciprocalGapEndpointMassBudget h q x
        (reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))) ≤
      reciprocalGapEndpointMassBudget h N x
        (reciprocalGapReciprocalMassCap N Y (Real.log Y - (31551 / 20000 : ℝ))) := by
    unfold reciprocalGapEndpointMassBudget
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg x)
    exact
      add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hD) (by norm_num only))
        (mul_le_mul_of_nonneg_left hm hc)
  dsimp only [reciprocalGapFullEndpointSeparation]
  linarith only [hm, hb]

end PseudoPrime.LLS.PaperStatements
