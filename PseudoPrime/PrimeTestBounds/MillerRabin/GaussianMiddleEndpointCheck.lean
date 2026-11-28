/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualInputs
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualProfile

/-! # Interval arithmetic for the direct middle endpoints -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A nonnegative upper endpoint for a row at a rational offset. -/
@[expose]
public def middleRowUpper (A : MiddleIntRow) (N : ℕ) (u v : ℤ) : ℚ :=
  (max 0 (A.evalInterval N u v).upper : ℤ) / (A.den : ℚ)

/-- The outward integer Horner evaluation bounds its analytic polynomial. -/
public theorem middle_row_upper_le (A : MiddleIntRow) (N : ℕ) (u v : ℤ) (hd : 0 < A.den)
    (hv : 0 < v) {o : ℝ} {P : Polynomial ℝ}
    (he : ((A.poly N).map (Rat.castHom ℝ)).eval ((u : ℝ) / v) = P.eval ((u : ℝ) / v + o)) :
    P.eval ((u : ℝ) / v + o) ≤ (middleRowUpper A N u v : ℝ) := by
  refine (middle_input_endpoint_le A N u v hd hv he).trans ?_
  simp only [middleRowUpper, Rat.cast_div, Rat.cast_intCast]
  exact
    div_le_div_of_nonneg_right (Int.cast_le.mpr (le_max_right _ _)) (Int.cast_nonneg_iff.mpr hd.le)

/-- Upper bound the positive exponential from its grid endpoint. -/
@[expose]
public def middleExpUpper (n : ℕ) : ℚ :=
  ((gaussianMidExpGrid n).upper : ℤ) / (100000000 : ℚ)

/-- The computed exponential upper endpoint encloses the exact exponential. -/
public theorem middle_exp_upper_le (n : ℕ) : Real.exp ((n : ℝ) / 80) ≤ (middleExpUpper n : ℝ) := by
  simpa only [middleExpUpper, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, Int.cast_ofNat] using
    (gaussian_mid_exp_grid n).2

/-- Compare the two decaying profile costs and the negative linear term
using rational enclosures at an endpoint. -/
@[expose]
public def middleEndpointLower (s β x U V : ℚ) (j k l : ℕ) : ℚ :=
  s * middleExpUpper j - β / 4 * x ^ 2 - U / middleTailExpDen k - V / middleTailExpDen l

/-- A rational endpoint certificate gives a lower bound for the residual.
Clamping the row endpoints to zero allows using just upper decay bounds. -/
public theorem middle_endpoint_lower_le (s β x U V : ℚ) (a : ℝ) (P : Fin 2 → Polynomial ℝ)
    (j k l : ℕ) (hs : s ≤ 0) (hU : 0 ≤ U) (hV : 0 ≤ V) (hj : (j : ℝ) / 80 = (x : ℝ) / 2)
    (hk : (k : ℝ) / 80 = a * (x : ℝ)) (hl : (l : ℝ) / 80 = (a - 1 / 2) * (x : ℝ))
    (hkp : 0 < middleTailExpDen k) (hlp : 0 < middleTailExpDen l)
    (hu : (P 0).eval (x : ℝ) ≤ (U : ℝ)) (hv : (P 1).eval (x : ℝ) ≤ (V : ℝ)) :
    (middleEndpointLower s β x U V j k l : ℝ) ≤
      gaussianMidResidual (s : ℝ) 0 (β : ℝ) (middleResidualRates a) P (x : ℝ) := by
  have he := middle_exp_upper_le j
  have ek := middle_tail_exp_le k hkp
  have el := middle_tail_exp_le l hlp
  rw [hj] at he
  rw [hk, ← neg_mul, Rat.cast_div, Rat.cast_one] at ek
  rw [hl, ← neg_mul, Rat.cast_div, Rat.cast_one] at el
  have hmain := mul_le_mul_of_nonpos_left he (Rat.cast_nonpos.mpr hs)
  have hcost {t : ℝ} {q : ℚ} {n : ℕ} (hq : 0 ≤ q) (ht : t ≤ (q : ℝ)) {z : ℝ}
    (hz : Real.exp z ≤ 1 / (middleTailExpDen n : ℝ)) :
    Real.exp z * t ≤ (q : ℝ) / (middleTailExpDen n : ℝ) := by
    exact
      (mul_le_mul_of_nonneg_left ht (Real.exp_pos z).le).trans
        (by
          simpa only [one_div, inv_mul_eq_div] using
            (mul_le_mul_of_nonneg_right hz (Rat.cast_nonneg.mpr hq)))
  have h₀ := hcost hU hu ek
  have h₁ := hcost hV hv el
  rw [gaussianMidResidual, gaussianDecaySum, Fin.sum_univ_two]
  change
    _ ≤
      _ + 0 - _ -
        (Real.exp (-a * (x : ℝ)) * (P 0).eval (x : ℝ) +
          Real.exp (-(a - 1 / 2) * (x : ℝ)) * (P 1).eval (x : ℝ))
  simp only [middleEndpointLower, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat]
  linarith only [hmain, h₀, h₁]

end PseudoPrime.PrimeTestBounds.MillerRabin
