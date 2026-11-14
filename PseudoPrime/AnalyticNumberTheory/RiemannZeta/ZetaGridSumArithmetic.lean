/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridLogArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridPowerArithmetic

/-! # Rational finite sums for the height-100 grid -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The exact rational components of `512/(s-1)+1/2` at the grid point
`s = 1/2 + k/128 + 100i`. This is the finite Euler–Maclaurin endpoint
coefficient and does not depend on a zero table. -/
def gridEndpointCoeff (k : ℕ) : ℚ × ℚ :=
  let u : ℚ := 1 / 2 + (k : ℚ) / 128 - 1
  (512 * u / (u ^ 2 + 10000) + 1 / 2, -51200 / (u ^ 2 + 10000))

/-- Casting the rational endpoint coefficient yields the complex coefficient
at the corresponding height-100 grid point. -/
theorem grid_endpoint_coeff_cast (k : ℕ) :
    Analysis.rationalComplexCast (gridEndpointCoeff k) =
      (512 : ℂ) / (((((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)) - 1) +
        1 / 2 := by
  apply Complex.ext
  · simp only [gridEndpointCoeff, Analysis.rationalComplexCast, Rat.cast_add, Rat.cast_div,
      Rat.cast_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one,
      Complex.add_re, Complex.sub_re, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.one_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.normSq_apply, Complex.add_im, Complex.sub_im, Complex.one_im,
      Complex.mul_im, mul_zero, mul_one, zero_mul, zero_add, sub_zero, add_zero]
    ring
  · simp only [gridEndpointCoeff, Analysis.rationalComplexCast, Rat.cast_neg, Rat.cast_div,
      Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
      Rat.cast_one, Complex.add_im, Complex.sub_im, Complex.div_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.one_im, Complex.mul_im, mul_zero, mul_one, zero_mul, zero_add, sub_zero, add_zero]
    ring

/-- The rational real part of the 511-term rounded sum plus its 512th
endpoint correction. Each logarithm and power is computed from the index;
the definition uses neither an imported table nor list indexing. -/
def gridFiniteValue (k : ℕ) : ℚ :=
  (∑ n ∈ Finset.Icc (1 : ℕ) 511, (gridPowerApprox k (gridLogApprox n)).1) +
    (Analysis.rationalComplexMul (gridEndpointCoeff k) (gridPowerApprox k (gridLogApprox 512))).1

/-- A contiguous half-open block of the rational grid sum. Partitioning the
511 terms permits independent kernel checks with bounded memory. -/
def gridFiniteBlock (k a b : ℕ) : ℚ :=
  ∑ n ∈ Finset.Ico a b, (gridPowerApprox k (gridLogApprox n)).1

/-- Split the finite grid sum into three blocks of 128 terms and a final
block of 127 terms. The separate endpoint correction is unchanged. -/
theorem grid_finite_value_split (k : ℕ) :
    gridFiniteValue k =
      gridFiniteBlock k 1 129 + gridFiniteBlock k 129 257 + gridFiniteBlock k 257 385 +
        gridFiniteBlock k 385 512 +
        (Analysis.rationalComplexMul (gridEndpointCoeff k)
            (gridPowerApprox k (gridLogApprox 512))).1 := by
  have hset : Finset.Icc (1 : ℕ) 511 = Finset.Ico 1 512 := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  simp only [gridFiniteValue, gridFiniteBlock, hset]
  have h1 :=
    Finset.sum_Ico_consecutive (fun n : ℕ => (gridPowerApprox k (gridLogApprox n)).1) (m := 1) (n :=
      129) (k := 257) (by norm_num only) (by norm_num only)
  have h2 :=
    Finset.sum_Ico_consecutive (fun n : ℕ => (gridPowerApprox k (gridLogApprox n)).1) (m := 1) (n :=
      257) (k := 385) (by norm_num only) (by norm_num only)
  have h3 :=
    Finset.sum_Ico_consecutive (fun n : ℕ => (gridPowerApprox k (gridLogApprox n)).1) (m := 1) (n :=
      385) (k := 512) (by norm_num only) (by norm_num only)
  linarith only [h1, h2, h3]

/-- Check the rational lower bound `6/5` required by the analytic grid
certificate. The checker is independent of zero existence and multiplicity. -/
def gridFiniteCheck (k : ℕ) : Bool :=
  decide ((6 / 5 : ℚ) ≤ gridFiniteValue k)

/-- A successful rational finite-sum check gives the corresponding real
lower bound after casting and identifying the endpoint coefficient. -/
theorem grid_finite_check_sound (k : ℕ) (h : gridFiniteCheck k = true) :
    let s : ℂ := (((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)
    (6 / 5 : ℝ) ≤
      ((∑ n ∈ Finset.Icc (1 : ℕ) 511,
            Analysis.rationalComplexCast (gridPowerApprox k (gridLogApprox n))) +
          ((512 : ℂ) / (s - 1) + 1 / 2) *
            Analysis.rationalComplexCast (gridPowerApprox k (gridLogApprox 512))).re := by
  have hc : (6 / 5 : ℚ) ≤ gridFiniteValue k := of_decide_eq_true h
  have hr := (Rat.cast_le (K := ℝ)).mpr hc
  simp only [gridFiniteValue, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sum] at hr
  dsimp only
  rw [← grid_endpoint_coeff_cast k, ← Analysis.rationalComplexCast_mul]
  simp only [Complex.add_re, Complex.re_sum, Analysis.rationalComplexCast]
  exact hr

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
