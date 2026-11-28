/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv
import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries
import PseudoPrime.AnalyticNumberTheory.Gamma.ResolventSeries
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Taylor

/-! # Laplace derivatives and reciprocal coefficients for Gaussian Gamma terms -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A translated Laplace moment has a finite expansion in the derivatives
of the original polynomial at the translation point. -/
theorem gamma_shift_moment_derivatives (P : Polynomial ℝ) (z : ℝ) {d : ℝ} (hd : 0 < d) :
    (∫ v in Set.Ioi (0 : ℝ), Real.exp (-d * v) * P.eval (z + v)) =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        ((Polynomial.derivative^[j]) P).eval z / d ^ (j + 1) := by
  have he (v : ℝ) :
    Real.exp (-d * v) * P.eval (z + v) = (Polynomial.taylor z P).eval v * Real.exp (-d * v) := by
    rw [Polynomial.taylor_eval, add_comm v z, mul_comm]
  simp only [he]
  rw [polynomial_laplace_moment _ hd, Polynomial.natDegree_taylor]
  apply Finset.sum_congr rfl
  intro j _
  have h :=
    congrArg (Polynomial.eval z)
      (congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := j)) P)
  rw [Polynomial.taylor_coeff, ← mul_div_assoc]
  congr 1
  rw [LinearMap.smul_apply, Polynomial.eval_smul] at h
  simpa only [nsmul_eq_mul, mul_comm] using h

/-- The higher derivative coefficients in H33 have summable reciprocal
powers of the shifted pole spacing. -/
theorem gamma_pole_power_summable {d : ℝ} (hd : 0 < d) {j : ℕ} (hj : 0 < j) :
    Summable fun n : ℕ ↦ (1 : ℝ) / (d + 2 * n) ^ (j + 1) := by
  have hs := Real.summable_nat_pow_inv.mpr (show 1 < j + 1 from Nat.succ_lt_succ hj)
  apply Summable.of_norm_bounded_eventually_nat hs
  filter_upwards [Nat.eventually_pos] with n hn
  have h₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h₁ : (n : ℝ) ≤ d + 2 * n := by linarith only [hd, h₀]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (pow_nonneg (h₀.le.trans h₁) _)), ←
    one_div]
  exact one_div_le_one_div_of_le (pow_pos h₀ _) (pow_le_pow_left₀ h₀.le h₁ _)

/-- The zeroth coefficient retains the reciprocal difference, whose
series converges even though its two separate parts are harmonic. -/
theorem gamma_pole_diff_summable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    Summable fun n : ℕ ↦ (1 : ℝ) / (2 * (b + n)) - 1 / (d + 2 * n) := by
  have h :=
    AnalyticNumberTheory.Gamma.summable_resolventDifference (s := (b : ℂ)) (t := ((d / 2 : ℝ) : ℂ))
      (by simpa only [Complex.ofReal_re] using hb.le)
      (by simpa only [Complex.ofReal_re] using div_nonneg hd.le (by norm_num only : (0 : ℝ) ≤ 2))
  have h₁ := (Complex.reCLM.summable h).mul_left (1 / 2 : ℝ)
  apply h₁.congr
  intro n
  have he : d + 2 * (n : ℝ) = 2 * (d / 2 + n) := by ring
  rw [he]
  simp only [Complex.reCLM_apply, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re, mul_sub,
    one_div_mul_one_div]

/-- The convergent reciprocal differences in the zeroth H33 coefficient
equal half the corresponding real digamma difference. -/
theorem gamma_pole_diff_tsum {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    (∑' n : ℕ, ((1 : ℝ) / (2 * (b + n)) - 1 / (d + 2 * n))) =
      ((Complex.digamma ((d / 2 : ℝ) : ℂ)).re - (Complex.digamma (b : ℂ)).re) / 2 := by
  have hb' : 0 < ((b : ℝ) : ℂ).re := by simpa only [Complex.ofReal_re] using hb
  have hd' : 0 < (((d / 2 : ℝ) : ℂ)).re := by
    simpa only [Complex.ofReal_re] using div_pos hd (by norm_num only : (0 : ℝ) < 2)
  have ha := AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries hd' hb'
  have hs := AnalyticNumberTheory.Gamma.summable_resolventDifference hb'.le hd'.le
  have h := congrArg Complex.re ha
  rw [Complex.sub_re, Complex.re_tsum hs] at h
  conv_rhs => rw [h, div_eq_inv_mul, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : d + 2 * (n : ℝ) = 2 * (d / 2 + n) := by ring
  rw [he]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_add, ← Complex.ofReal_one,
    ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re, mul_sub, ← one_div,
    one_div_mul_one_div]

/-- Regroup the H33 pole terms by derivative order. The constant term
is exchanged as a reciprocal difference, and every higher coefficient
is exchanged using its absolutely summable reciprocal power. -/
theorem gamma_pole_coefficients_tsum {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (N : ℕ) (v : ℕ → ℝ) :
    (∑' n : ℕ,
        (v 0 * (1 / (2 * (b + n)) - 1 / (d + 2 * n)) +
          ∑ j ∈ Finset.range N, v (j + 1) / (d + 2 * n) ^ (j + 2))) =
      v 0 * (∑' n : ℕ, (1 / (2 * (b + n)) - 1 / (d + 2 * n))) +
        ∑ j ∈ Finset.range N, v (j + 1) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2)) := by
  have h₀ := (gamma_pole_diff_summable hb hd).mul_left (v 0)
  have h (j : ℕ) : Summable (fun n : ℕ ↦ v (j + 1) / (d + 2 * n) ^ (j + 2)) := by
    simpa only [mul_one_div] using
      (gamma_pole_power_summable hd (Nat.zero_lt_succ j)).mul_left (v (j + 1))
  rw [h₀.tsum_add (summable_sum (fun j _ ↦ h j)), tsum_mul_left,
    Summable.tsum_finsetSum (fun j _ ↦ h j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← tsum_mul_left]
  exact tsum_congr (fun _ ↦ (mul_one_div _ _).symm)

/-- Subtracting the shifted tail from the complete Laplace integral gives
the finite decay moment as derivative sums at zero and at the cutoff. -/
theorem gamma_finite_decay_derivatives (P : Polynomial ℝ) {d z : ℝ} (hd : 0 < d) (hz : 0 ≤ z) :
    (∫ v in (0 : ℝ)..z, Real.exp (-d * v) * P.eval v) =
      (∑ j ∈ Finset.range (P.natDegree + 1), ((Polynomial.derivative^[j]) P).eval 0 / d ^ (j + 1)) -
        Real.exp (-d * z) *
          ∑ j ∈ Finset.range (P.natDegree + 1),
            ((Polynomial.derivative^[j]) P).eval z / d ^ (j + 1) := by
  let f := fun v : ℝ ↦ Real.exp (-d * v) * P.eval v
  have hcont : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul P.continuous
  have ha := (abs_laplace_integrable_and_le P hd).1
  have hi : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    refine ha.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun v ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  have htail :
    (∫ v in Set.Ioi z, f v) =
      Real.exp (-d * z) * ∫ v in Set.Ioi (0 : ℝ), Real.exp (-d * v) * P.eval (z + v) := by
    rw [← integral_translate_Ioi f z, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun v ↦ by simp only [f, mul_add, Real.exp_add, mul_assoc]
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hi hz, htail, gamma_shift_moment_derivatives P z hd]
  have hzero := gamma_shift_moment_derivatives P 0 hd
  simp only [zero_add] at hzero
  rw [hzero]

/-- At a pole to the right of the kernel pole in the shifted Laplace
coordinate, extract the full residue and its translated derivative sum. -/
theorem gamma_growing_moment {P : Polynomial ℝ} {a q z : ℝ} (hq : q < a) (hz : 0 ≤ z) :
    let d := a - q
    let M := fun y : ℝ ↦
      ∑ j ∈ Finset.range (P.natDegree + 1), ((Polynomial.derivative^[j]) P).eval y / d ^ (j + 1)
    Real.exp (-a * z) * (∫ v in (0 : ℝ)..z, Real.exp ((a - q) * (z - v)) * P.eval v) =
      Real.exp (-q * z) * M 0 - Real.exp (-a * z) * M z := by
  intro d M
  have he (v : ℝ) :
    Real.exp ((a - q) * (z - v)) * P.eval v =
      Real.exp (d * z) * (Real.exp (-d * v) * P.eval v) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    dsimp only [d]
    ring
  simp only [he, intervalIntegral.integral_const_mul]
  rw [← mul_assoc, ← Real.exp_add, gamma_finite_decay_derivatives P (sub_pos.mpr hq) hz]
  change Real.exp (-a * z + d * z) * (M 0 - Real.exp (-d * z) * M z) = _
  rw [mul_sub, ← mul_assoc _ (Real.exp (-d * z)), ← Real.exp_add]
  rw [show -a * z + d * z = -q * z by
      dsimp only [d]; ring]
  rw [show -q * z + -d * z = -a * z by
      dsimp only [d]; ring]

/-- Reflecting the argument multiplies the derivative of order `j` by
the corresponding power of minus one. -/
private theorem gamma_derivative_reflect (P : Polynomial ℝ) (z : ℝ) (j : ℕ) :
    (Polynomial.derivative^[j]) (P.comp (Polynomial.C z - Polynomial.X)) =
      (-1 : ℝ) ^ j • ((Polynomial.derivative^[j]) P).comp (Polynomial.C z - Polynomial.X) := by
  induction j generalizing P with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply, pow_zero, one_smul]
  | succ j
    ih =>
    have he :
      (P.comp (Polynomial.C z - Polynomial.X)).derivative =
        -P.derivative.comp (Polynomial.C z - Polynomial.X) := by
      rw [Polynomial.derivative_comp, Polynomial.derivative_sub, Polynomial.derivative_C,
        Polynomial.derivative_X, zero_sub, neg_mul, one_mul]
    rw [Function.iterate_succ_apply, he, ← neg_one_smul ℝ, Polynomial.iterate_derivative_smul, ih,
      Function.iterate_succ_apply, smul_smul, pow_succ, mul_comm (-1 : ℝ)]

/-- At a negative convolution rate, the forward moment becomes two
alternating derivative sums, evaluated at the height and at zero. -/
theorem gamma_forward_decay_derivatives (P : Polynomial ℝ) {d z : ℝ} (hd : 0 < d) (hz : 0 ≤ z) :
    (∫ v in (0 : ℝ)..z, Real.exp (-d * (z - v)) * P.eval v) =
      (∑ j ∈ Finset.range (P.natDegree + 1),
          (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval z / d ^ (j + 1)) -
        Real.exp (-d * z) *
          ∑ j ∈ Finset.range (P.natDegree + 1),
            (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0 / d ^ (j + 1) := by
  let Q := P.comp (Polynomial.C z - Polynomial.X)
  let f := fun v : ℝ ↦ Real.exp (-d * v) * Q.eval v
  have hf (v : ℝ) : Real.exp (-d * (z - v)) * P.eval v = f (z - v) := by
    simp only [f, Q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X, sub_sub_cancel]
  simp only [hf]
  rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  change (∫ v in (0 : ℝ)..z, Real.exp (-d * v) * Q.eval v) = _
  have hdeg : Q.natDegree = P.natDegree := by
    dsimp only [Q]
    rw [Polynomial.natDegree_comp,
      Polynomial.natDegree_sub_eq_right_of_natDegree_lt
        (by
          rw [Polynomial.natDegree_C, Polynomial.natDegree_X]; exact Nat.zero_lt_one),
      Polynomial.natDegree_X, mul_one]
  rw [gamma_finite_decay_derivatives Q hd hz, hdeg]
  simp only [Q, gamma_derivative_reflect, Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, sub_zero, sub_self]

/-- Bound one origin term by a geometric term at the initial positive rate. -/
private theorem gamma_origin_term_le {d z : ℝ} (hd : 0 < d) (j n : ℕ) :
    Real.exp (-(d + 2 * n) * z) / (d + 2 * n) ^ (j + 1) ≤
      (Real.exp (-d * z) / d ^ (j + 1)) * Real.exp (-2 * z) ^ n := by
  have hdn : d ≤ d + 2 * (n : ℝ) := by linarith only [Nat.cast_nonneg (α := ℝ) n]
  have he : -(d + 2 * (n : ℝ)) * z = -d * z + (n : ℝ) * (-2 * z) := by ring
  rw [he, Real.exp_add, Real.exp_natCast_mul]
  calc
    Real.exp (-d * z) * Real.exp (-2 * z) ^ n / (d + 2 * n) ^ (j + 1) ≤
        Real.exp (-d * z) * Real.exp (-2 * z) ^ n / d ^ (j + 1) :=
      div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (pow_nonneg (Real.exp_pos _).le _))
        (pow_pos hd _) (pow_le_pow_left₀ hd.le hdn _)
    _ = Real.exp (-d * z) / d ^ (j + 1) * Real.exp (-2 * z) ^ n := by ring

/-- The origin contribution for each derivative order is dominated by a
geometric series whenever the initial rate and evaluation height are positive. -/
theorem gamma_origin_term_summable {d z : ℝ} (hd : 0 < d) (hz : 0 < z) (j : ℕ) :
    Summable fun n : ℕ ↦ Real.exp (-(d + 2 * n) * z) / (d + 2 * n) ^ (j + 1) := by
  have hg :=
    (summable_geometric_of_lt_one (Real.exp_pos (-2 * z)).le
          (Real.exp_lt_one_iff.mpr (by linarith only [hz] : -2 * z < 0))).mul_left
      (Real.exp (-d * z) / d ^ (j + 1))
  refine
    Summable.of_nonneg_of_le
      (fun n ↦
        div_nonneg (Real.exp_pos _).le
          (pow_nonneg (add_nonneg hd.le (mul_nonneg zero_le_two (Nat.cast_nonneg n))) _))
      (gamma_origin_term_le hd j) hg

/-- The full origin contribution is summable after the finite derivative
expansion, so it can be separated from the signed reciprocal differences. -/
theorem gamma_origin_summable {d z : ℝ} (hd : 0 < d) (hz : 0 < z) (N : ℕ) (v : ℕ → ℝ) :
    Summable fun n : ℕ ↦
      Real.exp (-(d + 2 * n) * z) * ∑ j ∈ Finset.range N, v j / (d + 2 * n) ^ (j + 1) := by
  simp only [Finset.mul_sum]
  apply summable_sum
  intro j _
  exact ((gamma_origin_term_summable hd hz j).mul_left (v j)).congr fun n ↦ by ring

/-- Bound the full origin series by one finite sum of absolute derivative
coefficients and a closed geometric factor at positive height. -/
theorem gamma_origin_tsum_abs_le {d z : ℝ} (hd : 0 < d) (hz : 0 < z) (N : ℕ) (v : ℕ → ℝ) :
    |∑' n : ℕ, Real.exp (-(d + 2 * n) * z) * ∑ j ∈ Finset.range N, v j / (d + 2 * n) ^ (j + 1)| ≤
      (∑ j ∈ Finset.range N, |v j| * (Real.exp (-d * z) / d ^ (j + 1))) /
        (1 - Real.exp (-2 * z)) := by
  let A := ∑ j ∈ Finset.range N, |v j| * (Real.exp (-d * z) / d ^ (j + 1))
  have hq₀ := (Real.exp_pos (-2 * z)).le
  have hq₁ := Real.exp_lt_one_iff.mpr (show -2 * z < 0 by linarith only [hz])
  have h := norm_tsum_le_tsum_norm (gamma_origin_summable hd hz N v).norm
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  have hg := (summable_geometric_of_lt_one hq₀ hq₁).mul_left A
  refine (Summable.tsum_le_tsum ?_ (gamma_origin_summable hd hz N v).norm hg).trans_eq ?_
  · intro n
    have hdₙ : 0 ≤ d + 2 * (n : ℝ) := add_nonneg hd.le (mul_nonneg zero_le_two (Nat.cast_nonneg n))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le).trans ?_
    simp only [A, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [abs_div, abs_of_nonneg (pow_nonneg hdₙ _)]
    calc
      Real.exp (-(d + 2 * n) * z) * (|v j| / (d + 2 * n) ^ (j + 1)) =
          |v j| * (Real.exp (-(d + 2 * n) * z) / (d + 2 * n) ^ (j + 1)) :=
        by ring
      _ ≤ |v j| * (Real.exp (-d * z) / d ^ (j + 1) * Real.exp (-2 * z) ^ n) :=
        mul_le_mul_of_nonneg_left (gamma_origin_term_le hd j n) (abs_nonneg _)
      _ = _ := by rw [mul_assoc]
  · rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁, div_eq_mul_inv]

/-- A positive left endpoint supplies a uniform bound for the origin
series at every height to its right. -/
theorem gamma_origin_tsum_abs_le_from {d z z₀ : ℝ} (hd : 0 < d) (hz₀ : 0 < z₀) (hz : z₀ ≤ z) (N : ℕ)
    (v : ℕ → ℝ) :
    |∑' n : ℕ, Real.exp (-(d + 2 * n) * z) * ∑ j ∈ Finset.range N, v j / (d + 2 * n) ^ (j + 1)| ≤
      (∑ j ∈ Finset.range N, |v j| * (Real.exp (-d * z₀) / d ^ (j + 1))) /
        (1 - Real.exp (-2 * z₀)) := by
  refine (gamma_origin_tsum_abs_le hd (hz₀.trans_le hz) N v).trans ?_
  apply div_le_div₀
  · exact
      Finset.sum_nonneg fun j _ ↦
        mul_nonneg (abs_nonneg _) (div_nonneg (Real.exp_pos _).le (pow_nonneg hd.le _))
  · apply Finset.sum_le_sum
    intro j _
    exact
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hz (neg_nonpos.mpr hd.le)))
          (pow_nonneg hd.le _))
        (abs_nonneg _)
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [hz₀]))
  · exact sub_le_sub_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hz (by norm_num only))) 1

/-- Regroup the forward tail by derivative order and keep the exponentially
decaying origin terms separate. The zeroth reciprocal difference stays intact. -/
theorem gamma_forward_tail_tsum (P : Polynomial ℝ) {b d z : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hz : 0 < z) :
    let v := fun j : ℕ ↦ -((-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval z)
    let T := fun n : ℕ ↦
      Real.exp (-(d + 2 * n) * z) *
        ∑ j ∈ Finset.range (P.natDegree + 1),
          (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval 0 / (d + 2 * n) ^ (j + 1)
    (∑' n : ℕ,
        (P.eval z / (2 * (b + n)) -
            (∑ j ∈ Finset.range (P.natDegree + 1),
              (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) P).eval z / (d + 2 * n) ^ (j + 1)) +
          T n)) =
      P.eval z * (∑' n : ℕ, (1 / (2 * (b + n)) - 1 / (d + 2 * n))) +
        (∑ j ∈ Finset.range P.natDegree, v (j + 1) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) +
        ∑' n, T n := by
  intro v T
  let F := fun n : ℕ ↦
    P.eval z * (1 / (2 * (b + n)) - 1 / (d + 2 * n)) +
      ∑ j ∈ Finset.range P.natDegree, v (j + 1) / (d + 2 * n) ^ (j + 2)
  have hT : Summable T := gamma_origin_summable hd hz _ _
  have hF : Summable F := by
    apply ((gamma_pole_diff_summable hb hd).mul_left (P.eval z)).add
    apply summable_sum
    intro j _
    simpa only [mul_one_div] using
      (gamma_pole_power_summable hd (Nat.zero_lt_succ j)).mul_left (v (j + 1))
  have hsum :=
    gamma_pole_coefficients_tsum hb hd P.natDegree (fun j ↦ if j = 0 then P.eval z else v j)
  simp only [Nat.succ_ne_zero, ite_true, ite_false] at hsum
  change (∑' n, F n) = _ at hsum
  rw [← hsum, ← hF.tsum_add hT]
  apply tsum_congr
  intro n
  dsimp only [F, v]
  rw [Finset.sum_range_succ', pow_one, Function.iterate_zero_apply, pow_zero, one_mul, mul_sub,
    mul_one_div, mul_one_div]
  simp only [neg_div, Finset.sum_neg_distrib]
  ring

/-- The Taylor error of a decaying exponential on a nonnegative segment
is bounded by the magnitude of the first omitted term. -/
theorem gamma_decay_taylor_error {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (m : ℕ) :
    |Real.exp (-s * t) - ∑ j ∈ Finset.range (m + 1), ((-s) ^ j / (j.factorial : ℝ)) * t ^ j| ≤
      (s * t) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [mul_zero, Real.exp_zero, Finset.sum_range_succ', pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul, zero_pow (Nat.succ_ne_zero _), mul_zero,
      Finset.sum_const_zero, zero_add, sub_self, abs_zero, zero_div, le_refl]
  let f := fun x : ℝ ↦ Real.exp (-s * x)
  have hf : ContDiff ℝ ⊤ f := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  obtain ⟨x, hx, he⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := m) ht.ne (hf.of_le le_top).contDiffOn
  have hT :
    taylorWithinEval f m (Set.uIcc 0 t) 0 t =
      ∑ j ∈ Finset.range (m + 1), ((-s) ^ j / (j.factorial : ℝ)) * t ^ j := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc ht.ne) (hf.of_le le_top).contDiffAt
        Set.left_mem_uIcc,
      show iteratedDeriv j f = _ from iteratedDeriv_exp_const_mul _ _]
    simp only [sub_zero, smul_eq_mul, mul_zero, Real.exp_zero, mul_one, div_eq_mul_inv]
    ring
  rw [hT] at he
  change |f t - _| ≤ _
  rw [he, show iteratedDeriv (m + 1) f = _ from iteratedDeriv_exp_const_mul _ _, sub_zero, abs_div,
    abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hs, abs_of_nonneg (Real.exp_pos _).le,
    abs_pow, abs_of_nonneg ht.le, abs_of_nonneg (Nat.cast_nonneg _), mul_pow]
  rw [Set.uIoo_of_le ht.le] at hx
  have hE : Real.exp (-s * x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) hx.1.le)
  gcongr
  exact mul_le_of_le_one_right (pow_nonneg hs _) hE

/-- Bound the error of replacing a weakly decaying convolution by a finite
Taylor polynomial, given an absolute profile cap on its integration interval. -/
theorem gamma_forward_taylor_error (P : Polynomial ℝ) {d z M : ℝ} (hd : 0 ≤ d) (hz : 0 ≤ z)
    (hM : ∀ v ∈ Set.Icc 0 z, |P.eval v| ≤ M) (m : ℕ) :
    let T := fun v : ℝ ↦ ∑ j ∈ Finset.range (m + 1), ((-d) ^ j / (j.factorial : ℝ)) * (z - v) ^ j
    |(∫ v in (0 : ℝ)..z, Real.exp (-d * (z - v)) * P.eval v) - ∫ v in (0 : ℝ)..z, T v * P.eval v| ≤
      ((d * z) ^ (m + 1) / ((m + 1).factorial : ℝ)) * M * z := by
  intro T
  have he : Continuous (fun v : ℝ ↦ Real.exp (-d * (z - v))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hT : Continuous T :=
    continuous_finsetSum _ fun j _ ↦
      continuous_const.mul ((continuous_const.sub continuous_id).pow j)
  have he₁ :
    IntervalIntegrable (fun v ↦ Real.exp (-d * (z - v)) * P.eval v) MeasureTheory.volume 0 z :=
    (he.mul P.continuous).intervalIntegrable 0 z
  have hT₁ : IntervalIntegrable (fun v ↦ T v * P.eval v) MeasureTheory.volume 0 z :=
    (hT.mul P.continuous).intervalIntegrable 0 z
  rw [← intervalIntegral.integral_sub he₁ hT₁]
  rw [← Real.norm_eq_abs]
  have hZ : |z - 0| = z := by rw [sub_zero, abs_of_nonneg hz]
  refine
    (intervalIntegral.norm_integral_le_of_norm_le_const (C :=
          ((d * z) ^ (m + 1) / ((m + 1).factorial : ℝ)) * M) ?_).trans_eq
      ?_
  swap
  · rw [hZ]
  intro v hv
  rw [Set.uIoc_of_le hz] at hv
  rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
  have hV : 0 ≤ z - v := sub_nonneg.mpr hv.2
  refine mul_le_mul ?_ (hM v ⟨hv.1.le, hv.2⟩) (abs_nonneg _) ?_
  · refine (gamma_decay_taylor_error hd hV m).trans ?_
    exact
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg hd hV) (mul_le_mul_of_nonneg_left (sub_le_self _ hv.1.le) hd)
          _)
        (Nat.cast_nonneg _)
  · exact div_nonneg (pow_nonneg (mul_nonneg hd hz) _) (Nat.cast_nonneg _)

/-- Shift the forward real gamma logarithmic derivative twice to the right.
The two explicit reciprocals isolate the poles at zero and minus two. -/
theorem gamma_logDeriv_shift_four {s : ℂ} (hs : -4 < s.re) (h0 : s ≠ 0) (h2 : s ≠ -2) :
    logDeriv Complex.Gammaℝ s =
      -(Complex.log (Real.pi : ℂ)) / 2 + Complex.digamma (s / 2 + 2) / 2 - s⁻¹ - (s + 2)⁻¹ := by
  have hs2 : -2 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith only [hs]
  have hhalf (n : ℕ) : s / 2 ≠ -(n : ℂ) := by
    intro h
    cases n with
    | zero =>
      rw [Nat.cast_zero, neg_zero, div_eq_zero_iff] at h
      exact h.elim h0 two_ne_zero
    | succ n =>
      cases n with
      | zero =>
        apply h2
        calc
          s = s / 2 * 2 := by ring
          _ = -2 := by
            rw [h]; norm_num only [Nat.cast_ofNat]
      | succ n =>
        have hr := congrArg Complex.re h
        rw [Complex.neg_re, Complex.natCast_re, Nat.cast_succ, Nat.cast_succ] at hr
        linarith only [hs2, hr, Nat.cast_nonneg (α := ℝ) n]
  have hshift (n : ℕ) : s / 2 + 1 ≠ -(n : ℂ) := by
    intro h
    apply hhalf (n + 1)
    rw [Nat.cast_succ]
    linear_combination h
  rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat hhalf]
  have e₀ := Complex.digamma_apply_add_one (s / 2) hhalf
  have e₁ := Complex.digamma_apply_add_one (s / 2 + 1) hshift
  have harg : s / 2 + 1 + 1 = s / 2 + 2 := by ring
  rw [harg] at e₁
  have ha : (s / 2)⁻¹ = 2 * s⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have hb : (s / 2 + 1)⁻¹ = 2 * (s + 2)⁻¹ := by
    rw [show s / 2 + 1 = (s + 2) / 2 by ring, inv_div, div_eq_mul_inv]
  rw [ha] at e₀
  rw [hb] at e₁
  linear_combination -(e₀ + e₁) / 2

/-- On the right Gaussian contour, separate the shifted digamma baseline
and the two low forward poles in the real Gamma logarithmic derivative. -/
theorem gamma_forward_line_split (t : ℝ) :
    let s := ((9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let b := ((81 / 32 : ℝ) : ℂ)
    logDeriv Complex.Gammaℝ (s + 1 / 2) =
      (Complex.digamma b - Complex.log (Real.pi : ℂ)) / 2 +
          (Complex.digamma (b + Complex.I * ((t : ℂ) / 2)) - Complex.digamma b) / 2 -
        (s + 1 / 2)⁻¹ -
        (s + 5 / 2)⁻¹ := by
  intro s b
  have hr : (s + 1 / 2).re = 17 / 16 := by
    norm_num only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
      Complex.one_re]
  have h₀ : s + 1 / 2 ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hr
    norm_num only at hr
  have h₂ : s + 1 / 2 ≠ -2 := by
    intro h
    rw [h, Complex.neg_re, Complex.re_ofNat] at hr
    norm_num only at hr
  rw [gamma_logDeriv_shift_four
      (by
        rw [hr]; norm_num only)
      h₀ h₂]
  have harg : (s + 1 / 2) / 2 + 2 = b + Complex.I * ((t : ℂ) / 2) := by
    simp only [s, b, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [harg, show s + 1 / 2 + 2 = s + 5 / 2 by ring]
  ring

/-- Integrate the forward split against a weight for which the baseline,
shifted digamma difference, and both pole weights are integrable. -/
theorem gamma_forward_integral_split (W : ℝ → ℂ) :
    let s := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let b := ((81 / 32 : ℝ) : ℂ)
    let e := fun t : ℝ ↦ Complex.digamma (b + Complex.I * ((t : ℂ) / 2)) - Complex.digamma b
    let B := (Complex.digamma b - Complex.log (Real.pi : ℂ)) / 2
    let p := fun t : ℝ ↦ (s t + 1 / 2)⁻¹ * W t
    let q := fun t : ℝ ↦ (s t + 5 / 2)⁻¹ * W t
    MeasureTheory.Integrable W →
      MeasureTheory.Integrable (fun t ↦ e t * W t) →
      MeasureTheory.Integrable p →
      MeasureTheory.Integrable q →
      (∫ t : ℝ, logDeriv Complex.Gammaℝ (s t + 1 / 2) * W t) =
        B * (∫ t : ℝ, W t) + (2 : ℂ)⁻¹ * (∫ t : ℝ, e t * W t) - (∫ t : ℝ, p t) - ∫ t : ℝ, q t := by
  intro s b e B p q hW he hp hq
  have hg (t : ℝ) :
    logDeriv Complex.Gammaℝ (s t + 1 / 2) * W t =
      (B * W t + (2 : ℂ)⁻¹ * (e t * W t)) - p t - q t := by
    have h := gamma_forward_line_split t
    change
      logDeriv Complex.Gammaℝ (s t + 1 / 2) = B + e t / 2 - (s t + 1 / 2)⁻¹ - (s t + 5 / 2)⁻¹ at h
    rw [h]
    simp only [p, q, sub_mul, add_mul, div_eq_inv_mul, mul_assoc]
  simp only [hg]
  have hB := hW.const_mul B
  have hE := he.const_mul ((2 : ℂ)⁻¹)
  have h₂ := MeasureTheory.integral_sub ((hB.add hE).sub hp) hq
  have h₁ := MeasureTheory.integral_sub (hB.add hE) hp
  have h₀ := MeasureTheory.integral_add hB hE
  simp only [Pi.sub_apply, Pi.add_apply] at h₂ h₁ h₀
  rw [h₂, h₁, h₀, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end PseudoPrime.PrimeTestBounds.MillerRabin
