/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleOriginGamma
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries

/-! # Integral representation of the centered triangle gamma correction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive decay and width, the Laplace integral of the clipped linear
weight equals the difference of exponentials divided by the squared decay and width. -/
theorem triangle_origin_laplace {a H : ℝ} (ha : 0 < a) (hH : 0 < H) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * min (x / H) 1) =
      (1 - Real.exp (-a * H)) / (H * a ^ 2) := by
  let f (x : ℝ) := Real.exp (-a * x) * min (x / H) 1
  have hc : Continuous f := by
    unfold f; fun_prop
  have ht : Set.EqOn f (fun x => Real.exp (-a * x)) (Set.Ioi H) := by
    intro x hx
    unfold f
    rw [min_eq_right ((one_le_div hH).mpr hx.le), mul_one]
  have hi := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) H).congr_fun ht.symm measurableSet_Ioi
  change (∫ x in Set.Ioi (0 : ℝ), f x) = _
  rw [← Set.Ioc_union_Ioi_eq_Ioi hH.le,
    MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) hi,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ht,
    integral_exp_mul_Ioi (neg_lt_zero.mpr ha), ← intervalIntegral.integral_of_le hH.le]
  let F (x : ℝ) := -(a * x + 1) * Real.exp (-a * x) / (H * a ^ 2)
  have hd (x : ℝ) (hx : x ∈ Set.uIcc 0 H) : HasDerivAt F (f x) x := by
    rw [Set.uIcc_of_le hH.le] at hx
    have he := ((hasDerivAt_id x).const_mul (-a)).exp
    have h := (((((hasDerivAt_id x).const_mul a).add_const 1).neg).mul he).div_const (H * a ^ 2)
    apply h.congr_deriv
    unfold f
    rw [min_eq_left ((div_le_one hH).mpr hx.2)]
    simp only [Pi.neg_apply, id_eq, mul_one]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  unfold F
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- On the positive half-line the geometric series in exp(-2x) recovers
the denominator of the archimedean correction, including the clipped weight. -/
theorem triangle_origin_geometric {x H : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, Real.exp (-(2 * k + 1 / 2) * x) * min (x / H) 1) =
      Real.exp (-x / 2) * min (x / H) 1 / (1 - Real.exp (-2 * x)) := by
  have ht (k : ℕ) :
    Real.exp (-(2 * k + 1 / 2) * x) = Real.exp (-x / 2) * Real.exp (-2 * x) ^ k := by
    rw [← Real.exp_natCast_mul, ← Real.exp_add]
    congr 1
    ring
  simp_rw [ht, mul_right_comm (Real.exp (-x / 2)) _ (min _ _)]
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith only [hx]))]
  rfl

/-- The integral of each geometric summand at half-width 5/2 is exactly
two fifths of its origin series term. -/
theorem triangle_origin_term_integral (k : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(2 * k + 1 / 2) * x) * min (x / (5 / 2)) 1) =
      (2 / 5) * triangleOriginTerm k := by
  rw [triangle_origin_laplace (by positivity) (by norm_num only)]
  unfold triangleOriginTerm
  rw [neg_mul]
  field_simp

/-- Absolute convergence of the origin correction follows by comparison with
the reciprocal squares after shifting the index by one. -/
private theorem originTerm_summable : Summable triangleOriginTerm := by
  have h :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by decide))
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_nonneg_of_le _ _ h
  · intro n
    unfold triangleOriginTerm
    apply div_nonneg _ (sq_nonneg _)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
  · intro n
    unfold triangleOriginTerm
    apply (div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (sq_nonneg _)).trans
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) n]

/-- Integration of the positive geometric expansion identifies the half-line
origin gamma correction with its convergent pole series. -/
theorem triangle_origin_integral_series :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x / 2) * min (x / (5 / 2)) 1 / (1 - Real.exp (-2 * x))) =
      (2 / 5) * ∑' k : ℕ, triangleOriginTerm k := by
  let F (k : ℕ) (x : ℝ) := Real.exp (-(2 * k + 1 / 2) * x) * min (x / (5 / 2)) 1
  have hpos (k : ℕ) (x : ℝ) (hx : 0 < x) : 0 ≤ F k x := by
    exact mul_nonneg (Real.exp_pos _).le (le_min (by positivity) zero_le_one)
  have hi (k : ℕ) : MeasureTheory.IntegrableOn (F k) (Set.Ioi 0) := by
    apply
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (by positivity : 0 < 2 * (k : ℝ) + 1 / 2)) 0).mono'
        (by
          unfold F; fun_prop)
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume)
        (measurableSet_Ioi (a := (0 : ℝ)))] with
      x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos k x hx)]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.exp_pos _).le).trans_eq (mul_one _)
  have hnorm (k : ℕ) : (∫ x in Set.Ioi (0 : ℝ), ‖F k x‖) = (2 / 5) * triangleOriginTerm k := by
    apply Eq.trans _ (triangle_origin_term_integral k)
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact (Real.norm_eq_abs _).trans (abs_of_nonneg (hpos k x hx))
  have hsum := (originTerm_summable.mul_left (2 / 5 : ℝ)).congr (fun k => (hnorm k).symm)
  have he := MeasureTheory.integral_tsum_of_summable_integral_norm hi hsum
  rw [←
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => triangle_origin_geometric (H := 5 / 2) hx)]
  change (∫ x in Set.Ioi (0 : ℝ), ∑' k, F k x) = _
  rw [← he, ← tsum_mul_left]
  exact tsum_congr triangle_origin_term_integral

/-- In the half-line integral representation the centered gamma constant is
strictly below -2.84, by the integral-series identity and the series bound. -/
theorem triangle_origin_integral_upper :
    -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 - Real.log Real.pi +
        2 *
          (∫ x in Set.Ioi (0 : ℝ),
            Real.exp (-x / 2) * min (x / (5 / 2)) 1 / (1 - Real.exp (-2 * x))) <
      -(284 / 100) := by
  rw [triangle_origin_integral_series]
  have h := triangle_origin_gamma_upper
  unfold triangleOriginGamma at h
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
