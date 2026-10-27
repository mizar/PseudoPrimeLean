/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PowerSumInterpolation

/-! # Radial contour selectors for consecutive power sums -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For a nonnegative circle radius and a pole outside the closed disk, the
inverse-kernel integral vanishes. Apply Cauchy--Goursat on the disk, which avoids
the pole. This is the exterior case of the radial node selector. -/
theorem circleIntegral_inverse_kernel_eq_zero_outside {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hz : r < ‖z‖) :
    circleIntegral (fun w : ℂ ↦ (w - z)⁻¹) 0 r = 0 := by
  have hne : ∀ w ∈ Metric.closedBall (0 : ℂ) r, w - z ≠ 0 := by
    intro w hw heq
    have hwNorm : ‖w‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hwz : w = z := sub_eq_zero.mp heq
    rw [hwz] at hwNorm
    exact (not_le_of_gt hz) hwNorm
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
  · exact (continuous_id.sub continuous_const).continuousOn.inv₀ hne
  · intro w hw
    exact (differentiableAt_id.sub_const z).inv (hne w (Metric.ball_subset_closedBall hw.1))

/-- Every inverse power of order at least two has zero circle integral about zero.
Apply the integer-power integral formula. This removes all higher zero-pole terms
from the inverse-power kernel recurrence. -/
theorem circleIntegral_inverse_power_succ_succ (k : ℕ) (r : ℝ) :
    circleIntegral (fun w : ℂ ↦ w⁻¹ ^ (k + 2)) 0 r = 0 := by
  have hn : (-((k + 2 : ℕ) : ℤ)) ≠ -1 := by
    intro h
    have hcast : ((k + 2 : ℕ) : ℤ) = 1 := neg_injective h
    have hnat : k + 2 = 1 := by exact_mod_cast hcast
    exact (Nat.ne_of_gt ((by decide : 1 < 2).trans_le (Nat.le_add_left 2 k))) hnat
  have h := circleIntegral.integral_sub_zpow_of_ne hn (0 : ℂ) 0 r
  simpa only [sub_zero, zpow_neg, zpow_natCast, inv_pow] using h

/-- For a positive radius and a node off the circle, the inverse-power simple-pole
kernel is circle integrable at every natural order. Both denominator factors avoid
zero on the circle. This justifies subtraction in the selector recurrence. -/
theorem circleIntegrable_inverse_power_kernel {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ ≠ r) (k : ℕ) :
    CircleIntegrable (fun w : ℂ ↦ w⁻¹ ^ k * (w - z)⁻¹) 0 r := by
  have hwzero : ∀ w ∈ Metric.sphere (0 : ℂ) r, w ≠ 0 := by
    intro w hw
    apply norm_ne_zero_iff.mp
    have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    exact ne_of_gt (hwNorm.symm ▸ hr)
  have hwz : ∀ w ∈ Metric.sphere (0 : ℂ) r, w - z ≠ 0 := by
    intro w hw heq
    have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    exact hz ((congrArg norm (sub_eq_zero.mp heq)).symm.trans hwNorm)
  exact
    ContinuousOn.circleIntegrable hr.le
      (((continuous_id.continuousOn.inv₀ hwzero).pow k).mul
        ((continuous_id.sub continuous_const).continuousOn.inv₀ hwz))

/-- For a nonzero node off a positive circle, increasing the inverse-power order
subtracts the pure inverse-power moment and divides by the node. Verify the pointwise
identity using explicit inverse cancellations, then integrate it. This constructs
the radial selector without a residue-theorem assumption. -/
theorem circleIntegral_inverse_power_kernel_recurrence {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ ≠ r)
    (hz0 : z ≠ 0) (k : ℕ) :
    circleIntegral (fun w : ℂ ↦ w⁻¹ ^ (k + 1) * (w - z)⁻¹) 0 r =
      z⁻¹ *
        (circleIntegral (fun w : ℂ ↦ w⁻¹ ^ k * (w - z)⁻¹) 0 r -
          circleIntegral (fun w : ℂ ↦ w⁻¹ ^ (k + 1)) 0 r) := by
  have hInv : CircleIntegrable (fun w : ℂ ↦ w⁻¹ ^ (k + 1)) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    apply ContinuousOn.pow
    apply continuous_id.continuousOn.inv₀
    intro w hw
    have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    exact norm_ne_zero_iff.mp (ne_of_gt (hwNorm.symm ▸ hr))
  calc
    _ = circleIntegral (fun w : ℂ ↦ z⁻¹ * (w⁻¹ ^ k * (w - z)⁻¹ - w⁻¹ ^ (k + 1))) 0 r := by
      apply circleIntegral.integral_congr hr.le
      intro w hw
      have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
      have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (hwNorm.symm ▸ hr))
      have hwz : w - z ≠ 0 := by
        intro h
        exact hz ((congrArg norm (sub_eq_zero.mp h)).symm.trans hwNorm)
      change w⁻¹ ^ (k + 1) * (w - z)⁻¹ = z⁻¹ * (w⁻¹ ^ k * (w - z)⁻¹ - w⁻¹ ^ (k + 1))
      have hdiff : (w - z)⁻¹ - w⁻¹ = z * (w⁻¹ * (w - z)⁻¹) := by
        calc
          _ = (w * w⁻¹) * (w - z)⁻¹ - ((w - z) * (w - z)⁻¹) * w⁻¹ := by
            rw [mul_inv_cancel₀ hw0, mul_inv_cancel₀ hwz, one_mul, one_mul]
          _ = _ := by ring
      have hstep : w⁻¹ * (w - z)⁻¹ = z⁻¹ * ((w - z)⁻¹ - w⁻¹) := by
        rw [hdiff, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
      calc
        _ = w⁻¹ ^ k * (w⁻¹ * (w - z)⁻¹) := by
          rw [pow_succ]; ring
        _ = z⁻¹ * (w⁻¹ ^ k * ((w - z)⁻¹ - w⁻¹)) := by
          rw [hstep]; ring
        _ = _ := by
          rw [pow_succ]; ring
    _ = _ := by
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub (circleIntegrable_inverse_power_kernel hr hz k) hInv]

/-- For a nonzero node off a positive circle, express every positive inverse-power
kernel integral through the simple-pole integral. Induct using the recurrence and
the vanishing higher inverse-power integrals. This separates radial inclusion
from the order-dependent inverse node power. -/
theorem circleIntegral_inverse_power_kernel_formula {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ ≠ r)
    (hz0 : z ≠ 0) (k : ℕ) :
    circleIntegral (fun w : ℂ ↦ w⁻¹ ^ (k + 1) * (w - z)⁻¹) 0 r =
      z⁻¹ ^ (k + 1) * (circleIntegral (fun w : ℂ ↦ (w - z)⁻¹) 0 r - 2 * Real.pi * Complex.I) := by
  induction k with
  | zero =>
    have h := circleIntegral_inverse_power_kernel_recurrence hr hz hz0 0
    have hInv : circleIntegral (fun w : ℂ ↦ w⁻¹) 0 r = 2 * Real.pi * Complex.I := by
      simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) (ne_of_gt hr)
    simpa only [zero_add, pow_one, pow_zero, one_mul, hInv] using h
  | succ k
    ih =>
    rw [circleIntegral_inverse_power_kernel_recurrence hr hz hz0 (k + 1),
      circleIntegral_inverse_power_succ_succ, sub_zero, ih, pow_succ]
    ring

/-- For a nonzero node off a positive circle, the inverse-power kernel integral
is zero inside and minus the inverse node power times `2πi` outside. Apply the
interior Cauchy formula and exterior vanishing. This supplies the inverse-power
interpolation values needed by the maximal-node power-sum argument. -/
theorem circleIntegral_inverse_power_kernel_selector {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z‖ ≠ r)
    (hz0 : z ≠ 0) (k : ℕ) :
    circleIntegral (fun w : ℂ ↦ w⁻¹ ^ (k + 1) * (w - z)⁻¹) 0 r =
      if r < ‖z‖ then -(2 * Real.pi * Complex.I) * z⁻¹ ^ (k + 1) else 0 := by
  rw [circleIntegral_inverse_power_kernel_formula hr hz hz0]
  by_cases hout : r < ‖z‖
  · rw [ite_eq_left hout, circleIntegral_inverse_kernel_eq_zero_outside hr.le hout]
    ring
  · have hin : ‖z‖ < r := lt_of_le_of_ne (le_of_not_gt hout) hz
    have hball : z ∈ Metric.ball (0 : ℂ) r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hin
    rw [ite_eq_right hout, circleIntegral.integral_sub_inv_of_mem_ball hball, sub_self, mul_zero]

/-- For any node off a positive circle, weighting the inverse-power selector by
minus the node power gives `2πi` outside and zero inside, including a zero node.
Cancel the node powers in the nonzero case. This retains repeated nodes in the
finite counting identity for consecutive power sums. -/
theorem circleIntegral_inverse_power_kernel_weighted_selector {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : ‖z‖ ≠ r) (k : ℕ) :
    -(z ^ (k + 1)) * circleIntegral (fun w : ℂ ↦ w⁻¹ ^ (k + 1) * (w - z)⁻¹) 0 r =
      if r < ‖z‖ then 2 * Real.pi * Complex.I else 0 := by
  by_cases hz0 : z = 0
  · subst z
    rw [zero_pow (Nat.succ_ne_zero k), neg_zero, zero_mul, norm_zero,
      ite_eq_right (not_lt_of_ge hr.le)]
  · rw [circleIntegral_inverse_power_kernel_selector hr hz hz0 k]
    by_cases hout : r < ‖z‖
    · rw [ite_eq_left hout]
      rw [ite_eq_left hout]
      calc
        _ = (2 * Real.pi * Complex.I) * (z * z⁻¹) ^ (k + 1) := by
          rw [mul_pow]
          ring
        _ = _ := by rw [mul_inv_cancel₀ hz0, one_pow, mul_one]
    · simp only [ite_eq_right hout, mul_zero]

/-- For a polynomial and coefficient index, the coefficient of its monic linear
quotient is continuous in the division point. Use the explicit finite power-sum
formula. This justifies coefficientwise contour integration. -/
theorem continuous_polynomial_linear_quotient_coeff (P : Polynomial ℂ) (j : ℕ) :
    Continuous (fun w : ℂ ↦ (P /ₘ (Polynomial.X - Polynomial.C w)).coeff j) := by
  simp_rw [Polynomial.coeff_divByMonic_X_sub_C]
  exact continuous_finsetSum _ (fun i hi ↦ (continuous_id.pow _).mul continuous_const)

/-- Dividing a polynomial of degree at most positive `N` by a monic linear factor
leaves natural degree below `N`. Apply the exact division degree formula. This
restricts the selector to `N` consecutive power sums. -/
theorem polynomial_linear_quotient_natDegree_lt (P : Polynomial ℂ) (N : ℕ) (hN : 0 < N)
    (hP : P.natDegree ≤ N) (w : ℂ) : (P /ₘ (Polynomial.X - Polynomial.C w)).natDegree < N := by
  rw [Polynomial.natDegree_divByMonic P (Polynomial.monic_X_sub_C w), Polynomial.natDegree_X_sub_C]
  exact (Nat.sub_le_sub_right hP 1).trans_lt (Nat.sub_lt hN Nat.zero_lt_one)

/-- At a root `x` and a division point `w` where the polynomial is nonzero, the
quotient evaluation divided by the polynomial value equals the simple-pole kernel.
Evaluate monic division and cancel explicit nonzero factors. This identifies
selector values at every root, with repeated roots allowed. -/
theorem polynomial_linear_quotient_eval_div_at_root (P : Polynomial ℂ) (x w : ℂ) (hx : P.eval x = 0)
    (hw : P.eval w ≠ 0) : (P /ₘ (Polynomial.X - Polynomial.C w)).eval x / P.eval w = (w - x)⁻¹ := by
  have hwx : w - x ≠ 0 := by
    intro heq
    exact hw ((congrArg P.eval (sub_eq_zero.mp heq)).trans hx)
  have h :=
    congrArg (Polynomial.eval x) (Polynomial.modByMonic_add_div P (Polynomial.X - Polynomial.C w))
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hx] at h
  have hmul : (w - x) * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x = P.eval w := by
    linear_combination -h
  have hq : (P /ₘ (Polynomial.X - Polynomial.C w)).eval x = (w - x)⁻¹ * P.eval w := by
    calc
      _ = ((w - x)⁻¹ * (w - x)) * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x := by
        rw [inv_mul_cancel₀ hwx, one_mul]
      _ = _ := by rw [mul_assoc, hmul]
  rw [hq, mul_div_cancel_right₀ _ hw]

/-- For a polynomial, inverse-power order, and coefficient index, define the
coefficient integrand of the radial selector. Multiply the monic linear-quotient
coefficient by the inverse power and divide by the polynomial value. This is
integrated on a circle avoiding the roots. -/
noncomputable def radialSelectorIntegrand (P : Polynomial ℂ) (K j : ℕ) (w : ℂ) : ℂ :=
  w⁻¹ ^ K * (P /ₘ (Polynomial.X - Polynomial.C w)).coeff j / P.eval w

/-- For a polynomial, circle radius, inverse-power order, and coefficient cutoff,
form the selector polynomial by normalized contour integration of each quotient
coefficient. Only the first `N` coefficients occur. Its root values distinguish
nodes outside the circle from nodes inside. -/
noncomputable def radialSelectorPolynomial (P : Polynomial ℂ) (r : ℝ) (K N : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range N,
    Polynomial.C
        (-(2 * Real.pi * Complex.I)⁻¹ * circleIntegral (radialSelectorIntegrand P K j) 0 r) *
      Polynomial.X ^ j

/-- For positive coefficient cutoff, the radial selector has natural degree below
that cutoff. Bound the degree of each monomial and the finite sum. This exposes
a finite consecutive block in the interpolation identity. -/
theorem radialSelectorPolynomial_natDegree_lt (P : Polynomial ℂ) (r : ℝ) (K N : ℕ) (hN : 0 < N) :
    (radialSelectorPolynomial P r K N).natDegree < N := by
  apply
    lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_) (Nat.sub_lt hN Nat.zero_lt_one)
  intro j hj
  exact
    (Polynomial.natDegree_C_mul_X_pow_le _ j).trans
      (Nat.le_sub_of_add_le (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))

/-- For a positive circle avoiding all polynomial roots, every selector coefficient
integrand is circle integrable. Use continuity of the monic-quotient coefficient
and the nonvanishing denominators. This permits the finite sum interchange. -/
theorem circleIntegrable_radialSelectorIntegrand (P : Polynomial ℂ) {r : ℝ} (hr : 0 < r)
    (hP : ∀ w ∈ Metric.sphere (0 : ℂ) r, P.eval w ≠ 0) (K j : ℕ) :
    CircleIntegrable (radialSelectorIntegrand P K j) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  have hinv : ContinuousOn (fun w : ℂ ↦ w⁻¹) (Metric.sphere (0 : ℂ) r) :=
    continuous_id.continuousOn.inv₀
      (by
        intro w hw
        have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
        exact norm_ne_zero_iff.mp (ne_of_gt (hwNorm.symm ▸ hr)))
  exact
    ((hinv.pow K).mul (continuous_polynomial_linear_quotient_coeff P j).continuousOn).div
      P.continuous.continuousOn hP

/-- A constant right factor passes through a complex circle integral. Specialize
the scalar integration formula. This handles polynomial evaluation coefficients. -/
theorem circleIntegral_right_mul (f : ℂ → ℂ) (a : ℂ) (r : ℝ) :
    circleIntegral (fun w ↦ f w * a) 0 r = circleIntegral f 0 r * a := by
  simpa only [smul_eq_mul] using circleIntegral.integral_smul_const f a 0 r

/-- If the circle avoids polynomial roots and the polynomial degree is bounded by
the coefficient cutoff, evaluate the selector by one contour integral of the
linear quotient. Expand the quotient evaluation and interchange the finite sum
with the integral. This connects the polynomial to the radial kernel. -/
theorem radialSelectorPolynomial_eval (P : Polynomial ℂ) {r : ℝ} (hr : 0 < r) (K N : ℕ) (hN : 0 < N)
    (hdegree : P.natDegree ≤ N) (hP : ∀ w ∈ Metric.sphere (0 : ℂ) r, P.eval w ≠ 0) (x : ℂ) :
    (radialSelectorPolynomial P r K N).eval x =
      -(2 * Real.pi * Complex.I)⁻¹ *
        circleIntegral
          (fun w : ℂ ↦ w⁻¹ ^ K * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x / P.eval w) 0 r := by
  have hsum :
    circleIntegral (fun w : ℂ ↦ ∑ j ∈ Finset.range N, radialSelectorIntegrand P K j w * x ^ j) 0 r =
      ∑ j ∈ Finset.range N, circleIntegral (radialSelectorIntegrand P K j) 0 r * x ^ j := by
    rw [circleIntegral.integral_fun_sum (f := fun j w ↦ radialSelectorIntegrand P K j w * x ^ j)
        (s := Finset.range N)
        (fun j hj ↦
          (circleIntegrable_radialSelectorIntegrand P hr hP K j).mul_continuousOn
            continuous_const.continuousOn)]
    apply Finset.sum_congr rfl
    intro j hj
    exact circleIntegral_right_mul _ _ _
  have hpoint :
    (fun w : ℂ ↦ ∑ j ∈ Finset.range N, radialSelectorIntegrand P K j w * x ^ j) =
      (fun w : ℂ ↦ w⁻¹ ^ K * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x / P.eval w) := by
    funext w
    rw [Polynomial.eval_eq_sum_range' (polynomial_linear_quotient_natDegree_lt P N hN hdegree w)]
    simp only [radialSelectorIntegrand, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [radialSelectorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← hpoint, hsum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- For every polynomial root, the selector value times its positive-order node
power is one outside the circle and zero inside. Reduce the quotient integral
to the inverse-power kernel and cancel `2πi`. This counts roots with any specified
multiplicity indexing, including zero nodes. -/
theorem radialSelectorPolynomial_eval_root_weighted (P : Polynomial ℂ) {r : ℝ} (hr : 0 < r)
    (k N : ℕ) (hN : 0 < N) (hdegree : P.natDegree ≤ N)
    (hP : ∀ w ∈ Metric.sphere (0 : ℂ) r, P.eval w ≠ 0) (x : ℂ) (hx : P.eval x = 0) :
    x ^ (k + 1) * (radialSelectorPolynomial P r (k + 1) N).eval x = if r < ‖x‖ then 1 else 0 := by
  have hxoff : ‖x‖ ≠ r := by
    intro h
    have hxmem : x ∈ Metric.sphere (0 : ℂ) r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using h
    exact hP x hxmem hx
  have hIntegral :
    circleIntegral
        (fun w : ℂ ↦ w⁻¹ ^ (k + 1) * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x / P.eval w) 0 r =
      circleIntegral (fun w : ℂ ↦ w⁻¹ ^ (k + 1) * (w - x)⁻¹) 0 r := by
    apply circleIntegral.integral_congr hr.le
    intro w hw
    change
      w⁻¹ ^ (k + 1) * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x / P.eval w =
        w⁻¹ ^ (k + 1) * (w - x)⁻¹
    rw [mul_div_assoc, polynomial_linear_quotient_eval_div_at_root P x w hx (hP w hw)]
  have hC : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num only) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [radialSelectorPolynomial_eval P hr (k + 1) N hN hdegree hP x, hIntegral]
  calc
    _ =
        (2 * Real.pi * Complex.I)⁻¹ *
          (-(x ^ (k + 1)) * circleIntegral (fun w : ℂ ↦ w⁻¹ ^ (k + 1) * (w - x)⁻¹) 0 r) :=
      by ring
    _ = _ := by
      rw [circleIntegral_inverse_power_kernel_weighted_selector hr hxoff k]
      by_cases hout : r < ‖x‖
      · simp only [ite_eq_left hout, inv_mul_cancel₀ hC]
      · simp only [ite_eq_right hout, mul_zero]

/-- For a finite root family, express the number of nodes outside a root-free
circle as a coefficient-weighted block of consecutive power sums. Use the radial
selector at each node and the finite polynomial interpolation identity. Repeated
node values remain separate occurrences. This is the exact maximal-node counting
identity preceding the quantitative contour bound. -/
theorem radialSelectorPolynomial_power_sum_identity {n : ℕ} (z : Fin n → ℂ) (P : Polynomial ℂ)
    {r : ℝ} (hr : 0 < r) (k N : ℕ) (hN : 0 < N) (hdegree : P.natDegree ≤ N)
    (hP : ∀ w ∈ Metric.sphere (0 : ℂ) r, P.eval w ≠ 0) (hz : ∀ i, P.eval (z i) = 0) :
    ((Finset.univ.filter (fun i : Fin n ↦ r < ‖z i‖)).card : ℂ) =
      ∑ j ∈ Finset.range N,
        (radialSelectorPolynomial P r (k + 1) N).coeff j * (∑ i : Fin n, z i ^ (k + 1 + j)) := by
  classical
  have hcount :
    (∑ i : Fin n, z i ^ (k + 1) * (radialSelectorPolynomial P r (k + 1) N).eval (z i)) =
      ((Finset.univ.filter (fun i : Fin n ↦ r < ‖z i‖)).card : ℂ) := by
    simp_rw [radialSelectorPolynomial_eval_root_weighted P hr k N hN hdegree hP _ (hz _)]
    simp only [Finset.sum_boole]
  have hidentity :=
    weighted_polynomial_interpolation_eq_power_sums z (fun i ↦ z i ^ (k + 1))
      (fun i ↦ (radialSelectorPolynomial P r (k + 1) N).eval (z i))
      (radialSelectorPolynomial P r (k + 1) N)
      (radialSelectorPolynomial_natDegree_lt P r (k + 1) N hN) (fun _ ↦ rfl)
  rw [hcount] at hidentity
  simpa only [← pow_add] using hidentity

/-- For two polynomial values bounded by `B` at points separated by at least
positive `d`, bound the linear-quotient evaluation by `2B/d`. Evaluate monic
division and use the triangle inequality. This avoids coefficient estimates
for the quotient before contour integration. -/
theorem norm_polynomial_linear_quotient_eval_le (P : Polynomial ℂ) (w x : ℂ) (B d : ℝ) (hd : 0 < d)
    (hgap : d ≤ ‖w - x‖) (hw : ‖P.eval w‖ ≤ B) (hx : ‖P.eval x‖ ≤ B) :
    ‖(P /ₘ (Polynomial.X - Polynomial.C w)).eval x‖ ≤ 2 * B / d := by
  have h :=
    congrArg (Polynomial.eval x) (Polynomial.modByMonic_add_div P (Polynomial.X - Polynomial.C w))
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  have hmul : (w - x) * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x = P.eval w - P.eval x := by
    linear_combination -h
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ ‖(P /ₘ (Polynomial.X - Polynomial.C w)).eval x‖ * ‖w - x‖ :=
      mul_le_mul_of_nonneg_left hgap (norm_nonneg _)
    _ = ‖P.eval w - P.eval x‖ := by rw [mul_comm, ← norm_mul, hmul]
    _ ≤ ‖P.eval w‖ + ‖P.eval x‖ := norm_sub_le _ _
    _ ≤ 2 * B := by linarith only [hw, hx]

/-- For nodes and evaluation point in the unit disk, bound the root polynomial
by `2^n`. Bound each root factor by two and multiply. This controls the numerator
on both the separating circle and the coefficient-estimation circle. -/
theorem norm_root_product_eval_le_two_pow {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) {w : ℂ}
    (hw : ‖w‖ ≤ 1) : ‖(∏ i : Fin n, (Polynomial.X - Polynomial.C (z i))).eval w‖ ≤ (2 : ℝ) ^ n := by
  rw [Polynomial.eval_prod, Complex.norm_prod]
  calc
    _ ≤ ∏ i : Fin n, (2 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro i hi
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact (norm_sub_le w (z i)).trans (by linarith only [hw, hz i])
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- For a positive separating circle, a scaled denominator lower bound, and bounded
polynomial values, bound the selector at a separated point by `2B/(da)`.
Apply the quotient bound and normalized circle-integral estimate; the radius
cancels the extra inverse-power factor. This is the quantitative selector estimate. -/
theorem radialSelectorPolynomial_eval_norm_le (P : Polynomial ℂ) {r : ℝ} (hr : 0 < r) (k N : ℕ)
    (hN : 0 < N) (hdegree : P.natDegree ≤ N) (a B d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hsep : ∀ w ∈ Metric.sphere (0 : ℂ) r, a ≤ r ^ k * ‖P.eval w‖)
    (hbound : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖P.eval w‖ ≤ B) (x : ℂ) (hx : ‖P.eval x‖ ≤ B)
    (hgap : ∀ w ∈ Metric.sphere (0 : ℂ) r, d ≤ ‖w - x‖) :
    ‖(radialSelectorPolynomial P r (k + 1) N).eval x‖ ≤ 2 * B / (d * a) := by
  have hP : ∀ w ∈ Metric.sphere (0 : ℂ) r, P.eval w ≠ 0 := by
    intro w hw heq
    have h := hsep w hw
    rw [heq, norm_zero, mul_zero] at h
    exact (not_le_of_gt ha) h
  rw [radialSelectorPolynomial_eval P hr (k + 1) N hN hdegree hP x]
  have hpoint :
    ∀ w ∈ Metric.sphere (0 : ℂ) r,
      ‖w⁻¹ ^ (k + 1) * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x / P.eval w‖ ≤
        (2 * B / d) / (r * a) := by
    intro w hw
    have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    have hQ := norm_polynomial_linear_quotient_eval_le P w x B d hd (hgap w hw) (hbound w hw) hx
    have hdenom : r * a ≤ r ^ (k + 1) * ‖P.eval w‖ := by
      have h := mul_le_mul_of_nonneg_left (hsep w hw) hr.le
      convert h using 1
      rw [pow_succ]
      ring
    have hnorm :
      ‖w⁻¹ ^ (k + 1) * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x / P.eval w‖ =
        ‖(P /ₘ (Polynomial.X - Polynomial.C w)).eval x‖ / (r ^ (k + 1) * ‖P.eval w‖) := by
      simp only [norm_div, norm_mul, norm_pow, norm_inv, hwNorm, inv_pow]
      ring
    rw [hnorm]
    exact
      (div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hr ha) hdenom).trans
        (div_le_div_of_nonneg_right hQ (mul_nonneg hr.le ha.le))
  have hInt := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hpoint
  have hInt' :
    ‖-(2 * Real.pi * Complex.I)⁻¹ *
          circleIntegral
            (fun w : ℂ ↦ w⁻¹ ^ (k + 1) * (P /ₘ (Polynomial.X - Polynomial.C w)).eval x / P.eval w) 0
            r‖ ≤
      r * ((2 * B / d) / (r * a)) := by
    simpa only [smul_eq_mul, neg_mul, norm_neg] using hInt
  calc
    _ ≤ _ := hInt'
    _ = (r * (2 * B)) / (r * (d * a)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := mul_div_mul_left _ _ (ne_of_gt hr)

/-- For positive node count and nodes in the unit disk, choose a root-free circle
between `3/4` and one. The selector at order `3n+1` has coefficient norm sum at most
`8 * 160^n`. Use the scaled radial product lower bound, estimate values on the
half-radius circle, and apply Parseval coefficient bounds. Repeated roots are allowed. -/
theorem exists_radialSelector_root_product_coefficient_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ r ∈ Set.Icc (3 / 4 : ℝ) 1,
      (∀ w ∈ Metric.sphere (0 : ℂ) r,
          (∏ i : Fin n, (Polynomial.X - Polynomial.C (z i))).eval w ≠ 0) ∧
        (∑ j ∈ Finset.range n,
            ‖(radialSelectorPolynomial (∏ i : Fin n, (Polynomial.X - Polynomial.C (z i))) r
                    (3 * n + 1) n).coeff
                j‖) ≤
          8 * (160 : ℝ) ^ n := by
  let P := ∏ i : Fin n, (Polynomial.X - Polynomial.C (z i))
  have hdegree : P.natDegree ≤ n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i hi ↦ Polynomial.monic_X_sub_C (z i))]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    exact le_refl n
  obtain ⟨r, hr, hcircle⟩ := exists_scaled_circle_product_lower_bound z
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only) hr.1
  have hsep : ∀ w ∈ Metric.sphere (0 : ℂ) r, (1 / 40 : ℝ) ^ n ≤ r ^ (3 * n) * ‖P.eval w‖ := by
    intro w hw
    have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    simpa only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] using hcircle w hwNorm
  have hP : ∀ w ∈ Metric.sphere (0 : ℂ) r, P.eval w ≠ 0 := by
    intro w hw heq
    have h := hsep w hw
    rw [heq, norm_zero, mul_zero] at h
    exact (not_le_of_gt (pow_pos (by norm_num only : (0 : ℝ) < 1 / 40) n)) h
  have hpolybound :
    ∀ x : ℂ,
      ‖x‖ = (1 / 2 : ℝ) →
        ‖(radialSelectorPolynomial P r (3 * n + 1) n).eval x‖ ≤ 8 * (80 : ℝ) ^ n := by
    intro x hx
    have hxbound : ‖P.eval x‖ ≤ (2 : ℝ) ^ n :=
      norm_root_product_eval_le_two_pow z hz
        (by
          rw [hx]; norm_num only)
    have hcirclebound : ∀ w ∈ Metric.sphere (0 : ℂ) r, ‖P.eval w‖ ≤ (2 : ℝ) ^ n := by
      intro w hw
      apply norm_root_product_eval_le_two_pow z hz
      have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
      exact hwNorm.le.trans hr.2
    have hgap : ∀ w ∈ Metric.sphere (0 : ℂ) r, (1 / 4 : ℝ) ≤ ‖w - x‖ := by
      intro w hw
      have h := norm_sub_norm_le w x
      have hwNorm : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
      rw [hwNorm, hx] at h
      linarith only [h, hr.1]
    have hbound :=
      radialSelectorPolynomial_eval_norm_le P hrpos (3 * n) n hn hdegree ((1 / 40 : ℝ) ^ n)
        ((2 : ℝ) ^ n) (1 / 4) (pow_pos (by norm_num only) _) (by norm_num only) hsep hcirclebound x
        hxbound hgap
    convert hbound using 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv, one_mul]
    rw [show (80 : ℝ) = 2 * 40 by norm_num only, mul_pow]
    ring
  have hcoefficient :=
    sum_range_coeff_norm_le_circle_bound_mul_geom (p := radialSelectorPolynomial P r (3 * n + 1) n)
      (r := (1 / 2 : ℝ)) (B := 8 * (80 : ℝ) ^ n) (le_refl _)
      (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) n)) hpolybound n
  have hgeom : (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ n := by
    have h := geom_sum_mul (2 : ℝ) n
    norm_num only at h
    linarith only [h]
  refine ⟨r, hr, hP, ?_⟩
  calc
    _ ≤ _ := hcoefficient
    _ ≤ (8 * (80 : ℝ) ^ n) * (2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hgeom
        (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) n))
    _ = _ := by
      rw [mul_assoc, ← mul_pow]; norm_num only

/-- For positive node count, all nodes in the unit disk, and a specified unit-norm
node, one consecutive power sum at order `3n+1` through `4n` has norm at least
`1/(8 * 160^n)`. The radial selector counts at least one exterior node; its
coefficient norm bound forces a large moment. This gives an exponential maximal-node
block estimate without lower bounds on the other node norms or distinctness. -/
theorem exists_max_node_power_sum_norm_ge_consecutive_triple_block {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (i₀ : Fin n) (hi₀ : ‖z i₀‖ = 1) :
    ∃ j ∈ Finset.range n, 1 / (8 * (160 : ℝ) ^ n) ≤ ‖∑ i : Fin n, z i ^ (3 * n + 1 + j)‖ := by
  classical
  let P := ∏ i : Fin n, (Polynomial.X - Polynomial.C (z i))
  obtain ⟨r, hr, hP, hcoefficient⟩ := exists_radialSelector_root_product_coefficient_bound hn z hz
  let p := radialSelectorPolynomial P r (3 * n + 1) n
  let q := fun j : ℕ ↦ ∑ i : Fin n, z i ^ (3 * n + 1 + j)
  let count := (Finset.univ.filter (fun i : Fin n ↦ r < ‖z i‖)).card
  have hroot : ∀ i, P.eval (z i) = 0 := by
    intro i
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hdegree : P.natDegree ≤ n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i hi ↦ Polynomial.monic_X_sub_C (z i))]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
    exact le_refl n
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only) hr.1
  have hout : r < ‖z i₀‖ := by
    rw [hi₀]
    apply lt_of_le_of_ne hr.2
    intro heq
    apply hP (z i₀) ?_ (hroot i₀)
    simpa only [Metric.mem_sphere, dist_zero_right, hi₀] using heq.symm
  have hcount : (1 : ℝ) ≤ count := by
    have hpos : 0 < count :=
      Finset.card_pos.mpr ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout⟩⟩
    exact_mod_cast Nat.succ_le_of_lt hpos
  have hid : (count : ℂ) = ∑ j ∈ Finset.range n, p.coeff j * q j :=
    radialSelectorPolynomial_power_sum_identity z P hrpos (3 * n) n hn hdegree hP hroot
  obtain ⟨j, hj, hmax⟩ :=
    (Finset.range n).exists_max_image (fun j ↦ ‖q j‖) (Finset.nonempty_range_iff.mpr (ne_of_gt hn))
  have hnorm : (count : ℝ) ≤ ∑ k ∈ Finset.range n, ‖p.coeff k‖ * ‖q k‖ := by
    calc
      _ = ‖(count : ℂ)‖ := (Complex.norm_natCast count).symm
      _ = ‖∑ k ∈ Finset.range n, p.coeff k * q k‖ := by rw [hid]
      _ ≤ ∑ k ∈ Finset.range n, ‖p.coeff k * q k‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul]
  have hupper : (count : ℝ) ≤ ‖q j‖ * (8 * (160 : ℝ) ^ n) := by
    apply hnorm.trans
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖p.coeff k‖ * ‖q j‖ :=
        Finset.sum_le_sum (fun k hk ↦ mul_le_mul_of_nonneg_left (hmax k hk) (norm_nonneg _))
      _ = ‖q j‖ * ∑ k ∈ Finset.range n, ‖p.coeff k‖ := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoefficient (norm_nonneg _)
  refine ⟨j, hj, ?_⟩
  change 1 / (8 * (160 : ℝ) ^ n) ≤ ‖q j‖
  exact
    (div_le_iff₀ (mul_pos (by norm_num only) (pow_pos (by norm_num only) n))).mpr
      (by simpa only [mul_comm] using hcount.trans hupper)

/-- For any finite nonempty node family and a specified nonzero node, a consecutive
power sum at order `3n+1` through `4n` retains its node norm to that power with
factor `1/(8 * 160^n)`. Normalize at a maximal node and rescale the unit-disk
estimate. This removes the global unit-disk restriction. -/
theorem exists_near_node_power_sum_norm_ge_consecutive_triple_block {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℂ) (i₀ : Fin n) (hi₀ : 0 < ‖z i₀‖) :
    ∃ j ∈ Finset.range n,
      (1 / (8 * (160 : ℝ) ^ n)) * ‖z i₀‖ ^ (3 * n + 1 + j) ≤
        ‖∑ i : Fin n, z i ^ (3 * n + 1 + j)‖ := by
  obtain ⟨i, _, hmax⟩ :=
    (Finset.univ : Finset (Fin n)).exists_max_image (fun i ↦ ‖z i‖) ⟨i₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖z i‖ := hi₀.trans_le (hmax i₀ (Finset.mem_univ _))
  let w : Fin n → ℂ := fun j ↦ z j / z i
  have hw : ∀ j, ‖w j‖ ≤ 1 := by
    intro j
    rw [show w j = z j / z i by rfl, norm_div]
    exact (div_le_one hpos).mpr (hmax j (Finset.mem_univ _))
  have hiw : ‖w i‖ = 1 := by
    rw [show w i = z i / z i by rfl, div_self (norm_pos_iff.mp hpos), norm_one]
  obtain ⟨j, hj, hbound⟩ := exists_max_node_power_sum_norm_ge_consecutive_triple_block hn w hw i hiw
  have hsum :
    (∑ k : Fin n, w k ^ (3 * n + 1 + j)) =
      (∑ k : Fin n, z k ^ (3 * n + 1 + j)) / (z i) ^ (3 * n + 1 + j) := by
    simp only [w, div_pow, Finset.sum_div]
  rw [hsum, norm_div, norm_pow] at hbound
  have hscaled := (le_div_iff₀ (pow_pos hpos _)).mp hbound
  refine ⟨j, hj, ?_⟩
  have hcoefficient : 0 ≤ 1 / (8 * (160 : ℝ) ^ n) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) n))
  exact
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hmax i₀ (Finset.mem_univ _)) _)
          hcoefficient).trans
      hscaled

/-- For a nonempty finite set and a specified nonzero node, transfer the consecutive
block estimate through the finite enumeration. Repeated node values remain distinct
indices. This prepares the multiplicity expansion. -/
theorem exists_finset_near_node_power_sum_norm_ge_consecutive_triple_block {α : Type*}
    (s : Finset α) (hs : 0 < s.card) (z : α → ℂ) (i₀ : α) (hi₀ : i₀ ∈ s) (hpos : 0 < ‖z i₀‖) :
    ∃ j ∈ Finset.range s.card,
      (1 / (8 * (160 : ℝ) ^ s.card)) * ‖z i₀‖ ^ (3 * s.card + 1 + j) ≤
        ‖∑ i ∈ s, z i ^ (3 * s.card + 1 + j)‖ := by
  classical
  let e : s ≃ Fin s.card := s.equivFin
  let w : Fin s.card → ℂ := fun i ↦ z (e.symm i).val
  have hnode : w (e ⟨i₀, hi₀⟩) = z i₀ := by simp only [w, Equiv.symm_apply_apply]
  have hsum (m : ℕ) : (∑ i : Fin s.card, w i ^ m) = ∑ i ∈ s, z i ^ m :=
    (Equiv.sum_comp e.symm (fun i : s ↦ z i.val ^ m)).trans
      (Finset.sum_coe_sort s (fun i ↦ z i ^ m))
  obtain ⟨j, hj, hbound⟩ :=
    exists_near_node_power_sum_norm_ge_consecutive_triple_block hs w (e ⟨i₀, hi₀⟩)
      (by
        rw [hnode]; exact hpos)
  exact ⟨j, hj, by simpa only [hnode, hsum] using hbound⟩

/-- For a finite family with natural multiplicities and a specified positive-mass
node whose norm is at least positive `r`, a weighted power sum in the consecutive
triple block has the corresponding lower bound. Expand the multiplicities into
sigma occurrences and apply the finite-set estimate. This is the near-zero input
for a derivative order linear in the total local multiplicity. -/
theorem exists_finset_weighted_power_sum_norm_ge_consecutive_triple_block_of_near {α : Type*}
    (s : Finset α) (multiplicity : α → ℕ) (z : α → ℂ) (i₀ : α) (hi₀ : i₀ ∈ s)
    (hmult : 0 < multiplicity i₀) (r : ℝ) (hr : 0 < r) (hnear : r ≤ ‖z i₀‖) :
    ∃ j ∈ Finset.range (∑ i ∈ s, multiplicity i),
      (1 / (8 * (160 : ℝ) ^ (∑ i ∈ s, multiplicity i))) *
          r ^ (3 * (∑ i ∈ s, multiplicity i) + 1 + j) ≤
        ‖∑ i ∈ s, (multiplicity i : ℂ) * z i ^ (3 * (∑ i ∈ s, multiplicity i) + 1 + j)‖ := by
  classical
  let occurrences := s.sigma fun i ↦ Finset.range (multiplicity i)
  let node : (Σ i : α, ℕ) → ℂ := fun x ↦ z x.1
  have hcard : occurrences.card = ∑ i ∈ s, multiplicity i := by
    simp only [occurrences, Finset.card_sigma, Finset.card_range]
  have hmem : (⟨i₀, 0⟩ : Σ i : α, ℕ) ∈ occurrences :=
    Finset.mem_sigma.mpr ⟨hi₀, Finset.mem_range.mpr hmult⟩
  have hpos : 0 < occurrences.card := Finset.card_pos.mpr ⟨_, hmem⟩
  have hsum (m : ℕ) :
    (∑ x ∈ occurrences, node x ^ m) = ∑ i ∈ s, (multiplicity i : ℂ) * z i ^ m := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [node, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  obtain ⟨j, hj, hbound⟩ :=
    exists_finset_near_node_power_sum_norm_ge_consecutive_triple_block occurrences hpos node ⟨i₀, 0⟩
      hmem (hr.trans_le hnear)
  have hcoefficient : 0 ≤ 1 / (8 * (160 : ℝ) ^ occurrences.card) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) _))
  have hscaled :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hnear (3 * occurrences.card + 1 + j))
          hcoefficient).trans
      hbound
  refine ⟨j, by simpa only [hcard] using hj, ?_⟩
  simpa only [hcard, hsum] using hscaled

/-- For a finite node family embedded into a larger finite index type, padding
with zero nodes preserves every positive power sum. Use the injective finite-sum
identity and zero powers. This lets a shared count cap set the block length. -/
theorem sum_zero_padded_nodes_pow {n N : ℕ} (hnN : n ≤ N) (z : Fin n → ℂ) (m : ℕ) (hm : m ≠ 0) :
    (∑ i : Fin N, (if hi : i.val < n then z ⟨i.val, hi⟩ else 0) ^ m) = ∑ i : Fin n, z i ^ m := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE hnN) (Fin.castLE_injective hnN)
  · intro i hi
    have hnot : ¬i.val < n := by
      intro hlt
      apply hi
      exact ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    rw [dite_eq_right hnot, zero_pow hm]
  · intro i
    change z i ^ m = (if h : i.val < n then z ⟨i.val, h⟩ else 0) ^ m
    rw [dite_eq_left i.isLt]

/-- For a nonzero specified node and a count cap `N`, select a power in `3N+1`
through `4N` with the cap-dependent exponential signal. Pad the family with zero
nodes before applying the consecutive estimate. This avoids a block scale times
multiplicity order bound. -/
theorem exists_near_node_power_sum_norm_ge_consecutive_triple_block_of_cap {n N : ℕ} (hn : 0 < n)
    (hnN : n ≤ N) (z : Fin n → ℂ) (i₀ : Fin n) (hi₀ : 0 < ‖z i₀‖) :
    ∃ j ∈ Finset.range N,
      (1 / (8 * (160 : ℝ) ^ N)) * ‖z i₀‖ ^ (3 * N + 1 + j) ≤
        ‖∑ i : Fin n, z i ^ (3 * N + 1 + j)‖ := by
  let w : Fin N → ℂ := fun i ↦ if hi : i.val < n then z ⟨i.val, hi⟩ else 0
  let i : Fin N := Fin.castLE hnN i₀
  have hnode : w i = z i₀ := by
    change (if h : i₀.val < n then z ⟨i₀.val, h⟩ else 0) = z i₀
    rw [dite_eq_left i₀.isLt]
  obtain ⟨j, hj, hbound⟩ :=
    exists_near_node_power_sum_norm_ge_consecutive_triple_block (hn.trans_le hnN) w i
      (by
        rw [hnode]; exact hi₀)
  have hpower : 3 * N + 1 + j ≠ 0 :=
    ne_of_gt ((Nat.zero_lt_succ (3 * N)).trans_le (Nat.le_add_right _ j))
  refine ⟨j, hj, ?_⟩
  rw [hnode] at hbound
  simpa only [w, sum_zero_padded_nodes_pow hnN z _ hpower] using hbound

/-- For a nonempty finite set within a count cap, transfer the zero-padded
consecutive estimate through its finite enumeration. This prepares a block length
shared by all local supports with that cap. -/
theorem exists_finset_near_node_power_sum_norm_ge_consecutive_triple_block_of_cap {α : Type*}
    (s : Finset α) (hs : 0 < s.card) (N : ℕ) (hcap : s.card ≤ N) (z : α → ℂ) (i₀ : α) (hi₀ : i₀ ∈ s)
    (hpos : 0 < ‖z i₀‖) :
    ∃ j ∈ Finset.range N,
      (1 / (8 * (160 : ℝ) ^ N)) * ‖z i₀‖ ^ (3 * N + 1 + j) ≤ ‖∑ i ∈ s, z i ^ (3 * N + 1 + j)‖ := by
  classical
  let e : s ≃ Fin s.card := s.equivFin
  let w : Fin s.card → ℂ := fun i ↦ z (e.symm i).val
  have hnode : w (e ⟨i₀, hi₀⟩) = z i₀ := by simp only [w, Equiv.symm_apply_apply]
  have hsum (m : ℕ) : (∑ i : Fin s.card, w i ^ m) = ∑ i ∈ s, z i ^ m :=
    (Equiv.sum_comp e.symm (fun i : s ↦ z i.val ^ m)).trans
      (Finset.sum_coe_sort s (fun i ↦ z i ^ m))
  obtain ⟨j, hj, hbound⟩ :=
    exists_near_node_power_sum_norm_ge_consecutive_triple_block_of_cap hs hcap w (e ⟨i₀, hi₀⟩)
      (by
        rw [hnode]; exact hpos)
  exact ⟨j, hj, by simpa only [hnode, hsum] using hbound⟩

/-- For natural multiplicities with total mass at most `N` and a positive near-node
norm bound, obtain a weighted power sum at order `3N+1` through `4N` with factor
`1/(8 * 160^N)`. Expand multiplicities and pad unused mass with zero nodes. This
is the multiplicity-preserving local detector with derivative order linear in a
shared count cap. -/
theorem exists_finset_weighted_power_sum_norm_ge_consecutive_triple_block_of_cap {α : Type*}
    (s : Finset α) (multiplicity : α → ℕ) (z : α → ℂ) (N : ℕ) (hcap : (∑ i ∈ s, multiplicity i) ≤ N)
    (i₀ : α) (hi₀ : i₀ ∈ s) (hmult : 0 < multiplicity i₀) (r : ℝ) (hr : 0 < r)
    (hnear : r ≤ ‖z i₀‖) :
    ∃ j ∈ Finset.range N,
      (1 / (8 * (160 : ℝ) ^ N)) * r ^ (3 * N + 1 + j) ≤
        ‖∑ i ∈ s, (multiplicity i : ℂ) * z i ^ (3 * N + 1 + j)‖ := by
  classical
  let occurrences := s.sigma fun i ↦ Finset.range (multiplicity i)
  let node : (Σ i : α, ℕ) → ℂ := fun x ↦ z x.1
  have hcard : occurrences.card = ∑ i ∈ s, multiplicity i := by
    simp only [occurrences, Finset.card_sigma, Finset.card_range]
  have hmem : (⟨i₀, 0⟩ : Σ i : α, ℕ) ∈ occurrences :=
    Finset.mem_sigma.mpr ⟨hi₀, Finset.mem_range.mpr hmult⟩
  have hpos : 0 < occurrences.card := Finset.card_pos.mpr ⟨_, hmem⟩
  have hsum (m : ℕ) :
    (∑ x ∈ occurrences, node x ^ m) = ∑ i ∈ s, (multiplicity i : ℂ) * z i ^ m := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [node, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  obtain ⟨j, hj, hbound⟩ :=
    exists_finset_near_node_power_sum_norm_ge_consecutive_triple_block_of_cap occurrences hpos N
      (hcard.trans_le hcap) node ⟨i₀, 0⟩ hmem (hr.trans_le hnear)
  have hcoefficient : 0 ≤ 1 / (8 * (160 : ℝ) ^ N) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) _))
  have hscaled :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hnear (3 * N + 1 + j)) hcoefficient).trans
      hbound
  exact ⟨j, hj, by simpa only [hsum] using hscaled⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
