/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Integral comparisons for logarithmic power tails

The decreasing envelope (log x+1) x^(-r-1) has integral r^(-2)+r^(-1)
on the interval from one to infinity, for positive r.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive r and x, differentiate the explicit logarithmic-power primitive.
The derivative is (log x+1)x^(-r-1). The product rule and the power identity
reduce the calculation to rational arithmetic, enabling the improper integral evaluation. -/
theorem hasDerivAt_logPower_primitive {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ -(Real.log t / r + r⁻¹ ^ 2 + r⁻¹) * t ^ (-r))
      ((Real.log x + 1) * x ^ (-r - 1)) x := by
  have hd :=
    (((Real.hasDerivAt_log hx.ne').div_const r).add_const (r⁻¹ ^ 2 + r⁻¹)).neg.mul
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -r))
  have he :
    -(x⁻¹ / r) * x ^ (-r) + -(Real.log x / r + (r⁻¹ ^ 2 + r⁻¹)) * (-r * x ^ (-r - 1)) =
      (Real.log x + 1) * x ^ (-r - 1) := by
    rw [Real.rpow_sub_one hx.ne' (-r)]
    field_simp [hr.ne', hx.ne']
    ring
  simpa only [add_assoc] using he ▸ hd

/-- For positive r, the logarithmic-power primitive tends to zero at infinity.
Logarithm grows more slowly than x^r, and x^(-r) tends to zero.
This provides the upper endpoint limit in the improper integral. -/
theorem tendsto_logPower_primitive_zero {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (fun t : ℝ ↦ -(Real.log t / r + r⁻¹ ^ 2 + r⁻¹) * t ^ (-r)) Filter.atTop
      (nhds 0) := by
  have hl := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have hp := tendsto_rpow_neg_atTop hr
  have ht := ((hl.div_const r).add (hp.mul_const (r⁻¹ ^ 2 + r⁻¹))).neg
  have he :
    (fun t : ℝ ↦ -(Real.log t / t ^ r / r + t ^ (-r) * (r⁻¹ ^ 2 + r⁻¹))) =ᶠ[Filter.atTop]
      (fun t : ℝ ↦ -(Real.log t / r + r⁻¹ ^ 2 + r⁻¹) * t ^ (-r)) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.rpow_neg ht]
    ring
  simpa only [zero_div, zero_mul, add_zero, neg_zero] using ht.congr' he

/-- For x at least one, the logarithmic-power envelope is nonnegative for every r.
Both log x+1 and the power factor are nonnegative. This permits integral-test comparisons. -/
theorem logPower_envelope_nonneg {r x : ℝ} (hx : 1 ≤ x) : 0 ≤ (Real.log x + 1) * x ^ (-r - 1) :=
  mul_nonneg (add_nonneg (Real.log_nonneg hx) zero_le_one)
    (Real.rpow_nonneg (zero_le_one.trans hx) _)

/-- For positive r, the logarithmic-power envelope is integrable on (1,infinity).
Its nonnegative derivative primitive has a finite limit at infinity.
This verifies the integrability assumption of the sum-integral comparison. -/
theorem integrableOn_logPower_envelope {r : ℝ} (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ (Real.log x + 1) * x ^ (-r - 1)) (Set.Ioi 1) := by
  exact
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (fun x hx ↦ hasDerivAt_logPower_primitive hr (zero_lt_one.trans_le hx))
      (fun x hx ↦ logPower_envelope_nonneg hx.le) (tendsto_logPower_primitive_zero hr)

/-- For positive r, the integral of (log x+1)x^(-r-1) from one to infinity
is r^(-2)+r^(-1). Evaluate the primitive at one and its zero limit at infinity.
This supplies the explicit error allowance for logarithmic Dirichlet series. -/
theorem integral_logPower_envelope {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Set.Ioi 1, (Real.log x + 1) * x ^ (-r - 1)) = r⁻¹ ^ 2 + r⁻¹ := by
  have he :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx ↦ hasDerivAt_logPower_primitive hr (zero_lt_one.trans_le hx))
      (integrableOn_logPower_envelope hr) (tendsto_logPower_primitive_zero hr)
  simpa only [Real.log_one, zero_div, zero_add, Real.one_rpow, mul_one, zero_sub, neg_neg] using he

/-- At positive x, the envelope derivative equals x^(-r-2) times
1-(r+1)(log x+1). Differentiate both factors and normalize the real powers.
Its sign proves monotonicity on [1,infinity] for positive r. -/
theorem hasDerivAt_logPower_envelope {r x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ (Real.log t + 1) * t ^ (-r - 1))
      (x ^ (-r - 2) * (1 - (r + 1) * (Real.log x + 1))) x := by
  have hd :=
    ((Real.hasDerivAt_log hx.ne').add_const 1).mul
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -r - 1))
  have he :
    x⁻¹ * x ^ (-r - 1) + (Real.log x + 1) * ((-r - 1) * x ^ (-r - 1 - 1)) =
      x ^ (-r - 2) * (1 - (r + 1) * (Real.log x + 1)) := by
    rw [show -r - 2 = (-r - 1) - 1 by ring, Real.rpow_sub_one hx.ne' (-r - 1)]
    ring
  exact he ▸ hd

/-- For positive r, the logarithmic-power envelope decreases on [1,infinity].
Its derivative is nonpositive because log x is nonnegative there.
This allows the infinite sum from two to be bounded by the integral from one. -/
theorem antitoneOn_logPower_envelope {r : ℝ} (hr : 0 < r) :
    AntitoneOn (fun x : ℝ ↦ (Real.log x + 1) * x ^ (-r - 1)) (Set.Ici 1) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
      (fun x hx ↦
        (hasDerivAt_logPower_envelope (r := r)
            (zero_lt_one.trans_le hx)).continuousAt.continuousWithinAt)
      (fun x hx ↦
        (hasDerivAt_logPower_envelope (zero_lt_one.trans_le (interior_subset hx))).hasDerivWithinAt)
  intro x hx
  have hx1 : 1 ≤ x := interior_subset hx
  have hl := Real.log_nonneg hx1
  have hb : 1 - (r + 1) * (Real.log x + 1) ≤ 0 := by nlinarith only [hr, hl]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (zero_le_one.trans hx1) _) hb

/-- For positive r, the sum of the logarithmic-power envelope over integers at least two
is at most r^(-2)+r^(-1). Apply the decreasing integral test and the explicit integral.
This bounds von Mangoldt Dirichlet series without a prime-number-theorem input. -/
theorem tsum_logPower_envelope_le {r : ℝ} (hr : 0 < r) :
    (∑' n : ℕ, (Real.log (n + 2 : ℕ) + 1) * (n + 2 : ℕ) ^ (-r - 1)) ≤ r⁻¹ ^ 2 + r⁻¹ := by
  have ht :=
    AntitoneOn.tsum_comp_add_le_integral 1
      (by simpa only [Nat.cast_one] using antitoneOn_logPower_envelope hr)
      (by simpa only [Nat.cast_one] using integrableOn_logPower_envelope hr)
      (fun x hx ↦
        logPower_envelope_nonneg (r := r) (x := x)
          (by simpa only [Nat.cast_one] using (Set.mem_Ioi.mp hx).le))
  simp only [Nat.cast_one] at ht
  rw [integral_logPower_envelope hr] at ht
  simpa only [Nat.add_assoc] using ht

/-- The logarithmic inverse-square envelope past an integer cutoff is bounded by its
explicit integral. Use the logarithmic-power primitive with exponent one and the
decreasing integral comparison on the shifted natural sequence. This supplies the
quantitative logarithmic-over-height tail needed for zero-height bins. -/
theorem tsum_logPower_envelope_tail_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : ℕ, (Real.log ((n + N + 1 : ℕ) : ℝ) + 1) * ((n + N + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) ≤
      (Real.log (N : ℝ) + 2) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase := antitoneOn_logPower_envelope (r := (1 : ℝ)) (by norm_num only)
  have hanti :
    AntitoneOn (fun x : ℝ ↦ (Real.log x + 1) * x ^ (-(1 : ℝ) - 1)) (Set.Ici (N : ℝ)) := by
    intro x hx y hy hxy
    apply hbase
    · exact hNreal.trans hx
    · exact hNreal.trans hy
    · exact hxy
  have hi :=
    (integrableOn_logPower_envelope (by norm_num only : (0 : ℝ) < 1)).mono_set
      (Set.Ioi_subset_Ioi hNreal)
  have htail :=
    hanti.tsum_comp_add_le_integral N hi
      (fun x hx ↦
        logPower_envelope_nonneg (r := (1 : ℝ)) (by exact hNreal.trans (Set.mem_Ioi.mp hx).le))
  have hderiv :
    ∀ x ∈ Set.Ici (N : ℝ),
      HasDerivAt (fun t : ℝ ↦ -(Real.log t / 1 + (1 : ℝ)⁻¹ ^ 2 + (1 : ℝ)⁻¹) * t ^ (-(1 : ℝ)))
        ((Real.log x + 1) * x ^ (-(1 : ℝ) - 1)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hNr hx
    exact hasDerivAt_logPower_primitive (r := (1 : ℝ)) (by norm_num only) hx0
  have hlim := tendsto_logPower_primitive_zero (r := (1 : ℝ)) (by norm_num only)
  have hint := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hi hlim
  have hbound :
    (∫ x : ℝ in Set.Ioi (N : ℝ), (Real.log x + 1) * x ^ (-(1 : ℝ) - 1)) =
      (Real.log (N : ℝ) + 2) / N := by
    rw [hint]
    norm_num only
    rw [Real.rpow_neg (le_of_lt hNr)]
    field_simp
    rw [Real.rpow_one]
    ring
  rw [show (-(2 : ℝ)) = (-(1 : ℝ) - 1) by norm_num only]
  exact htail.trans_eq hbound

/-- For positive r, the logarithmic-power envelope evaluated on natural numbers is summable.
Apply the integral test past one; the finitely many earlier terms do not affect convergence.
This supplies absolute convergence for the von Mangoldt comparison. -/
theorem summable_logPower_envelope {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ ↦ (Real.log n + 1) * (n : ℝ) ^ (-r - 1)) := by
  exact
    AntitoneOn.summable_of_integrableOn_Ioi (N := 1) (f := fun x : ℝ ↦
      (Real.log x + 1) * x ^ (-r - 1))
      (by simpa only [Nat.cast_one] using antitoneOn_logPower_envelope hr)
      (by simpa only [Nat.cast_one] using integrableOn_logPower_envelope hr)
      (fun x hx ↦
        logPower_envelope_nonneg (r := r) (x := x)
          (by simpa only [Nat.cast_one] using (Set.mem_Ioi.mp hx).le))

end PseudoPrime.Analysis
