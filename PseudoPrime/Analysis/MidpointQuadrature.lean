/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SecondDerivativeInterpolation
public import PseudoPrime.Analysis.MeanSquareCauchySchwarz
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Lower midpoint quadrature bounds from explicit second derivatives -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For continuous convex g on an ordered interval, width times the midpoint
value is at most its integral. Average reflected pairs using convexity, then
integrate the reflection identity. This is the midpoint Jensen inequality. -/
theorem midpoint_mul_le_integral_of_convex {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ConvexOn ℝ (Set.Icc a b) g) (hc : ContinuousOn g (Set.Icc a b)) :
    (b - a) * g ((a + b) / 2) ≤ ∫ x in a..b, g x := by
  have hmem (x : ℝ) (hx : x ∈ Set.Icc a b) : a + b - x ∈ Set.Icc a b := by
    constructor <;> linarith only [hx.1, hx.2]
  have hci : ContinuousOn g (Set.uIcc a b) := by simpa only [Set.uIcc_of_le hab] using hc
  have hcr : ContinuousOn (fun x ↦ g (a + b - x)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact hc.comp (continuous_const.sub continuous_id).continuousOn hmem
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc a b) : 2 * g ((a + b) / 2) ≤ g x + g (a + b - x) := by
    have h :=
      hg.2 hx (hmem x hx) (by norm_num only : (0 : ℝ) ≤ 1 / 2) (by norm_num only : (0 : ℝ) ≤ 1 / 2)
        (by norm_num only)
    simp only [smul_eq_mul] at h
    have he : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (a + b - x) = (a + b) / 2 := by ring
    rw [he] at h
    linarith only [h]
  have h :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab intervalIntegrable_const
      (hci.intervalIntegrable.add hcr.intervalIntegrable) hpoint
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add hci.intervalIntegrable hcr.intervalIntegrable,
    intervalIntegral.integral_comp_sub_left g (a + b)] at h
  have ha : a + b - b = a := by ring
  have hb : a + b - a = b := by ring
  simp only [ha, hb, smul_eq_mul] at h
  linarith only [h]

/-- For explicit derivatives f',f'' on an ordered interval and f''>=-M,
the midpoint approximation minus M width^3/24 is a lower integral bound.
Quadratic correction gives convexity; its exact integral gives the error.
This supplies the single-cell bound for the Gaussian cutoff certificate. -/
theorem midpoint_integral_lower_of_second_deriv_ge {f f' f'' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x) (hb : ∀ x ∈ Set.Icc a b, -M ≤ f'' x) :
    (b - a) * f ((a + b) / 2) - M * (b - a) ^ 3 / 24 ≤ ∫ x in a..b, f x := by
  have hc :=
    concaveOn_quadratic_correction_of_second_deriv_le (fun x hx ↦ (hf x hx).neg)
      (fun x hx ↦ (hf' x hx).neg) (fun x hx ↦ neg_le_neg (hb x hx))
  have hconv : ConvexOn ℝ (Set.Icc a b) (fun x ↦ f x + M / 2 * x ^ 2) := by
    convert hc.neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hfc : ContinuousOn f (Set.Icc a b) := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun x ↦ f x + M / 2 * x ^ 2) (Set.Icc a b) :=
    hfc.add (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hi : IntervalIntegrable f MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hp : IntervalIntegrable (fun x : ℝ ↦ M / 2 * x ^ 2) MeasureTheory.volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have h := midpoint_mul_le_integral_of_convex hab hconv hcont
  rw [intervalIntegral.integral_add hi hp, intervalIntegral.integral_const_mul, integral_pow] at h
  have he :
    M / 2 * ((b ^ 3 - a ^ 3) / 3) - (b - a) * (M / 2 * ((a + b) / 2) ^ 2) =
      M * (b - a) ^ 3 / 24 := by
    ring
  nlinarith only [h, he]

/-- If each grid cell has the stated midpoint lower bound and f is integrable
on each cell, sum the bounds and telescope adjacent integrals.
This combines local certificates without any global convergence assumption. -/
theorem midpoint_sum_lower_of_cell_bounds {f : ℝ → ℝ} {p : ℕ → ℝ} {M : ℝ} {n : ℕ}
    (hi : ∀ k < n, IntervalIntegrable f MeasureTheory.volume (p k) (p (k + 1)))
    (hc :
      ∀ k < n,
        (p (k + 1) - p k) * f ((p k + p (k + 1)) / 2) - M * (p (k + 1) - p k) ^ 3 / 24 ≤
          ∫ x in p k..p (k + 1), f x) :
    (∑ k ∈ Finset.range n, (p (k + 1) - p k) * f ((p k + p (k + 1)) / 2)) -
        (∑ k ∈ Finset.range n, M * (p (k + 1) - p k) ^ 3 / 24) ≤
      ∫ x in p 0..p n, f x := by
  have h := Finset.sum_le_sum (fun k hk ↦ hc k (Finset.mem_range.mp hk))
  rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals hi] at h
  exact h

/-- For an ordered finite grid with explicit first and second derivatives on
each cell and lower curvature bound -M, the midpoint sum minus the cubic
cell errors is a lower bound for the full integral. This is the composite rule. -/
theorem midpoint_sum_lower_of_second_deriv_ge {f f' f'' : ℝ → ℝ} {p : ℕ → ℝ} {M : ℝ} {n : ℕ}
    (hab : ∀ k < n, p k ≤ p (k + 1))
    (hf : ∀ k < n, ∀ x ∈ Set.Icc (p k) (p (k + 1)), HasDerivAt f (f' x) x)
    (hf' : ∀ k < n, ∀ x ∈ Set.Icc (p k) (p (k + 1)), HasDerivAt f' (f'' x) x)
    (hb : ∀ k < n, ∀ x ∈ Set.Icc (p k) (p (k + 1)), -M ≤ f'' x) :
    (∑ k ∈ Finset.range n, (p (k + 1) - p k) * f ((p k + p (k + 1)) / 2)) -
        (∑ k ∈ Finset.range n, M * (p (k + 1) - p k) ^ 3 / 24) ≤
      ∫ x in p 0..p n, f x := by
  apply midpoint_sum_lower_of_cell_bounds
  · intro k hk
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (hab k hk)]
    exact fun x hx ↦ (hf k hk x hx).continuousAt.continuousWithinAt
  · intro k hk
    exact midpoint_integral_lower_of_second_deriv_ge (hab k hk) (hf k hk) (hf' k hk) (hb k hk)

/-- On a uniform finite grid, integrable cell bounds combine into the midpoint sum
minus n times the single-cell error. The width and center identities reduce the general
composite rule to this form, used by the fixed-point Gaussian cutoff certificate. -/
theorem uniform_midpoint_sum_lower_of_cell_bounds {f : ℝ → ℝ} {a h M : ℝ} {n : ℕ}
    (hi :
      ∀ k < n,
        IntervalIntegrable f MeasureTheory.volume (a + (k : ℝ) * h) (a + ((k + 1 : ℕ) : ℝ) * h))
    (hc :
      ∀ k < n,
        h * f (a + ((k : ℝ) + 1 / 2) * h) - M * h ^ 3 / 24 ≤
          ∫ x in (a + (k : ℝ) * h)..(a + ((k + 1 : ℕ) : ℝ) * h), f x) :
    h * (∑ k ∈ Finset.range n, f (a + ((k : ℝ) + 1 / 2) * h)) - (n : ℝ) * (M * h ^ 3 / 24) ≤
      ∫ x in a..(a + (n : ℝ) * h), f x := by
  have hw (k : ℕ) : a + ((k + 1 : ℕ) : ℝ) * h - (a + (k : ℝ) * h) = h := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hm (k : ℕ) :
    (a + (k : ℝ) * h + (a + ((k + 1 : ℕ) : ℝ) * h)) / 2 = a + ((k : ℝ) + 1 / 2) * h := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hs :=
    midpoint_sum_lower_of_cell_bounds (M := M) hi
      (fun k hk ↦ by
        simp only [hw, hm]
        exact hc k hk)
  simp only [hw, hm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_zero, zero_mul,
    add_zero] at hs
  rw [← Finset.mul_sum] at hs
  exact hs

/-- On a uniform grid of nonnegative width, explicit first and second derivatives
and curvature bounded below by -M imply the composite midpoint lower bound.
Continuity gives cell integrability; the single-cell theorem supplies all errors.
This removes quadrature assumptions from the Gaussian finite-node interface. -/
theorem uniform_midpoint_sum_lower_of_second_deriv_ge {f f' f'' : ℝ → ℝ} {a h M : ℝ} {n : ℕ}
    (hh : 0 ≤ h)
    (hf :
      ∀ k < n, ∀ x ∈ Set.Icc (a + (k : ℝ) * h) (a + ((k + 1 : ℕ) : ℝ) * h), HasDerivAt f (f' x) x)
    (hf' :
      ∀ k < n, ∀ x ∈ Set.Icc (a + (k : ℝ) * h) (a + ((k + 1 : ℕ) : ℝ) * h), HasDerivAt f' (f'' x) x)
    (hb : ∀ k < n, ∀ x ∈ Set.Icc (a + (k : ℝ) * h) (a + ((k + 1 : ℕ) : ℝ) * h), -M ≤ f'' x) :
    h * (∑ k ∈ Finset.range n, f (a + ((k : ℝ) + 1 / 2) * h)) - (n : ℝ) * (M * h ^ 3 / 24) ≤
      ∫ x in a..(a + (n : ℝ) * h), f x := by
  have hw (k : ℕ) : a + ((k + 1 : ℕ) : ℝ) * h - (a + (k : ℝ) * h) = h := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hm (k : ℕ) :
    (a + (k : ℝ) * h + (a + ((k + 1 : ℕ) : ℝ) * h)) / 2 = a + ((k : ℝ) + 1 / 2) * h := by
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  have hab (k : ℕ) : a + (k : ℝ) * h ≤ a + ((k + 1 : ℕ) : ℝ) * h := by
    rw [← sub_nonneg, hw]
    exact hh
  apply uniform_midpoint_sum_lower_of_cell_bounds
  · intro k hk
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (hab k)]
    exact fun x hx ↦ (hf k hk x hx).continuousAt.continuousWithinAt
  · intro k hk
    have hc := midpoint_integral_lower_of_second_deriv_ge (hab k) (hf k hk) (hf' k hk) (hb k hk)
    simpa only [hw, hm] using hc

/--
Inputs: a continuous complex-valued function, a center, a positive half-width, and a global
Lipschitz bound on that cell.
Claim: the center value squared, multiplied by the half-width, is bounded by the cell's squared
norm integral plus the explicit cubic Lipschitz error.
Proof: the triangle inequality bounds the center norm by the norm at each cell point plus the
Lipschitz variation; square this estimate and integrate the resulting pointwise bound.
Role: supplies a local lower-energy estimate for transferring large values on a height mesh to
continuous height integrals.
-/
theorem cell_norm_sq_le_integral_add_lipschitz_error {f : ℝ → ℂ} {x h L : ℝ} (hf : Continuous f)
    (hh : 0 < h) (hL : 0 ≤ L) (hLip : ∀ y, |y - x| ≤ h → ‖f x - f y‖ ≤ L * |y - x|) :
    h * ‖f x‖ ^ 2 ≤ (∫ y in (x - h)..(x + h), ‖f y‖ ^ 2) + 2 * h ^ 3 * L ^ 2 := by
  have hpoint : ∀ y ∈ Set.Icc (x - h) (x + h), ‖f x‖ ^ 2 ≤ 2 * ‖f y‖ ^ 2 + 2 * (L * h) ^ 2 := by
    intro y hy
    have hdist : |y - x| ≤ h := by
      rw [abs_le]
      constructor <;> linarith only [hy.1, hy.2, hh]
    have hdiff : f x = f y + (f x - f y) := by abel
    have htriangle := norm_add_le (f y) (f x - f y)
    rw [← hdiff] at htriangle
    have hb := hLip y hdist
    have hprod : 0 ≤ L * h := mul_nonneg hL hh.le
    have hsum : ‖f x‖ ≤ ‖f y‖ + L * h := by
      calc
        ‖f x‖ ≤ ‖f y‖ + ‖f x - f y‖ := htriangle
        _ ≤ ‖f y‖ + L * h := add_le_add_right (le_trans hb (mul_le_mul_of_nonneg_left hdist hL)) _
    have hsumSq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) hprod)).mpr hsum
    have hquad : (‖f y‖ + L * h) ^ 2 ≤ 2 * ‖f y‖ ^ 2 + 2 * (L * h) ^ 2 := by
      nlinarith only [sq_nonneg (‖f y‖ - L * h)]
    exact hsumSq.trans hquad
  have hcont : Continuous fun y : ℝ => 2 * ‖f y‖ ^ 2 + 2 * (L * h) ^ 2 :=
    continuous_const.mul (hf.norm.pow 2) |>.add continuous_const
  have hleft :
    IntervalIntegrable (fun _ : ℝ => (‖f x‖ ^ 2 : ℝ)) MeasureTheory.volume (x - h) (x + h) :=
    intervalIntegrable_const
  have hright :
    IntervalIntegrable (fun y : ℝ => 2 * ‖f y‖ ^ 2 + 2 * (L * h) ^ 2) MeasureTheory.volume (x - h)
      (x + h) :=
    hcont.intervalIntegrable (x - h) (x + h)
  have hmono :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (show x - h ≤ x + h by linarith only [hh]) hleft hright hpoint
  have hi1 : IntervalIntegrable (fun y : ℝ => ‖f y‖ ^ 2) MeasureTheory.volume (x - h) (x + h) :=
    (hf.norm.pow 2).intervalIntegrable (x - h) (x + h)
  have hi2 :
    IntervalIntegrable (fun _ : ℝ => (2 * (L * h) ^ 2 : ℝ)) MeasureTheory.volume (x - h) (x + h) :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_add (μ := MeasureTheory.volume) (hi1.const_mul 2) hi2] at hmono
  rw [intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)] at hmono
  have hconst : (∫ y in (x - h)..(x + h), (2 * (L * h) ^ 2 : ℝ)) = 4 * h ^ 3 * L ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hconst] at hmono
  have hleftInt : (∫ y in (x - h)..(x + h), (‖f x‖ ^ 2 : ℝ)) = 2 * h * ‖f x‖ ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hleftInt] at hmono
  nlinarith only [hmono]

/-- The squared endpoint difference is bounded by the interval length times the derivative's
squared integral energy, by the fundamental theorem of calculus and Cauchy–Schwarz. -/
theorem derivative_difference_sq_le_interval_energy {f g : ℝ → ℂ} {a x b : ℝ} (hax : a ≤ x)
    (hxb : x ≤ b) (hg : Continuous g) (hderiv : ∀ t ∈ Set.Icc a x, HasDerivAt f (g t) t) :
    ‖f x - f a‖ ^ 2 ≤ (x - a) * (∫ t in a..b, ‖g t‖ ^ 2) := by
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := x)
      (fun t ht =>
        hderiv t
          (by
            rcases Set.mem_uIcc.mp ht with h₁ | h₂
            · exact h₁
            · exact ⟨le_trans hax h₂.1, le_trans h₂.2 hax⟩))
      (hg.intervalIntegrable a x)
  have hCS :=
    PseudoPrime.Analysis.ExponentialMeanSquare.norm_intervalIntegral_mul_sq_le hax (f := g) (g :=
      fun _ : ℝ => (1 : ℂ)) hg.continuousOn continuousOn_const
  simp only [mul_one, norm_one, one_pow, intervalIntegral.integral_const, smul_eq_mul] at hCS
  rw [hFTC] at hCS
  have hsub :=
    intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume) (show a ≤ a by rfl) hax hxb
      (Filter.Eventually.of_forall fun t => sq_nonneg ‖g t‖)
      ((hg.norm.pow 2).intervalIntegrable a b)
  have hprod := mul_le_mul_of_nonneg_left hsub (sub_nonneg.mpr hax)
  nlinarith only [hCS, hprod]

/-- On a symmetric cell of half-width h, the midpoint value of a continuously differentiable
complex function is controlled by its squared norm integral and the derivative's squared integral
energy. This local estimate is the cell bound for mesh estimates with derivative energy. -/
theorem cell_norm_sq_le_integral_add_derivative_energy {f g : ℝ → ℂ} {x h : ℝ} (hf : Continuous f)
    (hg : Continuous g) (hh : 0 < h)
    (hderiv : ∀ y ∈ Set.Icc (x - h) (x + h), HasDerivAt f (g y) y) :
    h * ‖f x‖ ^ 2 ≤
      (∫ y in (x - h)..(x + h), ‖f y‖ ^ 2) + 2 * h ^ 2 * (∫ y in (x - h)..(x + h), ‖g y‖ ^ 2) := by
  let E : ℝ := ∫ y in (x - h)..(x + h), ‖g y‖ ^ 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact
      intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) (by linarith only [hh])
        (fun y hy => sq_nonneg ‖g y‖)
  have hvariation : ∀ y ∈ Set.Icc (x - h) (x + h), ‖f x - f y‖ ^ 2 ≤ h * E := by
    intro y hy
    by_cases hyx : y ≤ x
    · have hdiff :=
        derivative_difference_sq_le_interval_energy (f := f) (g := g) (a := y) (x := x) (b := x) hyx
          le_rfl hg
          (fun t ht => hderiv t ⟨le_trans hy.1 ht.1, le_trans ht.2 (by linarith only [hh])⟩)
      have hsub :=
        intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume)
          (by linarith only [hy.1]) hyx (by linarith only [hh])
          (Filter.Eventually.of_forall fun t => sq_nonneg ‖g t‖)
          ((hg.norm.pow 2).intervalIntegrable (x - h) (x + h))
      have hlen : x - y ≤ h := by linarith only [hy.1]
      have hlenprod : (x - y) * E ≤ h * E := mul_le_mul_of_nonneg_right hlen hE
      exact le_trans hdiff (le_trans (mul_le_mul_of_nonneg_left hsub (sub_nonneg.mpr hyx)) hlenprod)
    · have hxy : x ≤ y := le_of_not_ge hyx
      have hdiff :=
        derivative_difference_sq_le_interval_energy (f := f) (g := g) (a := x) (x := y) (b := y) hxy
          le_rfl hg
          (fun t ht => hderiv t ⟨le_trans (by linarith only [hh]) ht.1, le_trans ht.2 hy.2⟩)
      have hsub :=
        intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume) (by linarith only [hh])
          hxy hy.2 (Filter.Eventually.of_forall fun t => sq_nonneg ‖g t‖)
          ((hg.norm.pow 2).intervalIntegrable (x - h) (x + h))
      have hlen : y - x ≤ h := by linarith only [hy.2]
      have hlenprod : (y - x) * E ≤ h * E := mul_le_mul_of_nonneg_right hlen hE
      have hnorm : ‖f x - f y‖ ^ 2 = ‖f y - f x‖ ^ 2 := by rw [norm_sub_rev]
      rw [hnorm]
      exact le_trans hdiff (le_trans (mul_le_mul_of_nonneg_left hsub (sub_nonneg.mpr hxy)) hlenprod)
  have hpoint : ∀ y ∈ Set.Icc (x - h) (x + h), ‖f x‖ ^ 2 ≤ 2 * ‖f y‖ ^ 2 + 2 * h * E := by
    intro y hy
    have hdiff : f x = f y + (f x - f y) := by abel
    have htriangle := norm_add_le (f y) (f x - f y)
    rw [← hdiff] at htriangle
    have hsumSq :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htriangle
    have hquad : (‖f y‖ + ‖f x - f y‖) ^ 2 ≤ 2 * ‖f y‖ ^ 2 + 2 * ‖f x - f y‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖f y‖ - ‖f x - f y‖)]
    have hvar := hvariation y hy
    nlinarith only [hsumSq, hquad, hvar]
  have hcont : Continuous fun y : ℝ => 2 * ‖f y‖ ^ 2 + 2 * h * E :=
    continuous_const.mul (hf.norm.pow 2) |>.add continuous_const
  have hleft :
    IntervalIntegrable (fun _ : ℝ => (‖f x‖ ^ 2 : ℝ)) MeasureTheory.volume (x - h) (x + h) :=
    intervalIntegrable_const
  have hright :
    IntervalIntegrable (fun y : ℝ => 2 * ‖f y‖ ^ 2 + 2 * h * E) MeasureTheory.volume (x - h)
      (x + h) :=
    hcont.intervalIntegrable (x - h) (x + h)
  have hmono :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (show x - h ≤ x + h by linarith only [hh]) hleft hright hpoint
  have hi1 : IntervalIntegrable (fun y : ℝ => ‖f y‖ ^ 2) MeasureTheory.volume (x - h) (x + h) :=
    (hf.norm.pow 2).intervalIntegrable (x - h) (x + h)
  have hi2 :
    IntervalIntegrable (fun _ : ℝ => (2 * h * E : ℝ)) MeasureTheory.volume (x - h) (x + h) :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_add (μ := MeasureTheory.volume) (hi1.const_mul 2) hi2] at hmono
  rw [intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)] at hmono
  have hconst : (∫ y in (x - h)..(x + h), (2 * h * E : ℝ)) = 4 * h ^ 2 * E := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hconst] at hmono
  have hleftInt : (∫ y in (x - h)..(x + h), (‖f x‖ ^ 2 : ℝ)) = 2 * h * ‖f x‖ ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hleftInt] at hmono
  have hresult : h * ‖f x‖ ^ 2 ≤ (∫ y in (x - h)..(x + h), ‖f y‖ ^ 2) + 2 * h ^ 2 * E := by
    nlinarith only [hmono]
  simpa only [E] using hresult

/-- For a continuously differentiable complex function, the weighted sum of squared midpoint
values on an equally spaced grid is bounded by the full interval integral and the grid spacing
squared times the derivative's squared integral energy. The proof sums the local cell estimate and
telescopes both interval integrals. This is the sampling bound used to compare a height mesh with
the pre-sifted hybrid mean-square estimate. -/
theorem uniform_grid_norm_sq_le_height_and_derivative_energy {f g : ℝ → ℂ} {a h : ℝ} {n : ℕ}
    (hf : Continuous f) (hg : Continuous g) (hh : 0 < h) (hderiv : ∀ y, HasDerivAt f (g y) y) :
    (h / 2) * (∑ k ∈ Finset.range n, ‖f (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2) ≤
      (∫ x in a..(a + (n : ℝ) * h), ‖f x‖ ^ 2) +
        (h ^ 2 / 2) * (∫ x in a..(a + (n : ℝ) * h), ‖g x‖ ^ 2) := by
  let p : ℕ → ℝ := fun k => a + (k : ℝ) * h
  have hcell (k : ℕ) :
    (h / 2) * ‖f (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2 ≤
      (∫ x in (p k)..(p (k + 1)), ‖f x‖ ^ 2) +
        (h ^ 2 / 2) * (∫ x in (p k)..(p (k + 1)), ‖g x‖ ^ 2) := by
    have hcenter : a + ((k : ℝ) + 1 / 2) * h = (p k + p (k + 1)) / 2 := by
      dsimp only [p]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    have hstart : (p k + p (k + 1)) / 2 - h / 2 = p k := by
      dsimp only [p]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    have hend : (p k + p (k + 1)) / 2 + h / 2 = p (k + 1) := by
      dsimp only [p]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hcenter]
    have hlocal :=
      cell_norm_sq_le_integral_add_derivative_energy (f := f) (g := g) (x := (p k + p (k + 1)) / 2)
        (h := h / 2) hf hg (by linarith only [hh]) (fun y hy => hderiv y)
    rw [hstart, hend] at hlocal
    have herror : 2 * (h / 2) ^ 2 = h ^ 2 / 2 := by ring
    rw [herror] at hlocal
    exact hlocal
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun k hk => hcell k)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have htelF :
    (∑ k ∈ Finset.range n, ∫ x in (p k)..(p (k + 1)), ‖f x‖ ^ 2) = ∫ x in (p 0)..(p n), ‖f x‖ ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals (f := fun x : ℝ => ‖f x‖ ^ 2) (μ :=
      MeasureTheory.volume) (fun k hk => (hf.norm.pow 2).intervalIntegrable (p k) (p (k + 1)))
  have htelG :
    (∑ k ∈ Finset.range n, ∫ x in (p k)..(p (k + 1)), ‖g x‖ ^ 2) = ∫ x in (p 0)..(p n), ‖g x‖ ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals (f := fun x : ℝ => ‖g x‖ ^ 2) (μ :=
      MeasureTheory.volume) (fun k hk => (hg.norm.pow 2).intervalIntegrable (p k) (p (k + 1)))
  have henergySum :
    (∑ k ∈ Finset.range n, (h ^ 2 / 2) * (∫ x in (p k)..(p (k + 1)), ‖g x‖ ^ 2)) =
      (h ^ 2 / 2) * (∫ x in (p 0)..(p n), ‖g x‖ ^ 2) := by
    rw [← Finset.mul_sum, htelG]
  rw [htelF, henergySum] at hsum
  have hp0 : p 0 = a := by simp only [p, Nat.cast_zero, zero_mul, add_zero]
  have hpn : p n = a + (n : ℝ) * h := by rfl
  simpa only [hp0, hpn] using hsum

/-- For a finite family of continuously differentiable complex functions, the sum of their
weighted midpoint square sums is controlled by the integral of the family square sum and the
corresponding derivative energy. Sum the scalar mesh estimate over the family and exchange the
finite sums with each other and with the interval integrals. -/
theorem uniform_grid_sum_norm_sq_le_integrals {ι : Type*} (s : Finset ι) {f g : ι → ℝ → ℂ} {a h : ℝ}
    {n : ℕ} (hh : 0 < h) (hf : ∀ i ∈ s, Continuous (f i)) (hg : ∀ i ∈ s, Continuous (g i))
    (hderiv : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (g i t) t) :
    (h / 2) * (∑ k ∈ Finset.range n, ∑ i ∈ s, ‖f i (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2) ≤
      (∫ t in a..(a + (n : ℝ) * h), ∑ i ∈ s, ‖f i t‖ ^ 2) +
        (h ^ 2 / 2) * (∫ t in a..(a + (n : ℝ) * h), ∑ i ∈ s, ‖g i t‖ ^ 2) := by
  have hsum :=
    Finset.sum_le_sum (s := s)
      (fun i hi =>
        uniform_grid_norm_sq_le_height_and_derivative_energy (a := a) (h := h) (n := n) (hf i hi)
          (hg i hi) hh (hderiv i hi))
  have hcomm :
    (∑ k ∈ Finset.range n, ∑ i ∈ s, ‖f i (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2) =
      ∑ i ∈ s, ∑ k ∈ Finset.range n, ‖f i (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2 := by
    exact Finset.sum_comm
  have hleft :
    (h / 2) * (∑ k ∈ Finset.range n, ∑ i ∈ s, ‖f i (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2) =
      ∑ i ∈ s, (h / 2) * (∑ k ∈ Finset.range n, ‖f i (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2) := by
    rw [hcomm, Finset.mul_sum]
  have hfInt :
    (∫ t in a..(a + (n : ℝ) * h), ∑ i ∈ s, ‖f i t‖ ^ 2) =
      ∑ i ∈ s, ∫ t in a..(a + (n : ℝ) * h), ‖f i t‖ ^ 2 := by
    apply intervalIntegral.integral_finsetSum
    intro i hi
    exact ((hf i hi).norm.pow 2).intervalIntegrable _ _
  have hgInt :
    (∫ t in a..(a + (n : ℝ) * h), ∑ i ∈ s, ‖g i t‖ ^ 2) =
      ∑ i ∈ s, ∫ t in a..(a + (n : ℝ) * h), ‖g i t‖ ^ 2 := by
    apply intervalIntegral.integral_finsetSum
    intro i hi
    exact ((hg i hi).norm.pow 2).intervalIntegrable _ _
  rw [hleft]
  calc
    _ ≤
        ∑ i ∈ s,
          ((∫ t in a..(a + (n : ℝ) * h), ‖f i t‖ ^ 2) +
            (h ^ 2 / 2) * (∫ t in a..(a + (n : ℝ) * h), ‖g i t‖ ^ 2)) :=
      hsum
    _ =
        (∫ t in a..(a + (n : ℝ) * h), ∑ i ∈ s, ‖f i t‖ ^ 2) +
          (h ^ 2 / 2) * (∫ t in a..(a + (n : ℝ) * h), ∑ i ∈ s, ‖g i t‖ ^ 2) :=
      by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hfInt, ← hgInt]

/-- A nonnegative continuous function has no larger integral on a subinterval than on the
containing interval. Apply interval integral monotonicity and identify the interval integral over
the containing interval with the integral over its closed interval set. This permits a mesh estimate
on a slightly shorter height range to use a hybrid mean-square bound on the full height window. -/
theorem intervalIntegral_le_integral_Icc_of_nonneg {f : ℝ → ℝ} {c a b d : ℝ} (hca : c ≤ a)
    (hab : a ≤ b) (hbd : b ≤ d) (hf : ∀ t, 0 ≤ f t) (hcont : Continuous f) :
    (∫ t in a..b, f t) ≤ (∫ t in Set.Icc c d, f t ∂MeasureTheory.volume) := by
  have hmono :=
    intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume) hca hab hbd
      (Filter.Eventually.of_forall hf) (hcont.intervalIntegrable c d)
  rw [intervalIntegral.integral_of_le (hca.trans (hab.trans hbd)), ←
    MeasureTheory.integral_Icc_eq_integral_Ioc] at hmono
  exact hmono

/--
Inputs: a continuous complex-valued function, an initial height, a positive grid spacing, a
global Lipschitz bound on distances up to half a grid spacing, and a finite number of cells.
Claim: the squared norms at all cell midpoints, weighted by half the spacing, are bounded by the
height integral over the full grid interval and an explicit accumulated Lipschitz error.
Proof: apply the local cell estimate at each midpoint, sum over the finite range, and telescope the
adjacent interval integrals.
Role: converts a uniform finite height mesh into a continuous integral bound for later hybrid
large-sieve applications.
-/
theorem uniform_grid_norm_sq_le_height_integral {f : ℝ → ℂ} {a h L : ℝ} {n : ℕ} (hf : Continuous f)
    (hh : 0 < h) (hL : 0 ≤ L) (hLip : ∀ x y, |x - y| ≤ h / 2 → ‖f x - f y‖ ≤ L * |x - y|) :
    (h / 2) * (∑ k ∈ Finset.range n, ‖f (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2) ≤
      (∫ x in a..(a + (n : ℝ) * h), ‖f x‖ ^ 2) + (n : ℝ) * (h ^ 3 / 4) * L ^ 2 := by
  let p : ℕ → ℝ := fun k => a + (k : ℝ) * h
  have hcell (k : ℕ) :
    (h / 2) * ‖f (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2 ≤
      (∫ x in (p k)..(p (k + 1)), ‖f x‖ ^ 2) + h ^ 3 / 4 * L ^ 2 := by
    have hcenter : a + ((k : ℝ) + 1 / 2) * h = (p k + p (k + 1)) / 2 := by
      dsimp only [p]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    have hstart : (p k + p (k + 1)) / 2 - h / 2 = p k := by
      dsimp only [p]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    have hend : (p k + p (k + 1)) / 2 + h / 2 = p (k + 1) := by
      dsimp only [p]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hcenter]
    have hlocal :=
      cell_norm_sq_le_integral_add_lipschitz_error (f := f) (x := (p k + p (k + 1)) / 2) (h :=
        h / 2) hf (by linarith only [hh]) hL
        (fun y hy => by
          have hy' : |(p k + p (k + 1)) / 2 - y| ≤ h / 2 := by simpa only [abs_sub_comm] using hy
          simpa only [abs_sub_comm] using hLip ((p k + p (k + 1)) / 2) y hy')
    rw [hstart, hend] at hlocal
    have herror : 2 * (h / 2) ^ 3 * L ^ 2 = h ^ 3 / 4 * L ^ 2 := by ring
    rw [herror] at hlocal
    exact hlocal
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun k hk => hcell k)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have htel :
    (∑ k ∈ Finset.range n, ∫ x in (p k)..(p (k + 1)), ‖f x‖ ^ 2) = ∫ x in (p 0)..(p n), ‖f x‖ ^ 2 :=
    intervalIntegral.sum_integral_adjacent_intervals (f := fun x : ℝ => ‖f x‖ ^ 2) (μ :=
      MeasureTheory.volume) (fun k hk => (hf.norm.pow 2).intervalIntegrable (p k) (p (k + 1)))
  rw [htel] at hsum
  have hconst : ∑ k ∈ Finset.range n, (h ^ 3 / 4 * L ^ 2 : ℝ) = (n : ℝ) * (h ^ 3 / 4) * L ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hconst] at hsum
  have hp0 : p 0 = a := by simp only [p, Nat.cast_zero, zero_mul, add_zero]
  have hpn : p n = a + (n : ℝ) * h := by rfl
  simpa only [hp0, hpn] using hsum

end PseudoPrime.Analysis
