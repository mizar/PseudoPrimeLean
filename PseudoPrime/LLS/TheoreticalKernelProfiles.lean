/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements
public import PseudoPrime.Analysis.GammaCriticalLine
public import PseudoPrime.Analysis.NumericalLogBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Explicit profiles in Sections 6.2 and 6.3

The triangular and gamma profiles describe the real integrals and coefficients
after a kernel is inserted into Proposition 6.1. They are kept separate from the
analytic construction of a Mellin kernel and the proof of that proposition.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The triangular inverse-Mellin profile with width `2α`, for positive `u`.
Its compact support in logarithmic coordinates is the profile of Section 6.2.
The value at zero is irrelevant to its integrals. -/
noncomputable def triangularKernelProfile (α u : ℝ) : ℝ :=
  max 0 (2 * α - |Real.log u|)

/-- The gamma inverse-Mellin profile `sqrt u exp(-u)` on positive arguments.
Dividing it by `sqrt u` leaves the exponential density of Section 6.3. -/
noncomputable def gammaKernelProfile (u : ℝ) : ℝ :=
  Real.sqrt u * Real.exp (-u)

/-- The triangular profile is nonnegative for all real arguments.
This is the sign condition used when discarding terms in character averages. -/
theorem triangularKernelProfile_nonneg (α u : ℝ) : 0 ≤ triangularKernelProfile α u := by
  exact le_max_left _ _

/-- For positive width the triangular profile is positive at one.
This ensures that the nonnegative profile is nonzero. -/
theorem triangularKernelProfile_one {α : ℝ} (hα : 0 < α) : 0 < triangularKernelProfile α 1 := by
  unfold triangularKernelProfile
  rw [Real.log_one, abs_zero, sub_zero, max_eq_right (by linarith only [hα])]
  exact mul_pos (by norm_num only) hα

/-- Dividing the gamma profile by `sqrt u` gives `exp(-u)` when `u>0`.
Cancellation supplies its elementary truncated-mass integral. -/
theorem gammaKernelProfile_div_sqrt {u : ℝ} (hu : 0 < u) :
    gammaKernelProfile u / Real.sqrt u = Real.exp (-u) := by
  unfold gammaKernelProfile
  exact mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hu).ne'

/-- The exponential density integrated from zero to `λ` has mass
`1-exp(-λ)`. This evaluates the real integral in Section 6.3. -/
theorem integral_gamma_density (lambda : ℝ) :
    (∫ u in (0 : ℝ)..lambda, Real.exp (-u)) = 1 - Real.exp (-lambda) := by
  rw [intervalIntegral.integral_comp_neg, integral_exp]
  simp only [neg_zero, Real.exp_zero]

/-- The gamma profile has truncated weighted mass `1-exp(-lambda)` for
`lambda>0`. Ignore the zero endpoint and cancel the square root on the
open interval; integrate the remaining exponential density. -/
theorem integral_gammaKernelProfile {lambda : ℝ} (hl : 0 < lambda) :
    (∫ u in (0 : ℝ)..lambda, gammaKernelProfile u / Real.sqrt u) = 1 - Real.exp (-lambda) := by
  rw [← integral_gamma_density lambda]
  apply intervalIntegral.integral_congr_Ioo_of_le hl.le
  intro u hu
  exact gammaKernelProfile_div_sqrt hu.1

/-- The logarithmic denominator in the Section 6.2 simplification is
positive for `h≥28`. A logarithmic chord bound at fifty-four certifies the
endpoint fifty-six, and monotonicity gives the remaining indices. -/
theorem four_lt_log_two_mul {h : ℝ} (hh : 28 ≤ h) : 4 < Real.log (2 * h) := by
  have h54 : (398 / 100 : ℝ) < Real.log 54 := by
    rw [show (54 : ℝ) = 2 * 3 ^ (3 : ℕ) by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have h56 :=
    Analysis.log_gt_affine_of_anchor (a := 54) (b := 56) (y := 56) (by norm_num only)
      (by norm_num only) (by norm_num only) (le_refl _) h54
  have hm :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 56) (show 56 ≤ 2 * h by linarith only [hh])
  linarith only [h56, hm]

/-- The squared exponential difference at half-width expands into
`exp α + exp(-α) - 2`. This preserves the coefficient four in the paper's
triangular-kernel value at one half. -/
theorem exp_half_difference_sq (α : ℝ) :
    (Real.exp (α / 2) - Real.exp (-α / 2)) ^ 2 = Real.exp α + Real.exp (-α) - 2 := by
  have hp : Real.exp (α / 2) ^ 2 = Real.exp α := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (-α / 2) ^ 2 = Real.exp (-α) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp (α / 2) * Real.exp (-α / 2) = 1 := by
    rw [← Real.exp_add, show α / 2 + -α / 2 = 0 by ring, Real.exp_zero]
  nlinarith only [hp, hn, hm]

/-- The coefficient of `sqrt X` after choosing the triangular kernel
and `lambda=1` in Proposition 6.1. The exponential expression is the
kernel's value at one half and retains its factor four. -/
noncomputable def triangularKernelCoefficient (h α : ℝ) : ℝ :=
  h * (4 * α - 4 + 4 * Real.exp (-α)) - 4 * (Real.exp (α / 2) - Real.exp (-α / 2)) ^ 2

/-- At the Section 6.2 width `log(2h)/2`, the exponential is at most `h`
for `h≥2`. Express it as `sqrt(2h)` and compare squares. This controls
the negative kernel endpoint term. -/
theorem exp_half_log_two_mul_le {h : ℝ} (hh : 2 ≤ h) : Real.exp (Real.log (2 * h) / 2) ≤ h := by
  have hp : 0 < 2 * h := by linarith only [hh]
  have he : Real.exp (Real.log (2 * h) / 2) = Real.sqrt (2 * h) := by
    rw [show Real.log (2 * h) / 2 = Real.log (2 * h) * (1 / 2) by ring, Real.exp_mul,
      Real.exp_log hp, ← Real.sqrt_eq_rpow]
  rw [he]
  exact Real.sqrt_le_iff.mpr ⟨by linarith only [hh], by nlinarith only [hh]⟩

/-- For `h≥28`, the triangular coefficient strictly exceeds
`2h(log(2h)-4)`. Expansion leaves nonnegative exponential contributions
and a positive constant. Together with the logarithmic endpoint certificate,
this justifies division in the large-index estimate. -/
theorem triangularKernelCoefficient_gt {h : ℝ} (hh : 28 ≤ h) :
    2 * h * (Real.log (2 * h) - 4) < triangularKernelCoefficient h (Real.log (2 * h) / 2) := by
  unfold triangularKernelCoefficient
  rw [exp_half_difference_sq]
  have he := exp_half_log_two_mul_le ((by norm_num only : (2 : ℝ) ≤ 28).trans hh)
  have hm :=
    mul_nonneg (show 0 ≤ h - 1 by linarith only [hh]) (Real.exp_pos (-(Real.log (2 * h) / 2))).le
  nlinarith only [he, hm]

/-- For positive `u`, the derivative of the triangular weighted-mass
primitive is `(2α+log u)/sqrt u`. The product rule and `sqrt(u)^2=u`
supply the cancellation used in the Section 6.2 integral. -/
theorem hasDerivAt_triangular_mass_primitive (α : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ ↦ 2 * Real.sqrt v * (2 * α + Real.log v - 2))
      ((2 * α + Real.log u) / Real.sqrt u) u := by
  have hd :=
    ((Real.hasDerivAt_sqrt hu.ne').const_mul 2).mul
      (((Real.hasDerivAt_log hu.ne').const_add (2 * α)).sub_const 2)
  convert hd using 1
  have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hfirst : 2 * (1 / (2 * Real.sqrt u)) = 1 / Real.sqrt u := by
    rw [mul_one_div]
    simpa only [mul_one] using (mul_div_mul_left (c := (2 : ℝ)) 1 (Real.sqrt u) (by norm_num only))
  have hsecond : 2 * Real.sqrt u * u⁻¹ = 2 / Real.sqrt u := by
    rw [← div_eq_mul_inv]
    calc
      _ = 2 * Real.sqrt u / (Real.sqrt u * Real.sqrt u) :=
        congrArg (fun v : ℝ ↦ 2 * Real.sqrt u / v) (Real.mul_self_sqrt hu.le).symm
      _ = _ := mul_div_mul_right 2 (Real.sqrt u) hs
  rw [hfirst, one_div_mul_eq_div, hsecond, ← add_div]
  congr 1
  ring

/-- For nonnegative width, the weighted linear branch of the triangular
profile integrates from `exp(-2α)` to one as `4α-4+4exp(-α)`.
Use its square-root/logarithm primitive on this positive interval.
This supplies the nonzero branch of the Section 6.2 mass integral. -/
theorem integral_triangular_linear_branch {α : ℝ} (hα : 0 ≤ α) :
    (∫ u in Real.exp (-2 * α)..(1 : ℝ), (2 * α + Real.log u) / Real.sqrt u) =
      4 * α - 4 + 4 * Real.exp (-α) := by
  have ha : 0 < Real.exp (-2 * α) := Real.exp_pos _
  have hab : Real.exp (-2 * α) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hα])
  have hu {u : ℝ} (hm : u ∈ Set.uIcc (Real.exp (-2 * α)) 1) : 0 < u :=
    ha.trans_le ((Set.uIcc_of_le hab ▸ hm).1)
  have hc :
    ContinuousOn (fun u : ℝ ↦ (2 * α + Real.log u) / Real.sqrt u)
      (Set.uIcc (Real.exp (-2 * α)) 1) := by
    intro u hm
    exact
      ((continuousAt_const.add (Real.continuousAt_log (hu hm).ne')).div
          Real.continuous_sqrt.continuousAt (Real.sqrt_pos.mpr (hu hm)).ne').continuousWithinAt
  have he :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hm ↦ hasDerivAt_triangular_mass_primitive α (hu hm)) hc.intervalIntegrable
  rw [he]
  have hs : Real.sqrt (Real.exp (-2 * α)) = Real.exp (-α) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [Real.sqrt_one, Real.log_one, Real.log_exp, hs]
  ring

/-- Below `exp(-2α)`, including the zero endpoint, the triangular
profile divided by the square root vanishes. Compare logarithms on positive
arguments and use division by zero at the endpoint. -/
theorem triangular_density_zero {α u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ Real.exp (-2 * α)) :
    triangularKernelProfile α u / Real.sqrt u = 0 := by
  by_cases hzero : u = 0
  · subst u
    rw [Real.sqrt_zero, div_zero]
  · have hup : 0 < u := lt_of_le_of_ne hu (fun he ↦ hzero he.symm)
    have hl := Real.log_le_log hup hu'
    rw [Real.log_exp] at hl
    have hz : 2 * α - |Real.log u| ≤ 0 := by linarith only [hl, neg_le_abs (Real.log u)]
    rw [triangularKernelProfile, max_eq_left hz, zero_div]

/-- On the interval from `exp(-2α)` to one, the triangular profile
equals `2α+log u`. The logarithm is nonpositive, while the truncated linear
branch is nonnegative. This identifies the branch used in the mass integral. -/
theorem triangular_profile_linear {α u : ℝ} (hu : Real.exp (-2 * α) ≤ u) (hu' : u ≤ 1) :
    triangularKernelProfile α u = 2 * α + Real.log u := by
  have hup := (Real.exp_pos (-2 * α)).trans_le hu
  have hl := Real.log_le_log (Real.exp_pos (-2 * α)) hu
  rw [Real.log_exp] at hl
  have hl' := Real.log_nonpos hup.le hu'
  unfold triangularKernelProfile
  rw [abs_of_nonpos hl', sub_neg_eq_add, max_eq_right (by linarith only [hl])]

/-- For nonnegative width, the triangular profile has weighted mass
`4α-4+4exp(-α)` from zero to one. The lower branch vanishes and the
positive branch is evaluated by its logarithmic primitive. This completes
the real truncated integral used in Section 6.2. -/
theorem integral_triangularKernelProfile {α : ℝ} (hα : 0 ≤ α) :
    (∫ u in (0 : ℝ)..1, triangularKernelProfile α u / Real.sqrt u) =
      4 * α - 4 + 4 * Real.exp (-α) := by
  let a := Real.exp (-2 * α)
  let f := fun u : ℝ ↦ triangularKernelProfile α u / Real.sqrt u
  have ha : 0 < a := Real.exp_pos _
  have hab : a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hα])
  have hzero : Set.EqOn f (fun _ ↦ (0 : ℝ)) (Set.uIcc 0 a) := by
    intro u hu
    rw [Set.uIcc_of_le ha.le] at hu
    exact triangular_density_zero hu.1 hu.2
  have h0 : IntervalIntegrable f MeasureTheory.volume 0 a := by
    apply IntervalIntegrable.congr (f := fun _ ↦ (0 : ℝ)) _ intervalIntegrable_const
    intro u hu
    rw [Set.uIoc_of_le ha.le] at hu
    exact (triangular_density_zero hu.1.le hu.2).symm
  have hup {u : ℝ} (hu : u ∈ Set.uIcc a 1) : 0 < u := ha.trans_le ((Set.uIcc_of_le hab ▸ hu).1)
  have hc : ContinuousOn f (Set.uIcc a 1) := by
    intro u hu
    have hn : ContinuousAt (fun v : ℝ ↦ max 0 (2 * α - |Real.log v|)) u :=
      continuousAt_const.max (continuousAt_const.sub (Real.continuousAt_log (hup hu).ne').abs)
    exact
      (hn.div Real.continuous_sqrt.continuousAt (Real.sqrt_pos.mpr (hup hu)).ne').continuousWithinAt
  have hz : (∫ u in (0 : ℝ)..a, f u) = 0 := by
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
  have ht : (∫ u in a..(1 : ℝ), f u) = ∫ u in a..(1 : ℝ), (2 * α + Real.log u) / Real.sqrt u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact congrArg (fun r : ℝ ↦ r / Real.sqrt u) (triangular_profile_linear hu.1 hu.2)
  have he := intervalIntegral.integral_add_adjacent_intervals h0 hc.intervalIntegrable
  rw [hz, ht, integral_triangular_linear_branch hα, zero_add] at he
  exact he.symm

/-- For `h≥28`, the triangular coefficient inequality bounds `X`
by the square of `A/(2h(log(2h)-4))`. Use the strict coefficient lower
bound, its certified positivity and monotonicity of squaring on nonnegative
numbers. The analytic inequality remains an explicit input. -/
theorem triangular_kernel_bound_of_large_index {h X A : ℝ} (hh : 28 ≤ h) (hX : 0 ≤ X) (hA : 0 ≤ A)
    (hi : triangularKernelCoefficient h (Real.log (2 * h) / 2) * Real.sqrt X ≤ A) :
    X ≤ (A / (2 * h * (Real.log (2 * h) - 4))) ^ 2 := by
  have hd : 0 < 2 * h * (Real.log (2 * h) - 4) :=
    mul_pos (mul_pos (by norm_num only) (lt_of_lt_of_le (by norm_num only) hh))
      (sub_pos.mpr (four_lt_log_two_mul hh))
  have hm := mul_le_mul_of_nonneg_right (triangularKernelCoefficient_gt hh).le (Real.sqrt_nonneg X)
  have hs : Real.sqrt X ≤ A / (2 * h * (Real.log (2 * h) - 4)) :=
    (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hm.trans hi)
  have hsq := mul_le_mul hs hs (Real.sqrt_nonneg X) (div_nonneg hA hd.le)
  rw [Real.mul_self_sqrt hX] at hsq
  simpa only [pow_two] using hsq

/-- A positive gamma coefficient and a strict squared coefficient
certificate convert the Section 6.3 inequality into `X<c L²`.
Square the nonnegative left side and cancel the positive squared denominator.
This connects numerical certificates to an actual cutoff bound. -/
theorem gamma_bound_of_coefficient {h lambda X L M c : ℝ} (hX : 0 ≤ X) (hl : 0 ≤ lambda)
    (hL : 0 < L) (hd : 0 < h - 1 - h * Real.exp (-lambda))
    (hi : (h - 1 - h * Real.exp (-lambda)) * Real.sqrt X ≤ Real.sqrt lambda * (h - 1) * L * M)
    (hc : lambda * ((h - 1) * M) ^ 2 < c * (h - 1 - h * Real.exp (-lambda)) ^ 2) :
    X < c * L ^ 2 := by
  have hs := mul_self_le_mul_self (mul_nonneg hd.le (Real.sqrt_nonneg X)) hi
  have hsX : (h - 1 - h * Real.exp (-lambda)) ^ 2 * X ≤ lambda * ((h - 1) * M) ^ 2 * L ^ 2 := by
    calc
      _ = ((h - 1 - h * Real.exp (-lambda)) * Real.sqrt X) ^ 2 := by rw [mul_pow, Real.sq_sqrt hX]
      _ ≤ (Real.sqrt lambda * (h - 1) * L * M) ^ 2 := by simpa only [pow_two] using hs
      _ = _ := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hl]
        ring
  have ht := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hL)
  apply (mul_lt_mul_iff_of_pos_left (sq_pos_of_pos hd)).mp
  calc
    _ ≤ _ := hsX
    _ < _ := ht
    _ = _ := by ring

/-- For real index between seven and twenty-seven, the coefficient in
Theorem 1.3 strictly exceeds the gamma-kernel bound `33/50`. Rational bounds
on the logarithm give squared factors at least `(6/7)^2` and `(21/11)^2`.
This comparison transfers the Section 6.3 prime bound to the small-index
part of the Section 6.2 statement without changing its denominator. -/
theorem triangularCoefficient_gt_gamma_of_small_index {h : ℝ} (hh : 7 ≤ h) (hh' : h ≤ 27) :
    33 / 50 < (1 / 4 : ℝ) * (1 - 1 / h) ^ 2 * (Real.log (2 * h) / (Real.log (2 * h) - 4)) ^ 2 := by
  have h12 : (62 / 25 : ℝ) < Real.log 12 := by
    rw [show (12 : ℝ) = 3 * 2 ^ 2 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have h14 :=
    Analysis.log_gt_affine_of_anchor (a := 12) (b := 14) (y := 14) (by norm_num only)
      (by norm_num only) (by norm_num only) (le_refl _) h12
  have hlo : (21 / 8 : ℝ) < Real.log (2 * h) := by
    have hm :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 14) (show 14 ≤ 2 * h by linarith only [hh])
    norm_num only at h14
    linarith only [h14, hm]
  have h54 : Real.log 54 < (4 : ℝ) := by
    rw [show (54 : ℝ) = 2 * 3 ^ 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have hhi : Real.log (2 * h) < 4 :=
    (Real.log_le_log (by linarith only [hh] : (0 : ℝ) < 2 * h)
          (by linarith only [hh'] : 2 * h ≤ 54)).trans_lt
      h54
  have hd : 0 < 4 - Real.log (2 * h) := sub_pos.mpr hhi
  have hr : (21 / 11 : ℝ) < Real.log (2 * h) / (4 - Real.log (2 * h)) :=
    (lt_div_iff₀ hd).mpr (by linarith only [hlo])
  have hf : (6 / 7 : ℝ) ≤ 1 - 1 / h := by
    have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 7) hh
    norm_num only at hi
    linarith only [hi]
  have hs1 := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 6 / 7) hf
  have hs2 := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 21 / 11) hr.le
  have hm :=
    mul_le_mul hs1 hs2 (by norm_num only : (0 : ℝ) ≤ (21 / 11) * (21 / 11))
      (mul_self_nonneg (1 - 1 / h))
  have heq :
    (Real.log (2 * h) / (Real.log (2 * h) - 4)) ^ 2 =
      (Real.log (2 * h) / (4 - Real.log (2 * h))) ^ 2 := by
    rw [show Real.log (2 * h) - 4 = -(4 - Real.log (2 * h)) by ring, div_neg, neg_sq]
  rw [heq]
  nlinarith only [hm]

end PseudoPrime.LLS.PaperStatements
