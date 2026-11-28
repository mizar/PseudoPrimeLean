/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInterval600

/-! # The conductor and Euler envelope for section 122 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The conductor contribution 4rR(r) in (122.36), with the factor r
absorbed in the exponent 1 - 2a = -57/50. -/
noncomputable def quarterConductor644 (r : ℝ) : ℝ :=
  (4 * (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120) *
    (r ^ (-(57 / 50) : ℝ) * (2687 / 1000 + 2 * Real.log r) ^ 5)

/-- At radius at least one, the transform at the inverse square cutoff
gives the conductor term in the section 122 comparison. -/
theorem quarter_conductor_profile_644 {r : ℝ} (hr : 1 ≤ r) :
    4 * r * (quarterKernel644.transform (r ^ 2)⁻¹).re = quarterConductor644 r := by
  have hp := zero_lt_one.trans_le hr
  have hs : Real.log (r ^ 2)⁻¹ ≤ 2687 / 1000 := by
    rw [Real.log_inv]
    linarith only [Real.log_nonneg (one_le_pow₀ hr : 1 ≤ r ^ 2)]
  rw [quarter_transform_644 (inv_pos.mpr (sq_pos_of_pos hp)) hs, Real.log_inv, Real.log_pow,
    Nat.cast_ofNat]
  have he :
    -((107 / 100 : ℝ) * (2687 / 1000 - -(2 * Real.log r))) =
      -(107 / 100) * (2687 / 1000) + (-214 / 100) * Real.log r := by
    ring
  have hpow : r * Real.exp ((-214 / 100 : ℝ) * Real.log r) = r ^ (-(57 / 50) : ℝ) := by
    rw [mul_comm, mul_comm (-214 / 100 : ℝ), ← Real.rpow_def_of_pos hp, ← Real.rpow_add_one hp.ne']
    norm_num only
  rw [he, Real.exp_add]
  unfold quarterConductor644
  linear_combination
    (4 * (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120 *
        (2687 / 1000 + 2 * Real.log r) ^ 5) *
      hpow

/-- The logarithmic slope of the conductor term factors into a positive
weight and an affine function of the shifted logarithm. -/
theorem quarter_conductor_644_deriv {r : ℝ} (hr : 0 < r) :
    let C : ℝ := 4 * (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
    let v := 2687 / 1000 + 2 * Real.log r
    HasDerivAt quarterConductor644 (C * r ^ (-(57 / 50) : ℝ) * v ^ 4 * (10 - (57 / 50) * v) / r)
      r := by
  intro C v
  have h :=
    ((Real.hasDerivAt_rpow_const (p := -(57 / 50 : ℝ)) (Or.inl hr.ne')).mul
          ((((Real.hasDerivAt_log hr.ne').const_mul 2).const_add (2687 / 1000)).pow 5)).const_mul
      C
  apply h.congr_deriv
  rw [Real.rpow_sub_one hr.ne']
  dsimp only [v, Pi.pow_apply]
  field_simp [hr.ne']
  ring

/-- On the section 122 radius interval the conductor decreases and satisfies
the lower logarithmic slope required of the total Euler remainder. -/
theorem quarter_conductor_644_slope {r : ℝ} (hr : 316 ≤ r) :
    -(2.14 * quarterConductor644 r) ≤ r * deriv quarterConductor644 r ∧
      deriv quarterConductor644 r ≤ 0 := by
  have hp : 0 < r := by linarith only [hr]
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
  have hl : 4 ≤ Real.log r := by
    apply (Real.le_log_iff_exp_le hp).mpr
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [he, hr]
  let v := 2687 / 1000 + 2 * Real.log r
  let C : ℝ := 4 * (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
  have hW : 0 ≤ C * r ^ (-(57 / 50) : ℝ) * v ^ 4 := by
    dsimp only [C]; positivity
  have hv : 10.687 ≤ v := by
    dsimp only [v]; linarith only [hl]
  rw [(quarter_conductor_644_deriv hp).deriv]
  change
    -(2.14 * (C * (r ^ (-(57 / 50) : ℝ) * v ^ 5))) ≤
        r * (C * r ^ (-(57 / 50) : ℝ) * v ^ 4 * (10 - 57 / 50 * v) / r) ∧
      _
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hp.ne']
  constructor
  · nlinarith only [mul_nonneg hW (show 0 ≤ 10 + v by linarith only [hv])]
  · exact
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hW (by linarith only [hl]))
        hp.le

/-- On a closed radius interval starting at 316 or later, two certified endpoint values
give an affine upper bound for the conductor and the full Euler tail. -/
theorem quarter_euler_row_644 {a b r M U : ℝ} (ha : 316 ≤ a) (hr : r ∈ Set.Icc a b) (hM : 0 ≤ M)
    (hm : quarterConductor644 a + 4 * positiveTail644 (a ^ 2) ≤ M)
    (hu : quarterConductor644 b + 4 * positiveTail644 (b ^ 2) ≤ U) :
    quarterConductor644 r + 4 * positiveTail644 (r ^ 2) ≤ U + (2.14 * M / a) * (b - r) := by
  let E := fun x : ℝ ↦ quarterConductor644 x + 4 * positiveTail644 (x ^ 2)
  have hd (t : ℝ) (hi : t ∈ Set.Icc a b) :
    DifferentiableAt ℝ E t ∧ -(2.14 * E t) ≤ t * deriv E t ∧ deriv E t ≤ 0 := by
    obtain ⟨d, h, hlo, hhi⟩ :=
      euler644_tail_slope ((by norm_num only : (1 : ℝ) ≤ 316).trans (ha.trans hi.1))
    have hp : 0 < t := lt_of_lt_of_le (by norm_num only) (ha.trans hi.1)
    have hc := (quarter_conductor_644_deriv hp).differentiableAt.hasDerivAt
    have he : HasDerivAt E (deriv quarterConductor644 t + 4 * d) t := hc.add (h.const_mul 4)
    have hs := quarter_conductor_644_slope (ha.trans hi.1)
    refine ⟨he.differentiableAt, ?_, ?_⟩ <;> rw [he.deriv]
    · dsimp only [E]
      linarith only [hs.1, hlo]
    · linarith only [hs.2, hhi]
  apply
    euler_row_envelope (E := E) (c := 2.14) (by norm_num only)
      (lt_of_lt_of_le (by norm_num only) ha) hr hM hu hm _ (fun t ht ↦ (hd t ht).1)
      (fun t ht ↦ (hd t ht).2.1)
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun t hi ↦ (hd t hi).1.continuousAt.continuousWithinAt
  · exact fun t hi ↦ (hd t (interior_subset hi)).1.differentiableWithinAt
  · exact fun t hi ↦ (hd t (interior_subset hi)).2.2

/-- If the linear loss dominates the Euler slope budget, the combined
section 122 loss at every radius is bounded by its right endpoint budget. -/
theorem quarter_euler_loss_644 {a b r M U B : ℝ} (ha : 316 ≤ a) (hr : r ∈ Set.Icc a b) (hM : 0 ≤ M)
    (hm : quarterConductor644 a + 4 * positiveTail644 (a ^ 2) ≤ M)
    (hu : quarterConductor644 b + 4 * positiveTail644 (b ^ 2) ≤ U) (hB : 2.14 * M / a ≤ B) :
    B * r + (quarterConductor644 r + 4 * positiveTail644 (r ^ 2)) ≤ B * b + U := by
  have h := quarter_euler_row_644 ha hr hM hm hu
  linarith only [h, mul_le_mul_of_nonneg_right hB (sub_nonneg.mpr hr.2)]

end PseudoPrime.PrimeTestBounds.MillerRabin
