/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! # Trigonometric polynomial upper bound for the absolute sine -/

public section

namespace PseudoPrime.Analysis

/-- The cosine polynomial majorizes the absolute sine in the smoothed zero sum. -/
noncomputable def sineMajorant (z : ℝ) : ℝ :=
  2 / 3 - 7 * Real.cos (2 * z) / 18 - Real.cos (4 * z) / 18

/-- Factoring the difference on the unit interval bounds the absolute sine at every phase. -/
theorem abs_sin_le_majorant (z : ℝ) : |Real.sin z| ≤ sineMajorant z := by
  have h :
    sineMajorant z - |Real.sin z| =
      (1 - |Real.sin z|) * (2 * |Real.sin z| - 1) ^ 2 * (|Real.sin z| + 2) / 9 := by
    unfold sineMajorant
    rw [show 4 * z = 2 * (2 * z) by ring, Real.cos_two_mul (2 * z), Real.cos_two_mul_eq_one_sub, ←
      sq_abs (Real.sin z)]
    ring
  apply sub_nonneg.mp
  rw [h]
  exact
    div_nonneg
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr (Real.abs_sin_le_one z)) (sq_nonneg _))
        (add_nonneg (abs_nonneg _) (by norm_num only)))
      (by norm_num only)

/-- The cosine majorant is at most one, uniformly in the phase. -/
theorem sineMajorant_le_one (z : ℝ) : sineMajorant z ≤ 1 := by
  rw [sineMajorant, show 4 * z = 2 * (2 * z) by ring, Real.cos_two_mul (2 * z)]
  have h := Real.neg_one_le_cos (2 * z)
  nlinarith only [mul_nonneg
      (by linarith only [Real.neg_one_le_cos (2 * z)] : 0 ≤ 1 + Real.cos (2 * z))
      (by linarith only [h] : 0 ≤ 5 + 2 * Real.cos (2 * z))]

/-- Exact correction that joins the polynomial tail to the constant weight at two fifths. -/
noncomputable def sineMajorantShift : ℝ :=
  2 / 5 - sineMajorant (2 / 5)

/-- A fifth-order error bound for sine controls the correction at the cutoff. -/
theorem sineMajorantShift_bounds : 0 < sineMajorantShift ∧ sineMajorantShift < 3 / 1000 := by
  let y := Real.sin (2 / 5)
  have hp : 0 ≤ (2 : ℝ) / 5 := by norm_num only
  have h :=
    abs_le.mp
      (Real.sin_bound (x := 2 / 5)
        (by
          rw [abs_of_nonneg hp]; norm_num only))
  rw [abs_of_nonneg hp] at h
  have ha : (38923 : ℝ) / 100000 ≤ y := by
    dsimp only [y]; linarith only [h.1]
  have hb : y ≤ (38944 : ℝ) / 100000 := by
    dsimp only [y]; linarith only [h.2]
  have ha₀ : 0 ≤ (38923 : ℝ) / 100000 := by norm_num only
  have hy := ha₀.trans ha
  have he : sineMajorantShift = 2 / 5 - (2 / 9 + 11 / 9 * y ^ 2 - 4 / 9 * y ^ 4) := by
    unfold sineMajorantShift sineMajorant y
    rw [show (4 : ℝ) * (2 / 5) = 2 * (2 * (2 / 5)) by ring, Real.cos_two_mul (2 * (2 / 5)),
      Real.cos_two_mul_eq_one_sub]
    ring
  rw [he]
  constructor
  · linarith only [pow_le_pow_left₀ hy hb 2, pow_le_pow_left₀ ha₀ ha 4]
  · linarith only [pow_le_pow_left₀ ha₀ ha 2, pow_le_pow_left₀ hy hb 4]

/-- The zero-sum weight uses a constant below the cutoff and the shifted polynomial above. -/
noncomputable def sincWeight (z : ℝ) : ℝ :=
  if z ≤ 2 / 5 then 1 else (sineMajorant z + sineMajorantShift) / z

/-- The exact shift makes the two branches of the weight agree continuously at the cutoff. -/
theorem continuous_sincWeight : Continuous sincWeight := by
  apply continuous_if_le continuous_id continuous_const continuousOn_const
  · apply ContinuousOn.div
    · change ContinuousOn (fun z ↦ sineMajorant z + sineMajorantShift) _
      unfold sineMajorant
      fun_prop
    · exact continuous_id.continuousOn
    · intro z hz
      exact ne_of_gt (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2 / 5) hz)
  · intro z hz
    change z = 2 / 5 at hz
    subst z
    unfold sineMajorantShift
    ring

/-- For positive phases the continuous weight bounds the absolute sinc. -/
theorem abs_sin_div_le_sincWeight {z : ℝ} (hz : 0 < z) : |Real.sin z| / z ≤ sincWeight z := by
  unfold sincWeight
  split
  · apply (div_le_one hz).2
    simpa only [abs_of_pos hz] using (Real.abs_sin_le_abs (x := z))
  · exact
      div_le_div_of_nonneg_right
        ((abs_sin_le_majorant z).trans (le_add_of_nonneg_right sineMajorantShift_bounds.1.le)) hz.le

/-- The derivative of the cosine polynomial is an explicit sum of two sine terms. -/
theorem hasDerivAt_sineMajorant (z : ℝ) :
    HasDerivAt sineMajorant (7 / 9 * Real.sin (2 * z) + 2 / 9 * Real.sin (4 * z)) z := by
  unfold sineMajorant
  convert
    (((hasDerivAt_const z (2 / 3 : ℝ)).sub
          ((((hasDerivAt_id z).const_mul 2).cos.const_mul 7).div_const 18)).sub
      (((hasDerivAt_id z).const_mul 4).cos.div_const 18)) using
    1
  · rfl
  · dsimp only [id_eq]
    ring

/-- The slope is bounded by one because its two sine coefficients sum to one. -/
theorem abs_deriv_sineMajorant_le (z : ℝ) : |deriv sineMajorant z| ≤ 1 := by
  rw [(hasDerivAt_sineMajorant z).deriv]
  apply abs_le.mpr
  constructor
  · linarith only [Real.neg_one_le_sin (2 * z), Real.neg_one_le_sin (4 * z)]
  · linarith only [Real.sin_le_one (2 * z), Real.sin_le_one (4 * z)]

/-- The second derivative bound controls the integrated zero-count error. -/
theorem abs_deriv_deriv_sineMajorant_le (z : ℝ) : |deriv (deriv sineMajorant) z| ≤ 22 / 9 := by
  have h : deriv sineMajorant = fun x ↦ 7 / 9 * Real.sin (2 * x) + 2 / 9 * Real.sin (4 * x) :=
    funext fun x ↦ (hasDerivAt_sineMajorant x).deriv
  have hd :=
    ((((hasDerivAt_id z).const_mul 2).sin.const_mul (7 / 9)).add
        (((hasDerivAt_id z).const_mul 4).sin.const_mul (2 / 9))).deriv
  rw [h]
  change |deriv _ z| ≤ 22 / 9
  rw [show deriv (fun x : ℝ ↦ 7 / 9 * Real.sin (2 * x) + 2 / 9 * Real.sin (4 * x)) z = _ from hd]
  dsimp only [id_eq]
  exact
    abs_le.mpr
      ⟨by linarith only [Real.neg_one_le_cos (2 * z), Real.neg_one_le_cos (4 * z)], by
        linarith only [Real.cos_le_one (2 * z), Real.cos_le_one (4 * z)]⟩

/-- Analytic expression for the upper branch of the scaled ordinate weight. -/
noncomputable def sincTailWeight (β t : ℝ) : ℝ :=
  (sineMajorant (β * t) + sineMajorantShift) / (β * t ^ 2)

/-- Above the cutoff, including its endpoint, the scaled weight equals its smooth tail. -/
theorem sincWeight_div_eq_tail {β t : ℝ} (h : 2 / 5 ≤ β * t) :
    sincWeight (β * t) / t = sincTailWeight β t := by
  rcases h.eq_or_lt with he | hl
  · simp only [sincWeight, he.ge, ↓reduceIte]
    rw [sincTailWeight, ← he, sineMajorantShift]
    have hz : β * t ≠ 0 := by
      rw [← he]; norm_num only
    field_simp [mul_ne_zero_iff.mp hz |>.1, mul_ne_zero_iff.mp hz |>.2]
    linarith only [he]
  · simp only [sincWeight, not_le.mpr hl, ↓reduceIte, sincTailWeight, div_div]
    ring_nf

/-- The derivative in the upper branch factors into two terms without differentiating at
the junction. This expression is used inside the zero-count integral. -/
theorem hasDerivAt_sincTailWeight {β t : ℝ} (hb : β ≠ 0) (ht : t ≠ 0) :
    HasDerivAt (sincTailWeight β)
      (deriv sineMajorant (β * t) / t ^ 2 -
        2 * (sineMajorant (β * t) + sineMajorantShift) / (β * t ^ 3))
      t := by
  have hp := ((hasDerivAt_sineMajorant (β * t)).comp t ((hasDerivAt_id t).const_mul β))
  have hd :=
    (hp.add_const sineMajorantShift).div (((hasDerivAt_id t).pow 2).const_mul β)
      (mul_ne_zero hb (pow_ne_zero 2 ht))
  apply hd.congr_deriv
  rw [(hasDerivAt_sineMajorant (β * t)).deriv]
  simp only [Pi.pow_apply, id_eq, Function.comp_apply]
  field_simp [hb, ht]
  ring

/-- The derivative of the smooth tail is continuous on every positive closed interval. -/
theorem continuousOn_deriv_sincTail {β a b : ℝ} (hb : β ≠ 0) (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (deriv (sincTailWeight β)) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  let g := fun z ↦
    deriv sineMajorant (β * z) / z ^ 2 -
      2 * (sineMajorant (β * z) + sineMajorantShift) / (β * z ^ 3)
  have hg : ContinuousOn g (Set.Icc a b) := by
    intro t ht
    have ht0 := (ha.trans_le ht.1).ne'
    unfold g
    simp only [funext (fun x ↦ (hasDerivAt_sineMajorant x).deriv)]
    unfold sineMajorant
    fun_prop (disch :=
      first
      | exact ht0
      | exact hb
      | exact mul_ne_zero hb (pow_ne_zero 3 ht0)
      | exact pow_ne_zero 2 ht0)
  exact hg.congr fun t ht ↦ (hasDerivAt_sincTailWeight hb (ha.trans_le ht.1).ne').deriv

/-- The derivative kernel multiplying the integrated zero-count error after rescaling. -/
noncomputable def sincErrorKernel (z : ℝ) : ℝ :=
  (1 + deriv sineMajorant z) / z ^ 2 - 2 * (sineMajorant z + sineMajorantShift) / z ^ 3

/-- Adding the reciprocal-square term to the smooth weight derivative produces
the scaled kernel, with two powers of the smoothing width. -/
theorem sincErrorKernel_scale {β t : ℝ} (hb : 0 < β) (ht : 0 < t) :
    1 / t ^ 2 + deriv (sincTailWeight β) t = β ^ 2 * sincErrorKernel (β * t) := by
  rw [(hasDerivAt_sincTailWeight hb.ne' ht.ne').deriv, sincErrorKernel]
  field_simp [hb.ne', ht.ne']
  ring

/-- Differentiate the discrepancy kernel at a positive ordinate. The result
contains only reciprocal powers and the first two derivatives of the majorant. -/
theorem hasDerivAt_sincErrorKernel {z : ℝ} (hz : 0 < z) :
    HasDerivAt sincErrorKernel
      (deriv (deriv sineMajorant) z / z ^ 2 - (2 + 4 * deriv sineMajorant z) / z ^ 3 +
        6 * (sineMajorant z + sineMajorantShift) / z ^ 4)
      z := by
  have hd : ContDiff ℝ 2 sineMajorant := by
    unfold sineMajorant; fun_prop
  have hd' : ContDiff ℝ 1 (deriv sineMajorant) := hd.deriv'
  have h₂ : DifferentiableAt ℝ (deriv sineMajorant) z := hd'.differentiable one_ne_zero z
  have h₁ := (hasDerivAt_sineMajorant z).differentiableAt.hasDerivAt
  have h :=
    ((h₂.hasDerivAt.const_add 1).div ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz.ne')).sub
      (((h₁.add_const sineMajorantShift).const_mul 2).div ((hasDerivAt_id z).pow 3)
        (pow_ne_zero 3 hz.ne'))
  apply h.congr_deriv
  simp only [Pi.pow_apply, id_eq, mul_one]
  field_simp [hz.ne']
  ring

/-- For positive arguments the derivative of the discrepancy kernel admits an
integrable majorant with the three inverse powers from the Abel error estimate. -/
theorem abs_deriv_sincErrorKernel_le {z : ℝ} (hz : 0 < z) :
    |deriv sincErrorKernel z| ≤
      (22 / 9) / z ^ 2 + 6 / z ^ 3 + 6 * (1 + sineMajorantShift) / z ^ 4 := by
  have h₁ := abs_le.mp (abs_deriv_sineMajorant_le z)
  have hmid : |2 + 4 * deriv sineMajorant z| ≤ 6 :=
    abs_le.mpr ⟨by linarith only [h₁.1], by linarith only [h₁.2]⟩
  have hn := add_nonneg ((abs_nonneg _).trans (abs_sin_le_majorant z)) sineMajorantShift_bounds.1.le
  rw [(hasDerivAt_sincErrorKernel hz).deriv]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · apply (abs_sub _ _).trans
    rw [abs_div, abs_div, abs_of_pos (pow_pos hz 2), abs_of_pos (pow_pos hz 3)]
    exact
      add_le_add (div_le_div_of_nonneg_right (abs_deriv_deriv_sineMajorant_le z) (sq_nonneg _))
        (div_le_div_of_nonneg_right hmid (pow_nonneg hz.le 3))
  · rw [abs_div, abs_of_pos (pow_pos hz 4), abs_of_nonneg (mul_nonneg (by norm_num only) hn)]
    exact
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add_left (sineMajorant_le_one z) _) (by norm_num only))
        (pow_nonneg hz.le 4)

/-- The exact cutoff and shift put the two inverse-power moment allowances
strictly below 57 and 26 respectively. -/
theorem sincError_cutoff_budgets :
    let a : ℝ := 2 / 5
    (22 / 9) / a + 3 / a ^ 2 + 2 * (1 + sineMajorantShift) / a ^ 3 < 57 ∧
      (22 / 9) / a + 3 / (2 * a ^ 2) + 2 * (1 + sineMajorantShift) / (3 * a ^ 3) < 26 := by
  dsimp only
  constructor <;> ring_nf <;> linarith only [sineMajorantShift_bounds.2]

end PseudoPrime.Analysis
