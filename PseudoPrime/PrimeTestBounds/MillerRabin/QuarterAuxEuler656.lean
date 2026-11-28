/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine656

/-! # The positive part of the section 132 auxiliary Euler polynomial -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The section 132 quadratic profile, with twice the normalization
of the inverse symmetric Mellin transform. -/
noncomputable def quarterAuxProfile656 (x : ℝ) : ℝ :=
  3 / 8 + 3 * (11 / 10) / 8 * x + (11 / 10) ^ 2 / 8 * x ^ 2

/-- The two shifts of the inverse profile combine into a quadratic in
the logarithm of the prime power, after factoring out the common decay. -/
noncomputable def quarterAuxPair656 (s x : ℝ) : ℝ :=
  (Real.exp (-(11 / 10) * |s|) * quarterAuxProfile656 (x + |s|) +
      Real.exp ((11 / 10) * |s|) * quarterAuxProfile656 (x - |s|)) /
    2

/-- The polynomial in equation (132.7), with all ordered frequency pairs. -/
noncomputable def quarterAuxMix656 (F : ℝ → ℝ) : ℝ :=
  (∑ i,
        ∑ j,
          quarterAuxCoeff656 i * quarterAuxCoeff656 j *
            F (quarterAuxFrequency656 i - quarterAuxFrequency656 j)) /
      2 -
    ∑ i, quarterAuxCoeff656 i * F (quarterAuxFrequency656 i)

/-- The seven-frequency polynomial evaluated at the logarithm of a prime power. -/
noncomputable def quarterAuxPoly656 (x : ℝ) : ℝ :=
  quarterAuxMix656 (fun s ↦ quarterAuxPair656 s x)

private theorem aux_mix_add_656 (F G : ℝ → ℝ) :
    quarterAuxMix656 (fun s ↦ F s + G s) = quarterAuxMix656 F + quarterAuxMix656 G := by
  unfold quarterAuxMix656
  simp only [mul_add, Finset.sum_add_distrib, add_div]
  ring

private theorem aux_mix_scale_656 (F : ℝ → ℝ) (t : ℝ) :
    quarterAuxMix656 (fun s ↦ F s * t) = quarterAuxMix656 F * t := by
  unfold quarterAuxMix656
  simp only [← mul_assoc, ← Finset.sum_mul]
  ring

/-- The constant coefficient of the pair polynomial is its value at zero. -/
noncomputable def quarterAuxConstant656 : ℝ :=
  quarterAuxMix656 (fun s ↦ quarterAuxPair656 s 0)

/-- The linear coefficient comes from shifting the two quadratic profiles
in opposite directions. -/
noncomputable def quarterAuxLinear656 : ℝ :=
  quarterAuxMix656
    (fun s ↦
      (Real.exp (-(11 / 10) * |s|) * (33 / 80 + (11 / 10) ^ 2 / 4 * |s|) +
          Real.exp ((11 / 10) * |s|) * (33 / 80 - (11 / 10) ^ 2 / 4 * |s|)) /
        2)

/-- The quadratic coefficient is the profile's leading coefficient
multiplied by the mixed average of the two exponentials. -/
noncomputable def quarterAuxQuadratic656 : ℝ :=
  quarterAuxMix656
    (fun s ↦ (11 / 10) ^ 2 / 16 * (Real.exp (-(11 / 10) * |s|) + Real.exp ((11 / 10) * |s|)))

/-- The combined shifted profile is the quadratic whose three coefficients
are used in the numerical certificate. -/
theorem quarter_aux_poly_eq_656 (v : ℝ) :
    quarterAuxPoly656 v =
      quarterAuxQuadratic656 * v ^ 2 + quarterAuxLinear656 * v + quarterAuxConstant656 := by
  let A := fun s : ℝ ↦
    (11 / 10) ^ 2 / 16 * (Real.exp (-(11 / 10) * |s|) + Real.exp ((11 / 10) * |s|))
  let B := fun s : ℝ ↦
    (Real.exp (-(11 / 10) * |s|) * (33 / 80 + (11 / 10) ^ 2 / 4 * |s|) +
        Real.exp ((11 / 10) * |s|) * (33 / 80 - (11 / 10) ^ 2 / 4 * |s|)) /
      2
  have h (s : ℝ) : quarterAuxPair656 s v = A s * v ^ 2 + B s * v + quarterAuxPair656 s 0 := by
    dsimp only [quarterAuxPair656, quarterAuxProfile656, A, B]
    ring
  unfold quarterAuxPoly656 quarterAuxConstant656 quarterAuxQuadratic656 quarterAuxLinear656
  simp only [h, aux_mix_add_656, aux_mix_scale_656, A, B]

/-- A trace deficit between zero and four costs at most four times the
positive part of the polynomial. The weight is nonnegative. -/
theorem aux_euler_positive_le {α w p : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 4) (hw : 0 ≤ w) :
    α * w * p ≤ 4 * w * max p 0 := by
  have h₁ := mul_le_mul_of_nonneg_left (le_max_left p 0) (mul_nonneg hα hw)
  have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα' hw) (le_max_right p 0)
  exact h₁.trans h₂

/-- A quadratic with nonnegative leading coefficient lies below its
endpoint secant. Nonpositive endpoint values therefore exclude any
positive contribution between the left endpoint and the fixed split. -/
private theorem quadratic_nonpos_between {a b c l t v : ℝ} (ha : 0 ≤ a)
    (hl : a * l ^ 2 + b * l + c ≤ 0) (ht : a * t ^ 2 + b * t + c ≤ 0) (hlv : l ≤ v) (hvt : v ≤ t) :
    a * v ^ 2 + b * v + c ≤ 0 := by
  rcases eq_or_lt_of_le (hlv.trans hvt) with he | he
  · rw [le_antisymm (he ▸ hvt) hlv]
    exact hl
  apply nonpos_of_mul_nonpos_right (a := t - l) _ (sub_pos.mpr he)
  have h₁ := mul_nonpos_of_nonpos_of_nonneg hl (sub_nonneg.mpr hvt)
  have h₂ := mul_nonpos_of_nonpos_of_nonneg ht (sub_nonneg.mpr hlv)
  have h₃ := mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hlv)) (sub_nonneg.mpr hvt)
  have h₄ := neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr he.le) h₃)
  linear_combination h₁ + h₂ + h₄

/-- The positive part of a quadratic is dominated by a shifted quadratic
with zero boundary value. The low and high cases use endpoint signs
and upper bounds for the slope and leading coefficient at the split. -/
theorem aux_quadratic_positive_le {a b c l t A B v : ℝ} (ha : 0 ≤ a)
    (hl : a * l ^ 2 + b * l + c ≤ 0) (ht : a * t ^ 2 + b * t + c ≤ 0) (hA : 0 ≤ A) (hB : a ≤ B)
    (hd : 2 * a * t + b ≤ A) (hv : l ≤ v) :
    max (a * v ^ 2 + b * v + c) 0 ≤ if t ≤ v then A * (v - t) + B * (v - t) ^ 2 else 0 := by
  by_cases h : t ≤ v
  · rw [ite_eq_left h]
    have hu := sub_nonneg.mpr h
    have h₁ := mul_le_mul_of_nonneg_right hd hu
    have h₂ := mul_le_mul_of_nonneg_right hB (sq_nonneg (v - t))
    exact
      max_le (by linear_combination ht + h₁ + h₂)
        (add_nonneg (mul_nonneg hA hu) (mul_nonneg (ha.trans hB) (sq_nonneg _)))
  rw [ite_eq_right h]
  exact max_le (quadratic_nonpos_between ha hl ht hv (le_of_not_ge h)) le_rfl

/-- With the endpoint signs and the two coefficient bounds, the auxiliary
Euler trace costs only the positive tail at the fixed split 119/10. -/
theorem quarter_aux_euler_cut_656 {α w v l A B : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 4) (hw : 0 ≤ w)
    (hv : l ≤ v) (ha : 0 ≤ quarterAuxQuadratic656) (hl : quarterAuxPoly656 l ≤ 0)
    (ht : quarterAuxPoly656 (119 / 10) ≤ 0) (hA : 0 ≤ A) (hB : quarterAuxQuadratic656 ≤ B)
    (hd : 2 * quarterAuxQuadratic656 * (119 / 10) + quarterAuxLinear656 ≤ A) :
    α * w * quarterAuxPoly656 v ≤
      4 * w * (if (119 / 10 : ℝ) ≤ v then A * (v - 119 / 10) + B * (v - 119 / 10) ^ 2 else 0) := by
  apply (aux_euler_positive_le hα hα' hw).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num only) hw)
  rw [quarter_aux_poly_eq_656] at hl ht ⊢
  exact aux_quadratic_positive_le ha hl ht hA hB hd hv

end PseudoPrime.PrimeTestBounds.MillerRabin
