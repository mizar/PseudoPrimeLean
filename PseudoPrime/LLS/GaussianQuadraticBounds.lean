/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Quadratic comparisons for Gaussian residual profiles. -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The nonnegative quadratic root `(A + sqrt (A ^ 2 + 4 * K * d)) / (2 * K)`.
For positive `K` and `A` and nonnegative `d), it is positive and solves
`K * r ^ 2 = A * r + d). This is the variable triangular radius coefficient. -/
noncomputable def quadraticPositiveRoot (K A d : ℝ) : ℝ :=
  (A + Real.sqrt (A ^ 2 + 4 * K * d)) / (2 * K)

/-- If `K > 0`, `A > 0`, and `d ≥ 0`, the positive triangular root is positive and
solves its quadratic equation. Square the defining expression and cancel the nonzero
coefficient `K`. This provides the profile's exact margin identity. -/
theorem quadraticPositiveRoot_spec {K A d : ℝ} (hK : 0 < K) (hA : 0 < A) (hd : 0 ≤ d) :
    0 < quadraticPositiveRoot K A d ∧
      K * (quadraticPositiveRoot K A d) ^ 2 = A * quadraticPositiveRoot K A d + d := by
  let S := Real.sqrt (A ^ 2 + 4 * K * d)
  let r := (A + S) / (2 * K)
  have hdisc : 0 ≤ A ^ 2 + 4 * K * d := by
    have hm := mul_nonneg hK.le hd
    nlinarith only [sq_nonneg A, hm]
  have hs : 0 ≤ S := Real.sqrt_nonneg _
  have hs2 : S ^ 2 = A ^ 2 + 4 * K * d := Real.sq_sqrt hdisc
  have hr : 0 < r := div_pos (add_pos_of_pos_of_nonneg hA hs) (by linarith only [hK])
  have he : (2 * K) * r = A + S := by
    dsimp only [r]
    rw [mul_comm, div_mul_cancel₀ _ (by linarith only [hK] : 2 * K ≠ 0)]
  have hsub : S = 2 * K * r - A := by linarith only [he]
  rw [hsub] at hs2
  have hz : K * (K * r ^ 2 - A * r - d) = 0 := by nlinarith only [hs2]
  have hf : K * r ^ 2 - A * r - d = 0 := (mul_eq_zero.mp hz).resolve_left hK.ne'
  change 0 < r ∧ K * r ^ 2 = A * r + d
  exact ⟨hr, by linarith only [hf]⟩

/-- If `K > 0`, `d ≥ 0`, `K * r ^ 2 = A * r + d`, and `A + d ≤ K`,
then `r ≤ 1`. A hypothetical `r > 1` makes the difference between the quadratic
at `r` and at one positive, contradicting the equation. This supplies the profile's
upper-cutoff condition. -/
theorem quadraticRoot_le_one {K A d r : ℝ} (hK : 0 < K) (hd : 0 ≤ d) (heq : K * r ^ 2 = A * r + d)
    (hbudget : A + d ≤ K) : r ≤ 1 := by
  by_contra hh
  have hr1 : 1 < r := lt_of_not_ge hh
  have hgap : 0 < K * (r + 1) - A := by
    have hh' := mul_pos hK (show 0 < r - 1 by linarith only [hr1])
    nlinarith only [hh', hbudget, hd, hK]
  have hp := mul_pos (show 0 < r - 1 by linarith only [hr1]) hgap
  nlinarith only [hp, heq, hbudget]

/-- If `r > 0` solves `K * r ^ 2 = A * r + d` with `K > 0` and `d ≥ 0),
then every positive `a ≥ r` satisfies `A + d / a ≤ K * a`. Factor the difference
of the two quadratic values and divide by `a`. This is the profile's main margin
inequality. -/
theorem quadraticRoot_budget {K A d r a : ℝ} (hK : 0 < K) (hd : 0 ≤ d) (hr : 0 < r)
    (heq : K * r ^ 2 = A * r + d) (ha : r ≤ a) (ha0 : 0 < a) : A + d / a ≤ K * a := by
  have hmul : 0 ≤ (K * r - A) * r := by nlinarith only [heq, hd]
  have hkr : A ≤ K * r := by
    have h := nonneg_of_mul_nonneg_left hmul hr
    linarith only [h]
  have hKa := mul_nonneg hK.le (show 0 ≤ a by linarith only [ha0])
  have hprod : 0 ≤ (a - r) * (K * (a + r) - A) :=
    mul_nonneg (by linarith only [ha]) (by nlinarith only [hkr, hKa])
  have hpoly : A * a + d ≤ K * a ^ 2 := by nlinarith only [hprod, heq]
  have hdiv : d / a ≤ K * a - A := (div_le_iff₀ ha0).mpr (by nlinarith only [hpoly])
  linarith only [hdiv]

/-- Let `K > 0`, `d ≥ 0`, and `r > 0` solve `K * r ^ 2 = A * r + d`.
If `c > 0` satisfies `A * c + d ≤ K * c ^ 2`, then `r ≤ c). Factor the difference
of the quadratic values and use positivity of the second factor. This compares the
adaptive radius with explicit rational coefficients. -/
theorem quadraticRoot_le_of_budget {K A d r c : ℝ} (hK : 0 < K) (hd : 0 ≤ d) (hr : 0 < r)
    (hc : 0 < c) (heq : K * r ^ 2 = A * r + d) (hbound : A * c + d ≤ K * c ^ 2) : r ≤ c := by
  have hm : 0 ≤ (K * r - A) * r := by nlinarith only [heq, hd]
  have hkr : A ≤ K * r := by
    have hh := nonneg_of_mul_nonneg_left hm hr
    linarith only [hh]
  by_contra h
  have hrc : c < r := lt_of_not_ge h
  have hKc := mul_pos hK hc
  have hfactor : 0 < K * (r + c) - A := by nlinarith only [hkr, hKc]
  have hp := mul_pos (show 0 < r - c by linarith only [hrc]) hfactor
  nlinarith only [hp, heq, hbound]

/-- A rational discriminant inequality gives a uniform strict quadratic upper bound.
Complete the square; no sampling of the inverse-radius variable is needed. -/
theorem quadratic_lt_of_discriminant {b0 b1 H R z : ℝ} (hH : 0 < H)
    (hcert : b1 ^ 2 < 4 * H * (R - b0)) : b0 + b1 * z - H * z ^ 2 < R := by
  have hs := sq_nonneg (2 * H * z - b1)
  have hid : 4 * H * (b1 * z - H * z ^ 2) = b1 ^ 2 - (2 * H * z - b1) ^ 2 := by ring
  have hu : 4 * H * (b1 * z - H * z ^ 2) ≤ b1 ^ 2 := by linarith only [hid, hs]
  have hm : 4 * H * (b1 * z - H * z ^ 2) < 4 * H * (R - b0) := hu.trans_lt hcert
  have h4 : 0 < 4 * H := mul_pos (by norm_num only) hH
  by_contra hn
  have hz : 0 ≤ (4 * H) * ((b1 * z - H * z ^ 2) - (R - b0)) :=
    mul_nonneg h4.le (by linarith only [hn])
  nlinarith only [hm, hz]

end PseudoPrime.LLS
