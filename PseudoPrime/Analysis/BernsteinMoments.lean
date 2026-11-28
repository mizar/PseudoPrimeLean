/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.BernsteinIntegral

/-! # Exact monomial moments of Bernstein basis polynomials -/

public section

namespace PseudoPrime.Analysis

/-- Multiplication by the monomial of degree j raises the Bernstein degree
and index by j. Integrate the resulting single basis term. -/
theorem bernstein_basis_moment (n i j : ℕ) (hi : i ≤ n) :
    (∫ t : ℝ in 0..1, t ^ j * ((n.choose i : ℝ) * t ^ i * (1 - t) ^ (n - i))) =
      (n.choose i : ℝ) / ((n + j).choose (i + j) : ℝ) / ((n + j : ℕ) + 1) := by
  have hle : i + j ≤ n + j := Nat.add_le_add_right hi j
  have hc : ((n + j).choose (i + j) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (Nat.choose_pos hle)).ne'
  have hid (t : ℝ) :
    t ^ j * ((n.choose i : ℝ) * t ^ i * (1 - t) ^ (n - i)) =
      ((n.choose i : ℝ) / ((n + j).choose (i + j) : ℝ)) *
        (((n + j).choose (i + j) : ℝ) * t ^ (i + j) * (1 - t) ^ (n + j - (i + j))) := by
    rw [Nat.add_sub_add_right, pow_add]
    have h := div_mul_cancel₀ (n.choose i : ℝ) hc
    linear_combination -(t ^ j * t ^ i * (1 - t) ^ (n - i)) * h
  calc
    _ =
        ∫ t : ℝ in 0..1,
          ((n.choose i : ℝ) / ((n + j).choose (i + j) : ℝ)) *
            (((n + j).choose (i + j) : ℝ) * t ^ (i + j) * (1 - t) ^ (n + j - (i + j))) :=
      intervalIntegral.integral_congr (fun t _ ↦ hid t)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, bernstein_basis_integral _ _ hle, mul_one_div]

/-- Scale the unit Bernstein moment to a cell of width h. This gives the
exact rational moments used for the Taylor bounds in H15. -/
theorem bernstein_scaled_moment {h : ℝ} (hh : 0 < h) (n i j : ℕ) (hi : i ≤ n) :
    (∫ t in 0..h, t ^ j * ((n.choose i : ℝ) * (t / h) ^ i * (1 - t / h) ^ (n - i))) =
      h ^ (j + 1) * ((n.choose i : ℝ) / ((n + j).choose (i + j) : ℝ) / ((n + j : ℕ) + 1)) := by
  let g := fun t : ℝ ↦ t ^ j * ((n.choose i : ℝ) * (t / h) ^ i * (1 - t / h) ^ (n - i))
  have hc : Continuous g :=
    (continuous_id.pow j).mul
      ((continuous_const.mul ((continuous_id.div_const h).pow i)).mul
        ((continuous_const.sub (continuous_id.div_const h)).pow (n - i)))
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := 1) (f := fun t : ℝ ↦ h * t) (f' :=
      fun _ ↦ h) (g := g)
      (fun t _ ↦ by simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul h)
      continuous_const.continuousOn hc
  simp only [mul_zero, mul_one] at hsub
  change (∫ t in 0..h, g t) = _
  rw [← hsub, ← bernstein_basis_moment n i j hi, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Function.comp_apply, g, mul_div_cancel_left₀ _ hh.ne', mul_pow, pow_succ]
  ring

/-- Integrate a represented Bernstein profile against a monomial on a
positive-width cell by summing its exact basis moments. -/
theorem bernstein_profile_moment {h : ℝ} (hh : 0 < h) (n j : ℕ) (c : Fin (n + 1) → ℝ) {F : ℝ → ℝ}
    (hF :
      ∀ t ∈ Set.Icc 0 h,
        F t =
          ∑ i : Fin (n + 1),
            c i * ((n.choose i.val : ℝ) * (t / h) ^ i.val * (1 - t / h) ^ (n - i.val))) :
    (∫ t in 0..h, t ^ j * F t) =
      ∑ i : Fin (n + 1),
        c i *
          (h ^ (j + 1) *
            ((n.choose i.val : ℝ) / ((n + j).choose (i.val + j) : ℝ) / ((n + j : ℕ) + 1))) := by
  let g := fun (i : Fin (n + 1)) (t : ℝ) =>
    c i * (t ^ j * ((n.choose i.val : ℝ) * (t / h) ^ i.val * (1 - t / h) ^ (n - i.val)))
  have hg (i : Fin (n + 1)) : Continuous (g i) :=
    continuous_const.mul
      ((continuous_id.pow j).mul
        ((continuous_const.mul ((continuous_id.div_const h).pow i.val)).mul
          ((continuous_const.sub (continuous_id.div_const h)).pow (n - i.val))))
  calc
    _ = ∫ t in 0..h, ∑ i : Fin (n + 1), g i t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change t ^ j * F t = ∑ i : Fin (n + 1), g i t
      rw [hF t (Set.uIcc_of_le hh.le ▸ ht), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [g]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun i _ ↦ (hg i).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul,
        bernstein_scaled_moment hh n i.val j (Nat.le_of_lt_succ i.isLt)]

end PseudoPrime.Analysis
