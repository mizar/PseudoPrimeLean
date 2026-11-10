/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointLower

/-! # Elementary primitive for the joint quarter-bound estimate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The elementary primitive for the combined principal Chebyshev lower
integrand, with fixed kernel width `a`. It includes the main term and the
three terms in the explicit RH error bound. -/
noncomputable def quarterJointPrimitive (a t : ℝ) : ℝ :=
  t ^ (1 / 2 : ℝ) * (4 * a + 4 - Real.log t) -
    (19 / 30 : ℝ) * (t ^ (1 / 4 : ℝ) * (8 * a + 12 - 2 * Real.log t)) -
    (63 / 10 : ℝ) * (t ^ (-1 / 4 : ℝ) * (-8 * a + 4 + 2 * Real.log t)) -
    (1839 / 1000 : ℝ) * (t ^ (-1 / 2 : ℝ) * (-4 * a + Real.log t))

/-- The displayed affine-logarithm primitives differentiate to a power
times the common positive variation weight. The real-power addition rule
allows the four exponents used by the Chebyshev estimate. -/
theorem quarter_joint_power_deriv {a r t : ℝ} (ht : 0 < t) (hr : r ≠ 0) :
    HasDerivAt (fun z : ℝ ↦ z ^ r * ((2 * a + 1) / r + 1 / (2 * r ^ 2) - Real.log z / (2 * r)))
      (t ^ (r - 1) * (2 * a + 1 - Real.log t / 2)) t := by
  have h :=
    LLS.PaperStatements.jointPowerLog_deriv (t := t) (r := r) (a :=
      (2 * a + 1) / r + 1 / (2 * r ^ 2)) (b := -(1 / (2 * r))) ht
  convert h using 1
  · funext z
    ring
  · congr 1
    field_simp [hr]
    ring

/-- The joint principal primitive differentiates to the explicit RH
Chebyshev lower-bound integrand. Each power-log term is differentiated
separately and the exponents are combined on positive inputs. -/
theorem quarter_joint_primitive_deriv {a t : ℝ} (ht : 0 < t) :
    HasDerivAt (quarterJointPrimitive a)
      ((t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) *
        (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000))
      t := by
  have h1 := quarter_joint_power_deriv (a := a) (r := 1 / 2) ht (by norm_num only)
  have h2 := quarter_joint_power_deriv (a := a) (r := 1 / 4) ht (by norm_num only)
  have h3 := quarter_joint_power_deriv (a := a) (r := -1 / 4) ht (by norm_num only)
  have h4 := quarter_joint_power_deriv (a := a) (r := -1 / 2) ht (by norm_num only)
  have h :=
    ((h1.sub (h2.const_mul (19 / 30))).sub (h3.const_mul (63 / 10))).sub
      (h4.const_mul (1839 / 1000))
  have hp1 := Real.rpow_add ht (-3 / 2) 1
  have hp2 := Real.rpow_add ht (-3 / 2) (3 / 4)
  have hp3 := Real.rpow_add ht (-3 / 2) (1 / 4)
  norm_num only [Real.rpow_one, neg_div] at hp1 hp2 hp3
  convert h using 1
  · funext z
    dsimp only [quarterJointPrimitive, Pi.sub_apply]
    norm_num only
    ring
  · norm_num only [neg_div]
    rw [hp1, hp2, hp3]
    ring

/-- The explicit joint lower-bound integral equals the primitive difference
at its positive endpoints. The derivative and continuity of its integrand
justify the fundamental theorem of calculus. -/
theorem quarter_joint_integral_eq {a u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (∫ t in u..v,
        (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) *
          (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000)) =
      quarterJointPrimitive a v - quarterJointPrimitive a u := by
  have hc :
    ContinuousOn
      (fun t : ℝ ↦
        (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) *
          (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000))
      (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    intro t ht
    have hp := lt_of_lt_of_le hu ht.1
    have hr (r : ℝ) := Real.continuousAt_rpow_const t r (Or.inl hp.ne')
    have hd : ContinuousAt (fun z : ℝ ↦ z ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log z / 2)) t :=
      (hr (-3 / 2)).mul (continuousAt_const.sub ((Real.continuousAt_log hp.ne').div_const 2))
    have he :
      ContinuousAt
        (fun z : ℝ ↦
          z - (19 / 30 : ℝ) * z ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * z ^ (1 / 4 : ℝ) - 1839 / 1000)
        t :=
      ((continuousAt_id.sub ((hr (3 / 4)).const_mul (19 / 30))).sub
            ((hr (1 / 4)).const_mul (63 / 10))).sub_const
        (1839 / 1000)
    exact (hd.mul he).continuousWithinAt
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦
        quarter_joint_primitive_deriv (a := a)
          (by
            rw [Set.uIcc_of_le huv] at ht; exact lt_of_lt_of_le hu ht.1))
      hc.intervalIntegrable

/-- The lower endpoint of the joint primitive is an affine expression in
the width and `log 16`. Exact real-power evaluations give the constants used
in the high-index scalar margin. -/
theorem quarter_joint_primitive_sixteen (a : ℝ) :
    quarterJointPrimitive a 16 =
      (98717 / 3000 : ℝ) * a - (98717 / 12000 : ℝ) * Real.log 16 - 59 / 5 := by
  have hhalf : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by norm_num only
  have hquarter : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by norm_num only
  have hquarterInv : (16 : ℝ) ^ (-1 / 4 : ℝ) = 1 / 2 := by
    rw [neg_div, Real.rpow_neg (by norm_num only), hquarter]
    norm_num only
  have hhalfInv : (16 : ℝ) ^ (-1 / 2 : ℝ) = 1 / 4 := by
    rw [neg_div, Real.rpow_neg (by norm_num only), hhalf]
    norm_num only
  dsimp only [quarterJointPrimitive]
  rw [hhalf, hquarter, hquarterInv, hhalfInv]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
