/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerMoment
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Integral of the sixth logarithmic Euler moment -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real function underlying the sixth logarithmic Dirichlet moment.
Its nonnegative integer values bound the reflected Euler contribution. -/
noncomputable def target028LogSix (x : ℝ) : ℝ :=
  Real.log x ^ 6 * x ^ (-(79 / 50 : ℝ))

/-- For positive arguments, logarithmic substitution turns the sixth
Dirichlet moment into a Gamma density of rate `29/50`. -/
theorem target028_log_six_change {x : ℝ} (hx : 0 < x) :
    x⁻¹ * ((Real.log x) ^ 6 * Real.exp (-((29 / 50 : ℝ) * Real.log x))) = target028LogSix x := by
  rw [show -((29 / 50 : ℝ) * Real.log x) = Real.log x * (-(29 / 50 : ℝ)) by ring, ←
    Real.rpow_def_of_pos hx, ← Real.rpow_neg_one]
  dsimp only [target028LogSix]
  have he : (-1 : ℝ) + (-(29 / 50 : ℝ)) = -(79 / 50 : ℝ) := by norm_num only
  calc
    _ = Real.log x ^ 6 * (x ^ (-1 : ℝ) * x ^ (-(29 / 50 : ℝ))) := by ring
    _ = _ := by rw [← Real.rpow_add hx, he]

/-- The sixth logarithmic Dirichlet moment is integrable above one. Substitute
the logarithm and use the integrable Gamma density of positive rate. -/
theorem target028_log_six_integrable : MeasureTheory.IntegrableOn target028LogSix (Set.Ioi 1) := by
  have hi :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := (6 : ℝ)) (p := 1) (b := (29 / 50 : ℝ))
      (by norm_num only) (by norm_num only) (by norm_num only)
  have hi' :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t ^ 6 * Real.exp (-((29 / 50 : ℝ) * t)))
      (Set.Ioi 0) := by
    change
      MeasureTheory.IntegrableOn
        (fun t : ℝ ↦ t ^ ((6 : ℕ) : ℝ) * Real.exp (-(29 / 50 : ℝ) * t ^ (1 : ℝ))) _ at hi
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using hi
  have h :=
    (MeasureTheory.integrableOn_comp_log_Ioi (fun t : ℝ ↦ t ^ 6 * Real.exp (-((29 / 50 : ℝ) * t)))
          (a := 1) zero_lt_one).2
      (by simpa only [Real.log_one] using hi')
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  simpa only [smul_eq_mul] using target028_log_six_change (lt_trans zero_lt_one hx)

/-- The integral of the sixth logarithmic moment from one to infinity is
`6!/(29/50)^7`. Logarithmic substitution gives the standard Gamma integral. -/
theorem target028_log_six_integral :
    (∫ x : ℝ in Set.Ioi 1, target028LogSix x) = (720 : ℝ) / (29 / 50 : ℝ) ^ 7 := by
  have h :=
    MeasureTheory.integral_comp_log_Ioi (fun t : ℝ ↦ t ^ 6 * Real.exp (-((29 / 50 : ℝ) * t))) (a :=
      1) zero_lt_one
  simp only [Real.log_one] at h
  have he :
    (∫ x : ℝ in Set.Ioi 1, x⁻¹ * (Real.log x ^ 6 * Real.exp (-((29 / 50 : ℝ) * Real.log x)))) =
      ∫ x : ℝ in Set.Ioi 1, target028LogSix x := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact target028_log_six_change (lt_trans zero_lt_one hx)
  rw [show
      (∫ x : ℝ in Set.Ioi 1, x⁻¹ • (Real.log x ^ 6 * Real.exp (-((29 / 50 : ℝ) * Real.log x)))) =
        ∫ x : ℝ in Set.Ioi 1, target028LogSix x
      by simpa only [smul_eq_mul] using he] at h
  have hg :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (7 : ℝ)) (r := (29 / 50 : ℝ)) (by norm_num only)
      (by norm_num only)
  have hgamma : Real.Gamma 7 = 720 := by
    have h := Real.Gamma_nat_eq_factorial 6
    norm_num only [Nat.cast_ofNat, Nat.factorial] at h
    exact h
  have hg' :
    (∫ t : ℝ in Set.Ioi 0, t ^ 6 * Real.exp (-((29 / 50 : ℝ) * t))) = 720 / (29 / 50 : ℝ) ^ 7 := by
    rw [show (7 : ℝ) - 1 = ((6 : ℕ) : ℝ) by norm_num only] at hg
    simp only [Real.rpow_natCast, hgamma] at hg
    norm_num only at hg ⊢
    exact hg
  exact h.trans hg'

/-- At a positive argument, the derivative of the sixth logarithmic moment
has sign equal to the sign of `6 - (79/50) log x` for `x ≥ 1`. -/
theorem target028_log_six_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt target028LogSix
      (Real.log x ^ 5 * x ^ (-(129 / 50 : ℝ)) * (6 - (79 / 50 : ℝ) * Real.log x)) x := by
  have hd :=
    ((Real.hasDerivAt_log hx.ne').pow 6).mul
      (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -(79 / 50 : ℝ)))
  have he :
    6 * Real.log x ^ 5 * x⁻¹ * x ^ (-(79 / 50 : ℝ)) +
        Real.log x ^ 6 * (-(79 / 50 : ℝ) * x ^ (-(79 / 50 : ℝ) - 1)) =
      Real.log x ^ 5 * x ^ (-(129 / 50 : ℝ)) * (6 - (79 / 50 : ℝ) * Real.log x) := by
    have hp : x ^ (-(129 / 50 : ℝ)) = x ^ (-(79 / 50 : ℝ)) * x⁻¹ := by
      rw [← show -(79 / 50 : ℝ) - 1 = -(129 / 50 : ℝ) by norm_num only, Real.rpow_sub_one hx.ne']
      rw [div_eq_mul_inv]
    rw [show -(79 / 50 : ℝ) - 1 = -(129 / 50 : ℝ) by norm_num only, hp]
    ring
  exact he ▸ hd

/-- Rational logarithmic certificates place the maximum of the sixth-moment
integrand between 44 and 45. They will split the finite sum from the tail. -/
theorem target028_log_six_turning_bounds :
    Real.log 44 ≤ (379 / 100 : ℝ) ∧ (19 / 5 : ℝ) ≤ Real.log 45 := by
  have h1 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 44 6 32 3 (379 / 100) = true from by
          decide +kernel)).2
  have h2 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 45 6 32 (19 / 5) 4 = true from by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h1 h2
  exact ⟨h1, h2⟩

/-- The sixth logarithmic moment increases through 44. On this interval its
derivative is nonnegative by the certified turning-point bound. -/
theorem target028_log_six_increasing : MonotoneOn target028LogSix (Set.Icc 1 44) := by
  apply
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 44)
      (fun x hx ↦
        (target028_log_six_derivative (by linarith only [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx ↦
        (target028_log_six_derivative
            (by
              have h := interior_subset hx; linarith only [h.1])).hasDerivWithinAt)
  intro x hx
  have hm : x ∈ Set.Icc (1 : ℝ) 44 := interior_subset hx
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hm.1
  have hl := Real.log_le_log (by linarith only [hm.1]) hm.2
  have hs : 0 ≤ 6 - (79 / 50 : ℝ) * Real.log x := by
    linarith only [hl, target028_log_six_turning_bounds.1]
  exact mul_nonneg (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (by linarith only [hm.1]) _)) hs

/-- The sixth logarithmic moment decreases from 45 onward. Its derivative
is nonpositive on this half-line by the certified turning-point bound. -/
theorem target028_log_six_decreasing : AntitoneOn target028LogSix (Set.Ici 45) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 45)
      (fun x hx ↦
        (target028_log_six_derivative
            (by
              have h : (45 : ℝ) ≤ x := hx; linarith only [h])).continuousAt.continuousWithinAt)
      (fun x hx ↦
        (target028_log_six_derivative
            (by
              have h : (45 : ℝ) ≤ x := interior_subset hx; linarith only [h])).hasDerivWithinAt)
  intro x hx
  have hm : (45 : ℝ) ≤ x := interior_subset hx
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hm])
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 45) hm
  have hs : 6 - (79 / 50 : ℝ) * Real.log x ≤ 0 := by
    linarith only [hl, target028_log_six_turning_bounds.2]
  exact
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg hl0 _) (Real.rpow_nonneg (by linarith only [hm]) _)) hs

/-- The two integer values around the turning point are each at most 100.
Use the upper logarithm bound four and compare the negative power with `1/x`. -/
theorem target028_log_six_turning_value {x : ℝ} (hlo : 44 ≤ x) (hhi : x ≤ 45) :
    target028LogSix x ≤ 100 := by
  have hx : 0 < x := by linarith only [hlo]
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hlo])
  have h45 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 45 6 32 3 4 = true from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at h45
  have hl : Real.log x ≤ 4 := (Real.log_le_log hx hhi).trans h45
  have hp := pow_le_pow_left₀ hl0 hl 6
  have hr :=
    Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ x by linarith only [hlo])
      (show -(79 / 50 : ℝ) ≤ -1 by norm_num only)
  rw [Real.rpow_neg_one] at hr
  have hi : x⁻¹ ≤ (44 : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 44) hlo
  have hm :=
    mul_le_mul hp (hr.trans hi) (Real.rpow_nonneg hx.le _) (by norm_num only : (0 : ℝ) ≤ 4 ^ 6)
  dsimp only [target028LogSix]
  norm_num only at hm ⊢
  linarith only [hm]

/-- The sixth logarithmic Dirichlet series is bounded by its Gamma integral
plus 200. Split at the two integers surrounding the maximum and compare the
increasing and decreasing portions with their respective integrals. -/
theorem target028_log_six_integral_sum_bound :
    (∑' n : ℕ, Real.log n ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ))) ≤
      (720 : ℝ) / (29 / 50 : ℝ) ^ 7 + 200 := by
  have hn (x : ℝ) (hx : 1 ≤ x) : 0 ≤ target028LogSix x := by
    exact
      mul_nonneg (pow_nonneg (Real.log_nonneg hx) _) (Real.rpow_nonneg (by linarith only [hx]) _)
  have hpre :
    (∑ n ∈ Finset.Ico (1 : ℕ) 44, target028LogSix (n : ℝ)) ≤
      ∫ x : ℝ in (1 : ℝ)..44, target028LogSix x := by
    have hmono : MonotoneOn target028LogSix (Set.Icc ((1 : ℕ) : ℝ) ((44 : ℕ) : ℝ)) := by
      simpa only [Nat.cast_one, Nat.cast_ofNat] using target028_log_six_increasing
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      MonotoneOn.sum_le_integral_Ico (by decide : (1 : ℕ) ≤ 44) hmono
  have hi45 :=
    target028_log_six_integrable.mono_set (Set.Ioi_subset_Ioi (by norm_num only : (1 : ℝ) ≤ 45))
  have htail :=
    target028_log_six_decreasing.tsum_comp_add_le_integral 45
      (by simpa only [Nat.cast_ofNat] using hi45)
      (fun x hx ↦
        hn x
          (by
            have h : (45 : ℝ) < x := Set.mem_Ioi.mp hx
            linarith only [h]))
  have hsum := (refined_log_power_summable 6).sum_add_tsum_nat_add 46
  have h44 := target028_log_six_turning_value (x := 44) (by norm_num only) (by norm_num only)
  have h45 := target028_log_six_turning_value (x := 45) (by norm_num only) (by norm_num only)
  have hpart :
    (∑ n ∈ Finset.range 46, target028LogSix (n : ℝ)) =
      (∑ n ∈ Finset.Ico (1 : ℕ) 44, target028LogSix (n : ℝ)) + target028LogSix 44 +
        target028LogSix 45 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    congr 2
    rw [Finset.sum_Ico_eq_sub _ (by decide : (1 : ℕ) ≤ 44)]
    norm_num only [Finset.sum_range_one, Nat.cast_zero, target028LogSix, Real.log_zero]
    rw [sub_zero]
  have hsplit :=
    intervalIntegral.integral_Ioi_sub_Ioi target028_log_six_integrable
      (by norm_num only : (1 : ℝ) ≤ 44)
  have hi44 :=
    target028_log_six_integrable.mono_set (Set.Ioi_subset_Ioi (by norm_num only : (1 : ℝ) ≤ 44))
  have hsplit2 := intervalIntegral.integral_Ioi_sub_Ioi hi44 (by norm_num only : (44 : ℝ) ≤ 45)
  have hmid : 0 ≤ ∫ x : ℝ in (44 : ℝ)..45, target028LogSix x := by
    apply intervalIntegral.integral_nonneg (by norm_num only)
    intro x hx
    exact hn x (by linarith only [hx.1])
  change (∑' n : ℕ, target028LogSix (n : ℝ)) ≤ _
  change
    (∑ n ∈ Finset.range 46, target028LogSix (n : ℝ)) +
        (∑' n : ℕ, target028LogSix ((n + 46 : ℕ) : ℝ)) =
      ∑' n : ℕ, target028LogSix (n : ℝ) at hsum
  rw [← hsum, hpart]
  have htail' :
    (∑' n : ℕ, target028LogSix ((n + 46 : ℕ) : ℝ)) ≤ ∫ x : ℝ in Set.Ioi 45, target028LogSix x := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_ofNat] using htail
  rw [target028_log_six_integral] at hsplit
  linarith only [hpre, htail', h44, h45, hsplit, hsplit2, hmid]

/-- The reflected principal Euler term is bounded using the exact sixth-moment
integral and the two turning-point terms. This sharper bound is small enough
to support the low finite-cutoff comparisons. -/
theorem target028_reflected_euler_sharp {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
        x ^ (-(27 / 25 : ℝ)) *
        (((21 / 8 : ℝ) + Real.log x) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
          ((720 : ℝ) / (29 / 50 : ℝ) ^ 7 + 200)) := by
  apply (refined_reflected_one_explicit hx).trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add le_rfl target028_log_six_integral_sum_bound
  · positivity

end PseudoPrime.PrimeTestBounds.MillerRabin
