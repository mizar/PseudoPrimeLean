/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleKernelMass
public import PseudoPrime.Analysis.MellinLogMoments

/-! # Exact unit cutoffs of the actual rational-pole Mellin kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On (0,1], c>=0 keeps the rational-pole profile in its polynomial branch.
Combine the exponential with the square-root weight into a positive real power.
This pointwise identity reduces the cutoff integral to logarithmic moments. -/
private theorem rationalPole_profile_weight (m : ℕ) {a c u : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    Analysis.rationalPoleProfile m a c u / Real.sqrt u =
      (Real.exp (-c / a) / ((2 * a) ^ (2 * m - 1) * ((2 * m - 1).factorial : ℝ))) *
        (u ^ (((1 + a) / (2 * a)) - 1) * (2 * c - Real.log u) ^ (2 * m - 1)) := by
  have hl : Real.log u ≤ 2 * c :=
    (Real.log_nonpos hu.1.le hu.2).trans (mul_nonneg (by norm_num only) hc)
  rw [Analysis.rationalPoleProfile, ite_eq_left ⟨hu.1, hl⟩, div_pow]
  have he :
    Real.exp (-((2 * c - Real.log u) / (2 * a))) / Real.sqrt u =
      Real.exp (-c / a) * u ^ (((1 + a) / (2 * a)) - 1) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu.1, Real.rpow_def_of_pos hu.1, ← Real.exp_sub, ←
      Real.exp_add]
    congr 1
    apply (mul_left_injective₀ ha.ne')
    simp only [div_eq_mul_inv, mul_inv_rev, neg_mul, mul_sub, mul_add, ← mul_assoc, mul_one]
    ring_nf
    simp only [mul_assoc, mul_inv_cancel₀ ha.ne', mul_one, pow_two]
    ring
  calc
    _ =
        ((2 * c - Real.log u) ^ (2 * m - 1) /
            ((2 * a) ^ (2 * m - 1) * ((2 * m - 1).factorial : ℝ))) *
          (Real.exp (-((2 * c - Real.log u) / (2 * a))) / Real.sqrt u) :=
      by ring
    _ = _ := by
      rw [he]; ring

/-- For m>=1,0<a<1,c>=0, the actual kernel's unit cutoff equals an explicit
finite logarithmic-moment sum. Substitute the proved transform, expand the shifted
logarithmic power and integrate each term. No numerical quadrature is involved. -/
theorem rationalPole_cutoff_moment (m : ℕ) {a c : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a < 1)
    (hc : 0 ≤ c) :
    (∫ u : ℝ in (0 : ℝ)..1,
        ((rationalPoleMellinKernel m a c hm ha ha1).transform u).re / Real.sqrt u) =
      (Real.exp (-c / a) / ((2 * a) ^ (2 * m - 1) * ((2 * m - 1).factorial : ℝ))) *
        ∑ j ∈ Finset.range (2 * m - 1 + 1),
          ((Nat.choose (2 * m - 1) j : ℝ) * (2 * c) ^ (2 * m - 1 - j)) *
            ((j.factorial : ℝ) / ((1 + a) / (2 * a)) ^ (j + 1)) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  calc
    _ =
        ∫ u : ℝ in Set.Ioc 0 1,
          (Real.exp (-c / a) / ((2 * a) ^ (2 * m - 1) * ((2 * m - 1).factorial : ℝ))) *
            (u ^ (((1 + a) / (2 * a)) - 1) * (2 * c - Real.log u) ^ (2 * m - 1)) :=
      by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      rw [rationalPole_transform m hm ha ha1 hu.1, Complex.ofReal_re]
      exact rationalPole_profile_weight m ha hc hu
    _ = _ := by
      rw [MeasureTheory.integral_const_mul,
        (Analysis.shifted_log_moment (2 * m - 1) (2 * c)
            (div_pos (by linarith only [ha]) (mul_pos (by norm_num only) ha))).2]

/-- The actual fixed fourth-order kernel has unit cutoff
(484820459/528581976) exp(-14/13). Evaluate its four rational moment terms exactly.
This is the principal integral used in the quadratic coefficient certificate. -/
theorem rationalPole_four_cutoff :
    (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleFourKernel.transform u).re / Real.sqrt u) =
      (484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13)) := by
  rw [rationalPoleFourKernel, rationalPole_cutoff_moment _ _ _ _ (by norm_num only)]
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.choose,
    Nat.factorial, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  ring

/-- The actual fixed sixth-order kernel has unit cutoff (80993/14580) exp(-3).
Evaluate its six rational moment terms exactly. The shared index-four, five and six
coefficient certificates use this actual truncated integral. -/
theorem rationalPole_six_cutoff :
    (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) =
      (80993 / 14580 : ℝ) * Real.exp (-3) := by
  rw [rationalPoleSixKernel, rationalPole_cutoff_moment _ _ _ _ (by norm_num only)]
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.choose,
    Nat.factorial, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  ring

end PseudoPrime.LLS.PaperStatements
