/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaResolventCertificate
public import PseudoPrime.Analysis.LogDirichletNumericalBounds

/-! # Euler-ratio certificates for the Gamma resolvent

Small rational bounds for dyadic powers retain the zeta denominator at each node.
The same signed weights then have total centered error strictly below twenty-four.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A small rational lower bound for 2^(-(a-1/2)) at each nonzero resolvent node.
Zero is used at unused nodes. Exact twentieth-power checks certify the fractions;
the values reduce the Euler denominator to rational arithmetic. -/
def gammaResolventDyadicLower (a : ℚ) : ℚ :=
  if a = 11 / 20 then 28 / 29
  else
    if a = 16 / 20 then 4 / 5
    else
      if a = 20 / 20 then 7 / 10
      else
        if a = 34 / 20 then 13 / 30
        else
          if a = 46 / 20 then 2 / 7
          else
            if a = 64 / 20 then 2 / 13
            else if a = 90 / 20 then 1 / 16 else if a = 140 / 20 then 1 / 91 else 0

/-- The natural exponent 20a-10 for a certified resolvent scale. Extract the
numerator as a natural number; the finite check separately verifies that no
fractional part or negative value was lost. -/
def gammaResolventDyadicExponent (a : ℚ) : ℕ :=
  (20 * a - 10).num.toNat

/-- All resolvent nodes have nonnegative dyadic lower bounds, the advertised
integer exponent, and twentieth-power inequality d^20 2^m≤1. Verify the
finite rational and integer data in the kernel. -/
theorem gammaResolvent_dyadic_checks :
    gammaResolventCoefficients.Forall
      (fun ab ↦
        0 ≤ gammaResolventDyadicLower ab.1 ∧
          20 * ab.1 - 10 = (gammaResolventDyadicExponent ab.1 : ℚ) ∧
          gammaResolventDyadicLower ab.1 ^ 20 * 2 ^ gammaResolventDyadicExponent ab.1 ≤ 1) := by
  decide +kernel

/-- At every certified resolvent node, the supplied rational d is at most
2^(-(a-1/2)). Cast the finite checks and compare twentieth powers. This
makes the Euler denominator's numerical replacement sound. -/
theorem gammaResolvent_dyadic_lower_valid (ab : ℚ × ℚ) (hab : ab ∈ gammaResolventCoefficients) :
    (gammaResolventDyadicLower ab.1 : ℝ) ≤ (2 : ℝ) ^ (-((ab.1 : ℝ) - 1 / 2)) := by
  obtain ⟨hd, he, hc⟩ := List.forall_iff_forall_mem.mp gammaResolvent_dyadic_checks ab hab
  have hdR := (Rat.cast_le (K := ℝ)).mpr hd
  have hcR := (Rat.cast_le (K := ℝ)).mpr hc
  norm_num only [Rat.cast_pow, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat] at hdR hcR
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at heR
  have hr : -(gammaResolventDyadicExponent ab.1 : ℝ) / 20 = -((ab.1 : ℝ) - 1 / 2) := by
    linarith only [heR]
  simpa only [hr] using le_two_rpow_neg_twentieth hdR (gammaResolventDyadicExponent ab.1) hcR

/-- For a resolvent scale a, the rational Euler allowance plus archimedean
constant 8/5. Use r=a-1/2 and the certified lower bound d in the denominator
1+d/r. The individual centered Poisson estimate is established analytically. -/
noncomputable def gammaResolventEulerError (a : ℚ) : ℝ :=
  (((a : ℝ) - 1 / 2)⁻¹ ^ 2 + ((a : ℝ) + 1 / 2)⁻¹) /
      (1 + (gammaResolventDyadicLower a : ℝ) / ((a : ℝ) - 1 / 2)) +
    8 / 5

/-- The absolute weighted sum of the certified Euler and Gamma allowances
is strictly below 24. Evaluate the exact rational fractions in the reals.
This is the additive constant of the signed zero-mass estimate. -/
theorem gammaResolvent_euler_error_lt_twenty_four :
    (gammaResolventCoefficients.map (fun ab ↦ |(ab.2 : ℝ)| * gammaResolventEulerError ab.1)).sum <
      (24 : ℝ) := by
  norm_num only [gammaResolventCoefficients, gammaResolventEulerError, gammaResolventDyadicLower,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ite_true, ite_false]

/-- Given the certified centered errors for a finite family of Poisson values,
the signed combination is less than 11783423/25000000 times L plus 24.
Keep signs in the common main term and absolute weights only in the error sum.
This connects the rational error certificate to the analytic Poisson values. -/
theorem gammaResolvent_weighted_lt_of_euler_centered_bounds (P : ℚ → ℝ) (L : ℝ)
    (h : ∀ ab ∈ gammaResolventCoefficients, |P ab.1 - L / 2| ≤ gammaResolventEulerError ab.1) :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * P ab.1)).sum <
      (11783423 / 25000000 : ℝ) * L + 24 := by
  have ht :=
    sum_signed_centered_le gammaResolventCoefficients (fun ab ↦ (ab.2 : ℝ)) (fun ab ↦ P ab.1)
      (fun ab ↦ gammaResolventEulerError ab.1) (L / 2) h
  have he :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum * (L / 2) =
      (11783423 / 25000000 : ℝ) * L := by
    calc
      _ = ((gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2) * L := by ring
      _ = _ := by rw [gammaResolvent_mass_eq]
  rw [he] at ht
  exact ht.trans_lt (add_lt_add_right gammaResolvent_euler_error_lt_twenty_four _)

end PseudoPrime.Analysis
