/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSignedResolventWeight
public import PseudoPrime.Analysis.SignedResolventEulerBounds

/-! # Summable nonnegative Gaussian Mangoldt weights and retained prefixes -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The Mangoldt factor times the signed Euler weight at a natural input.
Input: any natural number, including zero and one.
Output: the common nonnegative weight used by infinite prefix comparisons.
Role: retain the actual Euler series while zero Mangoldt values remove the small inputs. -/
noncomputable def gaussianResolventMangoldtWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * gaussianResolventEulerWeight (n : ℝ)

/-- Claim: the actual signed Mangoldt Euler weight is summable.
Proof: apply the list theorem to the certified resolvent scales.
Role: permit the signed infinite Euler comparison and finite prefix subtraction. -/
theorem summable_gaussianResolventMangoldtWeight : Summable gaussianResolventMangoldtWeight := by
  exact
    summable_gamma_euler_list gaussianResolventCoefficients
      (List.forall_iff_forall_mem.mp gaussianResolvent_scales_gt_half)

/-- Claim: every natural input has nonnegative signed Mangoldt weight.
Proof: zero has zero Mangoldt value; positive inputs use Euler-weight positivity.
Role: allow one-sided comparisons of the weighted character series. -/
theorem gaussianResolventMangoldtWeight_nonneg (n : ℕ) : 0 ≤ gaussianResolventMangoldtWeight n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp only [gaussianResolventMangoldtWeight, h, ArithmeticFunction.map_zero, zero_mul, le_refl]
  · exact
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (gaussian_resolvent_euler_weight_nonneg (Nat.one_le_cast.mpr h))

/-- Input: real character values bounded in absolute value by one.
Claim: their signed Mangoldt Euler series is summable.
Proof: dominate its norm by the nonnegative summable Mangoldt weight.
Role: justify the left side of the signed infinite Poisson comparison. -/
theorem summable_gaussian_signed_euler (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    Summable (fun n ↦ -c n * gaussianResolventMangoldtWeight n) := by
  exact
    summable_signed_weight gaussianResolventMangoldtWeight c
      summable_gaussianResolventMangoldtWeight hc

/-- Input: a finite prefix and real values bounded by one in absolute value.
Claim: the signed infinite series is bounded by total mass minus twice the prefix,
with the prefix correction retained exactly.
Proof: summable pointwise comparison followed by finite-support summation.
Role: the infinite Euler-side input for the signed Poisson prefix bound. -/
theorem gaussian_signed_euler_tsum_prefix_le (B : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    (∑' n : ℕ, -c n * gaussianResolventMangoldtWeight n) ≤
      (∑' n : ℕ, gaussianResolventMangoldtWeight n) -
          2 * (∑ n ∈ B, gaussianResolventMangoldtWeight n) +
        ∑ n ∈ B, (1 - c n) * gaussianResolventMangoldtWeight n := by
  exact
    signed_weight_prefix_le gaussianResolventMangoldtWeight c
      summable_gaussianResolventMangoldtWeight gaussianResolventMangoldtWeight_nonneg hc B

/-- Input: any complex Dirichlet character and a finite prefix.
Claim: its real signed Euler sum obeys the infinite prefix bound with local correction.
Proof: real parts have absolute value at most the character norm, which is at most one.
Role: connect the infinite comparison directly to characters in the Poisson identity. -/
theorem gaussian_character_signed_euler_prefix_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (B : Finset ℕ) :
    (∑' n : ℕ, -(χ n).re * gaussianResolventMangoldtWeight n) ≤
      (∑' n : ℕ, gaussianResolventMangoldtWeight n) -
          2 * (∑ n ∈ B, gaussianResolventMangoldtWeight n) +
        ∑ n ∈ B, (1 - (χ n).re) * gaussianResolventMangoldtWeight n := by
  exact
    gaussian_signed_euler_tsum_prefix_le B (fun n ↦ (χ n).re)
      (fun n ↦ (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))

end PseudoPrime.Analysis
