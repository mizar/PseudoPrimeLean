/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedResolventWeight
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletBounds

/-! # Summability of the signed Gamma Euler weight

Finite resolvent coefficients may be combined before taking the infinite Mangoldt sum.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a finite rational list whose scales exceed one half.
Claim: the Mangoldt series weighted by the signed Euler combination is summable.
Proof: each exponent exceeds one, and a finite sum preserves summability.
Role: justify infinite signed prefix comparisons without dropping negative coefficients. -/
theorem summable_gamma_euler_list (l : List (ℚ × ℚ)) (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n *
          (l.map (fun ab ↦ (ab.2 : ℝ) * (n : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))))).sum) := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.sum_nil, mul_zero] using
      (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℝ)))
  | cons ab l ih =>
    have ha := hl ab List.mem_cons_self
    have hσ : 1 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by
      have hc : (1 / 2 : ℝ) < (ab.1 : ℝ) := by
        have hcast : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
        norm_num only at hcast
        exact hcast
      linarith only [hc]
    have hs := AnalyticNumberTheory.Arithmetic.summable_vonMangoldt_div_rpow hσ
    have ht := ih (fun a h ↦ hl a (List.mem_cons_of_mem ab h))
    have he :
      (fun n : ℕ ↦
          ArithmeticFunction.vonMangoldt n *
            ((ab :: l).map (fun a ↦ (a.2 : ℝ) * (n : ℝ) ^ (-(1 / 2 + (a.1 : ℝ))))).sum) =
        (fun n ↦
          (ab.2 : ℝ) * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + (ab.1 : ℝ))) +
            ArithmeticFunction.vonMangoldt n *
              (l.map (fun a ↦ (a.2 : ℝ) * (n : ℝ) ^ (-(1 / 2 + (a.1 : ℝ))))).sum) := by
      funext n
      simp only [List.map_cons, List.sum_cons, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      ring
    rw [he]
    exact (hs.mul_left (ab.2 : ℝ)).add ht

/-- The Mangoldt factor times the signed Euler weight at a natural input.
Input: any natural number, including zero and one.
Output: the common nonnegative weight used by infinite prefix comparisons.
Role: retain the actual Euler series while zero Mangoldt values remove the small inputs. -/
noncomputable def gammaResolventMangoldtWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * gammaResolventEulerWeight (n : ℝ)

/-- Claim: the actual signed Mangoldt Euler weight is summable.
Proof: apply the list theorem to the certified resolvent scales.
Role: permit the signed infinite Euler comparison and finite prefix subtraction. -/
theorem summable_gammaResolventMangoldtWeight : Summable gammaResolventMangoldtWeight := by
  exact
    summable_gamma_euler_list gammaResolventCoefficients
      (List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half)

/-- Claim: every natural input has nonnegative signed Mangoldt weight.
Proof: zero has zero Mangoldt value; positive inputs use Euler-weight positivity.
Role: allow one-sided comparisons of the weighted character series. -/
theorem gammaResolventMangoldtWeight_nonneg (n : ℕ) : 0 ≤ gammaResolventMangoldtWeight n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp only [gammaResolventMangoldtWeight, h, ArithmeticFunction.map_zero, zero_mul, le_refl]
  · exact
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (gamma_resolvent_euler_weight_nonneg (Nat.one_le_cast.mpr h))

/-- Input: real character values bounded in absolute value by one.
Claim: their signed Mangoldt Euler series is summable.
Proof: dominate its norm by the nonnegative summable Mangoldt weight.
Role: justify the left side of the signed infinite Poisson comparison. -/
theorem summable_gamma_signed_euler (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    Summable (fun n ↦ -c n * gammaResolventMangoldtWeight n) := by
  refine summable_gammaResolventMangoldtWeight.of_norm_bounded (fun n ↦ ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (gammaResolventMangoldtWeight_nonneg n)]
  exact
    (mul_le_mul_of_nonneg_right (hc n) (gammaResolventMangoldtWeight_nonneg n)).trans_eq (one_mul _)

/-- Input: a finite prefix and real values bounded by one in absolute value.
Claim: the signed infinite series is bounded by total mass minus twice the prefix,
with the prefix correction retained exactly.
Proof: summable pointwise comparison followed by finite-support summation.
Role: the infinite Euler-side input for the signed Poisson prefix bound. -/
theorem gamma_signed_euler_tsum_prefix_le (B : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    (∑' n : ℕ, -c n * gammaResolventMangoldtWeight n) ≤
      (∑' n : ℕ, gammaResolventMangoldtWeight n) - 2 * (∑ n ∈ B, gammaResolventMangoldtWeight n) +
        ∑ n ∈ B, (1 - c n) * gammaResolventMangoldtWeight n := by
  have hs := summable_gammaResolventMangoldtWeight
  have hb : Summable (fun n ↦ if n ∈ B then gammaResolventMangoldtWeight n else 0) :=
    summable_of_ne_finset_zero (fun n hn ↦ ite_eq_right hn)
  have hd : Summable (fun n ↦ if n ∈ B then (1 - c n) * gammaResolventMangoldtWeight n else 0) :=
    summable_of_ne_finset_zero (fun n hn ↦ ite_eq_right hn)
  have hp :
    ∀ n,
      -c n * gammaResolventMangoldtWeight n ≤
        gammaResolventMangoldtWeight n - 2 * (if n ∈ B then gammaResolventMangoldtWeight n else 0) +
          (if n ∈ B then (1 - c n) * gammaResolventMangoldtWeight n else 0) := by
    intro n
    split_ifs with h
    · ring_nf; exact le_rfl
    · nlinarith only [(abs_le.mp (hc n)).1, gammaResolventMangoldtWeight_nonneg n]
  have hi := (summable_gamma_signed_euler c hc).tsum_le_tsum hp ((hs.sub (hb.mul_left 2)).add hd)
  rw [(hs.sub (hb.mul_left 2)).tsum_add hd, hs.tsum_sub (hb.mul_left 2), tsum_mul_left] at hi
  have hbval :
    (∑' n : ℕ, if n ∈ B then gammaResolventMangoldtWeight n else 0) =
      ∑ n ∈ B, gammaResolventMangoldtWeight n := by
    rw [tsum_eq_sum (fun n hn ↦ ite_eq_right hn)]
    exact Finset.sum_congr rfl (fun n hn ↦ ite_eq_left hn)
  have hdval :
    (∑' n : ℕ, if n ∈ B then (1 - c n) * gammaResolventMangoldtWeight n else 0) =
      ∑ n ∈ B, (1 - c n) * gammaResolventMangoldtWeight n := by
    rw [tsum_eq_sum (fun n hn ↦ ite_eq_right hn)]
    exact Finset.sum_congr rfl (fun n hn ↦ ite_eq_left hn)
  rw [hbval, hdval] at hi
  exact hi

/-- Input: any complex Dirichlet character and a finite prefix.
Claim: its real signed Euler sum obeys the infinite prefix bound with local correction.
Proof: real parts have absolute value at most the character norm, which is at most one.
Role: connect the infinite comparison directly to characters in the Poisson identity. -/
theorem gamma_character_signed_euler_prefix_le {q : ℕ} (χ : DirichletCharacter ℂ q) (B : Finset ℕ) :
    (∑' n : ℕ, -(χ n).re * gammaResolventMangoldtWeight n) ≤
      (∑' n : ℕ, gammaResolventMangoldtWeight n) - 2 * (∑ n ∈ B, gammaResolventMangoldtWeight n) +
        ∑ n ∈ B, (1 - (χ n).re) * gammaResolventMangoldtWeight n := by
  exact
    gamma_signed_euler_tsum_prefix_le B (fun n ↦ (χ n).re)
      (fun n ↦ (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))

end PseudoPrime.Analysis
