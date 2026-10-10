/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.TruncatedValueBounds
public import PseudoPrime.LLS.PrimePowerDiskComparison

/-! Finite prime-power comparisons and logarithmic lower bounds for general L-functions. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For any general L-function data and real cutoff, reindex the real truncated sum by
primes and positive exponents. Mangoldt support removes other indices, and the coefficient
at a prime power is the sum of powers of local roots. No admissibility is needed.
This identity connects finite coefficient sums to local Euler-root comparisons. -/
theorem truncatedValueSum_re_eq_primePower (f : GeneralLFunction) (x : ℝ) :
    (f.truncatedValueSum x).re =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
          PaperStatements.primePowerComparisonWeight x p k * (f.primePowerCoefficient p k).re := by
  classical
  rw [truncatedValueSum, Complex.re_sum, ← Finset.Icc_add_one_left_eq_Ioc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  let g : ℕ → ℝ := fun n ↦
    (f.mangoldtCoefficient n).re *
      (ArithmeticFunction.vonMangoldt n * (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x)))
  have hg : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow n, g n) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, g n := by
    apply Finset.sum_filter_of_ne
    intro n _ hn
    by_contra hp
    have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp
    exact
      hn
        (by
          dsimp only [g]; rw [hz, zero_mul, mul_zero])
  change (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, g n) = _
  rw [← hg, AnalyticNumberTheory.Arithmetic.sum_primePow_eq_sum_primesLE]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k hk
  have hpk :=
    mangoldtCoefficient_prime_pow f (Nat.mem_primesLE.mp hp).2
      (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)
  dsimp only [g]
  rw [hpk]
  simp only [PaperStatements.primePowerComparisonWeight, Nat.cast_pow]
  ring

/-- For admissible data and cutoff at least one hundred, the real truncated L-value sum is
at least the degree times the alternating prime-power sum. Reindex by prime powers,
apply the closed-unit-disk comparison to each Ramanujan root, and sum over the roots.
This retains the sharper arithmetic expression needed for the general L-value lower bound. -/
theorem degree_mul_alternatingPrimePowerSum_le (f : GeneralLFunction) (hf : f.IsAdmissible) {x : ℝ}
    (hx : 100 ≤ x) :
    (f.degree : ℝ) * PaperStatements.alternatingPrimePowerSum x ≤ (f.truncatedValueSum x).re := by
  classical
  rw [truncatedValueSum_re_eq_primePower]
  unfold PaperStatements.alternatingPrimePowerSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpx : (p : ℝ) ≤ x :=
    (by exact_mod_cast (Nat.mem_primesLE.mp hp).1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
      (Nat.floor_le (le_trans (by norm_num only : (0 : ℝ) ≤ 100) hx))
  have hj (j : Fin f.degree) :=
    PaperStatements.prime_disk_interval_comparison hx (Nat.mem_primesLE.mp hp).2 hpx
      (hf.2.2.2.2.1 p (Nat.mem_primesLE.mp hp).2 j)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hleft :
    (∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
        ArithmeticFunction.vonMangoldt (p ^ k) * (-1 : ℝ) ^ k *
          (1 / ((p : ℝ) ^ k * Real.log ((p : ℝ) ^ k)) - 1 / (x * Real.log x))) =
      ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
        PaperStatements.primePowerComparisonWeight x p k * (-1 : ℝ) ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    unfold PaperStatements.primePowerComparisonWeight
    ring
  rw [hleft]
  refine h.trans_eq ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum, primePowerCoefficient, Complex.re_sum]

/-- For admissible RH data and cutoff at least one hundred, the negative logarithm of the
L-value norm is bounded by the negative alternating sum times the degree, the leading
conductor contribution and the uniform truncation error. Combine the root comparison with
the conductor-centered formula. This replaces the symmetric Mangoldt majorant
in the lower bound. -/
theorem neg_log_norm_L_one_le_alternating (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    -Real.log ‖f.L 1‖ ≤
      -(f.degree : ℝ) * PaperStatements.alternatingPrimePowerSum x +
        |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
        f.truncatedConductorErrorBound x := by
  have hx2 : 2 ≤ x := le_trans (by norm_num only : (2 : ℝ) ≤ 100) hx
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx
  obtain ⟨θ, hθ, he⟩ := exists_truncatedValue_conductor_error_le_uniform f hf hRH hx2
  have hT := degree_mul_alternatingPrimePowerSum_le f hf hx
  have hθC :
    |θ * Real.log f.analyticConductor / (Real.sqrt x * Real.log x)| ≤
      |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) := by
    rw [abs_div, abs_mul,
      abs_of_pos (mul_pos (Real.sqrt_pos.mpr (zero_lt_one.trans hx1)) (Real.log_pos hx1))]
    exact
      div_le_div_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hθ)
        (mul_nonneg (Real.sqrt_nonneg x) (Real.log_pos hx1).le)
  linarith only [(abs_le.mp he).1, (abs_le.mp hθC).1, hT]

/-- For admissible RH data and cutoff at least one hundred, the reciprocal L-value norm
is bounded by the exponential of the alternating-sum conductor bound. Exponentiate the
negative logarithm inequality and use the real logarithm of the reciprocal.
This is the general lower-value interface preceding quantitative Euler-product estimates. -/
theorem reciprocal_norm_L_one_le_exp_alternating (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x : ℝ} (hx : 100 ≤ x) :
    1 / ‖f.L 1‖ ≤
      Real.exp
        (-(f.degree : ℝ) * PaperStatements.alternatingPrimePowerSum x +
          |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
          f.truncatedConductorErrorBound x) := by
  apply (Real.le_exp_log (1 / ‖f.L 1‖)).trans
  apply Real.exp_le_exp.mpr
  rw [one_div, Real.log_inv]
  exact neg_log_norm_L_one_le_alternating f hf hRH hx

end PseudoPrime.LLS.Extensions.GeneralLFunction
