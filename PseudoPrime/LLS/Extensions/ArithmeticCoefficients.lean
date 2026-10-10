/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperDefinitions

/-!
# Arithmetic coefficients of general Euler data

Ramanujan root bounds control the prime-power coefficients and the Mangoldt coefficients.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- If the local roots at `p` have norm at most one, each positive or zero power
has norm at most one, so the sum defining `a_f(p^k)` has norm at most the degree.
The triangle inequality supplies the Ramanujan coefficient estimate. -/
theorem norm_primePowerCoefficient_le (f : GeneralLFunction) {p : ℕ} (h : ∀ j, ‖f.root p j‖ ≤ 1)
    (k : ℕ) : ‖f.primePowerCoefficient p k‖ ≤ f.degree := by
  calc
    _ ≤ ∑ j : Fin f.degree, ‖f.root p j ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin f.degree, (1 : ℝ) :=
      Finset.sum_le_sum fun j _ ↦ by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (h j)
    _ = f.degree := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- For admissible data, the Mangoldt coefficient at every natural index has norm at
most the degree. It vanishes outside prime powers; on prime powers, apply the local-root
norm bound and the triangle inequality. This controls arithmetic sums in the explicit formulas. -/
theorem norm_mangoldtCoefficient_le (f : GeneralLFunction) (hf : f.IsAdmissible) (n : ℕ) :
    ‖f.mangoldtCoefficient n‖ ≤ f.degree := by
  by_cases hn : IsPrimePow n
  · rw [mangoldtCoefficient, ite_eq_left hn]
    exact norm_primePowerCoefficient_le f (hf.2.2.2.2.1 n.minFac (Nat.minFac_prime hn.ne_one)) _
  · rw [mangoldtCoefficient, ite_eq_right hn, norm_zero]
    exact Nat.cast_nonneg f.degree

/-- For prime `p` and nonzero natural exponent `k`, the Mangoldt coefficient at `p^k`
equals the sum of kth powers of the local roots at `p`. The least prime factor and
factorization exponent recover the two indices. This matches Euler logarithmic derivatives
with the coefficient series. -/
theorem mangoldtCoefficient_prime_pow (f : GeneralLFunction) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    f.mangoldtCoefficient (p ^ k) = f.primePowerCoefficient p k := by
  rw [mangoldtCoefficient, ite_eq_left (hp.prime.isPrimePow.pow hk), hp.pow_minFac hk,
    hp.factorization_pow, Finsupp.single_eq_same]

/-- A uniform coefficient norm bound controls every finite real-weighted sum.
Only the coefficient bound is required; the triangle inequality supplies the estimate.
This permits degree-one character specialization before proving analytic admissibility. -/
theorem norm_finiteWeightedSum_le_of_bound (f : GeneralLFunction) {B : ℝ}
    (hb : ∀ n : ℕ, ‖f.mangoldtCoefficient n‖ ≤ B) (s : Finset ℕ) (w : ℕ → ℝ) :
    ‖∑ n ∈ s, f.mangoldtCoefficient n * (w n : ℂ)‖ ≤ B * ∑ n ∈ s, |w n| := by
  calc
    _ ≤ ∑ n ∈ s, ‖f.mangoldtCoefficient n * (w n : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ s, B * |w n| :=
      Finset.sum_le_sum fun n _ ↦ by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hb n) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- For admissible data and any finite set of natural indices with real weights,
the norm of the weighted Mangoldt-coefficient sum is at most the degree times the sum
of absolute weights. Apply the uniform coefficient bound termwise and the triangle inequality.
The logarithmic and reciprocal arithmetic sums are instances of this estimate. -/
theorem norm_finiteWeightedSum_le (f : GeneralLFunction) (hf : f.IsAdmissible) (s : Finset ℕ)
    (w : ℕ → ℝ) : ‖∑ n ∈ s, f.mangoldtCoefficient n * (w n : ℂ)‖ ≤ f.degree * ∑ n ∈ s, |w n| := by
  exact norm_finiteWeightedSum_le_of_bound f (norm_mangoldtCoefficient_le f hf) s w

/-- For admissible data and any real cutoff, the norm of the logarithmic L-value sum
is bounded by the degree times its sum of absolute weights. Substitute the weight
`Λ(n)/(n log n) * log(x/n)/log x` into the finite-sum estimate.
This supplies the arithmetic upper bound for the logarithmic formula. -/
theorem norm_logValueSum_le (f : GeneralLFunction) (hf : f.IsAdmissible) (x : ℝ) :
    ‖f.logValueSum x‖ ≤
      f.degree *
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          |ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) *
              (Real.log (x / n) / Real.log x)| :=
  norm_finiteWeightedSum_le f hf _ _

/-- For admissible data and any real cutoff, the norm of the truncated-value sum
is at most the degree times its sum of absolute weights. Apply the finite-sum estimate
to `Λ(n) * (1/(n log n) - 1/(x log x))`. This bounds the arithmetic term obtained by
combining the logarithmic and smoothed reciprocal formulas. -/
theorem norm_truncatedValueSum_le (f : GeneralLFunction) (hf : f.IsAdmissible) (x : ℝ) :
    ‖f.truncatedValueSum x‖ ≤
      f.degree *
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          |ArithmeticFunction.vonMangoldt n *
              (1 / ((n : ℝ) * Real.log n) - 1 / (x * Real.log x))| :=
  norm_finiteWeightedSum_le f hf _ _

end PseudoPrime.LLS.Extensions.GeneralLFunction
