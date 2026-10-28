/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.QuadraticExcludedEndpoint
public import PseudoPrime.Analysis.FiniteLinearBudget

/-! # Prime-factor budgets for the combined quadratic endpoint weight -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Group the structural quadratic exclusion coefficients over positive powers of a base,
retaining the cutoff and the zero cost of unit squares. Inputs are a level, cutoff,
weight and natural base; later results use prime bases. The output is the local real
cost used by the logarithmic prime-factor budget. -/
noncomputable def quadraticExcludedPrimeCost (q : ℕ) (x : ℝ) (w : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    if p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ then
      (if Nat.Coprime (p ^ k) q then if IsSquare (p ^ k) then 0 else 2 else 1) * w (p ^ k)
    else 0

/-- For nonzero N, nonnegative cutoff and a weight vanishing off prime powers,
the structural exclusion budget equals the sum of local costs over the distinct
prime factors of N. Reindex prime powers and commute finite sums. No positivity
of the weight is needed; square cancellation is retained before any upper bound. -/
theorem quadraticExcludedBudget_eq_sum_primeFactors {N : ℕ} (hN : N ≠ 0) (q : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (w : ℕ → ℝ) (hw : ∀ n : ℕ, ¬IsPrimePow n → w n = 0) :
    quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) w =
      ∑ p ∈ N.primeFactors, quadraticExcludedPrimeCost q x w p := by
  unfold quadraticExcludedBudget
  rw [sum_not_coprime_eq_sum_prime_powers _ N hx (fun n hn ↦ by rw [hw n hn, mul_zero])]
  symm
  unfold quadraticExcludedPrimeCost
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_filter]
  have hs :
    N.primeFactors.filter (fun p ↦ p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊) =
      (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter (fun p ↦ p.Prime ∧ p ∣ N) := by
    ext p
    constructor
    · intro hp
      have h := Finset.mem_filter.mp hp
      have ht := (Nat.mem_primeFactors_of_ne_zero hN).mp h.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨ht.1.pos, h.2⟩, ht⟩
    · intro hp
      have h := Finset.mem_filter.mp hp
      exact
        Finset.mem_filter.mpr
          ⟨(Nat.mem_primeFactors_of_ne_zero hN).mpr h.2, (Finset.mem_Ioc.mp h.1).2⟩
  rw [hs]

/-- Assume N is nonzero, the cutoff is nonnegative, and w vanishes off prime powers.
If each prime cost outside finite T is at most a*log p with a>=0, the total budget
is at most a*log N plus the positive excess costs on T. Apply the exact decomposition
and the generic finite linear budget. This is the scalar certification interface. -/
theorem quadraticExcludedBudget_le_primeBudget {N : ℕ} (hN : N ≠ 0) (q : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, ¬IsPrimePow n → w n = 0) (T : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (htail : ∀ p ∈ N.primeFactors, p ∉ T → quadraticExcludedPrimeCost q x w p ≤ a * Real.log p) :
    quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) w ≤
      a * Real.log N + ∑ p ∈ T, max 0 (quadraticExcludedPrimeCost q x w p - a * Real.log p) := by
  rw [quadraticExcludedBudget_eq_sum_primeFactors hN q hx w hw]
  exact
    PseudoPrime.Analysis.finite_sum_le_linear_budget_add_excess N.primeFactors T
      (quadraticExcludedPrimeCost q x w) (fun p ↦ Real.log p) ha (sum_log_primeFactors_le_log hN)
      htail

/-- For a prime base and any natural exponent, its power is square exactly when
the exponent is even. Read the exponent from the prime factorization; conversely
use the square representation of an even power. This removes square tests from
local quadratic prime costs. -/
theorem isSquare_prime_pow_iff_even {p k : ℕ} (hp : p.Prime) : IsSquare (p ^ k) ↔ Even k := by
  constructor
  · intro hs
    have he := Nat.isSquare_iff_even_factorization.mp hs p hp
    simpa only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self,
      mul_one] using he
  · intro hk
    exact hk.isSquare_pow p

/-- If the base is not coprime to the level, every positive-power coefficient is
one. Thus the local structural cost is the cutoff sum of the weights themselves.
Use coprimality of powers. No primality or weight positivity is needed; this is
the ramified branch of the finite scalar budget. -/
theorem quadraticExcludedPrimeCost_of_not_coprime {q p : ℕ} (hc : ¬Nat.Coprime p q) (x : ℝ)
    (w : ℕ → ℝ) :
    quadraticExcludedPrimeCost q x w p =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        if p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ then w (p ^ k) else 0 := by
  unfold quadraticExcludedPrimeCost
  apply Finset.sum_congr rfl
  intro k hk
  have hcp : ¬Nat.Coprime (p ^ k) q := fun h ↦
    hc ((Nat.coprime_pow_left_iff (Finset.mem_Icc.mp hk).1 p q).mp h)
  simp only [hcp, ite_false, one_mul]

/-- For a prime base coprime to the level, the local structural cost is twice the
cutoff weight sum on odd exponents. Even exponents are squares and contribute zero.
Use the exact square criterion before splitting the cutoff and parity cases.
This retains cancellation when producing numerical or analytic tail bounds. -/
theorem quadraticExcludedPrimeCost_of_coprime {q p : ℕ} (hp : p.Prime) (hc : Nat.Coprime p q)
    (x : ℝ) (w : ℕ → ℝ) :
    quadraticExcludedPrimeCost q x w p =
      2 *
        ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
          if p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ ∧ ¬Even k then w (p ^ k) else 0 := by
  unfold quadraticExcludedPrimeCost
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hcp : Nat.Coprime (p ^ k) q := (Nat.coprime_pow_left_iff (Finset.mem_Icc.mp hk).1 p q).mpr hc
  rw [ite_eq_left hcp]
  simp only [isSquare_prime_pow_iff_even hp]
  by_cases hcut : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊
  · by_cases he : Even k
    · simp only [hcut, he, ite_true, not_true_eq_false, and_false, ite_false, zero_mul, mul_zero]
    · simp only [hcut, he, ite_false, not_false_eq_true, and_self, ite_true]
  · simp only [hcut, ite_false, false_and, mul_zero]

/-- For x>=1 and a base p>x, every local prime-power term is absent, so its cost
is zero for any level and weight. The cutoff x^(1/k) is at most x for k>=1.
This makes the prime-cost certification finite in p without enumerating inputs N. -/
theorem quadraticExcludedPrimeCost_eq_zero_of_large {q p : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hp : (x : ℝ) < p) (w : ℕ → ℝ) : quadraticExcludedPrimeCost q x w p = 0 := by
  unfold quadraticExcludedPrimeCost
  apply Finset.sum_eq_zero
  intro k hk
  have hk1 : 1 ≤ (k : ℝ) := Nat.one_le_cast.mpr (Finset.mem_Icc.mp hk).1
  have he : (1 : ℝ) / k ≤ 1 := (div_le_one (lt_of_lt_of_le zero_lt_one hk1)).mpr hk1
  have hpow : x ^ ((1 : ℝ) / k) ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx he
  have hcut : ¬p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ := by
    intro hc
    have hr := (Nat.cast_le.mpr hc).trans (Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hx) _))
    exact (not_lt_of_ge (hr.trans hpow)) hp
  rw [ite_eq_right hcut]

/-- For a nonzero ambient modulus and x>=1, it suffices to check the logarithmic
cost bound only on primes p<=x outside finite T. Larger bases have zero cost and
log p is nonnegative. This reduces uniform tail certification to a finite prime
range while preserving the same total budget and exceptional excesses. -/
theorem quadraticExcludedBudget_le_primeBudget_of_finite_tail {N : ℕ} (hN : N ≠ 0) (q : ℕ) {x : ℝ}
    (hx : 1 ≤ x) (w : ℕ → ℝ) (hw : ∀ n : ℕ, ¬IsPrimePow n → w n = 0) (T : Finset ℕ) {a : ℝ}
    (ha : 0 ≤ a)
    (htail :
      ∀ p : ℕ,
        p.Prime → (p : ℝ) ≤ x → p ∉ T → quadraticExcludedPrimeCost q x w p ≤ a * Real.log p) :
    quadraticExcludedBudget q N (Finset.Ioc 0 ⌊x⌋₊) w ≤
      a * Real.log N + ∑ p ∈ T, max 0 (quadraticExcludedPrimeCost q x w p - a * Real.log p) := by
  apply quadraticExcludedBudget_le_primeBudget hN q (zero_le_one.trans hx) w hw T ha
  intro p hp hT
  have hprime := Nat.prime_of_mem_primeFactors hp
  by_cases hpx : (p : ℝ) ≤ x
  · exact htail p hprime hpx hT
  · rw [quadraticExcludedPrimeCost_eq_zero_of_large hx (lt_of_not_ge hpx)]
    exact mul_nonneg ha (Real.log_nonneg (Nat.one_le_cast.mpr hprime.one_le))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
