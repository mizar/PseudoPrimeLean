/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialMangoldtBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorSplitBounds

/-! # Prime-local count bounds for the nonunit exponential loss

Each prime contributes at most log X through its positive powers. Combining this
with a split of the prime support gives the local modulus budget needed for
uniform proper-subgroup bounds.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a prime p and X ≥ 1, its positive powers through floor X contribute at
most log X. Their Mangoldt values are log p; the maximal power is at most X.
This supplies the prime-local bound for the finite nonunit loss. -/
theorem prime_power_vonMangoldt_sum_le_log_cutoff {p : ℕ} (hp : p.Prime) {X : ℝ} (hX : 1 ≤ X) :
    ∑ k ∈ Finset.Icc 1 (p.log ⌊X⌋₊), ArithmeticFunction.vonMangoldt (p ^ k) ≤ Real.log X := by
  have hpow := Nat.pow_log_le_self p (Nat.floor_pos.mpr hX).ne'
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hr : (p : ℝ) ^ p.log ⌊X⌋₊ ≤ X := by
    exact
      (by exact_mod_cast hpow : (p : ℝ) ^ p.log ⌊X⌋₊ ≤ (⌊X⌋₊ : ℝ)).trans
        (Nat.floor_le (zero_le_one.trans hX))
  have hl := Real.log_le_log (pow_pos hp0 _) hr
  rw [Real.log_pow] at hl
  have he :
    ∑ k ∈ Finset.Icc 1 (p.log ⌊X⌋₊), ArithmeticFunction.vonMangoldt (p ^ k) =
      (p.log ⌊X⌋₊ : ℝ) * Real.log p := by
    calc
      _ = ∑ _k ∈ Finset.Icc 1 (p.log ⌊X⌋₊), Real.log p := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      _ = _ := by rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [he]
  exact hl

/-- For q ≠ 0 and X ≥ 1, the nonunit Mangoldt sum through X is at most
q.primeFactors.card * log X. Reindex by prime and positive exponent, then use
the prime-local bound. No parity, squarefreeness or small-factor condition is needed. -/
theorem sum_vonMangoldt_not_coprime_le_card_mul_log {q : ℕ} (hq : q ≠ 0) {X : ℝ} (hX : 1 ≤ X) :
    (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n ↦ ¬Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n) ≤
      (q.primeFactors.card : ℝ) * Real.log X := by
  classical
  let f : ℕ → ℝ := fun n ↦ if ¬Nat.Coprime n q then ArithmeticFunction.vonMangoldt n else 0
  have he :
    (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n ↦ ¬Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n) =
      ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p ↦ p ∣ q),
        ∑ k ∈ Finset.Icc 1 (p.log ⌊X⌋₊), ArithmeticFunction.vonMangoldt (p ^ k) := by
    rw [Finset.sum_filter]
    have hs : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n) = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊ with IsPrimePow n, f n := by
      have hi : Finset.Ioc 0 ⌊X⌋₊ = Finset.Icc 1 ⌊X⌋₊ := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.succ_le_iff]
      rw [hi, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : IsPrimePow n
      · rw [ite_eq_left hn]
      · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
        simp only [f, hz, ite_self]
    change (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n) = _
    rw [hs, sum_primePow_eq_sum_primesLE, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    by_cases hd : p ∣ q
    · rw [ite_eq_left hd]
      apply Finset.sum_congr rfl
      intro k hk
      have hc : ¬Nat.Coprime (p ^ k) q := by
        rw [Nat.coprime_pow_left_iff (Finset.mem_Icc.mp hk).1, hpp.coprime_iff_not_dvd]
        exact not_not_intro hd
      exact ite_eq_left hc
    · rw [ite_eq_right hd]
      apply Finset.sum_eq_zero
      intro k hk
      have hc := (hpp.coprime_iff_not_dvd.mpr hd).pow_left k
      exact ite_eq_right (not_not_intro hc)
  have hb :
    (∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p ↦ p ∣ q),
        ∑ k ∈ Finset.Icc 1 (p.log ⌊X⌋₊), ArithmeticFunction.vonMangoldt (p ^ k)) ≤
      ∑ _p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p ↦ p ∣ q), Real.log X :=
    Finset.sum_le_sum
      (fun p hp ↦
        prime_power_vonMangoldt_sum_le_log_cutoff
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1) hX)
  rw [he]
  apply hb.trans
  rw [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hX)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  exact
    Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2, hq⟩

/-- For x > 0, q ≠ 0 and X ≥ 1, the nonunit exponential sum is at most
q.primeFactors.card * log X. Its weights are at most one, so the unweighted
prime-local bound applies. Divide by sqrt x for the principal-character correction. -/
theorem commonFactorExponentialSum_le_card_mul_log {q : ℕ} (hq : q ≠ 0) {x X : ℝ} (hx : 0 < x)
    (hX : 1 ≤ X) : commonFactorExponentialSum x X q ≤ (q.primeFactors.card : ℝ) * Real.log X := by
  classical
  have he :
    commonFactorExponentialSum x X q ≤
      ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n ↦ ¬Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n := by
    unfold commonFactorExponentialSum
    apply Finset.sum_le_sum
    intro n _
    have hExp : Real.exp (-(n : ℝ) / x) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hx.le)
    exact
      (mul_le_mul_of_nonneg_right hExp ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
  exact he.trans (sum_vonMangoldt_not_coprime_le_card_mul_log hq hX)

/-- For positive x, q ≠ 0, X ≥ 1 and y > 1, the nonunit exponential loss is
at most (y + log q / log y) log X. Combine the local count bound with the support split.
This is the parameterized modulus-loss input for the uniform Gamma comparison. -/
theorem commonFactorExponentialSum_le_split_mul_log {q : ℕ} (hq : q ≠ 0) {x X y : ℝ} (hx : 0 < x)
    (hX : 1 ≤ X) (hy : 1 < y) :
    commonFactorExponentialSum x X q ≤ (y + Real.log q / Real.log y) * Real.log X :=
  (commonFactorExponentialSum_le_card_mul_log hq hx hX).trans
    (mul_le_mul_of_nonneg_right (primeFactors_card_le_cutoff_add_log_div hq hy)
      (Real.log_nonneg hX))

/-- For positive x, q ≠ 0, X ≥ 1 and log q > 1, splitting at (log q)^(2/3)
bounds the nonunit exponential loss by ((log q)^(2/3) + (3/2) log q / log log q) log X.
This is the local-loss contract in the uniform coefficient 4/5 plan. -/
theorem commonFactorExponentialSum_le_log_two_thirds {q : ℕ} (hq : q ≠ 0) {x X : ℝ} (hx : 0 < x)
    (hX : 1 ≤ X) (hL : 1 < Real.log q) :
    commonFactorExponentialSum x X q ≤
      ((Real.log q) ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * Real.log q / Real.log (Real.log q)) *
        Real.log X :=
  (commonFactorExponentialSum_le_card_mul_log hq hx hX).trans
    (mul_le_mul_of_nonneg_right (primeFactors_card_le_log_two_thirds hq hL) (Real.log_nonneg hX))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
