/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PairedEulerExcludedBounds
public import PseudoPrime.LLS.QuadraticExcludedPrimeBudget
public import PseudoPrime.LLS.GammaQuadraticLocalCorrection
public import PseudoPrime.Analysis.AlternatingPrefixBounds

/-! # Alternating prime-power cancellation and conductor-sensitive exclusion budgets -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a prime p and positive exponent k, express the paired Euler weight as a sum of two
geometric weights, one multiplied by k. Expand the Mangoldt value and real powers. This identity
supplies the monotonicity required for cancellation of consecutive prime powers. -/
theorem pairedEulerPrefixWeight_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) (p ^ k) =
      Real.log p / ((p : ℝ) ^ (5 / 4 : ℝ)) ^ k +
        ((3 / 4 : ℝ) * (Real.log p) ^ 2) * k / ((p : ℝ) ^ (11 / 4 : ℝ)) ^ k := by
  have he (t : ℝ) : ((p : ℝ) ^ k) ^ t = ((p : ℝ) ^ t) ^ k := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p) k t, mul_comm (k : ℝ) t,
      Real.rpow_mul_natCast (Nat.cast_nonneg p) t k]
  dsimp only [pairedEulerPrefixWeight]
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow, he (5 / 4),
    he (11 / 4)]
  ring

/-- For each prime p, the paired Euler weight decreases on positive powers of p. Apply the
geometric-weight decrease with bases p^(5/4) and p^(11/4). This permits alternating cancellation
without replacing every unramified power by twice its full weight. -/
theorem pairedEulerPrefixWeight_prime_pow_antitone {p : ℕ} (hp : p.Prime) :
    Antitone (fun j : ℕ ↦ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) (p ^ (j + 1))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hb : 1 ≤ (p : ℝ) ^ (5 / 4 : ℝ) :=
    (Real.one_lt_rpow hp1 (by norm_num only : (0 : ℝ) < 5 / 4)).le
  have ht := Real.rpow_le_rpow_of_exponent_le hp1.le (show (1 : ℝ) ≤ 11 / 4 by norm_num only)
  rw [Real.rpow_one] at ht
  have hd : 2 ≤ (p : ℝ) ^ (11 / 4 : ℝ) := (Nat.cast_le.mpr hp.two_le).trans ht
  have ha :=
    PseudoPrime.Analysis.geometric_log_weight_antitone (Real.log_natCast_nonneg p)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) (sq_nonneg (Real.log p))) hb hd
  intro i j hij
  dsimp only
  rw [pairedEulerPrefixWeight_prime_pow hp (Nat.succ_pos j),
    pairedEulerPrefixWeight_prime_pow hp (Nat.succ_pos i)]
  exact ha hij

/-- For Y at least one, a nonnegative weight decreasing on positive powers remains decreasing
after the cutoff p^k at most Y. Monotonicity of the real root cutoff proves the assertion. This
allows finite prime-power cancellation even when the last exponent has either parity. -/
theorem cutoff_prime_power_weight_antitone {p : ℕ} {Y : ℝ} (hY : 1 ≤ Y) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (ha : Antitone (fun j : ℕ ↦ w (p ^ (j + 1)))) :
    Antitone (fun j : ℕ ↦ if p ≤ ⌊Y ^ ((1 : ℝ) / (j + 1 : ℕ))⌋₊ then w (p ^ (j + 1)) else 0) := by
  apply antitone_nat_of_succ_le
  intro j
  have hd :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr (Nat.succ_pos j) : (0 : ℝ) < (j + 1 : ℕ))
      (Nat.cast_le.mpr (Nat.le_succ (j + 1)) : ((j + 1 : ℕ) : ℝ) ≤ (j + 1 + 1 : ℕ))
  have hf := Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hY hd)
  by_cases hn : p ≤ ⌊Y ^ ((1 : ℝ) / (j + 1 + 1 : ℕ))⌋₊
  · have ho := hn.trans hf
    rw [ite_eq_left hn, ite_eq_left ho]
    exact ha (Nat.le_succ j)
  · rw [ite_eq_right hn]
    split_ifs with ho
    · exact hw _
    · exact le_refl _

/-- For a prime p, Y at least one, and a nonnegative weight decreasing on positive powers,
the quadratic exclusion cost is bounded by the principal power prefix plus the first weight
when p is unramified. Pair odd and even powers; ramified primes have coefficient one. This is
the local estimate used before summing over level primes. -/
theorem quadraticExcludedPrimeCost_le_principal_add_first {q p : ℕ} (hp : p.Prime) {Y : ℝ}
    (hY : 1 ≤ Y) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (ha : Antitone (fun j : ℕ ↦ w (p ^ (j + 1)))) :
    quadraticExcludedPrimeCost q Y w p ≤
      (∑ k ∈ Finset.Icc 1 ⌊Real.log Y / Real.log 2⌋₊,
          if p ≤ ⌊Y ^ ((1 : ℝ) / k)⌋₊ then w (p ^ k) else 0) +
        if Nat.Coprime p q then w p else 0 := by
  classical
  by_cases hc : Nat.Coprime p q
  · rw [quadraticExcludedPrimeCost_of_coprime hp hc, ite_eq_left hc]
    let a (k : ℕ) := if p ≤ ⌊Y ^ ((1 : ℝ) / k)⌋₊ then w (p ^ k) else 0
    have had := cutoff_prime_power_weight_antitone hY w hw ha
    have ha0 (j : ℕ) : 0 ≤ a (j + 1) := by
      dsimp only [a]
      split_ifs
      · exact hw _
      · exact le_refl _
    have hb :=
      PseudoPrime.Analysis.odd_weighted_prefix_le_total_add_first had ha0 ⌊Real.log Y / Real.log 2⌋₊
    have hf : a 1 ≤ w p := by
      dsimp only [a]
      rw [Nat.pow_one]
      split_ifs
      · exact le_refl _
      · exact hw p
    have he :
      (2 *
          ∑ k ∈ Finset.Icc 1 ⌊Real.log Y / Real.log 2⌋₊,
            if p ≤ ⌊Y ^ ((1 : ℝ) / k)⌋₊ ∧ ¬Even k then w (p ^ k) else 0) =
        ∑ k ∈ Finset.Icc 1 ⌊Real.log Y / Real.log 2⌋₊, (if Even k then (0 : ℝ) else 2) * a k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hcut : p ≤ ⌊Y ^ ((1 : ℝ) / k)⌋₊
      · by_cases hk : Even k
        · simp only [a, hcut, hk, not_true_eq_false, true_and, ite_false, ite_true, mul_zero,
            zero_mul]
        · simp only [a, hcut, hk, not_false_eq_true, true_and, ite_false, ite_true]
      · simp only [a, hcut, false_and, ite_false, mul_zero]
    rw [he]
    exact hb.trans (add_le_add (le_refl _) hf)
  · rw [quadraticExcludedPrimeCost_of_not_coprime hc, ite_eq_right hc, add_zero]

/-- For a nonnegative weight on a finite support, the exclusion budget with conductor zero is
at most the full prefix. Every excluded index differs from one, so its coefficient is one.
This auxiliary principal budget permits reuse of the prime-factor decomposition. -/
theorem quadraticExcludedBudget_zero_le_prefix (N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) : quadraticExcludedBudget 0 N S w ≤ ∑ n ∈ S, w n := by
  classical
  have he : quadraticExcludedBudget 0 N S w = ∑ n ∈ S.filter (fun n ↦ ¬Nat.Coprime n N), w n := by
    dsimp only [quadraticExcludedBudget]
    apply Finset.sum_congr rfl
    intro n hn
    have hc : ¬Nat.Coprime n 0 := by
      intro h
      have he := (Nat.coprime_zero_right n).mp h
      subst n
      exact (Finset.mem_filter.mp hn).2 (Nat.coprime_one_left N)
    rw [ite_eq_right hc, one_mul]
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro n _ _
  exact hw n

/-- For a nonzero level N, Y at least one, and a nonnegative prime-power-supported weight
decreasing on positive powers, the quadratic exclusion budget is at most the full prefix plus
the first weight at each unramified level prime. Sum the alternating local estimate and compare
the conductor-zero budget with the full prefix. This bound retains square-power cancellation. -/
theorem quadraticExcludedBudget_le_prefix_add_unramified {N : ℕ} (hN : N ≠ 0) (q : ℕ) {Y : ℝ}
    (hY : 1 ≤ Y) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hs : ∀ n : ℕ, ¬IsPrimePow n → w n = 0)
    (ha : ∀ p : ℕ, p.Prime → Antitone (fun j : ℕ ↦ w (p ^ (j + 1)))) :
    quadraticExcludedBudget q N (Finset.Ioc 0 ⌊Y⌋₊) w ≤
      (∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, w n) +
        ∑ p ∈ N.primeFactors, if Nat.Coprime p q then w p else 0 := by
  classical
  have hb :
    ∀ p ∈ N.primeFactors,
      quadraticExcludedPrimeCost q Y w p ≤
        quadraticExcludedPrimeCost 0 Y w p + if Nat.Coprime p q then w p else 0 := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hc0 : ¬Nat.Coprime p 0 := fun hc ↦ hprime.ne_one ((Nat.coprime_zero_right p).mp hc)
    rw [quadraticExcludedPrimeCost_of_not_coprime hc0]
    exact quadraticExcludedPrimeCost_le_principal_add_first hprime hY w hw (ha p hprime)
  have hsum := Finset.sum_le_sum hb
  rw [Finset.sum_add_distrib, ←
    quadraticExcludedBudget_eq_sum_primeFactors hN q (zero_le_one.trans hY) w hs, ←
    quadraticExcludedBudget_eq_sum_primeFactors hN 0 (zero_le_one.trans hY) w hs] at hsum
  exact hsum.trans (add_le_add (quadraticExcludedBudget_zero_le_prefix N _ w hw) (le_refl _))

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.LLS

/-- A level prime coprime to the conductor divides the conductor quotient. Factor the level
as conductor times quotient and use primality. This locates every unramified exclusion charge
inside the conductor logarithmic saving. -/
theorem coprime_level_prime_mem_quotientFactors {q p : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : p ∈ q.primeFactors) (hc : Nat.Coprime p χ.conductor) :
    p ∈ (q / χ.conductor).primeFactors := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := (Nat.mem_primeFactors.mp hp).2.1
  rw [← AnalyticNumberTheory.DirichletLFunction.conductor_mul_quotient χ] at hd
  have hquot := (hprime.dvd_mul.mp hd).resolve_left (hprime.coprime_iff_not_dvd.mp hc)
  exact
    Nat.mem_primeFactors.mpr
      ⟨hprime, hquot, (AnalyticNumberTheory.DirichletLFunction.quotient_pos χ).ne'⟩

/-- For a character of nonzero level, the sum of logarithms of level primes coprime to the
conductor is at most the logarithm of the conductor quotient. Include these primes among the
quotient factors and apply the radical logarithm bound. No witness hypothesis is required. -/
theorem sum_log_unramified_level_primes_le_log_quotient {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ p ∈ q.primeFactors.filter (fun p ↦ Nat.Coprime p χ.conductor), Real.log p) ≤
      Real.log (q / χ.conductor : ℕ) := by
  have hsub :
    q.primeFactors.filter (fun p ↦ Nat.Coprime p χ.conductor) ⊆ (q / χ.conductor).primeFactors := by
    intro p hp
    exact
      coprime_level_prime_mem_quotientFactors χ (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hp).2
  exact
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p hp _ ↦
            Real.log_nonneg (Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors hp).one_le))).trans
      (AnalyticNumberTheory.Arithmetic.sum_log_primeFactors_le_log
        (AnalyticNumberTheory.DirichletLFunction.quotient_pos χ).ne')

/-- For nonnegative a and d, suppose each prime weight is at most a log p with the additional
allowance d only at two. Then the sum over unramified level primes is at most a times the
conductor-quotient logarithm plus d. Sum the scalar estimates and charge two at most once. This
separates a reusable conductor cost from a fixed exceptional-prime allowance. -/
theorem unramified_weight_sum_le_conductor_budget {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (w : ℕ → ℝ) {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hw : ∀ p : ℕ, p.Prime → w p ≤ a * Real.log p + if p = 2 then d else 0) :
    (∑ p ∈ q.primeFactors, if Nat.Coprime p χ.conductor then w p else 0) ≤
      a * Real.log (q / χ.conductor : ℕ) + d := by
  classical
  rw [← Finset.sum_filter]
  let F := q.primeFactors.filter (fun p ↦ Nat.Coprime p χ.conductor)
  have hs : (∑ p ∈ F, w p) ≤ ∑ p ∈ F, (a * Real.log p + if p = 2 then d else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    exact hw p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq'] at hs
  have he : (if 2 ∈ F then d else 0) ≤ d := by
    split_ifs
    · exact le_refl _
    · exact hd
  have hl := mul_le_mul_of_nonneg_left (sum_log_unramified_level_primes_le_log_quotient χ) ha
  exact hs.trans (add_le_add hl he)

/-- For a nonzero character level and Y at least one, assume a nonnegative prime-power weight
decreasing on positive powers and bounded at primes by a log p plus a nonnegative allowance d
at two. The quadratic exclusion budget is at most the full prefix plus a log of the conductor
quotient and d. Combine alternating cancellation with the quotient prime-factor bound. This
is the conductor-sensitive interface for negative-witness comparisons. -/
theorem quadraticExcludedBudget_le_prefix_add_conductor_budget {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 1 ≤ Y) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hs : ∀ n : ℕ, ¬IsPrimePow n → w n = 0)
    (hdec : ∀ p : ℕ, p.Prime → Antitone (fun j : ℕ ↦ w (p ^ (j + 1)))) {a d : ℝ} (ha : 0 ≤ a)
    (hd : 0 ≤ d) (hprime : ∀ p : ℕ, p.Prime → w p ≤ a * Real.log p + if p = 2 then d else 0) :
    AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget χ.conductor q (Finset.Ioc 0 ⌊Y⌋₊) w ≤
      (∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊, w n) + a * Real.log (q / χ.conductor : ℕ) + d := by
  have hbase :=
    AnalyticNumberTheory.Arithmetic.quadraticExcludedBudget_le_prefix_add_unramified (NeZero.ne q)
      χ.conductor hY w hw hs hdec
  have hquot := unramified_weight_sum_le_conductor_budget χ w ha hd hprime
  linarith only [hbase, hquot]

end PseudoPrime.LLS
