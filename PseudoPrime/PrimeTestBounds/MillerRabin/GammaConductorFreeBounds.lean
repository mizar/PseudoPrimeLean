/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeSubgroupBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaComparison

/-! # Conductor-free Gamma upper bounds for Miller-Rabin prime witnesses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- At any real scale and cutoff, if every prime divisor of q exceeds floor X,
the finite nonunit exponential sum is zero. Every retained positive noncoprime
index would have a common prime divisor below the cutoff, a contradiction.
No RH or positivity of the scale is needed. This removes finite modulus loss
under universal passage of small Miller-Rabin prime bases. -/
theorem commonFactorExponentialSum_eq_zero_of_prime_divisors_gt {q : ℕ} {X : ℝ}
    (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p) (x : ℝ) :
    commonFactorExponentialSum x X q = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hm := Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1
  obtain ⟨p, hp, hpk, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp (Finset.mem_filter.mp hk).2
  exact False.elim ((not_lt_of_ge ((Nat.le_of_dvd hm.1 hpk).trans hm.2)) (hdiv p hp hpq))

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd n>1, if every prime base through X passes the strong test,
the finite nonunit exponential sum is zero at every scale x.
A prime divisor in the cutoff would fail by nonunitness. Apply the generic
prime-divisor exclusion theorem without an analytic size condition. -/
theorem commonFactorExponentialSum_eq_zero_of_prime_passes {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    {X : ℝ}
    (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    (x : ℝ) : AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X n = 0 := by
  apply AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_eq_zero_of_prime_divisors_gt
  intro p hp hpd
  apply lt_of_not_ge
  intro hle
  have hX : (p : ℝ) ≤ X := (Nat.le_floor_iff' hp.ne_zero).mp hle
  exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp hpd (hpass p hp hX)

/-- Under GRH, every odd composite n with log n ≥ 30000 has a prime base
p ≤ (4/5)(log n)² failing the strong Miller-Rabin test.
Universal prime-base passage eliminates the finite nonunit loss; the conductor-free
subgroup budget then contradicts the certified strict Gamma main gap.
There is no numerical-gap, factorization-type or index assumption in the conclusion. -/
theorem exists_prime_witness_le_conductor_free_gamma_log_30000 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have ht := Real.log_le_sub_one_of_pos hn0
  have hn : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith only [ht, hL])
  have hnlarge : 20000 ≤ n := by exact_mod_cast (show (20000 : ℝ) ≤ n by linarith only [ht, hL])
  by_contra hnone
  have hpass :
    ∀ p : ℕ,
      p.Prime →
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 →
        PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hb
    by_contra hf
    exact hnone ⟨p, hp, hb, hf⟩
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ n →
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 → LLS.PaperStatements.residueInSubgroup n H p := by
    intro p hp _ hb
    exact hHpass (p : ZMod n) (hpass p hp hb)
  have hc :=
    LLS.PaperStatements.gamma_ramp_subgroup_comparison_conductor_free hnlarge H hH hGRH hL hsmall
  let x := (32 / 99 : ℝ) * (Real.log n) ^ 2
  have hcut : (99 / 40 : ℝ) * x = (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
    dsimp only [x]
    ring
  have hz := commonFactorExponentialSum_eq_zero_of_prime_passes hn hnOdd hpass x
  dsimp only at hc
  change
    _ ≤
      (11783423 / 25000000 : ℝ) * Real.log n + 899 / 25 +
        2 *
          (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x ((99 / 40 : ℝ) * x) n /
            Real.sqrt x) at hc
  rw [hcut, hz, zero_div, mul_zero, add_zero] at hc
  have hm := Analysis.nonOne_main_term_gap (show 0 < Real.log n by linarith only [hL])
  linarith only [hc, hm, hL]

/-- Under the same odd-composite, GRH and logarithmic entrance conditions,
the least prime strong-test rejecting base exists and is at most (4/5)(log n)².
Minimize the unbounded prime-rejection predicate rather than the cutoff.
Minimality compares every prime rejecting base, preserving the pointwise bound. -/
theorem exists_least_prime_witness_le_conductor_free_gamma_log_30000 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_le_conductor_free_gamma_log_30000 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under GRH for odd composite n with log n ≥ 30000, the canonical
two-adic decomposition n-1=2^s d has a prime base p ≤ (4/5)(log n)²
with p^d ≠ 1 and p^(2^j d) ≠ -1 for every j<s.
Unfold the rejection equivalence after the prime-witness theorem.
This is the explicit congruence form of the improved Miller-Rabin bound. -/
theorem exists_prime_rejecting_powers_le_conductor_free_gamma_log_30000 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_le_conductor_free_gamma_log_30000 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
