/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularSignedThresholdNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial
/-! # The unchanged triangular witness coefficient from scale two trillion -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If n>0 and A*(7/3)<log n, then 10^A<=n.
Compare logarithms using log 10<7/3, keeping exponent A symbolic.
This supplies large decimal cutoffs without evaluating their natural powers. -/
theorem decimal_le_of_log_upper {A n : ℕ} (hn : 0 < n)
    (hA : (A : ℝ) * (7 / 3) < Real.log n) : 10 ^ A ≤ n := by
  by_contra h
  have hR : (n : ℝ) ≤ (10 : ℝ) ^ A := by exact_mod_cast (lt_of_not_ge h).le
  have hl := Real.log_le_log (Nat.cast_pos.mpr hn) hR
  rw [Real.log_pow] at hl
  have hu := mul_le_mul_of_nonneg_left Analysis.log_ten_lt_seven_thirds.le
    (Nat.cast_nonneg (α := ℝ) A)
  linarith only [hA, hl, hu]

/-- A natural decimal lower bound implies A*log 10<=log n.
Keep the exponent symbolic while casting and applying logarithm monotonicity. -/
theorem decimal_log_lower {A n : ℕ} (hN : 10 ^ A ≤ n) :
    (A : ℝ) * Real.log 10 ≤ Real.log n := by
  have hp : 0 < (10 : ℝ) ^ A := pow_pos (by norm_num only) A
  have hc : (10 : ℝ) ^ A ≤ (n : ℝ) := by exact_mod_cast hN
  have h := Real.log_le_log hp hc
  simpa only [Real.log_pow] using h

/-- For log n>=2 trillion and q^2<=10^12*n, the local subgroup envelope is below
(282924/1000000)*log(n)^2. The logarithm bound log q<((L+28)/2) is below
(5319/10000)L. This controls the local numerical cutoff; rejection transfer is separate. -/
theorem triangular_threshold_local {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 12 * n) (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ (282924 / 1000000 : ℝ) * Real.log n ^ 2 := by
  have hR : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 12 * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by norm_num only))
    (Nat.cast_pos.mpr hn).ne', Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hcap : Real.log q ≤ (5319 / 10000 : ℝ) * Real.log n := by
    linarith only [hl, hL, Analysis.log_ten_lt_seven_thirds]
  have hp : (0 : ℝ) ≤ (5319 / 10000) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hp).mpr hcap
  apply max_le
  · nlinarith only [hL]
  · nlinarith only [hs, sq_nonneg (Real.log n)]

/-- Under GRH, an odd n>1 with Fermat subgroup index>=10^12 and log n>=2 trillion
has a rejecting prime at most (282924/1000000)*log(n)^2. Apply the generic
alpha-18 signed-gap consumer. Factor primes and subgroup-external primes both reject MR. -/
theorem exists_prime_triangular_largeIndex {n : ℕ} [NeZero n] (hn : 1 < n)
    (ho : Odd n) (hi : 1000000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (282924 / 1000000 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hiR : (1000000000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
    exact_mod_cast hi
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_factor_or_outside_of_triangular18_signed_gap
      (PrimeTest.fermatSubgroup n) hGRH (Analysis.triangular_threshold_scale_bounds hL).1
      (Analysis.triangular_threshold_gap hL hiR)
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop := (ZMod.isUnit_iff_coprime p n).mp
      (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH, every odd composite n>1 with log n>=2 trillion has a rejecting prime
within the unchanged coefficient-0.282924 cutoff. Classify at index 10^12;
transfer ambient passing bases to the local subgroup, reuse the uniform triple bound,
and apply the generic large-index gap. No factorization restriction remains. -/
theorem exists_prime_triangularThreshold {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (282924 / 1000000 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 12
  · have hJ : (10 ^ 12 : ℕ) ^ 3 ≤ n := by
      have h36 : 10 ^ 36 ≤ n := decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
        (by norm_num only [Nat.cast_ofNat]; linarith only [hL])
      simpa only [← pow_mul, Nat.reduceMul] using h36
    rcases finite_index_local_subgroup_or_uniform_korselt_triple hn ho hc
      (PrimeTest.fermatSubgroup n) le_rfl (by norm_num only : 1 ≤ 10 ^ 12) hJ hi with hl | ht
    · obtain ⟨q, hq, hqn, hsize, K, hK, hpass⟩ := hl
      have hqp : 0 < q := (by norm_num only : 0 < 2).trans_le hq
      let : NeZero q := ⟨hqp.ne'⟩
      obtain ⟨p, hp, hb, hr⟩ := exists_prime_witness_le_local_subgroup_envelope
        hn ho hq hqn K hK hpass hGRH
      exact ⟨p, hp, hb.trans (triangular_threshold_local (Nat.zero_lt_of_lt hn) hqp hsize hL), hr⟩
    · have hdecimal : 10 ^ 434782608696 ≤ n := decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
        (by norm_num only [Nat.cast_ofNat]; linarith only [hL])
      exact exists_prime_witness_le_0283_of_uniform_korselt_triple_card
        ho ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hGRH hdecimal
  · exact exists_prime_triangular_largeIndex hn ho
      (by exact_mod_cast (lt_of_not_ge hi).le) hGRH hL

/-- Under the logarithmic threshold assumptions, the least rejecting prime satisfies
the unchanged coefficient-0.282924 bound. Extract it from the all-input witness theorem. -/
theorem exists_least_triangularThreshold {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (282924 / 1000000 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_triangularThreshold hn ho hc hGRH hL)

/-- The sufficient decimal threshold 10^869565217392 implies log n>=2 trillion.
Use log 10>23/10 through the symbolic decimal-log lemma; never evaluate the huge power. -/
theorem triangularThreshold_decimal_log {n : ℕ} (hN : 10 ^ 869565217392 ≤ n) :
    (2000000000000 : ℝ) ≤ Real.log n := by
  have h := decimal_log_lower hN
  have hlo := mul_le_mul_of_nonneg_left Analysis.log_ten_gt_twenty_three_tenths.le
    (by norm_num only : (0 : ℝ) ≤ 869565217392)
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, hlo]

/-- Under GRH, odd composites n>=10^869565217392 have a rejecting prime below
(282924/1000000)*log(n)^2. Derive the new logarithmic threshold and apply
the all-input theorem, preserving the original coefficient. -/
theorem exists_prime_triangularDecimal {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hN : 10 ^ 869565217392 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (282924 / 1000000 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hL := triangularThreshold_decimal_log hN
  have hl := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr ho.pos)
  have hn : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith only [hl, hL])
  exact exists_prime_triangularThreshold hn ho hc hGRH hL

/-- Under the new decimal threshold, the least rejecting prime satisfies the
coefficient-0.282924 bound. Extract the least witness from the actual prime theorem. -/
theorem exists_least_triangularDecimal {n : ℕ} (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hN : 10 ^ 869565217392 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (282924 / 1000000 : ℝ) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨ho.pos.ne'⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_triangularDecimal ho hc hGRH hN)

end PseudoPrime.PrimeTestBounds.MillerRabin
