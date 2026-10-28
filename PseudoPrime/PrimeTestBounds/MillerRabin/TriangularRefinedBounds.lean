/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularRefinedNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularThresholdBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeTripleBounds

/-! # Refined triangular witnesses from logarithmic scale 1.1 trillion -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For log n>=1.1 trillion and q^2<=10^12*n, the local subgroup envelope is below
(71/250)*log(n)^2. The logarithm bound log q<((L+28)/2) is below
(5329/10000)L. This controls the local numerical cutoff; rejection transfer is separate. -/
theorem triangularEarlier_local {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 12 * n)
    (hL : (1100000000000 : ℝ) ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ (71 / 250 : ℝ) * Real.log n ^ 2 := by
  have hR : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 12 * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by norm_num only)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hcap : Real.log q ≤ (5329 / 10000 : ℝ) * Real.log n := by
    linarith only [hl, hL, Analysis.log_ten_lt_seven_thirds]
  have hp : (0 : ℝ) ≤ (5329 / 10000) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hp).mpr hcap
  apply max_le
  · nlinarith only [hL]
  · nlinarith only [hs, sq_nonneg (Real.log n)]

/-- Under GRH, an odd n>1 with Fermat subgroup index>=10^12 and log n>=1.1 trillion
has a rejecting prime at most (71/250)*log(n)^2. Apply the generic
alpha-18 signed-gap consumer. Factor primes and subgroup-external primes both reject MR. -/
theorem exists_prime_triangularEarlierIndex {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hi : 1000000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1100000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (71 / 250 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hiR : (1000000000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by exact_mod_cast hi
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_factor_or_outside_of_triangular18_signed_gap
      (PrimeTest.fermatSubgroup n) hGRH (Analysis.triangularEarlier_scale_bounds hL).1
      (Analysis.triangularEarlier_gap hL hiR)
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop :=
      (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH, every odd composite n>1 with log n>=1.1 trillion has a rejecting prime
within the coefficient-0.284 cutoff. Classify at index 10^12;
transfer ambient passing bases to the local subgroup, reuse the uniform triple bound,
and apply the generic large-index gap. No factorization restriction remains. -/
theorem exists_prime_triangularEarlier {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1100000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (71 / 250 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 12
  · have hJ : (10 ^ 12 : ℕ) ^ 3 ≤ n := by
      have h36 : 10 ^ 36 ≤ n :=
        decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
          (by
            norm_num only [Nat.cast_ofNat]; linarith only [hL])
      simpa only [← pow_mul, Nat.reduceMul] using h36
    rcases
      finite_index_local_subgroup_or_uniform_korselt_triple hn ho hc (PrimeTest.fermatSubgroup n)
        le_rfl (by norm_num only : 1 ≤ 10 ^ 12) hJ hi with
      hl | ht
    · obtain ⟨q, hq, hqn, hsize, K, hK, hpass⟩ := hl
      have hqp : 0 < q := (by norm_num only : 0 < 2).trans_le hq
      let : NeZero q := ⟨hqp.ne'⟩
      obtain ⟨p, hp, hb, hr⟩ :=
        exists_prime_witness_le_local_subgroup_envelope hn ho hq hqn K hK hpass hGRH
      exact ⟨p, hp, hb.trans (triangularEarlier_local (Nat.zero_lt_of_lt hn) hqp hsize hL), hr⟩
    · have hdecimal : 10 ^ 434782608696 ≤ n :=
        decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
          (by
            norm_num only [Nat.cast_ofNat]; linarith only [hL])
      obtain ⟨p, hp, hb, hr⟩ :=
        exists_prime_witness_le_0283_of_uniform_korselt_triple_card ho ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
          hGRH hdecimal
      refine ⟨p, hp, hb.trans ?_, hr⟩
      nlinarith only [sq_nonneg (Real.log n)]
  · exact exists_prime_triangularEarlierIndex hn ho (by exact_mod_cast (lt_of_not_ge hi).le) hGRH hL

/-- Under the logarithmic threshold assumptions, the least rejecting prime satisfies
the coefficient-0.284 bound. Extract it from the all-input witness theorem. -/
theorem exists_least_triangularEarlier {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1100000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (71 / 250 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_triangularEarlier hn ho hc hGRH hL)

/-- For log n>=2 trillion and q^2<=10^12*n, the local subgroup envelope is below
(28237/100000)*log(n)^2. The logarithm bound log q<((L+28)/2) is below
(5313/10000)L. This controls the local numerical cutoff; rejection transfer is separate. -/
theorem triangularRefined_local {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 12 * n)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ (28237 / 100000 : ℝ) * Real.log n ^ 2 := by
  have hR : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 12 * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by norm_num only)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hcap : Real.log q ≤ (5313 / 10000 : ℝ) * Real.log n := by
    linarith only [hl, hL, Analysis.log_ten_lt_seven_thirds]
  have hp : (0 : ℝ) ≤ (5313 / 10000) * Real.log n := by linarith only [hL]
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hp).mpr hcap
  apply max_le
  · nlinarith only [hL]
  · nlinarith only [hs, sq_nonneg (Real.log n)]

/-- Under GRH, an odd n>1 with Fermat subgroup index>=10^12 and log n>=2 trillion
has a rejecting prime at most (28237/100000)*log(n)^2. Apply the generic
alpha-18 signed-gap consumer. Factor primes and subgroup-external primes both reject MR. -/
theorem exists_prime_triangularRefinedIndex {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hi : 1000000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (28237 / 100000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hiR : (1000000000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by exact_mod_cast hi
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_factor_or_outside_of_triangular18_signed_gap
      (PrimeTest.fermatSubgroup n) hGRH (Analysis.triangularRefined_scale_bounds hL).1
      (Analysis.triangularRefined_gap hL hiR)
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop :=
      (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH, every odd composite n>1 with log n>=2 trillion has a rejecting prime
within the coefficient-0.28237 cutoff. Classify at index 10^12;
transfer ambient passing bases to the local subgroup, use the new triple bound,
and apply the generic large-index gap. No factorization restriction remains. -/
theorem exists_prime_triangularRefined {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (28237 / 100000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 12
  · have hJ : (10 ^ 12 : ℕ) ^ 3 ≤ n := by
      have h36 : 10 ^ 36 ≤ n :=
        decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
          (by
            norm_num only [Nat.cast_ofNat]; linarith only [hL])
      simpa only [← pow_mul, Nat.reduceMul] using h36
    rcases
      finite_index_local_subgroup_or_uniform_korselt_triple hn ho hc (PrimeTest.fermatSubgroup n)
        le_rfl (by norm_num only : 1 ≤ 10 ^ 12) hJ hi with
      hl | ht
    · obtain ⟨q, hq, hqn, hsize, K, hK, hpass⟩ := hl
      have hqp : 0 < q := (by norm_num only : 0 < 2).trans_le hq
      let : NeZero q := ⟨hqp.ne'⟩
      obtain ⟨p, hp, hb, hr⟩ :=
        exists_prime_witness_le_local_subgroup_envelope hn ho hq hqn K hK hpass hGRH
      exact ⟨p, hp, hb.trans (triangularRefined_local (Nat.zero_lt_of_lt hn) hqp hsize hL), hr⟩
    · have hnlarge : 20000 ≤ n := by
        have hl := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr ho.pos)
        exact_mod_cast (show (20000 : ℝ) ≤ n by linarith only [hl, hL])
      exact gaussianRefined_witness_card ho ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hnlarge hGRH hL
  · exact exists_prime_triangularRefinedIndex hn ho (by exact_mod_cast (lt_of_not_ge hi).le) hGRH hL

/-- Under the logarithmic threshold assumptions, the least rejecting prime satisfies
the coefficient-0.28237 bound. Extract it from the all-input witness theorem. -/
theorem exists_least_triangularRefined {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (28237 / 100000 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_triangularRefined hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
