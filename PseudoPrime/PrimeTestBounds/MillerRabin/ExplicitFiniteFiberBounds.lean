/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberFermatBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FermatQuotientAsymptoticTransfer
public import PseudoPrime.Analysis.RationalPowerThreshold

/-! # An explicit subquadratic logarithmic MR bound for nonsquarefree inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The input threshold N(u)=2^P(u), where P(u)=2^(2^u).
Keeping u symbolic avoids evaluation of the closed tower.
The final witness bound specializes u to 1388714689827. -/
noncomputable def explicitFiniteFiberInputThreshold (u : ℕ) : ℕ :=
  2 ^ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u

/-- For u≥2 the local prime threshold P(u) exceeds eight.
Compare binary exponents with u symbolic. This supplies the real-power
absorption bound in the transfer to N(u). -/
theorem eight_le_explicit_fiber_prime_threshold {u : ℕ} (hu : 2 ≤ u) :
    8 ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u := by
  change 8 ≤ 2 ^ (2 ^ u)
  exact
    (by decide : 8 ≤ 2 ^ (2 ^ 2)).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.pow_le_pow_right (by decide : 0 < 2) hu))

/-- For u≥2 and n≥N(u), the local prime threshold is at most log(n)^A
whenever 2A≥3. Expand the logarithm of N(u), retain log 2≥1/2,
and absorb the factor two by the rational real-power comparison. -/
theorem explicit_fiber_prime_threshold_le_log_power {n u : ℕ} {A : ℝ} (hu : 2 ≤ u) (hA : 3 ≤ 2 * A)
    (hn : explicitFiniteFiberInputThreshold u ≤ n) :
    (NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u : ℝ) ≤ (Real.log n) ^ A := by
  have hP8 : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u :=
    Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold hu)
  have hP0 := Nat.zero_lt_of_lt (NumberTheory.Heilbronn.one_lt_explicit_finite_fiber_threshold u)
  have hmono :=
    Real.log_le_log
      (Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0 < 2)) :
        (0 : ℝ) < explicitFiniteFiberInputThreshold u)
      (Nat.cast_le.mpr hn)
  rw [explicitFiniteFiberInputThreshold, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hmono
  have hmul :=
    mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith only [Real.log_two_gt_d9])
      (Nat.cast_nonneg (NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u) : (0 : ℝ) ≤ _)
  have hhalf :
    (NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u : ℝ) / 2 ≤ Real.log n := by
    linarith only [hmono, hmul]
  exact
    (Analysis.self_le_rpow_half_of_eight_le hP8 hA).trans
      (Real.rpow_le_rpow (by linarith only [hP8]) hhalf (by linarith only [hA]))

/-- Every odd nonsquarefree n>1 above N(1388714689827) has a prime MR witness
at most log(n)^(1838239/1000000). Apply the proved explicit Fermat-quotient theorem
at large square prime divisors; a smaller square prime divisor is itself
a bounded rejecting base. GRH and unspecified analytic thresholds are absent. -/
theorem exists_prime_witness_of_explicit_finite_fiber_threshold {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold (1388714689827) ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1838239 / 1000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold (1388714689827)) hn ho hns
      (1838239 / 1000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1838239 / 1000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_explicit_fiber_threshold
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above N(1388714689827), the least prime MR witness of every odd nonsquarefree
n>1 is at most log(n)^(1838239/1000000), strictly below log(n)^2. Minimize the proved
rejecting-prime predicate and compare the real exponents at log(n)>1.
This is an unconditional least-witness bound with a specified starting value. -/
theorem exists_least_prime_witness_of_explicit_finite_fiber_threshold {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold (1388714689827) ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1838239 / 1000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ := exists_prime_witness_of_explicit_finite_fiber_threshold hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (1388714689827 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (1838239 / 1000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 1388714689827 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1838239 / 1000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1838239 / 1000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (1838239 / 1000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- For every odd nonsquarefree n>1 above N(283000007562), a prime MR witness
is at most log(n)^(1850004/1000000). Apply the 74/40 finite-fiber Fermat bound
at large square prime divisors and use a smaller square prime divisor directly. -/
theorem exists_prime_witness_of_explicit_finite_fiber_threshold_74_40 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 283000007562 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1850004 / 1000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 283000007562) hn ho hns
      (1850004 / 1000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1850004 / 1000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_explicit_fiber_threshold_74_40
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above N(283000007562), the least prime MR witness of every odd
nonsquarefree n>1 is at most log(n)^(1850004/1000000), strictly below log(n)^2.
Minimize the rejecting-prime predicate and compare the exponents at log(n)>1. -/
theorem exists_least_prime_witness_of_explicit_finite_fiber_threshold_74_40 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 283000007562 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1850004 / 1000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_explicit_finite_fiber_threshold_74_40 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (283000007562 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (1850004 / 1000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 283000007562 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1850004 / 1000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1850004 / 1000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (1850004 / 1000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- For every odd nonsquarefree n>1 above N(242591045876), a prime MR witness
is at most log(n)^(184211/100000). Apply the 70/38 finite-fiber Fermat bound
at large square prime divisors and use a smaller square prime divisor directly. -/
theorem exists_prime_witness_of_explicit_finite_fiber_threshold_38_70 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 242591045876 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (184211 / 100000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 242591045876) hn ho hns
      (184211 / 100000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (184211 / 100000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_explicit_fiber_threshold_38_70
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above N(242591045876), the least prime MR witness of every odd
nonsquarefree n>1 is at most log(n)^(184211/100000), strictly below log(n)^2.
Minimize the rejecting-prime predicate and compare the exponents at log(n)>1. -/
theorem exists_least_prime_witness_of_explicit_finite_fiber_threshold_38_70 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 242591045876 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (184211 / 100000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_explicit_finite_fiber_threshold_38_70 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (242591045876 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (184211 / 100000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 242591045876 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 184211 / 100000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (184211 / 100000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (184211 / 100000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Every odd nonsquarefree n>1 above N(145000006050) has a prime MR
witness at most log(n)^(1843755/1000000). Apply the 59/32 Fermat-quotient
bound at large square prime divisors and use a smaller square divisor directly. -/
theorem exists_prime_witness_of_explicit_finite_fiber_threshold_32_59 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 145000006050 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1843755 / 1000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 145000006050) hn ho hns
      (1843755 / 1000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1843755 / 1000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_explicit_fiber_threshold_32_59
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above N(145000006050), the least prime MR witness of every odd
nonsquarefree n>1 is at most log(n)^(1843755/1000000), strictly below log(n)^2.
Minimize the rejecting-prime predicate and compare exponents at log(n)>1. -/
theorem exists_least_prime_witness_of_explicit_finite_fiber_threshold_32_59 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 145000006050 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1843755 / 1000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_explicit_finite_fiber_threshold_32_59 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (145000006050 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (1843755 / 1000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 145000006050 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1843755 / 1000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1843755 / 1000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (1843755 / 1000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Every odd nonsquarefree n>1 above N(4449271510) has a prime MR witness
at most log(n)^1.90000001698. Apply the 19/10 Fermat-quotient bound at large
square prime divisors and use a smaller square divisor directly. -/
theorem exists_prime_witness_of_explicit_finite_fiber_threshold_10_19 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 4449271510 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1900000016707 / 1000000000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 4449271510) hn ho hns
      (1900000016707 / 1000000000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1900000016707 / 1000000000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_explicit_fiber_threshold_10_19
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above N(4449271510), the least prime MR witness of every odd
nonsquarefree n>1 is at most log(n)^1.900000016707, strictly below log(n)^2.
Minimize the rejecting-prime predicate and compare exponents at log(n)>1. -/
theorem exists_least_prime_witness_of_explicit_finite_fiber_threshold_10_19 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 4449271510 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1900000016707 / 1000000000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_explicit_finite_fiber_threshold_10_19 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (4449271510 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (1900000016707 / 1000000000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 4449271510 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1900000016707 / 1000000000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1900000016707 / 1000000000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn
        (by norm_num only : (1900000016707 / 1000000000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Every odd nonsquarefree n>1 above N(76598623) has a prime MR witness
at most log(n)^1.9000007986. This improves the exponent at the smallest
coefficient threshold for the 19/10 scale. -/
theorem exists_prime_witness_of_explicit_finite_fiber_threshold_10_19_53m {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 76598623 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (19000007986 / 10000000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 76598623) hn ho hns
      (19000007986 / 10000000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (19000007986 / 10000000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_explicit_fiber_threshold_10_19_53m
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above N(76598623), the least prime MR witness of every odd
nonsquarefree n>1 is at most log(n)^1.9000007988 and strictly below log(n)^2. -/
theorem exists_least_prime_witness_of_explicit_finite_fiber_threshold_10_19_53m {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 76598623 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (19000007986 / 10000000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_explicit_finite_fiber_threshold_10_19_53m hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (76598623 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (19000007986 / 10000000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 76598623 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 19000007986 / 10000000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (19000007986 / 10000000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (19000007986 / 10000000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Every odd nonsquarefree input above `N(21518759)` has a prime MR witness
at most `(log n)^1.900003`. Transfer the free 10/19 Fermat-quotient bound
through its explicit prime threshold. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_10_19_149m {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 21518759 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1900003 / 1000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 21518759) hn ho hns
      (1900003 / 1000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1900003 / 1000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_free_finite_fiber_threshold_10_19_149m
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above `N(21518759)`, the least prime MR witness for every odd nonsquarefree
input is at most `(log n)^1.900003`, strictly below `(log n)^2`. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_10_19_149m {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 21518759 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1900003 / 1000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_10_19_149m hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (21518759 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (1900003 / 1000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 21518759 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1900003 / 1000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1900003 / 1000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (1900003 / 1000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Every odd nonsquarefree input above `N(1411732827)` has a prime
Miller–Rabin witness at most `(log n)^1.83`. The bound follows from the
free 150/82 finite-fiber estimate and its explicit smooth-number supply. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_150_82 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 1411732827 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (183 / 100 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 1411732827) hn ho hns (183 / 100)
      (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (183 / 100)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_free_finite_fiber_threshold_150_82
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above `N(1411732827)`, the least prime Miller–Rabin witness for every odd
nonsquarefree input is at most `(log n)^1.83`, strictly below `(log n)^2`. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_150_82 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 1411732827 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (183 / 100 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_150_82 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (1411732827 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (183 / 100)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 1411732827 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 183 / 100)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (183 / 100 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (183 / 100 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Above `N(1411732827)`, every odd nonsquarefree input has a prime
Miller–Rabin witness at most `(log n)^1.8297`, by the 75/41 finite-fiber bound. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_75_41 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 1411732827 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (18297 / 10000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 1411732827) hn ho hns (18297 / 10000)
      (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (18297 / 10000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_free_finite_fiber_threshold_75_41
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- For inputs above `N(1411732827)`, the least prime Miller–Rabin witness is
at most `(log n)^1.8297` and therefore strictly below `(log n)^2`. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_75_41 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 1411732827 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (18297 / 10000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_75_41 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (1411732827 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (18297 / 10000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 1411732827 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 18297 / 10000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (18297 / 10000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (18297 / 10000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Above `N(1411732827)`, every odd nonsquarefree input has a prime
Miller–Rabin witness at most `(log n)^1.82927`, using the sharpened 75/41
finite-fiber Fermat-quotient bound. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_75_41_182927 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 1411732827 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (182927 / 100000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 1411732827) hn ho hns
      (182927 / 100000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (182927 / 100000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_free_finite_fiber_threshold_75_41_182927
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above `N(1411732827)`, the least prime Miller–Rabin witness is at most
`(log n)^1.82927` and therefore strictly below `(log n)^2`. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_75_41_182927 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 1411732827 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (182927 / 100000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_75_41_182927 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (1411732827 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (182927 / 100000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 1411732827 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 182927 / 100000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (182927 / 100000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (182927 / 100000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

open PseudoPrime.NumberTheory.Heilbronn in
/-- Above `N(4,217,312,731)`, every odd nonsquarefree input has a prime
Miller–Rabin witness at most `(ln n)^(1.82861)`. Transfer the new 192/105
Fermat-quotient estimate through the uniform prime reduction. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_192_105_182861 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 4217312731 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (182861 / 100000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 4217312731) hn ho hns
      (182861 / 100000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (182861 / 100000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    exists_prime_nontrivial_power_of_free_finite_fiber_threshold_192_105_182861
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Above `N(4,217,312,731)`, the least prime Miller–Rabin witness is at most
`(ln n)^(1.82861)` and therefore strictly below `(ln n)^2`. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_192_105_182861 {n : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 4217312731 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (182861 / 100000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_192_105_182861 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (n := n) (u := 4217312731) (A := 182861 / 100000)
        (by norm_num only) (by norm_num only : (3 : ℝ) ≤ 2 * (182861 / 100000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 4217312731 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 182861 / 100000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (182861 / 100000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (182861 / 100000 : ℝ) < 2)
  have hWitness : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hWitness ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hWitness, (Nat.find_spec hWitness).1, (Nat.find_spec hWitness).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hWitness ⟨hs, hfail⟩⟩

/-- Inputs: an odd nonsquarefree `n ≥ N(21518759)`.
Claim: A prime Miller–Rabin witness is at most `(log n)^(1876/1000)`.
Content: Transfer the 30/16 Fermat-quotient bound through the prime reduction.
Proof: Apply the uniform Fermat-to-Miller–Rabin implication.
Role: Supplies the explicit witness bound used to identify the least witness. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_30_16_149m {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 21518759 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1876 / 1000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 21518759) hn ho hns (1876 / 1000)
      (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1876 / 1000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_free_finite_fiber_threshold_30_16_149m
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Inputs: an odd nonsquarefree `n ≥ N(21518759)`.
Claim: Its least prime Miller–Rabin witness is at most `(log n)^(1876/1000)`
and strictly below `(log n)^2`.
Content: The bound applies only to odd nonsquarefree inputs.
Proof: Use the prime-witness existence theorem and `Nat.find` minimality.
Role: Publishes the least-witness bound for the explicit 30/16 branch. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_30_16_149m {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 21518759 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1876 / 1000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_30_16_149m hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (21518759 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (1876 / 1000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 21518759 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1876 / 1000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1876 / 1000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (1876 / 1000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Inputs: an odd nonsquarefree `n ≥ N(21518759)`.
Claim: A prime Miller–Rabin witness is at most `(log n)^(1868/1000)`.
Content: Transfer the 28/15 Fermat-quotient bound through the prime reduction.
Proof: Apply the uniform Fermat-to-Miller–Rabin implication.
Role: Supplies the witness bound used to identify the least witness. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_28_15_149m {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 21518759 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1868 / 1000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 21518759) hn ho hns (1868 / 1000)
      (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1868 / 1000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    NumberTheory.Heilbronn.exists_prime_nontrivial_power_of_free_finite_fiber_threshold_28_15_149m
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Inputs: an odd nonsquarefree `n ≥ N(21518759)`.
Claim: Its least prime Miller–Rabin witness is at most `(log n)^(1868/1000)`
and strictly below `(log n)^2`. Proof: Use the prime-witness existence theorem
and `Nat.find` minimality. Role: Publishes the least-witness bound for 28/15. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_149m {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 21518759 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1868 / 1000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_28_15_149m hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (21518759 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (1868 / 1000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 21518759 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1868 / 1000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1868 / 1000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (1868 / 1000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

open PseudoPrime.NumberTheory.Heilbronn in
/-- Inputs: an odd nonsquarefree `n ≥ N(21518759)`.
Claim: A prime Miller–Rabin witness is at most `(log n)^(18666701/10000000)`.
Proof: Transfer the refined 28/15 Fermat-quotient bound through prime reduction.
Role: Supplies the witness bound used to identify the least witness. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_28_15_18666701 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 21518759 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (18666701 / 10000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 21518759) hn ho hns
      (18666701 / 10000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power (by norm_num only)
        (by norm_num only : (3 : ℝ) ≤ 2 * (18666701 / 10000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    exists_prime_nontrivial_power_of_free_finite_fiber_threshold_28_15_18666701
      (hp.odd_of_ne_two hp2) hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Inputs: an odd nonsquarefree `n ≥ N(21518759)`.
Claim: Its least prime Miller–Rabin witness is at most `(log n)^(1866920/1000000)`
and strictly below `(log n)^2`. Proof: Use witness existence and `Nat.find`.
Role: Publishes the refined least-witness bound for 28/15. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_18666701 {n : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 21518759 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (18666701 / 10000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_28_15_18666701 hn ho hns hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power (by norm_num only : 2 ≤ (21518759 : ℕ))
        (by norm_num only : (3 : ℝ) ≤ 2 * (18666701 / 10000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold 21518759 :=
      Nat.cast_le.mpr (eight_le_explicit_fiber_prime_threshold (by norm_num only))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 18666701 / 10000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (18666701 / 10000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (18666701 / 10000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

open PseudoPrime.NumberTheory.Heilbronn in
/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(u)` and `u≥17,431,511`.
Claim: a prime Miller–Rabin witness is at most `(log n)^(1.8666703)`.
Proof: Transfer the parameterized 28/15 Fermat-quotient bound through prime
reduction. Role: supplies the witness for the lower-start least-witness result. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_28_15_18666703 {n u : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hu : 17431511 ≤ u)
    (hlarge : explicitFiniteFiberInputThreshold u ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (18666703 / 10000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u) hn ho hns (18666703 / 10000000)
      (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power
        (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu)
        (by norm_num only : (3 : ℝ) ≤ 2 * (18666703 / 10000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    exists_prime_nontrivial_power_of_free_finite_fiber_threshold_28_15_18666703
      (hp.odd_of_ne_two hp2) hu hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(u)` and `u≥17,431,511`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.8666703)`
and strictly below `(log n)^2`. Proof: Use the witness existence theorem and
`Nat.find` minimality. Role: publishes the lower-start least-witness bound. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_18666703 {n u : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n) (hu : 17431511 ≤ u)
    (hlarge : explicitFiniteFiberInputThreshold u ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (18666703 / 10000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_28_15_18666703 hn ho hns hu hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power
        (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu)
        (by norm_num only : (3 : ℝ) ≤ 2 * (18666703 / 10000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u :=
      Nat.cast_le.mpr
        (eight_le_explicit_fiber_prime_threshold
          (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 18666703 / 10000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (18666703 / 10000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (18666703 / 10000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(17,456,612)`.
Claim: a prime Miller–Rabin witness is at most `(log n)^(1.8666703)`.
Proof: Specialize the parameterized lower-start theorem to its first valid u.
Role: exposes the concrete starting threshold. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_28_15_17456612 {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hlarge : explicitFiniteFiberInputThreshold 17456612 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (18666703 / 10000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) :=
  exists_prime_witness_of_free_finite_fiber_threshold_28_15_18666703 hn ho hns (by norm_num only)
    hlarge

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(17,456,612)`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.8666703)`
and strictly below `(log n)^2`. Proof: Specialize the generic least-witness
theorem to `u=17,456,612`. Role: publishes the concrete lower-start bound. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_17456612 {n : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 17456612 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (18666703 / 10000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s :=
  exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_18666703 hn ho hns
    (by norm_num only) hlarge

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(17,431,511)`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.8666703)`
and strictly below `(log n)^2`. Specialize the parameterized least-witness
theorem at the reduced explicit threshold. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_17431511 {n : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 17431511 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (18666703 / 10000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s :=
  exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_18666703 hn ho hns
    (by norm_num only) hlarge

open PseudoPrime.NumberTheory.Heilbronn in
/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(u)` and `u≥17,431,511`.
Claim: a prime Miller–Rabin witness is at most `(log n)^(1.866670171)`.
Proof: Transfer the sharper 28/15 Fermat bound through prime reduction.
Role: supplies the witness for the improved least-witness theorem. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_28_15_1866670171 {n u : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hu : 17431511 ≤ u)
    (hlarge : explicitFiniteFiberInputThreshold u ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1866670171 / 1000000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u) hn ho hns
      (1866670171 / 1000000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power
        (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1866670171 / 1000000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    exists_prime_nontrivial_power_of_free_finite_fiber_threshold_28_15_1866670171
      (hp.odd_of_ne_two hp2) hu hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(u)` and `u≥17,431,511`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.866670171)`
and strictly below `(log n)^2`. Proof: apply `Nat.find` to the existence
theorem. Role: publishes the improved least-witness bound. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_1866670171 {n u : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n) (hu : 17431511 ≤ u)
    (hlarge : explicitFiniteFiberInputThreshold u ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1866670171 / 1000000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_28_15_1866670171 hn ho hns hu hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power
        (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1866670171 / 1000000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u :=
      Nat.cast_le.mpr
        (eight_le_explicit_fiber_prime_threshold
          (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1866670171 / 1000000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1866670171 / 1000000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (1866670171 / 1000000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(17,431,511)`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.866670171)`
and strictly below `(log n)^2`. Proof: specialize the parameterized theorem
to its explicit start. Role: exposes the improved concrete threshold. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_17431511_1866670171 {n : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 17431511 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1866670171 / 1000000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s :=
  exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_1866670171 hn ho hns
    (by norm_num only) hlarge

open PseudoPrime.NumberTheory.Heilbronn in
/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(u)` and `u≥17,431,511`.
Claim: a prime Miller–Rabin witness is at most `(log n)^(1.86667011)`.
Proof: Transfer the refined 28/15 Fermat bound through prime reduction.
Role: supplies the witness for the improved least-witness theorem. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_28_15_186667011 {n u : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hu : 17431511 ≤ u)
    (hlarge : explicitFiniteFiberInputThreshold u ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (186667011 / 100000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u) hn ho hns (186667011 / 100000000)
      (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power
        (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu)
        (by norm_num only : (3 : ℝ) ≤ 2 * (186667011 / 100000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    exists_prime_nontrivial_power_of_free_finite_fiber_threshold_28_15_186667011
      (hp.odd_of_ne_two hp2) hu hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(u)` and `u≥17,431,511`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.86667011)`
and strictly below `(log n)^2`. Proof: apply `Nat.find` to the existence
theorem. Role: publishes the sharper least-witness bound. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_186667011 {n u : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n) (hu : 17431511 ≤ u)
    (hlarge : explicitFiniteFiberInputThreshold u ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (186667011 / 100000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_28_15_186667011 hn ho hns hu hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power
        (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu)
        (by norm_num only : (3 : ℝ) ≤ 2 * (186667011 / 100000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u :=
      Nat.cast_le.mpr
        (eight_le_explicit_fiber_prime_threshold
          (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 186667011 / 100000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (186667011 / 100000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (186667011 / 100000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(17,431,511)`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.86667011)`
and strictly below `(log n)^2`. Proof: specialize the parameterized theorem
to its explicit start. Role: publishes the concrete improved bound. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_17431511_186667011 {n : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 17431511 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (186667011 / 100000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s :=
  exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_186667011 hn ho hns
    (by norm_num only) hlarge

open PseudoPrime.NumberTheory.Heilbronn in
/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(u)` and `u≥17,431,511`.
Claim: a prime Miller–Rabin witness is at most `(log n)^(1.866670047)`.
Proof: Transfer the refined 28/15 Fermat bound through prime reduction.
Role: supplies the witness for the improved least-witness theorem. -/
theorem exists_prime_witness_of_free_finite_fiber_threshold_28_15_1866670047 {n u : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (hu : 17431511 ≤ u)
    (hlarge : explicitFiniteFiberInputThreshold u ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (Real.log n) ^ (1866670047 / 1000000000 : ℝ) ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  apply
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound (P :=
      NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u) hn ho hns
      (1866670047 / 1000000000) (by norm_num only)
      (explicit_fiber_prime_threshold_le_log_power
        (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1866670047 / 1000000000)) hlarge)
  intro p hp hp2 hpLarge
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q, hq, hb, hpow⟩ :=
    exists_prime_nontrivial_power_of_free_finite_fiber_threshold_28_15_1866670047
      (hp.odd_of_ne_two hp2) hu hpLarge
  exact ⟨q, hq.pos, hb, hpow⟩

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(u)` and `u≥17,431,511`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.866670047)`
and strictly below `(log n)^2`. Proof: apply `Nat.find` to the existence
theorem. Role: publishes the sharper least-witness bound. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_1866670047 {n u : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n) (hu : 17431511 ≤ u)
    (hlarge : explicitFiniteFiberInputThreshold u ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1866670047 / 1000000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_of_free_finite_fiber_threshold_28_15_1866670047 hn ho hns hu hlarge
  have hLn : 1 < Real.log n := by
    have hbound :=
      explicit_fiber_prime_threshold_le_log_power
        (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu)
        (by norm_num only : (3 : ℝ) ≤ 2 * (1866670047 / 1000000000)) hlarge
    have hP : (8 : ℝ) ≤ NumberTheory.Heilbronn.explicitFiniteFiberPrimeThreshold u :=
      Nat.cast_le.mpr
        (eight_le_explicit_fiber_prime_threshold
          (Nat.le_trans (by norm_num only : 2 ≤ 17431511) hu))
    by_contra h
    have hupper :=
      Real.rpow_le_one (Real.log_nonneg (Nat.one_le_cast.mpr hn.le)) (le_of_not_gt h)
        (by norm_num only : (0 : ℝ) ≤ 1866670047 / 1000000000)
    exact (by norm_num only : ¬(8 : ℝ) ≤ 1) (hP.trans (hbound.trans hupper))
  have hstrict : (Real.log n) ^ (1866670047 / 1000000000 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (by norm_num only : (1866670047 / 1000000000 : ℝ) < 2)
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  have hleastbound := (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hleastbound,
      hleastbound.trans_lt hstrict, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Inputs: an odd nonsquarefree `n>1` with `n≥N(17,431,511)`.
Claim: its least prime Miller–Rabin witness is at most `(log n)^(1.866670047)`
and strictly below `(log n)^2`. Proof: specialize the parameterized theorem
to its explicit start. Role: publishes the concrete improved bound. -/
theorem exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_17431511_1866670047 {n : ℕ}
    (hn : 1 < n) (ho : Odd n) (hns : ¬Squarefree n)
    (hlarge : explicitFiniteFiberInputThreshold 17431511 ≤ n) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (1866670047 / 1000000000 : ℝ) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s :=
  exists_least_prime_witness_of_free_finite_fiber_threshold_28_15_1866670047 hn ho hns
    (by norm_num only) hlarge

end PseudoPrime.PrimeTestBounds.MillerRabin
