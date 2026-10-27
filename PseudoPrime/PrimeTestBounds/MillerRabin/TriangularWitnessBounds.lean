/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSignedLargeIndexWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexClassification
public import PseudoPrime.Analysis.NumericalLogBounds

/-! # Strong Miller--Rabin witnesses with an improved large-index branch

The finite-index classification and certified alpha-18 large-index comparison
combine at the decimal start 10^9565217391305, without a squarefreeness
restriction on the odd composite input.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH for odd n > 1 whose Fermat subgroup has index at least 10^9
and log n >= 22000000000000, there is a prime strong witness at most
(282924/1000000)log(n)^2.
A level prime cannot be a unit; an outside prime contradicts Fermat containment
of every strong pass. No additional kernel error or subgroup-choice premise remains. -/
theorem exists_prime_witness_le_0283_of_large_fermat_index {n : ℕ} [NeZero n] (hn : 1 < n)
    (ho : Odd n) (hi : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlog : (22000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_factor_or_outside_triangular18_signed_large_index
      (PrimeTest.fermatSubgroup n) hi hGRH hlog
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hc := (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hc) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Monotone decimal exponents transfer a large natural cutoff to a smaller one.
Keep the exponents variable to avoid evaluating the huge natural powers. -/
private theorem triangular_decimal_cutoff_mono {a b n : ℕ} (hab : a ≤ b) (hN : 10 ^ b ≤ n) :
    10 ^ a ≤ n := by exact (Nat.pow_le_pow_right (by decide : 0 < 10) hab).trans hN

/-- For n >= 10^9565217391305, log n >= 22000000000000.
Use logarithmic monotonicity and the proved lower bound for log 10;
this supplies the conservative common decimal threshold. -/
theorem log_ge_triangular_large_index_of_decimal {n : ℕ} (hN : 10 ^ 9565217391305 ≤ n) :
    (22000000000000 : ℝ) ≤ Real.log n := by
  have hp : 0 < (10 : ℝ) ^ (9565217391305 : ℕ) := pow_pos (by norm_num only) _
  have hc : (10 : ℝ) ^ (9565217391305 : ℕ) ≤ (n : ℝ) := by exact_mod_cast hN
  have hl := Real.log_le_log hp hc
  rw [Real.log_pow] at hl
  norm_num only at hl
  linarith only [hl, Analysis.log_ten_gt_twenty_three_tenths]

/-- Under GRH, every odd composite n >= 10^9565217391305 has a prime
strong Miller--Rabin witness at most (282924/1000000)log(n)^2. Both the finite-index
classification and the unrestricted large-index branch supply this coefficient. -/
theorem exists_prime_witness_le_0282924 {n : ℕ} (ho : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 9565217391305 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hL := log_ge_triangular_large_index_of_decimal hN
  have hp : 0 < (n : ℝ) := by exact_mod_cast Odd.pos ho
  have hl := Real.log_le_sub_one_of_pos hp
  have hn : 1 < n := by exact_mod_cast (by linarith only [hL, hl] : (1 : ℝ) < n)
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9
  · have hsmall :=
      triangular_decimal_cutoff_mono (by decide : (434782608696 : ℕ) ≤ 9565217391305) hN
    exact
      exists_prime_witness_le_0283_of_small_fermat_index ho hcomp (PrimeTest.fermatSubgroup n)
        (le_refl _) hi hGRH hsmall
  · have hlarge : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index := by
      have h := (lt_of_not_ge hi).le
      norm_num only at h
      exact h
    obtain ⟨p, hp, hb, hf⟩ :=
      exists_prime_witness_le_0283_of_large_fermat_index hn ho hlarge hGRH hL
    exact ⟨p, hp, hb, hf⟩

/-- Under GRH, the least prime strong Miller--Rabin witness for every odd
composite n >= 10^9565217391305 is at most (282924/1000000)log(n)^2.
Minimize the prime rejection predicate after obtaining the bounded witness. -/
theorem exists_least_prime_witness_le_0282924 {n : ℕ} (ho : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 9565217391305 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_0282924 ho hcomp hGRH hN
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hfail ↦
      Nat.find_min' hex ⟨hr, hfail⟩⟩

/-- Preserve the former coefficient-0.282976 statement for callers.
The sharper all-input statement implies it by coefficient monotonicity. -/
theorem exists_prime_witness_le_0282976 {n : ℕ} (ho : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 9565217391305 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (282976 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hfail⟩ := exists_prime_witness_le_0282924 ho hcomp hGRH hN
  have hcoef : (282924 / 1000000 : ℝ) ≤ 282976 / 1000000 := by norm_num only
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log n))), hfail⟩

/-- Preserve the former coefficient-0.282977 statement for callers.
The sharper all-input statement implies it by coefficient monotonicity. -/
theorem exists_prime_witness_le_0282977 {n : ℕ} (ho : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 9565217391305 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (282977 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hfail⟩ := exists_prime_witness_le_0282924 ho hcomp hGRH hN
  have hcoef : (282924 / 1000000 : ℝ) ≤ 282977 / 1000000 := by norm_num only
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log n))), hfail⟩

/-- Preserve the former coefficient-0.282982 theorem for downstream callers.
The sharper all-input statement implies it by monotonicity of the coefficient. -/
theorem exists_prime_witness_le_0282982 {n : ℕ} (ho : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 9565217391305 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (282982 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hfail⟩ := exists_prime_witness_le_0282924 ho hcomp hGRH hN
  have hcoef : (282924 / 1000000 : ℝ) ≤ 282982 / 1000000 := by norm_num only
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log n))), hfail⟩

/-- The coefficient-0.282924 theorem also implies the former coefficient-0.283
bound. This keeps the existing public statement available to downstream callers. -/
theorem exists_prime_witness_le_0283 {n : ℕ} (ho : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 9565217391305 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (283 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hfail⟩ := exists_prime_witness_le_0282924 ho hcomp hGRH hN
  have hcoef : (282924 / 1000000 : ℝ) ≤ 283 / 1000 := by norm_num only
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log n))), hfail⟩

/-- Under GRH for odd n above the common decimal threshold,
strong passage for every prime base through (283/1000)log(n)^2 is equivalent
to primality. The composite direction uses the all-branch witness theorem;
the prime direction restricts the existing log-squared criterion. -/
theorem prime_iff_millerRabin_for_all_primes_le_0283_log_sq {n : ℕ} (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 9565217391305 ≤ n) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ (283 / 1000 : ℝ) * (Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  constructor
  · intro hpass
    by_contra hcomp
    obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_0283 ho hcomp hGRH hN
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    have hL := log_ge_triangular_large_index_of_decimal hN
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Odd.pos ho
    have hl := Real.log_le_sub_one_of_pos hnpos
    have hn : 1 < n := by exact_mod_cast (by linarith only [hL, hl] : (1 : ℝ) < n)
    have hcap : (283 / 1000 : ℝ) * (Real.log n) ^ 2 ≤ (Real.log n) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (by norm_num only)
    exact
      (prime_iff_millerRabin_for_all_primes_le_log_sq hGRH hn ho).mpr hp p hprime (hb.trans hcap)

end PseudoPrime.PrimeTestBounds.MillerRabin
