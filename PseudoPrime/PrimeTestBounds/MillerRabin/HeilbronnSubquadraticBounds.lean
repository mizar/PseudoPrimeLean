/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnFermatBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.FermatQuotientAsymptoticTransfer

/-! # An unconditional exponent 15/8 for odd nonsquarefree MR inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every sufficiently large odd nonsquarefree n has a prime MR rejecting base at most
log(n)^(15/8). Apply the proved Heilbronn Fermat bound through the local square-prime
transfer; small square prime factors are handled by their own rejecting prime base. -/
theorem eventually_exists_prime_witness_le_fifteen_eighths_of_not_squarefree :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧
              (q : ℝ) ≤ (Real.log n) ^ (15 / 8 : ℝ) ∧
              ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
      Filter.atTop := by
  apply
    eventually_exists_prime_witness_le_log_power_of_fermat_quotient_bound
      (by norm_num only : (0 : ℝ) < 15 / 8)
  apply NumberTheory.Heilbronn.eventually_exists_prime_nontrivial_power_le_log_power.mono
  intro p h hp hp2
  obtain ⟨q, hq, hb, hpow⟩ := h hp hp2
  exact ⟨q, hq.pos, hb, hpow⟩

/-- The least prime MR witness, including two, is eventually at most log(n)^(15/8)
for odd nonsquarefree n. Minimize the verified rejecting-prime predicate. -/
theorem eventually_exists_least_prime_witness_le_fifteen_eighths_of_not_squarefree :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧
              ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
              (q : ℝ) ≤ (Real.log n) ^ (15 / 8 : ℝ) ∧
              ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
      Filter.atTop := by
  classical
  apply eventually_exists_prime_witness_le_fifteen_eighths_of_not_squarefree.mono
  intro n h hn ho hns
  obtain ⟨q, hq, hb, hf⟩ := h hn ho hns
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb, fun s hs hfail ↦
      Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Every sufficiently large odd nonsquarefree n has a prime MR witness strictly below
log(n)^2. Compare the proved exponent 15/8 with two once log(n)>1. -/
theorem eventually_exists_prime_witness_lt_log_sq_of_not_squarefree :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧ (q : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
      Filter.atTop := by
  have hL : Filter.Tendsto (fun n : ℕ ↦ Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_prime_witness_le_fifteen_eighths_of_not_squarefree,
    hL.eventually_gt_atTop 1] with n h hl hn ho hns
  obtain ⟨q, hq, hb, hf⟩ := h hn ho hns
  have hpow : (Real.log n) ^ (15 / 8 : ℝ) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hl (by norm_num only : (15 / 8 : ℝ) < 2)
  exact ⟨q, hq, hb.trans_lt hpow, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
