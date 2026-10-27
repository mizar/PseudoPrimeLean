/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeightLayerSmoothSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.FermatQuotientAsymptoticTransfer

/-! # MR logarithmic exponents above 116/63 for odd nonsquarefree inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For every fixed A>116/63, sufficiently large odd nonsquarefree inputs have
a prime MR rejecting base at most log(n)^A. Transfer the proved nonzero
Fermat quotient bound, handling small square prime divisors uniformly.
The threshold depends only on A, and GRH is not assumed. -/
theorem eventually_exists_prime_witness_of_height_layers {A : ℝ} (hA : (116 / 63 : ℝ) < A) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧ (q : ℝ) ≤ (Real.log n) ^ A ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
      Filter.atTop := by
  have hAp : 0 < A := lt_trans (by norm_num only : (0 : ℝ) < 116 / 63) hA
  apply eventually_exists_prime_witness_le_log_power_of_fermat_quotient_bound hAp
  apply (NumberTheory.Heilbronn.eventually_exists_prime_nontrivial_power_of_height_layers hA).mono
  intro p h hp hp2
  obtain ⟨q, hq, hb, hpow⟩ := h hp hp2
  exact ⟨q, hq.pos, hb, hpow⟩

/-- For fixed A>116/63, the least prime MR witness on every sufficiently large
odd nonsquarefree input is at most log(n)^A. Minimize the proved rejecting
prime predicate. This is a bound on the least witness, not just one selected base. -/
theorem eventually_exists_least_prime_witness_of_height_layers {A : ℝ} (hA : (116 / 63 : ℝ) < A) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧
              ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
              (q : ℝ) ≤ (Real.log n) ^ A ∧
              ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
      Filter.atTop := by
  classical
  apply (eventually_exists_prime_witness_of_height_layers hA).mono
  intro n h hn ho hns
  obtain ⟨q, hq, hb, hf⟩ := h hn ho hns
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb, fun s hs hfail ↦
      Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- For each fixed 0<epsilon<10/63, the least prime MR witness on all sufficiently
large odd nonsquarefree inputs is at most log(n)^(2-epsilon), strictly below
log(n)^2. The starting threshold may depend on epsilon; no endpoint is asserted. -/
theorem eventually_exists_least_prime_witness_of_epsilon_lt_ten_sixty_thirds {epsilon : ℝ}
    (he0 : 0 < epsilon) (he1 : epsilon < 10 / 63) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧
              ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
              (q : ℝ) ≤ (Real.log n) ^ (2 - epsilon) ∧
              (q : ℝ) < (Real.log n) ^ 2 ∧
              ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
      Filter.atTop := by
  have hA : (116 / 63 : ℝ) < 2 - epsilon := by linarith only [he1]
  have hL : Filter.Tendsto (fun n : ℕ ↦ Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_least_prime_witness_of_height_layers hA,
    hL.eventually_gt_atTop 1] with n h hLn hn ho hns
  obtain ⟨q, hq, hf, hb, hleast⟩ := h hn ho hns
  have ht : (Real.log n) ^ (2 - epsilon) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hLn (show 2 - epsilon < (2 : ℝ) by linarith only [he0])
  exact ⟨q, hq, hf, hb, hb.trans_lt ht, hleast⟩

/-- For A>116/63, the eventual least-prime MR bound on all odd composites is
equivalent to its restriction to squarefree odd composites. Combine that
restriction with the newly proved nonsquarefree bound using a common threshold.
This identifies the remaining input family without assuming its bound. -/
theorem eventually_least_prime_witness_iff_squarefree_of_height_layers {A : ℝ}
    (hA : (116 / 63 : ℝ) < A) :
    (Filter.Eventually
        (fun n : ℕ ↦
          1 < n →
            Odd n →
            ¬n.Prime →
            ∃ q : ℕ,
              q.Prime ∧
                ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
                (q : ℝ) ≤ (Real.log n) ^ A ∧
                ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
        Filter.atTop) ↔
      (Filter.Eventually
        (fun n : ℕ ↦
          1 < n →
            Odd n →
            ¬n.Prime →
            Squarefree n →
            ∃ q : ℕ,
              q.Prime ∧
                ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
                (q : ℝ) ≤ (Real.log n) ^ A ∧
                ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
        Filter.atTop) := by
  constructor
  · intro h
    exact h.mono (fun n hn hng ho hcomp _ ↦ hn hng ho hcomp)
  · intro hs
    filter_upwards [hs, eventually_exists_least_prime_witness_of_height_layers hA] with n hsq hns hn
      ho hcomp
    by_cases hsf : Squarefree n
    · exact hsq hn ho hcomp hsf
    · exact hns hn ho hsf

end PseudoPrime.PrimeTestBounds.MillerRabin
