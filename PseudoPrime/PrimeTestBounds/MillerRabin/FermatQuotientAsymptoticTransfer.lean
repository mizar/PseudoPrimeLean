/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FermatQuotientTransfer
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform asymptotic transfer of external Fermat-quotient estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A Fermat-quotient log-power bound for all odd primes p at least P transfers
to every odd nonsquarefree n>1 with P at most log(n)^alpha. A square prime divisor
below P is itself a bounded rejecting base; larger square divisors use the assumed
estimate. This removes small local primes without a finite certificate. -/
theorem exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound {n P : ℕ} (hn : 1 < n)
    (ho : Odd n) (hns : ¬Squarefree n) (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hP : (P : ℝ) ≤ (Real.log n) ^ alpha)
    (hF :
      ∀ p : ℕ,
        p.Prime →
          p ≠ 2 →
          P ≤ p →
          ∃ b : ℕ, 0 < b ∧ (b : ℝ) ≤ (Real.log p) ^ alpha ∧ (b : ZMod (p ^ 2)) ^ (p - 1) ≠ 1) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (Real.log n) ^ alpha ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ p * p ∣ n := by
    by_contra h
    exact hns (Nat.squarefree_iff_prime_squarefree.mpr (fun p hp hd ↦ h ⟨p, hp, hd⟩))
  obtain ⟨p, hp, hd⟩ := hex
  have hsq : p ^ 2 ∣ n := by simpa only [pow_two] using hd
  have hpn : p ∣ n := (dvd_mul_right p p).trans hd
  have hp2 : p ≠ 2 := fun he ↦ ho.not_two_dvd_nat (he ▸ hpn)
  by_cases hlarge : P ≤ p
  · exact
      exists_prime_witness_le_log_power_of_fermat_quotient_bound hn ho hp hp2 hsq alpha halpha
        (hF p hp hp2 hlarge)
  · exact
      ⟨p, hp, (Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))).trans hP,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩

/-- For alpha>0, an eventual Fermat-quotient bound at odd primes implies an
eventual prime MR witness bound log(n)^alpha on all odd nonsquarefree inputs.
Extract the prime threshold and let log(n)^alpha grow beyond it, then apply the
uniform arithmetic transfer. The external analytic bound is retained as a hypothesis. -/
theorem eventually_exists_prime_witness_le_log_power_of_fermat_quotient_bound {alpha : ℝ}
    (ha : 0 < alpha)
    (hF :
      Filter.Eventually
        (fun p : ℕ ↦
          p.Prime →
            p ≠ 2 →
            ∃ b : ℕ, 0 < b ∧ (b : ℝ) ≤ (Real.log p) ^ alpha ∧ (b : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
        Filter.atTop) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ r : ℕ,
            r.Prime ∧
              (r : ℝ) ≤ (Real.log n) ^ alpha ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n))
      Filter.atTop := by
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp hF
  have ht : Filter.Tendsto (fun n : ℕ ↦ (Real.log n) ^ alpha) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply (ht.eventually_ge_atTop (P : ℝ)).mono
  intro n hn hng ho hns
  exact
    exists_prime_witness_le_log_power_of_uniform_fermat_quotient_bound hng ho hns alpha ha.le hn
      (fun p hp hp2 hlarge ↦ hP p hlarge hp hp2)

end PseudoPrime.PrimeTestBounds.MillerRabin
