/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ParameterizedHeilbronnSmoothSupply

/-! # Nontrivial Fermat bases for every log exponent above 28/15 -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For fixed A>28/15, all sufficiently large odd primes p have a prime
q<=log(p)^A with q^(p-1) nontrivial modulo p^2. The threshold may depend on A,
while the result is uniform in p and uses no GRH or external Fermat estimate. -/
theorem eventually_exists_prime_nontrivial_power_le_log_power_of_exponent {A : ℝ}
    (hA : (28 / 15 : ℝ) < A) :
    Filter.Eventually
      (fun p : ℕ ↦
        p.Prime →
          p ≠ 2 → ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ A ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
      Filter.atTop := by
  obtain ⟨P, hP⟩ := exists_uniform_heilbronn_interval_bound (r := 16185) (by norm_num only)
  filter_upwards [eventually_smooth_count_at_cutoff_of_exponent hA,
    Filter.eventually_ge_atTop P] with p hsm hlarge hp hp2
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk, hkp, hlo, hhi, hcount⟩ := hP p (hp.odd_of_ne_two hp2) hlarge
  obtain ⟨q, hq, hqB, hpow⟩ :=
    exists_prime_nontrivial_power_of_interval_and_smooth hcount (hsm k hk hlo hhi)
  have hB := Nat.lt_add_one_iff.mp hqB
  have hle : (q : ℝ) ≤ (Real.log p) ^ A :=
    (Nat.cast_le.mpr hB).trans
      (Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le)) _))
  exact ⟨q, hq, hle, hpow⟩

end PseudoPrime.NumberTheory.Heilbronn
