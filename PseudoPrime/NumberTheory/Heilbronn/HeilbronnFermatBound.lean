/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnSmoothSupply

/-! # A proved logarithmic-power bound for nontrivial Fermat bases -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For every sufficiently large odd prime p there is a prime q<=log(p)^(15/8)
with q^(p-1) nontrivial modulo p^2. Combine the proved interval bound with the
quantitative smooth-number supply. No GRH or external Fermat estimate is assumed. -/
theorem eventually_exists_prime_nontrivial_power_le_log_power :
    Filter.Eventually
      (fun p : ℕ ↦
        p.Prime →
          p ≠ 2 →
          ∃ q : ℕ,
            q.Prime ∧ (q : ℝ) ≤ (Real.log p) ^ (15 / 8 : ℝ) ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1)
      Filter.atTop := by
  obtain ⟨P, hP⟩ := exists_uniform_heilbronn_interval_bound (r := 16185) (by norm_num only)
  filter_upwards [eventually_smooth_count_at_cutoff, Filter.eventually_ge_atTop P] with p hsm hlarge
    hp hp2
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk, hkp, hlo, hhi, hcount⟩ := hP p (hp.odd_of_ne_two hp2) hlarge
  obtain ⟨q, hq, hqB, hpow⟩ :=
    exists_prime_nontrivial_power_of_interval_and_smooth hcount (hsm k hk hlo hhi)
  have hB := Nat.lt_add_one_iff.mp hqB
  have hle : (q : ℝ) ≤ (Real.log p) ^ (15 / 8 : ℝ) :=
    (Nat.cast_le.mpr hB).trans
      (Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le)) _))
  exact ⟨q, hq, hle, hpow⟩

end PseudoPrime.NumberTheory.Heilbronn
