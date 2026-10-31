/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSquareConductorGap

/-! # Logarithmic budgets for omitted primes in a square factor -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If n=f*m^2 with positive f,m, primes dividing n but omitted by f
have twice their logarithmic weight bounded by log n-log f. Place those
primes in the square part and expand log n exactly. The ambient factor
four is absent here, reserving its logarithm for the dyadic loss. -/
theorem gamma_odd_conductor_square_log_budget {n f m : ℕ} (hn : n = f * m ^ 2) (hf : 0 < f)
    (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (homit : ∀ p ∈ S, ¬p ∣ f) :
    2 * (∑ p ∈ S, Real.log p) ≤ Real.log n - Real.log f := by
  have hpart : S ⊆ m.primeFactors := by
    intro p hp
    have hnprime := hS hp
    have hprime := Nat.prime_of_mem_primeFactors hnprime
    exact
      Nat.mem_primeFactors.mpr
        ⟨hprime,
          gamma_square_only_prime_dvd_part hn (dvd_refl f) hprime
            (Nat.dvd_of_mem_primeFactors hnprime) (homit p hp),
          hm.ne'⟩
  have hsum := gamma_conductor_subset_log_budget hm S hpart
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : Real.log (n : ℝ) = Real.log f + 2 * Real.log m := by
    rw [hn, Nat.cast_mul, Nat.cast_pow, Real.log_mul hfR.ne' (pow_ne_zero 2 hmR.ne'), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  linarith only [hsum, he]

end PseudoPrime.Analysis
