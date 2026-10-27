/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaActualPrimeCosts

/-! # Actual square and dyadic losses in one conductor budget -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For odd input primes with local value minus one, arbitrary positive-power
prefix losses total at most 2M times their logarithmic weight. The local
parity-cancelled bound and the certified odd-prime allowance supply the
estimate used in both conductor parity branches. -/
theorem gamma_actual_odd_input_square_sum_le {n f : ℕ} (hn : Odd n) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (∑ p ∈ S, Real.log p) * (2 * (11783423 / 25000000 : ℝ)) := by
  have hpoint :=
    Finset.sum_le_sum
      (fun p hp ↦
        (gamma_actual_minus_one_prime_cost_le χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp)
              (K p) (by linarith only [hx])).trans
          (mul_le_mul_of_nonneg_left (gamma_odd_input_prime_square_allowance_le hn (hS hp) hx)
            (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors (hS hp)).one_le))))
  simpa only [Finset.sum_mul] using hpoint

/-- For n=f*m^2 odd, actual arbitrary-power square losses are absorbed by
M(log n-log f). The arithmetic budget reserves the entire log-four gap.
This is the square-part interface for the odd-conductor dyadic branch. -/
theorem gamma_actual_odd_conductor_square_cost_absorbed {n f m : ℕ} (hn : n = f * m ^ 2)
    (hodd : Odd n) (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) {x : ℝ}
    (hx : 10000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log n := by
  have hpoint := gamma_actual_odd_input_square_sum_le hodd S hS χ hχ K hx
  have hgap :=
    gamma_odd_conductor_square_log_budget hn hf hm S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hgap (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hpoint, hw]

/-- For n=d*m^2 odd, d dividing f and f<=4d, actual arbitrary-power
square losses are absorbed by M(log(4n)-log f). All local numerical
conditions are certified. This supplies the even-conductor square budget. -/
theorem gamma_actual_square_cost_absorbed_by_conductor_gap {n d m f : ℕ} (hn : n = d * m ^ 2)
    (hodd : Odd n) (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d)
    (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) := by
  have hpoint := gamma_actual_odd_input_square_sum_le hodd S hS χ hχ K hx
  have hgap :=
    gamma_square_only_prime_log_gap_budget hn hd hm hf hdf hfd S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hgap (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hpoint, hw]

/-- For n=f*m^2 odd and chi(2) in {1,-1}, arbitrary-power square and
dyadic losses together fit M log(4n)+12/25. The square part uses only
log n-log f; the separate log four pays for the dyadic minus-one branch.
At value one the actual signed dyadic loss is nonpositive. -/
theorem gamma_actual_odd_conductor_square_dyadic_cost_le {n f m : ℕ} (hn : n = f * m ^ 2)
    (hodd : Odd n) (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1) (hχ2 : χ 2 = 1 ∨ χ 2 = -1)
    (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) +
        gammaActualPrimeLocalCost χ 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (12 / 25 : ℝ) := by
  have hs := gamma_actual_odd_conductor_square_cost_absorbed hn hodd hf hm S hS χ hχ K hx
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hn ▸ Nat.mul_pos hf (pow_pos hm 2)).ne'
  rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hn0]
  rcases hχ2 with h2 | h2
  · have ht :=
      gamma_actual_one_prime_cost_nonpos χ Nat.prime_two (by simpa only [Nat.cast_ofNat] using h2)
        K2 (by linarith only [hx])
    have hl : 0 ≤ (11783423 / 25000000 : ℝ) * Real.log 4 :=
      mul_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only))
    linarith only [hs, ht, hl]
  · have ht := gamma_actual_dyadic_minus_one_cost_le χ h2 K2 hx
    linarith only [hs, ht]

/-- For n=d*m^2 odd and even f dividing the ambient 4d allowance, actual
arbitrary-power square and dyadic losses total at most M log(4n)+3/4.
The square gap and the even-conductor dyadic certificate are combined once.
This supplies the even branch of the joint local witness comparison. -/
theorem gamma_actual_even_conductor_square_dyadic_cost_le {n d m f : ℕ} (hn : n = d * m ^ 2)
    (hodd : Odd n) (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d)
    (heven : Even f) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f)
    (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x : ℝ} (hx : 20000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) +
        gammaActualPrimeLocalCost χ 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) := by
  have hs :=
    gamma_actual_square_cost_absorbed_by_conductor_gap hn hodd hd hm hf hdf hfd S hS χ hχ K
      (by linarith only [hx])
  have ht := gamma_even_modulus_actual_dyadic_cost_le χ heven K2 hx
  change gammaActualPrimeLocalCost χ 2 K2 x ≤ (3 / 4 : ℝ) at ht
  linarith only [hs, ht]

/-- At the prescribed refined scale, the odd and even conductor branches
share the uniform square-plus-dyadic allowance 3/4. The odd branch has
f=d and chi(2) in {1,-1}; the even branch uses the certified ramified
loss. Arithmetic input and branch data remain explicit for character transfer. -/
theorem gamma_refined_actual_square_dyadic_cost_le {n d m f : ℕ} (hn : n = d * m ^ 2) (hodd : Odd n)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d)
    (χ : DirichletCharacter ℂ f) (hbranch : (f = d ∧ (χ 2 = 1 ∨ χ 2 = -1)) ∨ Even f) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {L : ℝ}
    (hL : 100 * Real.log 10 ≤ L) :
    (11783423 / 25000000 : ℝ) * Real.log f +
        (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) (gammaRefinedScale L)) +
        gammaActualPrimeLocalCost χ 2 K2 (gammaRefinedScale L) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (3 / 4 : ℝ) := by
  have hx := gamma_refined_scale_ge_twenty_thousand hL
  rcases hbranch with ⟨rfl, h2⟩ | he
  · have h :=
      gamma_actual_odd_conductor_square_dyadic_cost_le hn hodd hd hm S hS χ hχ h2 K K2
        (by linarith only [hx])
    linarith only [h]
  · exact
      gamma_actual_even_conductor_square_dyadic_cost_le hn hodd hd hm hf hdf hfd he S hS χ hχ K K2
        hx

end PseudoPrime.Analysis
