/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicRamifiedBudget

/-! # Odd-conductor dyadic losses and the square-part gap -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Actual local loss at a character value minus one: the finite odd-power
Euler correction plus the full signed ramp series normalized by sqrt x.
The finite set selects odd exponents; even Euler corrections vanish.
This abbreviation keeps the shared conductor accounting readable. -/
noncomputable def gammaMinusOneActualLocalCost {f : ℕ} (χ : DirichletCharacter ℂ f) (p : ℕ)
    (K : Finset ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ K, (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) +
    Real.log p *
      ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
        Real.sqrt x)

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

/-- A prime factor of an odd input is at least three, and its combined
square allowance is at most 2M for every x>=10000. Oddness excludes two;
the certified small and large odd-prime bounds supply the numerical margin.
This local fact is shared by both positive-power prefix interfaces. -/
theorem gamma_odd_input_prime_square_allowance_le {n p : ℕ} (hn : Odd n) (hp : p ∈ n.primeFactors)
    {x : ℝ} (hx : 10000 ≤ x) : gammaSquareCombinedCost p x ≤ 2 * (11783423 / 25000000 : ℝ) := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpne : p ≠ 2 := by
    intro he
    exact hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors hp)
  have hp3 : 3 ≤ p := Nat.succ_le_iff.mpr (lt_of_le_of_ne hprime.two_le (Ne.symm hpne))
  exact (gamma_odd_prime_square_cost_le hprime hp3 hx).trans (by norm_num only)

/-- The actual selected odd Euler and full ramp losses over odd input
primes are at most 2M times their logarithmic weight. Sum the local cost
comparison and the certified allowance. This separates analytic local
estimates from the subsequent arithmetic conductor-gap accounting. -/
theorem gamma_odd_input_minus_one_local_cost_sum_le {n f : ℕ} (hn : Odd n) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    (∑ p ∈ S, gammaMinusOneActualLocalCost χ p (K p) x) ≤
      (∑ p ∈ S, Real.log p) * (2 * (11783423 / 25000000 : ℝ)) := by
  have hpoint :=
    Finset.sum_le_sum
      (fun p hp ↦
        (gamma_minus_one_actual_prime_cost_le χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp)
              (K p) (by linarith only [hx])).trans
          (mul_le_mul_of_nonneg_left (gamma_odd_input_prime_square_allowance_le hn (hS hp) hx)
            (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors (hS hp)).one_le))))
  change (∑ p ∈ S, gammaMinusOneActualLocalCost χ p (K p) x) ≤ _ at hpoint
  simpa only [Finset.sum_mul] using hpoint

/-- For an odd input n=f*m^2, every selected minus-one local loss is
absorbed by M log n-M log f at all scales x>=10000. The proved odd-prime
cost certificate removes numerical premises. This leaves M log four
available for the independent odd-conductor dyadic branch. -/
theorem gamma_odd_conductor_square_actual_cost_absorbed {n f m : ℕ} (hn : n = f * m ^ 2)
    (hodd : Odd n) (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) {x : ℝ}
    (hx : 10000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaMinusOneActualLocalCost χ p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log n := by
  have hpoint := gamma_odd_input_minus_one_local_cost_sum_le hodd S hS χ hχ K hx
  have hgap :=
    gamma_odd_conductor_square_log_budget hn hf hm S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hgap (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hpoint, hw]

/-- For n=f*m^2 odd and chi(2)=-1, the actual square-prime losses and
dyadic loss together fit M log(4n)+12/25 at x>=10000. First absorb the
odd square primes into log n-log f, then spend the separate log four
on the certified dyadic loss. No conductor difference is used twice. -/
theorem gamma_odd_conductor_square_and_dyadic_cost_le {n f m : ℕ} (hn : n = f * m ^ 2)
    (hodd : Odd n) (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1) (hχ2 : χ 2 = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaMinusOneActualLocalCost χ p (K p) x) +
        gammaMinusOneActualLocalCost χ 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (12 / 25 : ℝ) := by
  have hs := gamma_odd_conductor_square_actual_cost_absorbed hn hodd hf hm S hS χ hχ K hx
  have hd := gamma_dyadic_minus_one_actual_cost_le χ hχ2 K2 hx
  change
    gammaMinusOneActualLocalCost χ 2 K2 x - (11783423 / 25000000 : ℝ) * Real.log 4 ≤
      (12 / 25 : ℝ) at hd
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hn ▸ Nat.mul_pos hf (pow_pos hm 2)).ne'
  rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hn0]
  linarith only [hs, hd]

/-- At the prescribed scale for L>=100 log ten, the odd-conductor square
and minus-one dyadic branches obey the same 12/25 budget. The scale theorem
discharges the threshold x>=10000. This connects the exact conductor
accounting to the intended logarithmic witness comparison. -/
theorem gamma_refined_odd_conductor_square_and_dyadic_cost_le {n f m : ℕ} (hn : n = f * m ^ 2)
    (hodd : Odd n) (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1) (hχ2 : χ 2 = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (11783423 / 25000000 : ℝ) * Real.log f +
        (∑ p ∈ S, gammaMinusOneActualLocalCost χ p (K p) (gammaRefinedScale L)) +
        gammaMinusOneActualLocalCost χ 2 K2 (gammaRefinedScale L) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (12 / 25 : ℝ) := by
  exact
    gamma_odd_conductor_square_and_dyadic_cost_le hn hodd hf hm S hS χ hχ hχ2 K K2
      (by linarith only [gamma_refined_scale_ge_twenty_thousand hL])

/-- For an odd integer input n>=10^100 with n=f*m^2 and chi(2)=-1,
the actual square and dyadic losses at the prescribed scale use the
conductor gap once and leave at most 12/25. The integer range supplies
L=log n, avoiding an independent analytic scale assumption. -/
theorem gamma_refined_input_odd_conductor_square_and_dyadic_cost_le {n f m : ℕ} (hn : n = f * m ^ 2)
    (hodd : Odd n) (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1) (hχ2 : χ 2 = -1) (K : ℕ → Finset ℕ)
    (K2 : Finset ℕ) (hlarge : 10 ^ 100 ≤ n) :
    (11783423 / 25000000 : ℝ) * Real.log f +
        (∑ p ∈ S, gammaMinusOneActualLocalCost χ p (K p) (gammaRefinedScale (Real.log n))) +
        gammaMinusOneActualLocalCost χ 2 K2 (gammaRefinedScale (Real.log n)) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + (12 / 25 : ℝ) := by
  exact
    gamma_refined_odd_conductor_square_and_dyadic_cost_le hn hodd hf hm S hS χ hχ hχ2 K K2
      (gamma_refined_log_range_of_decimal hlarge)

end PseudoPrime.Analysis
