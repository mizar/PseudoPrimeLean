/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64OddEulerBounds
public import PseudoPrime.Analysis.OddRampSmallScale
public import PseudoPrime.Analysis.Phase64FirstCellLocalBounds

/-! # Phase-candidate square-part and dyadic conductor absorption -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For every prime at least three, local value minus one, arbitrary finite
positive-power prefix and scale at least 1600, the actual phase cost is at most
227/250 times log p. Combine the signed odd Euler and continuous ramp certificates. -/
theorem phase64_actual_odd_minus_one_cost_le {f p : ℕ} (χ : DirichletCharacter ℂ f) (hp : p.Prime)
    (hp3 : 3 ≤ p) (hχ : χ p = -1) (K : Finset ℕ) {x : ℝ} (hx : 1600 ≤ x) :
    finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p K x ≤
      (227 / 250 : ℝ) * Real.log p := by
  have he :=
    finiteSigned_minus_one_positive_prefix_le_cost χ hp hχ phaseResolvent64Coefficients
      phase64_node_exponents_pos (fun u hu ↦ phaseResolvent64_euler_nonneg hu) K
  have hr := gamma_ramp_neg_one_series_le_count hp.one_lt (by linarith only [hx] : 0 < x)
  have hrc := hr.trans (odd_ramp_count_le_of_ge_1600 hp3 hx)
  have hl := Real.log_natCast_nonneg p
  have hw := mul_le_mul_of_nonneg_left hrc hl
  have hec := mul_le_mul_of_nonneg_left (phase64_odd_euler_cost_uniform hp hp3) hl
  dsimp only [finiteSignedActualPrimeLocalCost]
  rw [hχ]
  nlinarith only [he, hw, hec]

/-- The odd minus-one local cost is at most twice the phase coefficient mass
times log p at all scales at least 1600. The rational local allowance has strict
slack below twice the mass; nonnegativity of log p transfers the comparison. -/
theorem phase64_actual_odd_minus_one_cost_le_mass {f p : ℕ} (χ : DirichletCharacter ℂ f)
    (hp : p.Prime) (hp3 : 3 ≤ p) (hχ : χ p = -1) (K : Finset ℕ) {x : ℝ} (hx : 1600 ≤ x) :
    finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p K x ≤
      2 * (90992831 / 200000000 : ℝ) * Real.log p := by
  have h := phase64_actual_odd_minus_one_cost_le χ hp hp3 hχ K hx
  have hl := Real.log_natCast_nonneg p
  nlinarith only [h, hl]

/-- For any subset of an odd input's prime factors with character value minus
one, sum the phase local costs within twice the coefficient mass times their
logarithmic weight. Oddness excludes the separately budgeted prime two. -/
theorem phase64_actual_square_sum_le {n f : ℕ} (hn : Odd n) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) {x : ℝ}
    (hx : 1600 ≤ x) :
    (∑ p ∈ S, finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p (K p) x) ≤
      (∑ p ∈ S, Real.log p) * (2 * (90992831 / 200000000 : ℝ)) := by
  have hpoint :=
    Finset.sum_le_sum
      (fun p hp ↦
        phase64_actual_odd_minus_one_cost_le_mass χ (Nat.prime_of_mem_primeFactors (hS hp))
          (by
            have hpne : p ≠ 2 := fun he ↦
              hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors (hS hp))
            exact
              Nat.succ_le_iff.mpr
                (lt_of_le_of_ne (Nat.prime_of_mem_primeFactors (hS hp)).two_le (Ne.symm hpne)))
          (hχ p hp) (K p) hx)
  simpa only [Finset.sum_mul, mul_comm (2 * (90992831 / 200000000 : ℝ))] using hpoint

/-- For odd n=f*m^2, omitted minus-one prime losses are absorbed by the gap
M(log n-log f), at every scale at least 1600. The square-part logarithmic
budget and certified local estimates leave log four unspent. -/
theorem phase64_actual_square_cost_absorbed {n f m : ℕ} (hn : n = f * m ^ 2) (hodd : Odd n)
    (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f)
    (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) {x : ℝ} (hx : 1600 ≤ x) :
    (90992831 / 200000000 : ℝ) * Real.log f +
        (∑ p ∈ S, finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p (K p) x) ≤
      (90992831 / 200000000 : ℝ) * Real.log n := by
  have hs := phase64_actual_square_sum_le hodd S hS χ hχ K hx
  have hg :=
    gamma_odd_conductor_square_log_budget hn hf hm S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 90992831 / 200000000)
  nlinarith only [hs, hw]

/-- For odd conductor data n=f*m^2 and dyadic value one or minus one, the
square-prime and dyadic costs fit M log(4n)+473/1000 at scale at least 1600.
Spend the square gap and log-four allowance separately, without double counting. -/
theorem phase64_actual_square_dyadic_cost_le {n f m : ℕ} (hn : n = f * m ^ 2) (hodd : Odd n)
    (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f)
    (hχ : ∀ p ∈ S, χ p = -1) (hχ2 : χ 2 = 1 ∨ χ 2 = -1) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x : ℝ}
    (hx : 1600 ≤ x) :
    (90992831 / 200000000 : ℝ) * Real.log f +
        (∑ p ∈ S, finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p (K p) x) +
        finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K2 x ≤
      (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) + (473 / 1000 : ℝ) := by
  have hs := phase64_actual_square_cost_absorbed hn hodd hf hm S hS χ hχ K hx
  have hd :
    finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K2 x -
        (90992831 / 200000000 : ℝ) * Real.log 4 ≤
      (473 / 1000 : ℝ) := by
    rcases hχ2 with h2 | h2
    · have h :=
        finiteSigned_actual_one_prime_cost_nonpos phaseResolvent64Coefficients χ Nat.prime_two
          (by simpa only [Nat.cast_ofNat] using h2) K2 (by linarith only [hx] : 0 < x)
      have hl : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num only)
      nlinarith only [h, hl]
    · exact phase64_actual_dyadic_minus_one_cost_le χ h2 K2 hx
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hn ▸ Nat.mul_pos hf (pow_pos hm 2)).ne'
  rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hn0]
  linarith only [hs, hd]

/-- On the certified level cell 64 to 64.001, the odd-conductor square and
dyadic budget applies to the actual phase scale. The proved scale lower bound
is above 1600, so no integer or scale enumeration is needed. -/
theorem phase64_first_cell_square_dyadic_cost_le {n f m : ℕ} (hn : n = f * m ^ 2) (hodd : Odd n)
    (hf : 0 < f) (hm : 0 < m) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f)
    (hχ : ∀ p ∈ S, χ p = -1) (hχ2 : χ 2 = 1 ∨ χ 2 = -1) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {L : ℝ}
    (hlo : 64 ≤ L) (hhi : L ≤ 64001 / 1000) :
    (90992831 / 200000000 : ℝ) * Real.log f +
        (∑ p ∈ S,
          finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p (K p)
            (L ^ 2 / (99 / 40))) +
        finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K2 (L ^ 2 / (99 / 40)) ≤
      (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) + (473 / 1000 : ℝ) := by
  exact
    phase64_actual_square_dyadic_cost_le hn hodd hf hm S hS χ hχ hχ2 K K2
      ((by norm_num only : (1600 : ℝ) ≤ 163840 / 99).trans (scale64_cell_of_level hlo hhi).1)

/-- For n=d*m^2 odd, d dividing the positive conductor f and f at most 4d,
the omitted minus-one local costs fit M(log(4n)-log f) at scale at least 1600.
This is the conductor-gap interface for the even branch. -/
theorem phase64_actual_square_cost_absorbed_by_gap {n d m f : ℕ} (hn : n = d * m ^ 2) (hodd : Odd n)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 1600 ≤ x) :
    (90992831 / 200000000 : ℝ) * Real.log f +
        (∑ p ∈ S, finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p (K p) x) ≤
      (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) := by
  have hs := phase64_actual_square_sum_le hodd S hS χ hχ K hx
  have hg :=
    gamma_square_only_prime_log_gap_budget hn hd hm hf hdf hfd S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 90992831 / 200000000)
  nlinarith only [hs, hw]

/-- For even conductor data f, the square-prime and dyadic phase costs fit
M log(4n)+427/500 at scale at least 1600. The dyadic character value is zero;
combine its certified local allowance with the square-part gap once. -/
theorem phase64_actual_even_square_dyadic_cost_le {n d m f : ℕ} (hn : n = d * m ^ 2) (hodd : Odd n)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (heven : Even f)
    (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x : ℝ} (hx : 1600 ≤ x) :
    (90992831 / 200000000 : ℝ) * Real.log f +
        (∑ p ∈ S, finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p (K p) x) +
        finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K2 x ≤
      (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) + (427 / 500 : ℝ) := by
  have hs := phase64_actual_square_cost_absorbed_by_gap hn hodd hd hm hf hdf hfd S hS χ hχ K hx
  have ht :=
    phase64_actual_dyadic_zero_cost_le χ (gamma_even_modulus_character_two_zero χ heven) K2 hx
  linarith only [hs, ht]

/-- Both actual conductor parity branches obey the common phase allowance
M log(4n)+427/500 at scales at least 1600. The odd branch retains the stronger
473/1000 allowance, while the even branch supplies the common cap. -/
theorem phase64_actual_all_square_dyadic_cost_le {n d m f : ℕ} (hn : n = d * m ^ 2) (hodd : Odd n)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d)
    (χ : DirichletCharacter ℂ f) (hbranch : (f = d ∧ (χ 2 = 1 ∨ χ 2 = -1)) ∨ Even f) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x : ℝ}
    (hx : 1600 ≤ x) :
    (90992831 / 200000000 : ℝ) * Real.log f +
        (∑ p ∈ S, finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ p (K p) x) +
        finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K2 x ≤
      (90992831 / 200000000 : ℝ) * Real.log (4 * (n : ℝ)) + (427 / 500 : ℝ) := by
  rcases hbranch with ⟨rfl, h2⟩ | he
  · have h := phase64_actual_square_dyadic_cost_le hn hodd hd hm S hS χ hχ h2 K K2 hx
    linarith only [h]
  · exact phase64_actual_even_square_dyadic_cost_le hn hodd hd hm hf hdf hfd he S hS χ hχ K K2 hx

end PseudoPrime.Analysis
