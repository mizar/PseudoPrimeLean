/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaOddPrimePowerCosts
public import PseudoPrime.Analysis.ExponentialRampLocalSeries

/-! # Actual signed ramp corrections combined with Gamma prime costs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At a positive power with local value zero, the actual signed ramp
correction is at most one copy of the ramp weight. The inequality W<=exp(-u)
proves this for every real u. This is the sharper ramified local comparison. -/
theorem exponentialRampLocalCorrection_zero_le_weight (u : ℝ) {k : ℕ} (hk : 0 < k) :
    exponentialRampLocalCorrection 0 u k ≤ exponentialRampWeight u := by
  simp only [exponentialRampLocalCorrection, zero_pow hk.ne', add_zero, Complex.one_re, one_mul]
  linarith only [(exponentialRampWeight_bounds u).2]

/-- Number of positive powers retained by the actual ramp cutoff at scale x.
The cutoff is (99/40)x. This natural-floor count gives a uniform bound for
ramified primes and, with one extra unit, for the minus-one local value. -/
noncomputable def gammaRampPowerCount (p : ℕ) (x : ℝ) : ℝ :=
  (⌊Real.log ((99 / 40 : ℝ) * x) / Real.log p⌋₊ : ℝ)

/-- The actual normalized ramified ramp series is bounded by its cutoff count
divided by sqrt x for p>1 and x>0. Specialize the proved signed local series
bound at zero before dividing by the nonnegative scale factor. -/
theorem gamma_ramp_zero_series_le_count {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x ≤
      gammaRampPowerCount p x / Real.sqrt x := by
  have h := exponentialRamp_prime_power_correction_le_count (c := (0 : ℂ)) (Or.inl rfl) hp hx
  norm_num only at h
  simp only [ite_false, add_zero] at h
  exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg x)

/-- For local value minus one, the actual normalized signed ramp series is
bounded by the cutoff count plus one, divided by sqrt x. The existing parity
count retains nonpositive even powers and the cutoff tail. This supplies the
ramp part to combine with twice the odd Euler cost. -/
theorem gamma_ramp_neg_one_series_le_count {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) :
    (∑' k : ℕ, exponentialRampLocalCorrection (-1) ((p : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x ≤
      (gammaRampPowerCount p x + 1) / Real.sqrt x := by
  have h :=
    exponentialRamp_prime_power_correction_le_count (c := (-1 : ℂ)) (Or.inr (Or.inr rfl)) hp hx
  rw [ite_eq_left rfl] at h
  exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg x)

/-- Per-log-prime upper allowance for ramified Euler and actual signed ramp
losses at positive scale. The Euler cost retains all signed resolvent nodes;
the ramp count retains the actual cutoff. Used in the common conductor budget. -/
noncomputable def gammaRamifiedCombinedCost (p : ℕ) (x : ℝ) : ℝ :=
  gammaPrimeEulerCost p + gammaRampPowerCount p x / Real.sqrt x

/-- Per-log-prime upper allowance for character value minus one. Twice the
exact odd Euler cost is combined with the signed ramp count plus one. This
is the local cost to compare against the square-part conductor gap. -/
noncomputable def gammaSquareCombinedCost (p : ℕ) (x : ℝ) : ℝ :=
  2 * gammaPrimeOddEulerCost p + (gammaRampPowerCount p x + 1) / Real.sqrt x

/-- For a prime and positive scale, the actual finite Euler powers plus the
full signed ramified ramp series are bounded by log p times the combined
ramified allowance. Use the exact Euler cost and the actual ramp count bound
before applying a conductor budget. -/
theorem gamma_ramified_actual_prime_cost_le {p : ℕ} (hp : p.Prime) (K : Finset ℕ) {x : ℝ}
    (hx : 0 < x) :
    (∑ k ∈ K, gammaResolventMangoldtWeight (p ^ (k + 1))) +
        Real.log p *
          ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
            Real.sqrt x) ≤
      Real.log p * gammaRamifiedCombinedCost p x := by
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have he := sum_gammaResolventMangoldtWeight_primePowers_le_cost hp K
  have hr := mul_le_mul_of_nonneg_left (gamma_ramp_zero_series_le_count hp.one_lt hx) hl
  dsimp only [gammaRamifiedCombinedCost]
  rw [mul_add]
  exact add_le_add he hr

/-- For a prime with character value minus one and positive scale, the actual
finite odd-power Euler correction and full signed ramp correction are bounded
by log p times the square-part allowance. Even ramp powers remain nonpositive
in the underlying series estimate. This is the combined local square loss. -/
theorem gamma_minus_one_actual_prime_cost_le {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime)
    (hχ : χ p = -1) (K : Finset ℕ) {x : ℝ} (hx : 0 < x) :
    (∑ k ∈ K, (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) +
        Real.log p *
          ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
            Real.sqrt x) ≤
      Real.log p * gammaSquareCombinedCost p x := by
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have he := gamma_minus_one_odd_prime_correction_le_cost χ hp hχ K
  have hr := mul_le_mul_of_nonneg_left (gamma_ramp_neg_one_series_le_count hp.one_lt hx) hl
  have h := add_le_add he hr
  dsimp only [gammaSquareCombinedCost]
  nlinarith only [h]

/-- Actual finite ramified Euler prefixes and full signed ramp series share
one conductor logarithmic budget on any subset of conductor primes.
The arithmetic budget and the actual per-prime comparison discharge both
abstract premises. This is the joint local interface for the final witness bound. -/
theorem gamma_ramified_actual_cost_le_conductor_dual_cap {q : ℕ} (hq : 0 < q) (S : Finset ℕ)
    (hS : S ⊆ q.primeFactors) (K : ℕ → Finset ℕ) {x μ : ℝ} (hx : 0 < x) (hμ : 0 ≤ μ) :
    (∑ p ∈ S,
        ((∑ k ∈ K p, gammaResolventMangoldtWeight (p ^ (k + 1))) +
          Real.log p *
            ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
              Real.sqrt x))) ≤
      μ * Real.log q + ∑ p ∈ S, Real.log p * max (gammaRamifiedCombinedCost p x - μ) 0 := by
  have hpoint :=
    Finset.sum_le_sum
      (fun p hp ↦
        gamma_ramified_actual_prime_cost_le (Nat.prime_of_mem_primeFactors (hS hp)) (K p) hx)
  have hlog (p : ℕ) (hp : p ∈ S) : 0 ≤ Real.log p :=
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors (hS hp)).one_le)
  exact
    hpoint.trans
      (ramified_cost_le_dual_cap S (fun p ↦ Real.log p) (fun p ↦ gammaRamifiedCombinedCost p x) hμ
        hlog (gamma_conductor_subset_log_budget hq S hS))

end PseudoPrime.Analysis
