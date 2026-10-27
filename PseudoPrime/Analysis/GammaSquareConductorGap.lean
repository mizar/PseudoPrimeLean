/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRampPrimeCosts

/-! # Square-part prime costs and the ambient conductor gap -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If n=d*m^2 and d divides the primitive conductor f, a prime dividing n
but not f must divide m. Primality splits the product and removes the square
exponent. This places the omitted ambient primes in the square-part budget. -/
theorem gamma_square_only_prime_dvd_part {n d m f p : ℕ} (hn : n = d * m ^ 2) (hdf : d ∣ f)
    (hp : p.Prime) (hpn : p ∣ n) (hpf : ¬p ∣ f) : p ∣ m := by
  rw [hn] at hpn
  rcases hp.dvd_mul.mp hpn with hd | hm
  · exact False.elim (hpf (dvd_trans hd hdf))
  · exact hp.dvd_of_dvd_pow hm

/-- For n=d*m^2, positive d,m,f and f<=4d, twice the logarithmic weight
of any subset of square-part primes is at most log(4n)-log f. The square
factor gives twice log m, and monotonicity bounds log f by log(4d).
This is the arithmetic allowance for absorbing square-only local losses. -/
theorem gamma_square_part_log_gap_budget {n d m f : ℕ} (hn : n = d * m ^ 2) (hd : 0 < d)
    (hm : 0 < m) (hf : 0 < f) (hfd : f ≤ 4 * d) (S : Finset ℕ) (hS : S ⊆ m.primeFactors) :
    2 * (∑ p ∈ S, Real.log p) ≤ Real.log (4 * (n : ℝ)) - Real.log f := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hlog := Real.log_le_log hfR (by exact_mod_cast hfd : (f : ℝ) ≤ 4 * (d : ℝ))
  have hsum := gamma_conductor_subset_log_budget hm S hS
  have he : Real.log (4 * (n : ℝ)) = Real.log (4 * (d : ℝ)) + 2 * Real.log m := by
    rw [hn, Nat.cast_mul, Nat.cast_pow, ← mul_assoc,
      Real.log_mul (mul_ne_zero (by norm_num only : (4 : ℝ) ≠ 0) hdR.ne') (pow_ne_zero 2 hmR.ne'),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  linarith only [hlog, hsum, he]

/-- Primes dividing the ambient input but omitted by the primitive conductor
obey twice the logarithmic conductor-gap budget when n=d*m^2, d divides f
and f<=4d. Place those primes in the square part and apply the proved budget.
This discharges the arithmetic premise of the square-prime absorption step. -/
theorem gamma_square_only_prime_log_gap_budget {n d m f : ℕ} (hn : n = d * m ^ 2) (hd : 0 < d)
    (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (homit : ∀ p ∈ S, ¬p ∣ f) :
    2 * (∑ p ∈ S, Real.log p) ≤ Real.log (4 * (n : ℝ)) - Real.log f := by
  have hpart : S ⊆ m.primeFactors := by
    intro p hp
    have hnprime := hS hp
    have hprime := Nat.prime_of_mem_primeFactors hnprime
    exact
      Nat.mem_primeFactors.mpr
        ⟨hprime,
          gamma_square_only_prime_dvd_part hn hdf hprime (Nat.dvd_of_mem_primeFactors hnprime)
            (homit p hp),
          hm.ne'⟩
  exact gamma_square_part_log_gap_budget hn hd hm hf hfd S hpart

/-- If the combined square-prime allowance is at most 2M at every omitted
prime, the actual Euler and ramp losses are absorbed by the change from
M log f to M log(4n). The arithmetic gap is proved from n=d*m^2, d|f and f<=4d.
The explicit per-prime numerical bound remains a separate required input. -/
theorem gamma_square_actual_cost_absorbed_by_conductor_gap {n d m f : ℕ} (hn : n = d * m ^ 2)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (homit : ∀ p ∈ S, ¬p ∣ f) (χ : DirichletCharacter ℂ f)
    (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) {x M : ℝ} (hx : 0 < x) (hM : 0 ≤ M)
    (hcost : ∀ p ∈ S, gammaSquareCombinedCost p x ≤ 2 * M) :
    M * Real.log f +
        (∑ p ∈ S,
          ((∑ k ∈ K p,
              (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) +
            Real.log p *
              ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
                Real.sqrt x))) ≤
      M * Real.log (4 * (n : ℝ)) := by
  have hpoint :=
    Finset.sum_le_sum
      (fun p hp ↦
        (gamma_minus_one_actual_prime_cost_le χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp)
              (K p) hx).trans
          (mul_le_mul_of_nonneg_left (hcost p hp)
            (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors (hS hp)).one_le))))
  rw [← Finset.sum_mul] at hpoint
  have hgap := gamma_square_only_prime_log_gap_budget hn hd hm hf hdf hfd S hS homit
  have hweighted := mul_le_mul_of_nonneg_left hgap hM
  nlinarith only [hpoint, hweighted]

/-- A character taking value minus one at a prime cannot have that prime
divide its modulus. Otherwise the character vanishes at the resulting nonunit.
This removes the omitted-prime premise from the actual square-loss interface. -/
theorem gamma_minus_one_prime_not_dvd_modulus {f p : ℕ} (χ : DirichletCharacter ℂ f) (hp : p.Prime)
    (hχ : χ p = -1) : ¬p ∣ f := by
  intro hpf
  have hnu : ¬IsUnit (p : ZMod f) := by
    simpa only [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp, not_not] using hpf
  have hz := χ.map_nonunit hnu
  rw [hχ] at hz
  norm_num only at hz

/-- Character value minus one implies that each selected prime is absent from the
modulus. Apply the arithmetic conductor-gap absorption without an additional
omitted-prime hypothesis. The quantitative combined-cost bound is still required. -/
theorem gamma_minus_one_actual_cost_absorbed_by_conductor_gap {n d m f : ℕ} (hn : n = d * m ^ 2)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x M : ℝ} (hx : 0 < x) (hM : 0 ≤ M)
    (hcost : ∀ p ∈ S, gammaSquareCombinedCost p x ≤ 2 * M) :
    M * Real.log f +
        (∑ p ∈ S,
          ((∑ k ∈ K p,
              (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) +
            Real.log p *
              ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
                Real.sqrt x))) ≤
      M * Real.log (4 * (n : ℝ)) := by
  exact
    gamma_square_actual_cost_absorbed_by_conductor_gap hn hd hm hf hdf hfd S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
      χ hχ K hx hM hcost

/-- For x at least one, the cutoff count is bounded by its real logarithmic
quotient. Positivity of both logarithms permits the natural-floor inequality.
This removes the discrete cutoff from quantitative scale estimates. -/
theorem gamma_ramp_count_le_log {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x) :
    gammaRampPowerCount p x ≤ Real.log ((99 / 40 : ℝ) * x) / Real.log p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hcut : (1 : ℝ) ≤ (99 / 40 : ℝ) * x := by nlinarith only [hx]
  exact Nat.floor_le (div_nonneg (Real.log_nonneg hcut) (Real.log_nonneg hpR.le))

/-- The square-prime combined allowance is bounded by the exact odd Euler
cost plus a continuous logarithmic ramp allowance at every x at least one.
This prepares the numerical absorption bound while keeping the Euler signs. -/
theorem gamma_square_combined_cost_le_log {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x) :
    gammaSquareCombinedCost p x ≤
      2 * gammaPrimeOddEulerCost p +
        (Real.log ((99 / 40 : ℝ) * x) / Real.log p + 1) / Real.sqrt x := by
  exact
    add_le_add le_rfl
      (div_le_div_of_nonneg_right (add_le_add (gamma_ramp_count_le_log hp hx) le_rfl)
        (Real.sqrt_nonneg x))

end PseudoPrime.Analysis
