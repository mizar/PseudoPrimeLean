/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorSquareFactorCost

/-! # Analytic prime-by-prime bounds for untapered endpoint costs -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The local quadratic prime cost is linear in the weight for arbitrary real
coefficients. Distribute the finite sum and its cutoff cases. This separates
the geometric reciprocal contribution from the logarithmic contribution. -/
theorem quadraticExcludedPrimeCost_linear_weight (q p : ℕ) (x : ℝ) (w v : ℕ → ℝ) (a b : ℝ) :
    quadraticExcludedPrimeCost q x (fun n ↦ a * w n + b * v n) p =
      a * quadraticExcludedPrimeCost q x w p + b * quadraticExcludedPrimeCost q x v p := by
  unfold quadraticExcludedPrimeCost
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hcut : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊
  · simp only [ite_eq_left hcut]
    ring
  · simp only [ite_eq_right hcut, mul_zero, add_zero]

/-- At a prime p and nonnegative cutoff, the conductor-zero local cost equals
the full prime-power-supported weight on indices divisible by p. Reuse the exact
prime-factor decomposition and note that an excluded index is not one.
This connects local costs to established common-factor logarithmic estimates. -/
theorem quadraticPrimeCost_zero_eq_common {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 0 ≤ x) (w : ℕ → ℝ)
    (hw : ∀ m : ℕ, ¬IsPrimePow m → w m = 0) :
    quadraticExcludedPrimeCost 0 x w p =
      ∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun m ↦ ¬Nat.Coprime m p), w m := by
  have hpf : p.primeFactors = {p} := by
    simpa only [pow_one] using Nat.primeFactors_prime_pow (by norm_num only : (1 : ℕ) ≠ 0) hp
  have hb := quadraticExcludedBudget_eq_sum_primeFactors hp.ne_zero 0 hx w hw
  rw [hpf, Finset.sum_singleton] at hb
  rw [← hb]
  apply Finset.sum_congr rfl
  intro m hm
  have hc : ¬Nat.Coprime m 0 := by
    intro h
    have he := (Nat.coprime_zero_right m).mp h
    subst m
    exact (Finset.mem_filter.mp hm).2 (Nat.coprime_one_left p)
  rw [ite_eq_right hc, one_mul]

/-- For a prime p and arbitrary cutoff, the conductor-zero untapered reciprocal
cost is at most log p/(p-1). Extend the nonnegative geometric terms beyond the
root cutoff and use the finite geometric bound. No finite input enumeration is used. -/
theorem quadraticPrimeCost_zero_reciprocal_le {p : ℕ} (hp : p.Prime) (x : ℝ) :
    quadraticExcludedPrimeCost 0 x (fun m ↦ ArithmeticFunction.vonMangoldt m / m) p ≤
      Real.log p / (p - 1) := by
  have hc : ¬Nat.Coprime p 0 := fun h ↦ hp.ne_one ((Nat.coprime_zero_right p).mp h)
  rw [quadraticExcludedPrimeCost_of_not_coprime hc]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, Real.log p / (p : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hcut : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊
      · rw [ite_eq_left hcut,
          ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1),
          ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]
      · rw [ite_eq_right hcut]
        exact
          div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_le))
            (pow_nonneg (Nat.cast_nonneg p) k)
    _ ≤ _ := sum_log_div_prime_pow_le hp

/-- For a prime p and positive cutoff, the conductor-zero logarithmic local
cost is at most half the logarithm square. Identify its common-factor sum and
specialize the existing prime-power estimate to the singleton prime support. -/
theorem quadraticPrimeCost_zero_logarithmic_le {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 0 < x) :
    quadraticExcludedPrimeCost 0 x (logWeightedMangoldtTerm x) p ≤ (Real.log x) ^ 2 / 2 := by
  rw [quadraticPrimeCost_zero_eq_common hp hx.le _
      (fun _ hn ↦ logWeightedMangoldtTerm_eq_zero_of_not_primePow hn)]
  change commonFactorLogWeightedSum x p ≤ _
  have h := commonFactorLogWeightedSum_le hp.ne_zero hx
  have hpf : p.primeFactors = {p} := by
    simpa only [pow_one] using Nat.primeFactors_prime_pow (by norm_num only : (1 : ℕ) ≠ 0) hp
  rw [hpf, Finset.card_singleton] at h
  norm_num only [Nat.cast_one, mul_one] at h
  linarith only [h]

/-- A prime power in the real root cutoff lies below x. Cast the floor bound
and use the inverse-power equivalence. This supplies positivity of local weights
without enumerating exponents or replacing the cutoff by a larger initial sum. -/
theorem prime_pow_le_of_root_cutoff {p k : ℕ} {x : ℝ} (hx : 0 ≤ x) (hk : 0 < k)
    (hcut : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊) : ((p ^ k : ℕ) : ℝ) ≤ x := by
  have hr := (Nat.cast_le.mpr hcut).trans (Nat.floor_le (Real.rpow_nonneg hx _))
  rw [one_div] at hr
  have h := (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) hx (Nat.cast_pos.mpr hk)).mp hr
  simpa only [Real.rpow_natCast, Nat.cast_pow] using h

/-- For a prime p, arbitrary conductor q and weights nonnegative at admissible
powers, the quadratic local cost is at most twice its conductor-zero cost.
The structural coefficient is at most two. The ramified branch can use coefficient
one separately; this lemma supplies an unconditional unramified envelope. -/
theorem quadraticPrimeCost_le_twice_zero {p : ℕ} (hp : p.Prime) (q : ℕ) (x : ℝ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ → 0 ≤ w (p ^ k)) :
    quadraticExcludedPrimeCost q x w p ≤ 2 * quadraticExcludedPrimeCost 0 x w p := by
  have hc : ¬Nat.Coprime p 0 := fun h ↦ hp.ne_one ((Nat.coprime_zero_right p).mp h)
  rw [quadraticExcludedPrimeCost_of_not_coprime hc, Finset.mul_sum]
  dsimp only [quadraticExcludedPrimeCost]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hcut : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊
  · simp only [ite_eq_left hcut]
    have hcoeff :
      (if Nat.Coprime (p ^ k) q then if IsSquare (p ^ k) then (0 : ℝ) else 2 else 1) ≤ 2 := by
      split_ifs <;> norm_num only
    exact mul_le_mul_of_nonneg_right hcoeff (hw k hk hcut)
  · simpa only [ite_eq_right hcut, mul_zero] using (le_rfl : (0 : ℝ) ≤ 0)

end PseudoPrime.AnalyticNumberTheory.Arithmetic

namespace PseudoPrime.LLS.PaperStatements

/-- The elementary principal prime-cost envelope:
A(x)*log p/(p-1)+(log x)^2/(2sqrt x). The first term bounds the untapered
geometric reciprocal prefix; the second bounds the logarithmic prefix.
Later results supply primality and x>1. -/
noncomputable def untaperedPrimeEnvelope (x : ℝ) (p : ℕ) : ℝ :=
  excludedReciprocalCoefficient x * (Real.log p / (p - 1)) + (Real.log x) ^ 2 / (2 * Real.sqrt x)

open AnalyticNumberTheory.Arithmetic in
/-- At x>1, the principal untapered local prime cost is bounded by the explicit
envelope. Use local weight linearity and the separate reciprocal and logarithmic
estimates with nonnegative multipliers. This is the analytic local-rate input. -/
theorem untaperedPrimeCost_zero_le_envelope {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 < x) :
    quadraticExcludedPrimeCost 0 x (untaperedExcludedEndpointWeight x) p ≤
      untaperedPrimeEnvelope x p := by
  change
    quadraticExcludedPrimeCost 0 x
        (fun m ↦
          excludedReciprocalCoefficient x * (ArithmeticFunction.vonMangoldt m / m) +
            (1 / Real.sqrt x) * logWeightedMangoldtTerm x m)
        p ≤
      _
  rw [quadraticExcludedPrimeCost_linear_weight]
  have hr :=
    mul_le_mul_of_nonneg_left (quadraticPrimeCost_zero_reciprocal_le hp x)
      (excludedReciprocalCoefficient_pos hx).le
  have hl :=
    mul_le_mul_of_nonneg_left (quadraticPrimeCost_zero_logarithmic_le hp (zero_lt_one.trans hx))
      (one_div_nonneg.mpr (Real.sqrt_nonneg x))
  have he : (1 / Real.sqrt x) * ((Real.log x) ^ 2 / 2) = (Real.log x) ^ 2 / (2 * Real.sqrt x) := by
    ring
  rw [he] at hl
  exact add_le_add hr hl

open AnalyticNumberTheory.Arithmetic in
/-- At a positive prime power in the cutoff, the untapered endpoint weight is
nonnegative. The root cutoff puts its index below x, so the logarithmic term
and the untapered reciprocal term are both nonnegative. -/
theorem untaperedEndpointWeight_nonneg_at_cutoff {p k : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 < x)
    (hk : 0 < k) (hcut : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊) :
    0 ≤ untaperedExcludedEndpointWeight x (p ^ k) := by
  have hx0 := zero_lt_one.trans hx
  have hpow := prime_pow_le_of_root_cutoff hx0.le hk hcut
  have hlog := logWeightedMangoldtTerm_nonneg hx0 (pow_pos hp.pos k) (Nat.le_floor hpow)
  dsimp only [untaperedExcludedEndpointWeight]
  exact
    add_nonneg
      (mul_nonneg (excludedReciprocalCoefficient_pos hx).le
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)))
      (mul_nonneg (one_div_nonneg.mpr (Real.sqrt_nonneg x)) hlog)

open AnalyticNumberTheory.Arithmetic in
/-- If p divides the conductor, its untapered local structural cost is at
most the principal envelope. Both the conductor and conductor-zero coefficients
are one on positive powers. This supplies the ramified rate without a hypothesis. -/
theorem untaperedPrimeCost_le_envelope_of_dvd {p : ℕ} (hp : p.Prime) (q : ℕ) (hpq : p ∣ q) {x : ℝ}
    (hx : 1 < x) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤
      untaperedPrimeEnvelope x p := by
  have hc : ¬Nat.Coprime p q := fun h ↦ (hp.coprime_iff_not_dvd.mp h) hpq
  have hc0 : ¬Nat.Coprime p 0 := fun h ↦ hp.ne_one ((Nat.coprime_zero_right p).mp h)
  rw [quadraticExcludedPrimeCost_of_not_coprime hc, ← quadraticExcludedPrimeCost_of_not_coprime hc0]
  exact untaperedPrimeCost_zero_le_envelope hp hx

open AnalyticNumberTheory.Arithmetic in
/-- For every prime p and conductor q at x>1, the untapered local structural
cost is at most twice the principal envelope. Use coefficient<=2 on admissible
powers and their nonnegative weights. This supplies the unramified envelope
without asserting any quadratic-character value. -/
theorem untaperedPrimeCost_le_twice_envelope {p : ℕ} (hp : p.Prime) (q : ℕ) {x : ℝ} (hx : 1 < x) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤
      2 * untaperedPrimeEnvelope x p := by
  have h :=
    quadraticPrimeCost_le_twice_zero hp q x (untaperedExcludedEndpointWeight x)
      (fun k hk hcut ↦ untaperedEndpointWeight_nonneg_at_cutoff hp hx (Finset.mem_Icc.mp hk).1 hcut)
  exact
    h.trans
      (mul_le_mul_of_nonneg_left (untaperedPrimeCost_zero_le_envelope hp hx)
        (by norm_num only : (0 : ℝ) ≤ 2))

end PseudoPrime.LLS.PaperStatements
