/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorSquareFactorCost
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.UntaperedPrimeCostBounds

/-! # Analytic prime-by-prime bounds for untapered endpoint costs -/

@[expose] public section

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
