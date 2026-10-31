/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialTaylorCertificates

/-! # Positive exponential Taylor sums and endpoint transport -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The first n nonnegative exponential Taylor terms at rational height t.
For t at least zero the sum is a lower bound for exp(t). The rational value
is used to evaluate reserved prime-power rows at later rational scales. -/
def gammaPositiveTaylor (t : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, t ^ i / (i.factorial : ℚ)

/-- Input: a nonnegative rational height and any term count.
Claim: the rational Taylor polynomial is nonnegative.
Proof: each summand is nonnegative. This supplies the sign needed
when multiplying a certified lower exponential endpoint. -/
theorem gamma_positive_taylor_nonneg {t : ℚ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ gammaPositiveTaylor t n := by
  exact Finset.sum_nonneg (fun i _ ↦ div_nonneg (pow_nonneg ht i) (Nat.cast_nonneg i.factorial))

/-- Input: a nonnegative rational height and any term count.
Claim: the cast Taylor polynomial is at most the actual exponential.
Proof: cast the sum and use Real.sum_le_exp_of_nonneg.
This transfers the exact polynomial used in reserved rows to the real bound. -/
theorem gamma_positive_taylor_le_exp {t : ℚ} (ht : 0 ≤ t) (n : ℕ) :
    (gammaPositiveTaylor t n : ℝ) ≤ Real.exp (t : ℝ) := by
  simpa only [gammaPositiveTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using
    Real.sum_le_exp_of_nonneg ((Rat.cast_nonneg (K := ℝ)).mpr ht) n

/-- Input: a nonnegative endpoint below exp(-v/2).
Claim: its square is below exp(-v). Proof: multiply the endpoint bounds
and combine exponents. This supplies a reusable full-scale endpoint. -/
theorem gamma_exp_endpoint_square_le {v e : ℝ} (he : 0 ≤ e) (hev : e ≤ Real.exp (-v / 2)) :
    e ^ 2 ≤ Real.exp (-v) := by
  calc
    e ^ 2 ≤ Real.exp (-v / 2) * Real.exp (-v / 2) := by
      simpa only [pow_two] using mul_le_mul hev hev he (Real.exp_pos (-v / 2)).le
    _ = Real.exp (-v) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Input: u at most v and any lower endpoint e for exp(-v).
Claim: Taylor transport from v to u preserves the lower bound.
Proof: multiply the endpoint and Taylor bounds and combine exponents.
This separates transport from the choice of an endpoint certificate. -/
theorem gamma_exp_taylor_lower {u v e : ℝ} (huv : u ≤ v) (hev : e ≤ Real.exp (-v)) (n : ℕ) :
    e * (∑ i ∈ Finset.range n, (v - u) ^ i / (i.factorial : ℝ)) ≤ Real.exp (-u) := by
  have hp : 0 ≤ ∑ i ∈ Finset.range n, (v - u) ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg
      (fun i _ ↦ div_nonneg (pow_nonneg (sub_nonneg.mpr huv) i) (Nat.cast_nonneg i.factorial))
  calc
    _ ≤ Real.exp (-v) * Real.exp (v - u) :=
      mul_le_mul hev (Real.sum_le_exp_of_nonneg (sub_nonneg.mpr huv) n) hp (Real.exp_pos (-v)).le
    _ = Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Input: u at most v and a nonnegative endpoint e at most exp(-v/2).
Claim: e squared times the exponential Taylor sum at v-u bounds exp(-u).
Proof: square the endpoint, multiply the two exponential bounds,
and combine exponents. This lets one fixed half-scale row move to later scales. -/
theorem gamma_exp_square_taylor_lower {u v e : ℝ} (huv : u ≤ v) (he : 0 ≤ e)
    (hev : e ≤ Real.exp (-v / 2)) (n : ℕ) :
    e ^ 2 * (∑ i ∈ Finset.range n, (v - u) ^ i / (i.factorial : ℝ)) ≤ Real.exp (-u) := by
  exact gamma_exp_taylor_lower huv (gamma_exp_endpoint_square_le he hev) n

end PseudoPrime.Analysis
