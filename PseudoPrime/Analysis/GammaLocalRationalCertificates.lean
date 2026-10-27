/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedRampCellBounds
public import PseudoPrime.Analysis.GammaExpRationalBounds
public import PseudoPrime.Analysis.GammaRationalRampCertificates
public import PseudoPrime.Analysis.GammaPrimeEulerIntervals

/-! # Rational signed local prefixes with certified natural cutoffs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If the next prime power is beyond the real cutoff, all powers from
that index onward have height at least the ramp endpoint. Compare natural
powers before dividing by the positive scale. This removes logarithmic floors
from the executable finite-prefix certificates. -/
theorem gamma_prime_power_tail_of_natural_cutoff {p N k : ℕ} (hp : 1 < p) {hi : ℝ} (hhi : 0 < hi)
    (hcut : (99 / 40 : ℝ) * hi ≤ (p : ℝ) ^ (N + 1)) (hk : N ≤ k) :
    99 / 40 ≤ (p : ℝ) ^ (k + 1) / hi := by
  have hpow : (p : ℝ) ^ (N + 1) ≤ (p : ℝ) ^ (k + 1) := by
    exact_mod_cast Nat.pow_le_pow_right (zero_lt_one.trans hp) (Nat.succ_le_succ hk)
  exact (le_div_iff₀ hhi).mpr (hcut.trans hpow)

/-- The actual signed ramified series on a positive closed scale cell
is bounded by a finite signed prefix of any certified natural length N.
The next-power inequality makes the omitted tail nonpositive.
This preserves signed cancellation without a logarithmic-floor computation. -/
theorem gamma_ramified_series_le_natural_cell_prefix {p N : ℕ} (hp : 1 < p) {x lo hi : ℝ}
    (hlo : 0 < lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) (hcut : (99 / 40 : ℝ) * hi ≤ (p : ℝ) ^ (N + 1)) :
    (∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x ≤
      max
          (∑ k ∈ Finset.range N,
            (2 * exponentialRampWeight ((p : ℝ) ^ (k + 1) / hi) -
              Real.exp (-((p : ℝ) ^ (k + 1) / lo))))
          0 /
        Real.sqrt lo := by
  have hx := hlo.trans_le hlox
  have hhi := hx.trans_le hxhi
  let u := fun k : ℕ ↦ (p : ℝ) ^ (k + 1) / x
  have ht : ∀ k, 99 / 40 ≤ u (k + N) := fun k ↦
    (gamma_prime_power_tail_of_natural_cutoff hp hhi hcut (Nat.le_add_left N k)).trans
      (div_le_div₀ (pow_nonneg (Nat.cast_nonneg p) _) le_rfl hx hxhi)
  have hs :=
    exponentialRampLocalCorrection_tsum_le_prefix (Or.inl rfl) hx u
      (prime_power_div_scale_ge_linear hp hx) N ht
  have hb :=
    Finset.sum_le_sum (s := Finset.range N)
      (fun k hk ↦
        gamma_ramified_local_term_le_signed_cell (pow_nonneg (Nat.cast_nonneg p) (k + 1)) hlo hlox
          hxhi (Nat.succ_pos k))
  have hm := (hs.trans hb).trans (le_max_left _ 0)
  exact
    (div_le_div_of_nonneg_right hm (Real.sqrt_nonneg x)).trans
      (div_le_div₀ (le_max_right _ _) le_rfl (Real.sqrt_pos.mpr hlo) (Real.sqrt_le_sqrt hlox))

/-- At a nonnegative rational height, the actual ramp is at most the
reciprocal positive Taylor upper bound times its exact rational ramp factor.
Use factor nonnegativity and the actual factor identity.
This gives the upper exponential side of the signed local interval. -/
theorem gamma_rational_ramp_upper_valid {t : ℚ} (ht : 0 ≤ t) :
    exponentialRampWeight (t : ℝ) ≤
      ((gammaExpTaylorUpper t * gammaRationalRampFactor t : ℚ) : ℝ) := by
  rw [exponentialRampWeight_eq_rational_factor, Rat.cast_mul]
  exact
    mul_le_mul_of_nonneg_right (gamma_exp_taylor_upper_valid ht)
      ((Rat.cast_nonneg (K := ℝ)).mpr (gamma_rational_ramp_factor_nonneg t))

/-- The rational signed prefix at prime p on cell [lo,hi].
Use the ramp upper envelope at hi and the exponential lower envelope
at lo in every retained power. The difference is kept before summation. -/
def gammaSignedRampPrefixUpper (p N : ℕ) (lo hi : ℚ) (terms : ℕ) : ℚ :=
  ∑ k ∈ Finset.range N,
    (2 *
        (gammaExpTaylorUpper ((p : ℚ) ^ (k + 1) / hi) *
          gammaRationalRampFactor ((p : ℚ) ^ (k + 1) / hi)) -
      gammaExpTaylorLower ((p : ℚ) ^ (k + 1) / lo) terms)

/-- Positive rational cell endpoints and the per-power Taylor tail
conditions make the signed rational prefix an upper bound on the real
finite prefix. Apply both one-sided exponential bounds and sum.
This is the numerical soundness interface for all local prime rows. -/
theorem gamma_signed_ramp_prefix_upper_valid (p N : ℕ) {lo hi : ℚ} (hlo : 0 < lo) (hhi : 0 < hi)
    (terms : ℕ) (hsize : ∀ k ∈ Finset.range N, ((p : ℚ) ^ (k + 1) / lo) / (terms + 1 : ℕ) ≤ 1 / 2) :
    (∑ k ∈ Finset.range N,
        (2 * exponentialRampWeight ((p : ℝ) ^ (k + 1) / (hi : ℝ)) -
          Real.exp (-((p : ℝ) ^ (k + 1) / (lo : ℝ))))) ≤
      (gammaSignedRampPrefixUpper p N lo hi terms : ℝ) := by
  simp only [gammaSignedRampPrefixUpper, Rat.cast_sum, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  apply Finset.sum_le_sum
  intro k hk
  have hu :=
    gamma_rational_ramp_upper_valid (div_nonneg (pow_nonneg (Nat.cast_nonneg p) (k + 1)) hhi.le)
  have hl :=
    gamma_exp_taylor_lower_valid (div_nonneg (pow_nonneg (Nat.cast_nonneg p) (k + 1)) hlo.le)
      (hsize k hk)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_mul] at hu hl
  linarith only [hu, hl]

end PseudoPrime.Analysis
