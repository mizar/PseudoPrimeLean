/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessCutoff

/-! # Integer multiplication certificates for Gaussian cutoffs -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A seven-term integer Taylor certificate and a cleared-denominator comparison
certify the squared cutoff at scale `u/v` for every logarithm above `m/d`. -/
theorem gaussian_cutoff_of_mul_cert {m d u v Q : ℕ} (T : ℕ → ℕ) (hd : 0 < d) (hv : 0 < v)
    (hQ : 0 < Q) (hzero : T 0 = Q)
    (hstep : ∀ j < 6, (11000 * d) ^ 2 * (j + 1) * T (j + 1) ≤ m ^ 2 * T j)
    (hcmp :
      u ^ 2 * 33659 * m * (∑ j ∈ Finset.range 7, T j) + 53 * 33659 * v ^ 2 * d * Q ≤
        36360 * v ^ 2 * m * (∑ j ∈ Finset.range 7, T j))
    {L : ℝ} (ha : 663 ≤ (m : ℝ) / d) (hL : (m : ℝ) / d ≤ L) :
    (((u : ℝ) / v) * L / 2) ^ 2 ≤ gaussianWitnessCutoff L := by
  let S := ∑ j ∈ Finset.range 7, T j
  have hS : 0 < (S : ℝ) :=
    Nat.cast_pos.mpr
      (hQ.trans_le
        (by
          rw [← hzero]
          exact
            Finset.single_le_sum (fun j _ ↦ Nat.zero_le (T j)) (by decide : 0 ∈ Finset.range 7)))
  have hdp : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hvp : 0 < (v : ℝ) := Nat.cast_pos.mpr hv
  have hap : 0 < (m : ℝ) / d := (by norm_num only : (0 : ℝ) < 663).trans_le ha
  have hmp : 0 < (m : ℝ) := (div_pos_iff_of_pos_right hdp).mp hap
  have hT :=
    Analysis.exp_mul_cert_sum_le (m ^ 2) ((11000 * d) ^ 2) Q 6 T
      (pow_pos (Nat.mul_pos (by decide) hd) 2) hzero hstep
  have harg : (↑(m ^ 2) : ℝ) / ↑((11000 * d) ^ 2 : ℕ) = ((m : ℝ) / d / 11000) ^ 2 := by
    push_cast
    rw [← div_pow, div_div, mul_comm (11000 : ℝ)]
  rw [harg] at hT
  have he : Real.exp (-((m : ℝ) / d / 11000) ^ 2) ≤ (Q : ℝ) / S := by
    rw [Real.exp_neg]
    apply (le_div_iff₀ hS).mpr
    rw [← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos _)]
    exact hT
  apply
    gaussianCell_cutoff_le (c := ((u : ℝ) / v) ^ 2 / 4) ha hL he _
      (by
        ring_nf; exact le_rfl)
  have hc :
    (u : ℝ) ^ 2 * 33659 * m * S + 53 * 33659 * (v : ℝ) ^ 2 * d * Q ≤
      36360 * (v : ℝ) ^ 2 * m * S := by
    exact_mod_cast hcmp
  field_simp [hdp.ne', hvp.ne', hmp.ne', hS.ne']
  nlinarith only [hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
