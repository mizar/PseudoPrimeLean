/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedWindowTransport
public import PseudoPrime.Analysis.GammaLocalPrimeRows
public import PseudoPrime.Analysis.GammaEnvelopePrimeRows

/-! # Existing checked rows bound the full signed endpoint numerator -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: p>1, positive endpoints and a natural power cutoff above the ramp.
Claim: the full signed window numerator is bounded by the finite mixed prefix
minus theta. Sum the convergent endpoint series and discard only its negative
tail. Role: reuse existing rational prefix certificates for window transport. -/
theorem gamma_ramified_window_numerator_le_natural_prefix {p m : ℕ} (hp : 1 < p) {lo hi θ : ℝ}
    (hlo : 0 < lo) (hhi : 0 < hi) (hcut : (99 / 40 : ℝ) * hi ≤ (p : ℝ) ^ (m + 1)) :
    gammaRamifiedWindowNumerator p lo hi θ ≤
      (∑ k ∈ Finset.range m,
          (2 * exponentialRampWeight ((p : ℝ) ^ (k + 1) / hi) -
            Real.exp (-((p : ℝ) ^ (k + 1) / lo)))) -
        θ := by
  have hsh :=
    summable_exponentialRampLocalCorrection (c := (0 : ℂ)) (Or.inl rfl) hhi _
      (prime_power_div_scale_ge_linear hp hhi)
  have heh := summable_exp_neg_of_linear_lower hhi _ (prime_power_div_scale_ge_linear hp hhi)
  have hel := summable_exp_neg_of_linear_lower hlo _ (prime_power_div_scale_ge_linear hp hlo)
  let F := fun k : ℕ ↦
    exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / hi) (k + 1) +
        Real.exp (-((p : ℝ) ^ (k + 1) / hi)) -
      Real.exp (-((p : ℝ) ^ (k + 1) / lo))
  have hs : Summable F := (hsh.add heh).sub hel
  have heq := hs.sum_add_tsum_nat_add m
  have ht : (∑' k : ℕ, F (k + m)) ≤ 0 := by
    apply tsum_nonpos
    intro k
    have hh := gamma_prime_power_tail_of_natural_cutoff hp hhi hcut (Nat.le_add_left m k)
    dsimp only [F, exponentialRampLocalCorrection]
    simp only [zero_pow (Nat.succ_ne_zero _), add_zero, Complex.one_re, one_mul,
      exponentialRampWeight_eq_zero hh, mul_zero, zero_sub, neg_add_cancel, zero_sub]
    exact neg_nonpos.mpr (Real.exp_pos _).le
  have hall :
    (∑' k : ℕ, F k) =
      gammaRamifiedRampMass p hi + gammaPrimeExponentialMass p hi -
        gammaPrimeExponentialMass p lo := by
    exact
      ((hsh.add heh).tsum_sub hel).trans
        (congrArg (fun a : ℝ ↦ a - gammaPrimeExponentialMass p lo) (hsh.tsum_add heh))
  have hprefix :
    (∑ k ∈ Finset.range m, F k) =
      ∑ k ∈ Finset.range m,
        (2 * exponentialRampWeight ((p : ℝ) ^ (k + 1) / hi) -
          Real.exp (-((p : ℝ) ^ (k + 1) / lo))) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [F, exponentialRampLocalCorrection]
    simp only [zero_pow (Nat.succ_ne_zero _), add_zero, Complex.one_re, one_mul, sub_add_cancel]
  rw [hall, hprefix] at heq
  dsimp only [gammaRamifiedWindowNumerator]
  linarith only [heq, ht]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a checked cell and an envelope-checked prime row, with arbitrary
theta. Claim: the existing ramp endpoint bounds the full signed window
numerator minus theta. Reuse the natural tail cutoff and rational prefix.
Role: support adaptive Euler envelopes without new per-prime power data. -/
theorem GammaLocalPrimeRow.window_numerator_le_of_envelope (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime)
    (hc : r.envelopeCheck c = true) (θ : ℝ) :
    gammaRamifiedWindowNumerator r.prime c.lo c.hi θ ≤ (r.rampUpper : ℝ) - θ := by
  obtain ⟨hlo, hlohi, hslo, hrootlo, hshi, hroothi, htheta⟩ := c.check_sound hcell
  obtain ⟨hlog, hnum⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hcut, hsize, hr, hcost, hex⟩ := of_decide_eq_true hnum
  have hcutR := (Rat.cast_le (K := ℝ)).mpr hcut
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast] at hcutR
  have hs :=
    gamma_ramified_window_numerator_le_natural_prefix hp.one_lt hlo (hlo.trans_le hlohi) (θ := θ)
      hcutR
  have hP :=
    gamma_signed_ramp_prefix_upper_valid r.prime r.powers ((Rat.cast_pos (K := ℝ)).mp hlo)
      ((Rat.cast_pos (K := ℝ)).mp (hlo.trans_le hlohi)) r.expTerms hsize
  exact hs.trans (sub_le_sub_right (hP.trans ((Rat.cast_le (K := ℝ)).mpr hr)) θ)

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a checked local row and cell, a prime base and any theta.
Claim: its existing Euler and ramp endpoints bound the full Euler cost and
signed window numerator. Reuse the checked finite prefix and tail condition.
Role: supply the window interface without generating new numerical data. -/
theorem GammaLocalPrimeRow.window_bounds (r : GammaLocalPrimeRow) (c : GammaLocalCellData)
    (hcell : c.check = true) (hp : r.prime.Prime) (hc : r.check c = true) (θ : ℝ) :
    gammaPrimeEulerCost r.prime ≤ (r.eulerUpper : ℝ) ∧
      gammaRamifiedWindowNumerator r.prime c.lo c.hi θ ≤ (r.rampUpper : ℝ) - θ := by
  obtain ⟨hlo, hlohi, hslo, hrootlo, hshi, hroothi, htheta⟩ := c.check_sound hcell
  obtain ⟨hab, hnum⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hlog, hEuler⟩ := Bool.and_eq_true_iff.mp hab
  obtain ⟨he, hcut, hsize, hr, hcost, hex⟩ := of_decide_eq_true hnum
  have hE := (gamma_prime_euler_interval_check_sound hEuler).2.trans ((Rat.cast_le (K := ℝ)).mpr he)
  norm_num only [Rat.cast_natCast] at hE
  have hcutR := (Rat.cast_le (K := ℝ)).mpr hcut
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast] at hcutR
  have hs :=
    gamma_ramified_window_numerator_le_natural_prefix hp.one_lt hlo (hlo.trans_le hlohi) (θ := θ)
      hcutR
  have hP :=
    gamma_signed_ramp_prefix_upper_valid r.prime r.powers ((Rat.cast_pos (K := ℝ)).mp hlo)
      ((Rat.cast_pos (K := ℝ)).mp (hlo.trans_le hlohi)) r.expTerms hsize
  exact ⟨hE, hs.trans (sub_le_sub_right (hP.trans ((Rat.cast_le (K := ℝ)).mpr hr)) θ)⟩

end PseudoPrime.Analysis
