/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventDerivative
public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventInversion
public import PseudoPrime.AnalyticNumberTheory.General.ShiftedGammaBounds

/-!
# Shifted gamma-pole resolvents and their Mellin integrals
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- With Re κ ≥ 0 and σ ≥ 1, the nth shifted gamma pole has norm at least n+1.
Use its real part and the norm bound. This controls all power-weighted pole series. -/
theorem gammaPole_norm_lower {κ : ℂ} (hκ : 0 ≤ κ.re) {σ : ℝ} (hσ : 1 ≤ σ) (n : ℕ) :
    (n : ℝ) + 1 ≤ ‖-((σ : ℂ) + κ + 2 * (n : ℂ))‖ := by
  rw [norm_neg]
  have h := Complex.re_le_norm ((σ : ℂ) + κ + 2 * (n : ℂ))
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
    Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero] at h
  linarith only [h, hσ, hκ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- For Re κ ≥ 0, σ ≥ 1 and p > 1, the inverse-pth-power gamma pole norms are summable.
Compare the pole norm with n+1 and apply the shifted real p-series.
This supplies the mass assumptions for Mellin interchange and differentiation. -/
theorem summable_gammaPole_power_mass {κ : ℂ} (hκ : 0 ≤ κ.re) {σ : ℝ} (hσ : 1 ≤ σ) {p : ℝ}
    (hp : 1 < p) : Summable (fun n : ℕ ↦ (1 : ℝ) / ‖-((σ : ℂ) + κ + 2 * (n : ℂ))‖ ^ p) := by
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hp)
  have ht : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ p)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  apply
    Summable.of_nonneg_of_le (fun n ↦ div_nonneg zero_le_one (Real.rpow_nonneg (norm_nonneg _) _))
      (fun n ↦ ?_) ht
  rw [← one_div]
  exact
    div_le_div_of_nonneg_left zero_le_one
      (Real.rpow_pos_of_pos (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]) p)
      (Real.rpow_le_rpow (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
        (gammaPole_norm_lower hκ hσ n) (zero_lt_one.trans hp).le)

/-- For Re s > 0 and Re κ ≥ 0, half the reciprocal gamma argument equals the
reciprocal of s+κ+2n. The denominator is nonzero by its real part; clear it algebraically.
This removes the factor two from the digamma series. -/
theorem halfArgument_resolvent_eq {s κ : ℂ} (hs : 0 < s.re) (hκ : 0 ≤ κ.re) (n : ℕ) :
    (1 / ((s + κ) / 2 + n)) / 2 = 1 / (s + κ + 2 * (n : ℂ)) := by
  have hn : s + κ + 2 * (n : ℂ) ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
      Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, Complex.zero_re] at he
    linarith only [he, hs, hκ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have he : (s + κ) / 2 + n = (s + κ + 2 * (n : ℂ)) / 2 := by ring
  rw [he, one_div_div]
  field_simp [hn]

/-- For a complex shift with `Re κ ≥ 0` and real `σ ≥ 1`, the negative centered series
at poles `-(σ + κ + 2n)` has derivative `∑ n, 1/(σ + κ + 2n)²` at zero.
Pole separation and summable inverse-square pole mass justify termwise differentiation.
This identifies the derivative term for one gamma factor in the completion. -/
theorem hasDerivAt_gammaPole_centeredSum_zero {κ : ℂ} (hκ : 0 ≤ κ.re) {σ : ℝ} (hσ : 1 ≤ σ) :
    HasDerivAt
      (fun z : ℂ ↦
        -(∑' n : ℕ,
            (1 / (z - (-((σ : ℂ) + κ + 2 * (n : ℂ)))) + 1 / (-((σ : ℂ) + κ + 2 * (n : ℂ))))))
      (∑' n : ℕ, 1 / ((σ : ℂ) + κ + 2 * (n : ℂ)) ^ 2) 0 := by
  have h :=
    General.hasDerivAt_centeredResolventSum_zero (fun n : ℕ ↦ -((σ : ℂ) + κ + 2 * (n : ℂ)))
      (fun _ ↦ 1)
      (fun n ↦ by
        have hn := gammaPole_norm_lower hκ hσ n
        linarith only [hn, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
      (by
        simpa only [Nat.cast_one, Real.rpow_two] using
          summable_gammaPole_power_mass hκ hσ (show (1 : ℝ) < 2 by norm_num only))
  have hh := h.neg
  convert hh using 1
  · funext z
    simp only [Pi.neg_apply, Nat.cast_one, one_mul]
  · rw [← tsum_neg]
    simp only [Nat.cast_one, neg_sq, neg_div, neg_neg]

/-- For Re κ ≥ 0, σ ≥ 1, τ > 0 and x > 1, the normalized centered gamma-pole integral
is its shifted residue sum minus the inverse-square pole sum.
Power-mass Mellin inversion and splitting each residue prove the formula.
This evaluates one gamma factor's contribution. -/
theorem normalized_integral_gammaPoleResolvent_eq {κ : ℂ} (hκ : 0 ≤ κ.re) {σ τ x : ℝ} (hσ : 1 ≤ σ)
    (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ, ∑' n : ℕ, General.centeredResolventKernel (-((σ : ℂ) + κ + 2 * (n : ℂ))) x τ y) =
      General.gammaShiftSum x κ σ - ∑' n : ℕ, 1 / ((σ : ℂ) + κ + 2 * (n : ℂ)) ^ 2 := by
  have hi : Summable (fun n : ℕ ↦ (1 : ℂ) / ((σ : ℂ) + κ + 2 * (n : ℂ)) ^ 2) := by
    apply
      Summable.of_norm_bounded
        (summable_gammaPole_power_mass hκ hσ (show (1 : ℝ) < 2 by norm_num only))
    intro n
    rw [norm_div, norm_one, norm_pow, norm_neg, Real.rpow_two]
  have hz := General.summable_gammaShiftResidues hx hσ hκ
  have he :=
    General.normalized_integral_tsum_centeredResolventKernel
      (fun n : ℕ ↦ -((σ : ℂ) + κ + 2 * (n : ℂ))) (fun _ ↦ 1)
      (fun n ↦ by
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero,
          sub_zero]
        linarith only [hσ, hκ, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
      hτ hx
      (by
        simpa only [Nat.cast_one] using
          summable_gammaPole_power_mass hκ hσ (show (1 : ℝ) < 3 / 2 by norm_num only))
  simp only [Nat.cast_one, one_mul, neg_sq] at he
  rw [he, General.gammaShiftSum, ← hz.tsum_sub hi]
  exact
    tsum_congr
      (fun n ↦ by
        unfold General.gammaShiftResidue
        ring)

end PseudoPrime.AnalyticNumberTheory.Gamma
