/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComplexExponentialBounds
public import PseudoPrime.AnalyticNumberTheory.Gamma.ReciprocalPoleMellin

/-!
# Uniform reciprocal gamma residue bounds

Retaining the power difference at the first pole gives a bound independent of the shift,
including the repeated pole at zero. The remaining residues have a universal square-summable
majorant, so each gamma factor contributes at most `(log x + constant) / x`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For a nonzero gamma shift and positive cutoff, the index-zero residue is the power
minus one divided by `x * (1 + κ) * κ`. Factor out the inverse cutoff and combine the
simple-pole denominators. This exposes cancellation as the shift tends to zero. -/
theorem reciprocalGammaResidue_zero_eq {κ : ℂ} (hκ : κ ≠ 0) {x : ℝ} (hx : 0 < x) :
    reciprocalGammaResidue κ 0 x = ((x : ℂ) ^ (-κ) - 1) / ((x : ℂ) * (1 + κ) * κ) := by
  have hp : reciprocalGammaPole κ 0 = -1 + (-κ) := by
    simp only [reciprocalGammaPole, Nat.cast_zero, mul_zero, add_zero]
    ring
  have he : reciprocalGammaPole κ 0 ≠ -1 := by
    rw [hp]
    intro h
    apply hκ
    have h0 : -κ = 0 := add_left_cancel (h.trans (add_zero (-1 : ℂ)).symm)
    exact neg_eq_zero.mp h0
  rw [reciprocalGammaResidue, ite_eq_right he, hp,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_neg_one]
  have hd : (-1 + -κ) * (-1 + -κ + 1) = (1 + κ) * κ := by ring
  rw [hd]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- For a gamma shift with nonnegative real part and cutoff greater than one, the first
residue has norm at most `log x / x`, uniformly in the shift. At zero use the repeated-pole
value; otherwise the power difference cancels the shift norm in the denominator.
This controls the only residue whose separate denominator estimate is not uniform. -/
theorem norm_reciprocalGammaResidue_zero_le {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x) :
    ‖reciprocalGammaResidue κ 0 x‖ ≤ Real.log x / x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  by_cases hk : κ = 0
  · subst κ
    simp only [reciprocalGammaResidue, reciprocalGammaPole, Nat.cast_zero, mul_zero, add_zero,
      ite_true, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos hx), abs_of_pos hx0, le_refl]
  · have h1 : 1 ≤ ‖1 + κ‖ := by
      have hr := Complex.re_le_norm (1 + κ)
      simp only [Complex.add_re, Complex.one_re] at hr
      linarith only [hr, hκ]
    have hn : 0 < ‖κ‖ := norm_pos_iff.mpr hk
    rw [reciprocalGammaResidue_zero_eq hk hx0, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx0]
    apply (div_le_iff₀ (mul_pos (mul_pos hx0 (zero_lt_one.trans_le h1)) hn)).mpr
    have hb := Analysis.norm_cpow_neg_sub_one_le hκ hx
    have hc : Real.log x * ‖κ‖ ≤ Real.log x * (‖1 + κ‖ * ‖κ‖) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hn.le h1) (Real.log_pos hx).le
    have he : (Real.log x / x) * (x * ‖1 + κ‖ * ‖κ‖) = Real.log x * (‖1 + κ‖ * ‖κ‖) := by
      simp only [← mul_assoc, div_mul_cancel₀ _ hx0.ne']
    rw [he]
    exact hb.trans hc

/-- For a gamma shift with nonnegative real part and a positive index, the reciprocal
coefficient is at most `4 / (n + 1)^2`, independently of the shift. Combine the pole-norm
lower bound with the inverse-square coefficient bound. This supplies a universal tail. -/
theorem reciprocalGammaCoefficient_le_uniform {κ : ℂ} (hκ : 0 ≤ κ.re) {n : ℕ} (hn : n ≠ 0) :
    reciprocalGammaCoefficient κ n ≤ 4 / ((n : ℝ) + 1) ^ 2 := by
  have h := gammaPole_norm_lower hκ (σ := 1) le_rfl n
  simp only [Complex.ofReal_one] at h
  change (n : ℝ) + 1 ≤ ‖reciprocalGammaPole κ n‖ at h
  have hn0 : 0 < (n : ℝ) + 1 := by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  exact
    (reciprocalGammaCoefficient_le hκ hn).trans
      (div_le_div_of_nonneg_left (by norm_num only) (pow_pos hn0 2) (pow_le_pow_left₀ hn0.le h 2))

/-- For a gamma shift with nonnegative real part and cutoff greater than one, every
positive-index residue is bounded by `4 / ((n + 2)^2 * x)`. Exclude the repeated pole
and apply the uniform coefficient bound. This permits a shift-independent series estimate. -/
theorem norm_reciprocalGammaResidue_succ_le {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x) (n : ℕ) :
    ‖reciprocalGammaResidue κ (n + 1) x‖ ≤ (4 / ((n : ℝ) + 2) ^ 2) / x := by
  have he : reciprocalGammaPole κ (n + 1) ≠ -1 := by
    intro he
    exact Nat.succ_ne_zero n (reciprocalGammaPole_eq_neg_one_index hκ he)
  have hc : reciprocalGammaCoefficient κ (n + 1) ≤ 4 / ((n : ℝ) + 2) ^ 2 := by
    have h := reciprocalGammaCoefficient_le_uniform hκ (Nat.succ_ne_zero n)
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using h
  exact
    (norm_reciprocalGammaResidue_le_of_ne hκ hx he).trans
      (div_le_div_of_nonneg_right hc (zero_lt_one.trans hx).le)

/-- The sum of the universal tail majorant `4 / (n + 2)^2` over natural indices.
It is a finite nonnegative real constant, independent of all gamma shifts and cutoffs.
Together with the first-pole logarithm it bounds each reciprocal gamma residue sum. -/
noncomputable def reciprocalGammaTailBound : ℝ :=
  ∑' n : ℕ, 4 / ((n : ℝ) + 2) ^ 2

/-- The reciprocal gamma tail coefficients `4 / (n + 2)^2` are summable.
Shift the inverse-square real p-series by two and multiply by four. This ensures that the
universal gamma-tail constant is the sum of an absolutely convergent series. -/
theorem summable_reciprocalGammaTailCoefficient :
    Summable (fun n : ℕ ↦ (4 : ℝ) / ((n : ℝ) + 2) ^ 2) := by
  have hs :=
    (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (show 1 < (2 : ℕ) by decide))
  simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one_div] using hs.mul_left (4 : ℝ)

/-- For a gamma shift with nonnegative real part and cutoff greater than one, the norm of
the positive-index residue sum is at most the universal gamma-tail constant divided by
the cutoff. Sum the uniform pointwise bound using absolute convergence.
This bounds every gamma factor's tail with the same constant. -/
theorem norm_tsum_reciprocalGammaResidue_succ_le {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x) :
    ‖∑' n : ℕ, reciprocalGammaResidue κ (n + 1) x‖ ≤ reciprocalGammaTailBound / x := by
  have hs := (summable_nat_add_iff 1).mpr (summable_norm_reciprocalGammaResidue hκ hx)
  apply (norm_tsum_le_tsum_norm hs).trans
  have hb :=
    Summable.tsum_le_tsum (norm_reciprocalGammaResidue_succ_le hκ hx) hs
      (summable_reciprocalGammaTailCoefficient.div_const x)
  simpa only [tsum_div_const, reciprocalGammaTailBound] using hb

/-- For a gamma shift with nonnegative real part and cutoff greater than one, the whole
residue sum has norm at most `(log x + reciprocalGammaTailBound) / x`, with a constant
independent of the shift. Split off the first residue and add the uniform tail estimate.
This supplies uniform archimedean errors over fixed-degree L-function families. -/
theorem norm_tsum_reciprocalGammaResidue_le_uniform {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x) :
    ‖∑' n : ℕ, reciprocalGammaResidue κ n x‖ ≤ (Real.log x + reciprocalGammaTailBound) / x := by
  have hs := (summable_norm_reciprocalGammaResidue hκ hx).of_norm
  rw [hs.tsum_eq_zero_add]
  apply (norm_add_le _ _).trans
  have hb :=
    add_le_add (norm_reciprocalGammaResidue_zero_le hκ hx)
      (norm_tsum_reciprocalGammaResidue_succ_le hκ hx)
  simpa only [add_div] using hb

end PseudoPrime.AnalyticNumberTheory.Gamma
