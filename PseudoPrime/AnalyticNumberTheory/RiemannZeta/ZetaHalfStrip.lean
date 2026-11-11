/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripLeftBoundary
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripRight
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaEntireGrowth

/-! # Uniform zeta bound on a vertical strip -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `Re s ≥ -1/2`, the pole-cancelled zeta function is bounded by a
fixed multiple of `(‖s‖ + 1)^3`. Monotonicity of the sawtooth remainder
makes the existing growth estimate uniform in the real part. -/
private theorem zeta_strip_polynomial {s : ℂ} (hs : (-(1 / 2) : ℝ) ≤ s.re) :
    ‖riemannZeta₁ s‖ ≤ (sawtoothRemainderBound (-(1 / 2)) + 2) * (‖s‖ + 1) ^ 3 := by
  have hc : 0 ≤ sawtoothRemainderBound (-(1 / 2)) := sawtoothRemainderBound_nonneg _
  have hC := sawtoothRemainderBound_antitone (a := -(1 / 2)) (b := s.re) (by norm_num only) hs
  have hn := norm_riemannZeta₁_le_of_reGt_neg_one (by linarith only [hs])
  have hz : 0 ≤ ‖s‖ := norm_nonneg s
  have hscale :
    ‖s‖ * (‖s‖ + 1) ^ 2 * sawtoothRemainderBound s.re ≤
      ‖s‖ * (‖s‖ + 1) ^ 2 * sawtoothRemainderBound (-(1 / 2)) :=
    mul_le_mul_of_nonneg_left hC (mul_nonneg hz (sq_nonneg _))
  have htarget :
    ‖s‖ + (‖s‖ + 1) / 2 + ‖s‖ * (‖s‖ + 1) ^ 2 * sawtoothRemainderBound (-(1 / 2)) ≤
      (sawtoothRemainderBound (-(1 / 2)) + 2) * (‖s‖ + 1) ^ 3 := by
    have hp := mul_nonneg hc (sq_nonneg (‖s‖ + 1))
    have hq := mul_nonneg hz (sq_nonneg (‖s‖ + 1))
    nlinarith only [hz, hp, hq, sq_nonneg ‖s‖]
  linarith only [hn, hscale, htarget]

/-- On `Re s ≥ -1/2`, dividing the pole-cancelled zeta function by
`(s + 2)^2` does not increase its norm. The denominator norm is at least 1. -/
private theorem zeta_strip_div_le {s : ℂ} (hs : (-(1 / 2) : ℝ) ≤ s.re) :
    ‖riemannZeta₁ s / (s + 2) ^ 2‖ ≤ ‖riemannZeta₁ s‖ := by
  have ht : (2 : ℂ).re = 2 := rfl
  have hre := Complex.abs_re_le_norm (s + 2)
  simp only [Complex.add_re, ht] at hre
  have hpos : (1 : ℝ) ≤ ‖s + 2‖ := by
    have hab := le_abs_self (s.re + 2)
    linarith only [hs, hre, hab]
  have hsquare : (1 : ℝ) ≤ ‖s + 2‖ ^ 2 := by nlinarith only [hpos]
  rw [norm_div, norm_pow]
  exact div_le_self (norm_nonneg _) hsquare

/-- On the closed strip, the cubic polynomial in the complex norm is bounded
by an exponential of the absolute imaginary part. -/
private theorem zeta_strip_cube {s : ℂ} (hlo : (-(1 / 2) : ℝ) ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    (‖s‖ + 1) ^ 3 ≤ 27 * Real.exp (3 * |s.im|) := by
  have hre : |s.re| ≤ 2 := abs_le.mpr (by constructor <;> linarith only [hlo, hhi])
  have hn := Complex.norm_le_abs_re_add_abs_im s
  have hexp := Real.add_one_le_exp |s.im|
  have hbase : ‖s‖ + 1 ≤ 3 * Real.exp |s.im| := by
    have h := abs_nonneg s.im
    linarith only [hre, hn, hexp, h]
  have hc := pow_le_pow_left₀ (by linarith only [norm_nonneg s] : 0 ≤ ‖s‖ + 1) hbase 3
  rw [mul_pow] at hc
  have heq : (3 : ℝ) ^ 3 * Real.exp |s.im| ^ 3 = 27 * Real.exp (3 * |s.im|) := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
  exact hc.trans_eq heq

/-- The auxiliary function is differentiable in the open strip and
continuous on its closure. Its sole possible denominator zero is outside
the strip. -/
private theorem zeta_strip_diff :
    DiffContOnCl ℂ (fun s : ℂ ↦ riemannZeta₁ s / (s + 2) ^ 2)
      (Complex.re ⁻¹' Set.Ioo (-(1 / 2) : ℝ) (3 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  have hsub :
    closure (Complex.re ⁻¹' Set.Ioo (-(1 / 2) : ℝ) (3 / 2)) ⊆
      Complex.re ⁻¹' Set.Ici (-(1 / 2) : ℝ) := by
    apply closure_minimal ?_ (isClosed_Ici.preimage Complex.continuous_re)
    intro s hs
    exact hs.1.le
  intro s hs
  have hs' : (-(1 / 2) : ℝ) ≤ s.re := hsub hs
  have hne : s + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have ht : (2 : ℂ).re = 2 := rfl
    simp only [Complex.add_re, Complex.zero_re, ht] at hre
    linarith only [hs', hre]
  exact
    ((differentiable_riemannZeta₁ s).div ((differentiableAt_id.add_const 2).pow 2)
        (pow_ne_zero 2 hne)).differentiableWithinAt

/-- The auxiliary function satisfies the double-exponential growth condition
for Phragmén–Lindelöf on the open strip. The polynomial growth is dominated
by an exponential in the ordinate, and then by the required larger bound. -/
private theorem zeta_strip_growth :
    ∃ c < Real.pi / ((3 / 2 : ℝ) - (-(1 / 2))),
      ∃ B,
        Asymptotics.IsBigO
          (Filter.comap (abs ∘ Complex.im) Filter.atTop ⊓
            Filter.principal (Complex.re ⁻¹' Set.Ioo (-(1 / 2) : ℝ) (3 / 2)))
          (fun s : ℂ ↦ riemannZeta₁ s / (s + 2) ^ 2)
          (fun s : ℂ ↦ Real.exp (B * Real.exp (c * |s.im|))) := by
  refine ⟨1, ?_, 3, ?_⟩
  · have hp := Real.pi_gt_three
    norm_num only
    linarith only [hp]
  · apply Asymptotics.IsBigO.of_bound (27 * (sawtoothRemainderBound (-(1 / 2)) + 2))
    have hmem :
      ∀ᶠ s : ℂ in Filter.principal (Complex.re ⁻¹' Set.Ioo (-(1 / 2) : ℝ) (3 / 2)),
        (-(1 / 2) : ℝ) < s.re ∧ s.re < 3 / 2 :=
      Filter.eventually_principal.mpr (fun _ hs ↦ hs)
    filter_upwards [hmem.filter_mono inf_le_right] with s hs
    have hc : 0 ≤ sawtoothRemainderBound (-(1 / 2)) + 2 := by
      have h := sawtoothRemainderBound_nonneg (-(1 / 2))
      linarith only [h]
    have hscale : 0 ≤ 27 * (sawtoothRemainderBound (-(1 / 2)) + 2) :=
      mul_nonneg (by norm_num only) hc
    have hmain := zeta_strip_polynomial hs.1.le
    have hdiv := zeta_strip_div_le hs.1.le
    have hcube := zeta_strip_cube hs.1.le hs.2.le
    have hexp : Real.exp (3 * |s.im|) ≤ Real.exp (3 * Real.exp |s.im|) := by
      apply Real.exp_le_exp.mpr
      have h := Real.add_one_le_exp |s.im|
      linarith only [h]
    simp only [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      ‖riemannZeta₁ s / (s + 2) ^ 2‖ ≤ ‖riemannZeta₁ s‖ := hdiv
      _ ≤ (sawtoothRemainderBound (-(1 / 2)) + 2) * (‖s‖ + 1) ^ 3 := hmain
      _ ≤ (sawtoothRemainderBound (-(1 / 2)) + 2) * (27 * Real.exp (3 * |s.im|)) :=
        mul_le_mul_of_nonneg_left hcube hc
      _ = (27 * (sawtoothRemainderBound (-(1 / 2)) + 2)) * Real.exp (3 * |s.im|) := by ring
      _ ≤ (27 * (sawtoothRemainderBound (-(1 / 2)) + 2)) * Real.exp (3 * Real.exp |s.im|) :=
        mul_le_mul_of_nonneg_left hexp hscale

/-- For `-1/2 ≤ Re s ≤ 3/2`, the pole-cancelled auxiliary function
`riemannZeta₁ s / (s + 2)^2` has norm at most `4/5`. Apply the ordinary
Phragmén–Lindelöf principle using the two explicit boundary estimates. -/
theorem norm_zeta_strip_aux {s : ℂ} (hlo : (-(1 / 2) : ℝ) ≤ s.re) (hhi : s.re ≤ 3 / 2) :
    ‖riemannZeta₁ s / (s + 2) ^ 2‖ ≤ (4 / 5 : ℝ) := by
  exact
    PhragmenLindelof.vertical_strip (f := fun z : ℂ ↦ riemannZeta₁ z / (z + 2) ^ 2) (z := s)
      zeta_strip_diff zeta_strip_growth (fun _ h ↦ norm_zeta_strip_left h)
      (fun _ h ↦ norm_zeta_strip_right h) hlo hhi

/-- For `-1/2 ≤ Re s ≤ 3/2` and `s ≠ 1`, the zeta norm is at most
`(4/5) * ‖s+2‖^2 / ‖s-1‖`. Undo the pole cancellation in the auxiliary
Phragmén–Lindelöf bound. -/
theorem norm_zeta_le_strip {s : ℂ} (hlo : (-(1 / 2) : ℝ) ≤ s.re) (hhi : s.re ≤ 3 / 2)
    (hne : s ≠ 1) : ‖riemannZeta s‖ ≤ (4 / 5 : ℝ) * ‖s + 2‖ ^ 2 / ‖s - 1‖ := by
  have hzeq : riemannZeta₁ s = (s - 1) * riemannZeta s :=
    ((eq_inv_mul_iff_mul_eq₀ (sub_ne_zero.mpr hne)).mp (riemannZeta_eq_inv_sub_mul hne)).symm
  have hminus : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hplus : 0 < ‖s + 2‖ := by
    have hsne : s + 2 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have ht : (2 : ℂ).re = 2 := rfl
      simp only [Complex.add_re, Complex.zero_re, ht] at hre
      linarith only [hlo, hre]
    exact norm_pos_iff.mpr hsne
  have haux := norm_zeta_strip_aux hlo hhi
  rw [hzeq, norm_div, norm_mul, norm_pow] at haux
  have hm := (div_le_iff₀ (pow_pos hplus 2)).1 haux
  apply (le_div_iff₀ hminus).2
  nlinarith only [hm]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
