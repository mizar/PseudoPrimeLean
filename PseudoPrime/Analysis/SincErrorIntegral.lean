/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SineMajorant
import all PseudoPrime.Analysis.SineMajorant
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Inverse-power integrals for the sinc count discrepancy -/

public section

namespace PseudoPrime.Analysis

/-- For positive integer degree and nonnegative log and constant coefficients,
the elementary antiderivative bounds each finite upper truncation. -/
theorem sincError_power_integral {a b s t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {n : ℕ} (hn : 0 < n) :
    (∫ x in a..b, (s * Real.log (x / a) + t) / x ^ (n + 1)) ≤ (t + s / n) / (n * a ^ n) := by
  let F := fun x : ℝ ↦ -((s * (Real.log x - Real.log a) + t + s / n) / (n * x ^ n))
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hd {x : ℝ} (hx : 0 < x) : HasDerivAt F ((s * Real.log (x / a) + t) / x ^ (n + 1)) x := by
    have h₁ := ((((Real.hasDerivAt_log hx.ne').sub_const (Real.log a)).const_mul s).add_const t)
    have h₂ := ((hasDerivAt_id x).pow n).const_mul (n : ℝ)
    apply (((h₁.add_const (s / n)).div h₂ (mul_ne_zero hn' (pow_ne_zero n hx.ne'))).neg).congr_deriv
    rw [Real.log_div hx.ne' ha.ne']
    simp only [Pi.pow_apply, id_eq, mul_one]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp only [Nat.succ_sub_one, pow_succ, Nat.cast_succ]
    field_simp [hx.ne', hn']
    ring
  have hi :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx ↦ hd (ha.trans_le ((Set.uIcc_of_le hab) ▸ hx : x ∈ Set.Icc a b).1))
      (by
        apply ContinuousOn.intervalIntegrable
        intro x hx
        have hp := ha.trans_le ((Set.uIcc_of_le hab) ▸ hx : x ∈ Set.Icc a b).1
        fun_prop (disch :=
          first
          | exact ha.ne'
          | exact div_ne_zero hp.ne' ha.ne'
          | exact pow_ne_zero _ hp.ne'))
  rw [hi]
  dsimp only [F]
  rw [sub_self, mul_zero, zero_add]
  have hnum :=
    add_nonneg (add_nonneg (mul_nonneg hs (sub_nonneg.mpr (Real.log_le_log ha hab))) ht)
      (div_nonneg hs (Nat.cast_nonneg n))
  have hden := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (pow_nonneg (ha.trans_le hab).le n)
  linarith only [div_nonneg hnum hden]

/-- The sum of the three integrated inverse-power majorants costs at most
57 times the constant coefficient plus 26 times the logarithmic coefficient. -/
theorem sincError_three_terms {b s t : ℝ} (hb : 2 / 5 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    let I := fun n : ℕ ↦ ∫ x in (2 / 5 : ℝ)..b, (s * Real.log (x / (2 / 5)) + t) / x ^ (n + 1)
    (22 / 9) * I 1 + 6 * I 2 + 6 * (1 + sineMajorantShift) * I 3 ≤ 57 * t + 26 * s := by
  intro I
  have H (n : ℕ) (hn : 0 < n) :=
    sincError_power_integral (by norm_num only : (0 : ℝ) < 2 / 5) hb hs ht hn
  have h₃ :=
    mul_le_mul_of_nonneg_left (H 3 (by decide))
      (show 0 ≤ 6 * (1 + sineMajorantShift) by linarith only [sineMajorantShift_bounds.1])
  have h₀ := mul_le_mul_of_nonneg_right sincError_cutoff_budgets.1.le ht
  have h₁ := mul_le_mul_of_nonneg_right sincError_cutoff_budgets.2.le hs
  have hA := H 1 (by decide)
  have hB := H 2 (by decide)
  change I 1 ≤ _ at hA
  change I 2 ≤ _ at hB
  change 6 * (1 + sineMajorantShift) * I 3 ≤ _ at h₃
  norm_num only [Nat.cast_one, Nat.cast_ofNat, pow_one, div_one] at hA hB h₃
  ring_nf at hA hB h₃ h₀ h₁ ⊢
  linarith only [hA, hB, h₃, h₀, h₁]

/-- The integral of the absolute discrepancy-kernel derivative on any truncation
is bounded for both the constant and logarithmic weights, including their sums. -/
theorem sincError_weighted_integral {b s t : ℝ} (hb : 2 / 5 ≤ b) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ x in (2 / 5 : ℝ)..b, (s * Real.log (x / (2 / 5)) + t) * |deriv sincErrorKernel x|) ≤
      57 * t + 26 * s := by
  let w := fun x : ℝ ↦ s * Real.log (x / (2 / 5)) + t
  let f := fun (n : ℕ) (x : ℝ) ↦ w x / x ^ (n + 1)
  have hp {x : ℝ} (hx : x ∈ Set.uIcc (2 / 5 : ℝ) b) : 0 < x :=
    (by norm_num only : (0 : ℝ) < 2 / 5).trans_le ((Set.uIcc_of_le hb) ▸ hx : x ∈ Set.Icc _ _).1
  have hf (n : ℕ) : IntervalIntegrable (f n) MeasureTheory.volume (2 / 5) b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    dsimp only [f, w]
    fun_prop (disch :=
      first
      | norm_num only; done
      | exact pow_ne_zero _ (hp hx).ne'
      | exact div_ne_zero (hp hx).ne' (by norm_num only))
  have hd : ContDiff ℝ 2 sineMajorant := by
    unfold sineMajorant; fun_prop
  have hd' : ContDiff ℝ 1 (deriv sineMajorant) := hd.deriv'
  have hd'' : ContDiff ℝ 0 (deriv (deriv sineMajorant)) := hd'.deriv'
  have hi :
    IntervalIntegrable (fun x ↦ w x * |deriv sincErrorKernel x|) MeasureTheory.volume (2 / 5)
      b := by
    apply ContinuousOn.intervalIntegrable
    apply
      ContinuousOn.congr _
        (fun x hx ↦ congrArg (fun u : ℝ ↦ w x * |u|) (hasDerivAt_sincErrorKernel (hp hx)).deriv)
    intro x hx
    dsimp only [w]
    have h₀ := hd.continuous
    have h₁ := hd'.continuous
    have h₂ := hd''.continuous
    fun_prop (disch :=
      first
      | norm_num only; done
      | exact pow_ne_zero _ (hp hx).ne'
      | exact div_ne_zero (hp hx).ne' (by norm_num only))
  have h1 := (hf 1).const_mul (22 / 9 : ℝ)
  have h2 := (hf 2).const_mul (6 : ℝ)
  have h3 := (hf 3).const_mul (6 * (1 + sineMajorantShift))
  apply le_trans (intervalIntegral.integral_mono_on hb hi ((h1.add h2).add h3) ?_)
  · simp only [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_add (h1.add h2) h3,
      intervalIntegral.integral_const_mul]
    exact sincError_three_terms hb hs ht
  · intro x hx
    have hw : 0 ≤ w x :=
      add_nonneg
        (mul_nonneg hs
          (Real.log_nonneg ((one_le_div (by norm_num only : (0 : ℝ) < 2 / 5)).mpr hx.1)))
        ht
    have h :=
      mul_le_mul_of_nonneg_left
        (abs_deriv_sincErrorKernel_le ((by norm_num only : (0 : ℝ) < 2 / 5).trans_le hx.1)) hw
    apply h.trans_eq
    dsimp only [Pi.add_apply, f]
    ring

end PseudoPrime.Analysis
