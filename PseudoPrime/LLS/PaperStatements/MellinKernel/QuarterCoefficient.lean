/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MethodBarrier.SmallIndex

/-! # A uniform quarter barrier for the ambient common-kernel coefficient -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For every h>=2 and positive cutoff, the ambient denominator is at most
2*(h-1)*mass*sqrt(cutoff). Retain the endpoint inequality A<=B and the weight
integral bound A<=2M sqrt(cutoff). Used in the uniform coefficient obstruction. -/
theorem ambientDenominator_le_mass_sqrt (K : MellinKernel) {h : ℕ} (hh : 2 ≤ h) {lambda : ℝ}
    (hl : 0 < lambda) :
    ambientDenominator K h lambda ≤ 2 * (((h : ℝ) - 1) * K.mass) * Real.sqrt lambda := by
  have ha := truncated_weight_le_endpoint K hl
  have hw := integral_weight_le K hl
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hl.le] at hw
  have hhR : (2 : ℝ) ≤ h := by exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr (show (1 : ℝ) ≤ h by linarith only [hhR]))
  unfold ambientDenominator
  nlinarith only [ha, hm]

/-- For every h>=2 and positive cutoff with positive ambient denominator,
the common-kernel method coefficient is at least one quarter. Square the denominator
bound and cancel its positive square. This applies uniformly to admissible kernels. -/
theorem ambientMethodCoefficient_ge_one_quarter (K : MellinKernel) {h : ℕ} (hh : 2 ≤ h) {lambda : ℝ}
    (hl : 0 < lambda) (hd : 0 < ambientDenominator K h lambda) :
    (1 / 4 : ℝ) ≤ ambientMethodCoefficient K h lambda := by
  have hb := ambientDenominator_le_mass_sqrt K hh hl
  have hs := pow_le_pow_left₀ hd.le hb 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hl.le] at hs
  unfold ambientMethodCoefficient
  rw [div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith only [hs]

/-- For any positive epsilon and constant C, no eventually admissible family of
kernels, indices and cutoffs has ambient coefficient at most C*L^(-epsilon).
The quarter lower bound contradicts decay to zero. This rules out fixed exponent
savings within this coefficient formula, not for other analytic methods. -/
theorem not_eventually_ambientMethodCoefficient_le_log_power_saving {epsilon C : ℝ}
    (he : 0 < epsilon) (K : ℝ → MellinKernel) (h : ℝ → ℕ) (lambda : ℝ → ℝ)
    (hadm :
      Filter.Eventually
        (fun L ↦ 2 ≤ h L ∧ 0 < lambda L ∧ 0 < ambientDenominator (K L) (h L) (lambda L))
        Filter.atTop) :
    ¬Filter.Eventually
        (fun L ↦ ambientMethodCoefficient (K L) (h L) (lambda L) ≤ C * L ^ (-epsilon))
        Filter.atTop := by
  intro hu
  have ht := (tendsto_rpow_neg_atTop he).const_mul C
  have hzero : Filter.Tendsto (fun L : ℝ ↦ C * L ^ (-epsilon)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ht
  have hs := hzero.eventually_lt_const (by norm_num only : (0 : ℝ) < 1 / 4)
  obtain ⟨L, ha, hb, hc⟩ := (hadm.and (hu.and hs)).exists
  exact
    not_lt_of_ge ((ambientMethodCoefficient_ge_one_quarter (K L) ha.1 ha.2.1 ha.2.2).trans hb) hc

end PseudoPrime.LLS.PaperStatements.MellinKernel
