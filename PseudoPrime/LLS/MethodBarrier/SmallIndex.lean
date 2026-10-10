/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MethodBarrier.MellinKernel

/-! Coefficient obstruction for the ambient-conductor common-kernel method
at indices four through six. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Nonnegative Mellin weight makes its truncated integral no larger than the
full endpoint value. This controls the change of index in the comparison denominator. -/
theorem truncated_weight_le_endpoint (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) :
    (∫ u in (0 : ℝ)..lambda, (K.transform u).re / Real.sqrt u) ≤ (K.function (1 / 2)).re := by
  rw [intervalIntegral.integral_of_le hlambda.le, ← integral_weight_Ioi_eq K]
  apply MeasureTheory.setIntegral_mono_set (integrableOn_weight_Ioi K)
  · exact
      (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
        (fun u hu ↦ div_nonneg (K.mellin_nonneg u hu) (Real.sqrt_nonneg u))
  · exact MeasureTheory.ae_of_all _ (fun u hu ↦ hu.1)

/-- Main term minus endpoint cost for index `h` and positive cutoff `lambda`.
A positive value is required before the explicit-formula comparison can be divided. -/
noncomputable def ambientDenominator (K : MellinKernel) (h : ℕ) (lambda : ℝ) : ℝ :=
  (h : ℝ) * (∫ u in (0 : ℝ)..lambda, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re

/-- Leading coefficient obtained by the common-kernel comparison, using the
ambient conductor cost for each of the `h - 1` nonprincipal characters. -/
noncomputable def ambientMethodCoefficient (K : MellinKernel) (h : ℕ) (lambda : ℝ) : ℝ :=
  lambda * (((h : ℝ) - 1) * K.mass / ambientDenominator K h lambda) ^ 2

/-- For `h ≤ 6`, nonnegative weight bounds the normalized denominator by that
at index six; the discarded tail supplies the required sign. -/
theorem normalized_denominator_le_six (K : MellinKernel) {h : ℕ} (hh6 : h ≤ 6) {lambda : ℝ}
    (hlambda : 0 < lambda) :
    5 * ambientDenominator K h lambda ≤ ((h : ℝ) - 1) * indexSixDenominator K lambda := by
  have ha := truncated_weight_le_endpoint K hlambda
  have hh : (h : ℝ) ≤ 6 := by exact_mod_cast hh6
  have hp := mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr ha)
  unfold ambientDenominator indexSixDenominator
  nlinarith only [hp]

/-- At indices four through six, positive denominators imply a coefficient
of at least `60/121`. Normalize to index six and apply the Fourier dual bound. -/
theorem ambientMethodCoefficient_ge (K : MellinKernel) {h : ℕ} (hh4 : 4 ≤ h) (hh6 : h ≤ 6)
    {lambda : ℝ} (hlambda : 0 < lambda) (hd : 0 < ambientDenominator K h lambda) :
    (60 / 121 : ℝ) ≤ ambientMethodCoefficient K h lambda := by
  have hh : (4 : ℝ) ≤ h := by exact_mod_cast hh4
  have hhpos : 0 < (h : ℝ) - 1 := by linarith only [hh]
  have hc := normalized_denominator_le_six K hh6 hlambda
  have hds : 0 < indexSixDenominator K lambda := by nlinarith only [hc, hd, hhpos]
  have hm := mass_pos K
  have hr :
    5 * K.mass / indexSixDenominator K lambda ≤
      ((h : ℝ) - 1) * K.mass / ambientDenominator K h lambda := by
    apply (div_le_div_iff₀ hds hd).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hc hm.le]
  have hr0 : 0 ≤ 5 * K.mass / indexSixDenominator K lambda :=
    div_nonneg (mul_nonneg (by norm_num only) hm.le) hds.le
  have hs := pow_le_pow_left₀ hr0 hr 2
  exact (indexSixMethodCoefficient_ge K hlambda hds).trans (mul_le_mul_of_nonneg_left hs hlambda.le)

/-- The coefficient requested by Theorem 1.3 at a fixed positive epsilon. -/
noncomputable def smallIndexTargetWithSlack (h : ℕ) : ℝ :=
  (1 / 4 + 1 / 200) * (1 - 1 / (h : ℝ)) ^ 2 *
    (Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4)) ^ 2

/-- For indices four through six, Theorem 1.3's coefficient at epsilon `1/200`
is below the method barrier. Use `log(2h) < 5/2` and `1 - 1/h ≤ 5/6`. -/
theorem smallIndexTargetWithSlack_lt_barrier {h : ℕ} (hh4 : 4 ≤ h) (hh6 : h ≤ 6) :
    smallIndexTargetWithSlack h < (60 / 121 : ℝ) := by
  have h4 : (4 : ℝ) ≤ h := by exact_mod_cast hh4
  have h6 : (h : ℝ) ≤ 6 := by exact_mod_cast hh6
  have hp : 0 < (h : ℝ) := by linarith only [h4]
  have hl0 : 0 ≤ Real.log (2 * (h : ℝ)) :=
    (Real.log_pos (by linarith only [h4] : (1 : ℝ) < 2 * (h : ℝ))).le
  have hl : Real.log (2 * (h : ℝ)) < 5 / 2 :=
    (Real.log_le_log (mul_pos (by norm_num only) hp) (by linarith only [h6])).trans_lt
      IndexSixBarrier.log_twelve_lt_five_halves
  have hd : 0 < 4 - Real.log (2 * (h : ℝ)) := by linarith only [hl]
  have hr : Real.log (2 * (h : ℝ)) / (4 - Real.log (2 * (h : ℝ))) < 5 / 3 := by
    apply (div_lt_iff₀ hd).mpr
    linarith only [hl]
  have hr0 := div_nonneg hl0 hd.le
  have hs : (Real.log (2 * (h : ℝ)) / (4 - Real.log (2 * (h : ℝ)))) ^ 2 < (5 / 3 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_self_lt_mul_self hr0 hr
  have ha0 : 0 ≤ 1 - 1 / (h : ℝ) := by
    have he := (div_le_one hp).mpr (show (1 : ℝ) ≤ h by linarith only [h4])
    linarith only [he]
  have ha : 1 - 1 / (h : ℝ) ≤ 5 / 6 := by
    have he := one_div_le_one_div_of_le hp h6
    linarith only [he]
  have has := pow_le_pow_left₀ ha0 ha 2
  have hneg :
    Real.log (2 * (h : ℝ)) / (Real.log (2 * (h : ℝ)) - 4) =
      -(Real.log (2 * (h : ℝ)) / (4 - Real.log (2 * (h : ℝ)))) := by
    rw [show Real.log (2 * (h : ℝ)) - 4 = -(4 - Real.log (2 * (h : ℝ))) by ring, div_neg]
  unfold smallIndexTargetWithSlack
  rw [hneg, neg_sq]
  have hb :=
    mul_le_mul_of_nonneg_right has
      (sq_nonneg (Real.log (2 * (h : ℝ)) / (4 - Real.log (2 * (h : ℝ)))))
  nlinarith only [hb, hs, IndexSixBarrier.rational_gap]

/-- No admissible common Mellin kernel reaches the requested small-index
coefficient at epsilon `1/200` with the ambient-conductor comparison.
This excludes that certificate method, not the arithmetic theorem. -/
theorem no_small_index_mellin_certificate {h : ℕ} (hh4 : 4 ≤ h) (hh6 : h ≤ 6) :
    ¬∃ (K : MellinKernel) (lambda : ℝ),
        0 < lambda ∧
          0 < ambientDenominator K h lambda ∧
          ambientMethodCoefficient K h lambda ≤ smallIndexTargetWithSlack h := by
  rintro ⟨K, lambda, hlambda, hd, hc⟩
  exact
    (not_le_of_gt (smallIndexTargetWithSlack_lt_barrier hh4 hh6))
      ((ambientMethodCoefficient_ge K hh4 hh6 hlambda hd).trans hc)

end PseudoPrime.LLS.PaperStatements.MellinKernel
