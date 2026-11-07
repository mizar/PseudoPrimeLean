/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleLocalShift

/-! # Certified constants for the low triple bridge -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 8192 in
/-- The upper end of the sixty-cell interval is below three times `log 530000`.
The rational logarithm checker certifies the comparison used to bound the
smallest prime factor throughout that interval. -/
theorem lowBridge_log_530000 : (988 / 25 : ℝ) < 3 * Real.log 530000 := by
  have hc : Analysis.rationalLogIntervalCheck 530000 19 16 (659 / 50) (1319 / 100) = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

set_option maxRecDepth 8192 in
/-- The upper end of the rounded interval is below three times `log 600000`.
The rational logarithm checker supplies the bound for the fixed-radius branch. -/
theorem lowBridge_log_600000 : (9977 / 250 : ℝ) < 3 * Real.log 600000 := by
  have hc : Analysis.rationalLogIntervalCheck 600000 19 16 (1663 / 125) (2661 / 200) = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

set_option maxRecDepth 8192 in
/-- A rational lower bound for the full logarithmic spacing correction at
`530000`. A square-root comparison and the checked logarithm enclosure
provide the constant used in the sixty-cell bridge. -/
theorem lowBridge_spacing_530000 :
    (54753 / 10000000 : ℝ) ≤ Real.log (1 + (4 * Real.sqrt (530000 - 1) - 2) / 530000) := by
  have hc :
    Analysis.rationalLogIntervalCheck (53291 / 53000) 0 8 (54753 / 10000000) (548 / 100000) =
      true := by
    decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hs : (728 : ℝ) ≤ Real.sqrt (530000 - 1) := by
    apply (Real.le_sqrt (by norm_num only) (by norm_num only)).2
    norm_num only
  have hx : (53291 / 53000 : ℝ) ≤ 1 + (4 * Real.sqrt (530000 - 1) - 2) / 530000 := by
    norm_num only [div_eq_mul_inv] at hs ⊢
    linarith only [hs]
  exact hl.trans (Real.log_le_log (by norm_num only) hx)

set_option maxRecDepth 8192 in
/-- A rational lower bound for the full logarithmic spacing correction at
`600000`. The square-root and logarithm enclosures are used in the fixed
radius and prime-rounding branch. -/
theorem lowBridge_spacing_600000 :
    (3217 / 625000 : ℝ) ≤ Real.log (1 + (4 * Real.sqrt (600000 - 1) - 2) / 600000) := by
  have hc :
    Analysis.rationalLogIntervalCheck (5025803 / 5000000) 0 8 (3217 / 625000) (515 / 100000) =
      true := by
    decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hs : (77459 / 100 : ℝ) ≤ Real.sqrt (600000 - 1) := by
    apply (Real.le_sqrt (by norm_num only) (by norm_num only)).2
    norm_num only
  have hx : (5025803 / 5000000 : ℝ) ≤ 1 + (4 * Real.sqrt (600000 - 1) - 2) / 600000 := by
    norm_num only [div_eq_mul_inv] at hs ⊢
    linarith only [hs]
  exact hl.trans (Real.log_le_log (by norm_num only) hx)

/-- On the low bridge, a uniform Korselt triple has a rejecting prime at a
radius using the certified rational spacing saving. The upper logarithmic
endpoint supplies the factor bound, and monotonicity of squaring transfers
the witness from the exact shift to the rational one used by the cells. -/
theorem uniformKorselt_reject_low_shift {n p q r : ℕ} (hn : 1 < n) (ho : Odd n)
    (hnp : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpO : Odd p) (hqO : Odd q)
    (hrO : Odd r) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp5 : 5 ≤ (p : ℝ))
    (hU : Real.log n ≤ 988 / 25) {b d : ℝ} (hb : 8 ≤ b)
    (hd : d < LLS.PaperStatements.fullEndpointEvenGapCorrection b) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (max b ((2 / 3 : ℝ) * Real.log n - 54753 / 30000000 - d)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  have hlog : Real.log n < 3 * Real.log 530000 := hU.trans_lt lowBridge_log_530000
  obtain ⟨a, ha, hab, haf⟩ :=
    uniformKorselt_reject_shift hn ho hnp hp hq hr hpO hqO hrO hpq hqr hu hGRH 530000 hp5
      (by norm_num only) hlog hb hd
  have hle :
    max b
        ((2 / 3 : ℝ) * Real.log n -
          (1 / 3 : ℝ) * Real.log (1 + (4 * Real.sqrt (530000 - 1) - 2) / 530000) -
          d) ≤
      max b ((2 / 3 : ℝ) * Real.log n - 54753 / 30000000 - d) := by
    apply max_le_max le_rfl
    linarith only [lowBridge_spacing_530000]
  have hnonneg :
    0 ≤
      max b
        ((2 / 3 : ℝ) * Real.log n -
          (1 / 3 : ℝ) * Real.log (1 + (4 * Real.sqrt (530000 - 1) - 2) / 530000) -
          d) :=
    (by linarith only [hb] : 0 ≤ b).trans (le_max_left _ _)
  have hsq := mul_self_le_mul_self hnonneg hle
  exact ⟨a, ha, hab.trans (by simpa only [pow_two] using hsq), haf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
