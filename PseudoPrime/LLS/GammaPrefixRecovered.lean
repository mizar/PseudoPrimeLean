/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianSeededPrefix

/-! # Recovered credit from the unchanged Euler seed and ten-node checkpoints -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The existing 35 checked rows give seed credit 15877/5000. Transfer their exact
rational sum to the actual Mangoldt prefix, with no RH or new finite data. -/
theorem recovered_seed_prefix :
    (15877 / 5000 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊(100 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have hs :
    (15877 / 5000 : ℚ) ≤ (Analysis.smallSeedRows.map Analysis.GammaFiniteEulerRow.lower).sum := by
    decide +kernel
  have hr :=
    Analysis.gamma_finite_row_block_lower Analysis.smallSeedRows 0 100 Analysis.small_seed_primes
      Analysis.small_seed_rows_check Analysis.small_seed_distinct Analysis.small_seed_members
  have hc := (Rat.cast_le (K := ℝ)).mpr hs
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  simpa only [Nat.floor_ofNat] using hc.trans hr

/-- Under RH the unchanged seed boundary exceeds 9.24823. Keep the signed
products before rounding; this supplies the recovered transport boundary credit. -/
theorem recovered_seed_boundary (hRH : RiemannHypothesis) :
    (924823 / 100000 : ℝ) ≤ gammaEulerBoundaryTail 100 := by
  have h :=
    gamma_euler_boundary_tail_lower gamma_seed100_weight_upper (by norm_num only)
      gamma_seed100_psi_upper gamma_seed100_slope_lower (by norm_num only)
      (gamma_logWeightedMangoldtSum_nonneg (by norm_num only : (0 : ℝ) < 100))
      (sharp_smoothed100 hRH) gamma_seed100_main_lower
  linarith only [h]

/-- The unchanged rational seed error envelope is at most 93/1250.
Kernel arithmetic recovers the margin previously lost in the 3/40 cap. -/
theorem recovered_seed_error_check : errorSeed100Budget ≤ 93 / 1250 := by decide +kernel

/-- The actual seed error budget is at most 93/1250, independently of RH.
Reapply the same node envelope rather than strengthening the old rounded cap. -/
theorem recovered_seed_error : gammaEulerTailErrorBudget 100 ≤ (93 / 1250 : ℝ) := by
  have hr : Real.sqrt (100 : ℝ) ≤ 10 := Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hl := (Analysis.rationalLogIntervalCheck_sound error_seed100_log_check).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have h :=
    gammaEulerTailErrorBudget_le_envelope (by norm_num only : (1 : ℝ) ≤ 100) hr hl
      (fun a ↦ ((errorSeed100Ratios a).2 : ℝ))
      (fun ab hab ↦ (Analysis.gamma_finite_ratio_check_sound error_seed100_ratio_check ab hab).2)
  have hc : gammaEulerTailErrorBudget 100 ≤ (errorSeed100Budget : ℝ) := by
    norm_num only [errorSeed100Budget, gammaEulerErrorEnvelope, Rat.cast_list_sum, List.map_map,
      Function.comp_def, Rat.cast_mul, Rat.cast_abs, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
      Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one] at h ⊢
    exact h
  have he := (Rat.cast_le (K := ℝ)).mpr recovered_seed_error_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at he
  exact hc.trans he

/-- The existing Taylor checker gives log(1000)<=6.908. This refines only a
scalar envelope input; no quadrature node or prime-power row is added. -/
theorem recovered_log1000 : Real.log (1000 : ℝ) ≤ 1727 / 250 := by
  have hc : Analysis.rationalLogIntervalCheck 1000 10 16 (69 / 10) (1727 / 250) = true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using (Analysis.rationalLogIntervalCheck_sound hc).2

/-- The rational square 31.623 squared exceeds 1000, bounding the actual root
for the recovered checkpoint error and smoothed-sum estimates. -/
theorem recovered_sqrt1000 : Real.sqrt (1000 : ℝ) ≤ 31623 / 1000 := by
  exact Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩

/-- Under RH the actual smoothed sum at 1000 is at least 196933/200.
Insert the recovered logarithm and root caps in the refined one-sided bound. -/
theorem recovered_smoothed1000 (hRH : RiemannHypothesis) :
    (196933 / 200 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 := by
  have h := logWeightedMangoldtSum_ge_rational_refined hRH (by norm_num only : (1 : ℝ) < 1000)
  linarith only [h, recovered_sqrt1000, recovered_log1000]

/-- Under RH the actual smoothed sum at 900 is at most 888467/1000.
Retain the existing lower logarithm anchor in the corrected one-sided bound. -/
theorem recovered_smoothed900 (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 900 ≤ (888467 / 1000 : ℝ) := by
  have h := logWeightedMangoldtSum_le_rational_corrected hRH (by norm_num only : (1 : ℝ) < 900)
  have hs : Real.sqrt (900 : ℝ) ≤ 30 := Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs, sharp_log900]

/-- Under RH psi(1000)>=913. The asymmetric smoothed difference uses the
negative cap at 900 and the unchanged log(10/9) certificate. -/
theorem recovered_psi1000 (hRH : RiemannHypothesis) : (913 : ℝ) ≤ Chebyshev.psi 1000 := by
  apply
    psi_lower_of_one_sided_log_cap (x := 900) (U := -11533 / 1000) (V := 3067 / 200) (R :=
      105361 / 1000000) (by norm_num only) (by norm_num only)
  · linarith only [recovered_smoothed900 hRH]
  · linarith only [recovered_smoothed1000 hRH]
  · norm_num only
  · convert sharp_log_ratio using 1
    norm_num only
  · norm_num only

/-- Under RH the actual checkpoint boundary is at most 8.10051.
The same ten node coefficients now use psi>=913 and S>=984.665. -/
theorem recovered_boundary1000 (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 1000 ≤ (810051 / 100000 : ℝ) := by
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 435675 / 1000000000)
      checkpoint1000_weight_lower (by norm_num only : (0 : ℝ) ≤ 913) (recovered_psi1000 hRH)
      checkpoint1000_slope_upper (by norm_num only) (by norm_num only : (0 : ℝ) ≤ 196933 / 200)
      (recovered_smoothed1000 hRH) checkpoint1000_main_upper
  linarith only [h]

/-- The checkpoint-1000 envelope with refined root and logarithm inputs.
It uses the unchanged ten certified power intervals and bounds the actual budget. -/
def recoveredError1000 : ℚ :=
  (Analysis.gammaResolventCoefficients.map
      (fun ab ↦
        let σ := (1 / 2 : ℚ) + ab.1
        let v := (checkpoint1000Ratios ab.1).2
        |ab.2| *
          ((1 / 20 : ℚ) * (σ ^ 2 * ((31623 / 1000) * v) / (σ - 1 / 2)) +
            (1839 / 1000 : ℚ) * (v * (1 + σ * (1727 / 250))) +
            (21 / 20 : ℚ) * (σ * v)))).sum

/-- Exact rational arithmetic bounds the refined envelope by 217/25000.
This statement concerns the new envelope, not the older root-32 envelope. -/
theorem recovered_error1000_check : recoveredError1000 ≤ 217 / 25000 := by decide +kernel

/-- The actual checkpoint-1000 error budget is at most 217/25000.
Transfer the refined scalar inputs and unchanged node endpoints through the envelope theorem. -/
theorem recovered_error1000 : gammaEulerTailErrorBudget 1000 ≤ (217 / 25000 : ℝ) := by
  have h :=
    gammaEulerTailErrorBudget_le_envelope (by norm_num only : (1 : ℝ) ≤ 1000) recovered_sqrt1000
      recovered_log1000 (fun a ↦ ((checkpoint1000Ratios a).2 : ℝ))
      (fun ab hab ↦ (Analysis.gamma_finite_ratio_check_sound checkpoint1000_node_check ab hab).2)
  have hc : gammaEulerTailErrorBudget 1000 ≤ (recoveredError1000 : ℝ) := by
    norm_num only [recoveredError1000, gammaEulerErrorEnvelope, Rat.cast_list_sum, List.map_map,
      Function.comp_def, Rat.cast_mul, Rat.cast_abs, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
      Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one] at h ⊢
    exact h
  have he := (Rat.cast_le (K := ℝ)).mpr recovered_error1000_check
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at he
  exact hc.trans he

/-- Under RH a target boundary/error pair transports the recovered seed to
an actual Gamma prefix. This keeps the strengthened seed independent of any old rounded credit. -/
theorem recovered_prefix_at (hRH : RiemannHypothesis) {b B E : ℝ} (hb : 1 ≤ b)
    (hB : gammaEulerBoundaryTail b ≤ B) (hE : gammaEulerTailErrorBudget b ≤ E) :
    15877 / 5000 + 924823 / 100000 - B - (93 / 1250 + E) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  exact
    gamma_euler_prefix_lower_of_transport_bounds hRH (by norm_num only) hb recovered_seed_prefix
      (recovered_seed_boundary hRH) hB (add_le_add recovered_seed_error hE)

/-- A recovered prefix credit persists to later real cutoffs by nonnegative summands.
The rational credit is transported without any additional arithmetic hypothesis. -/
theorem recovered_prefix_mono {a b : ℝ} {c : ℚ} (hab : a ≤ b)
    (hc : (c : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m) :
    (c : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  exact Analysis.gamma_euler_prefix_lower_mono (Nat.floor_mono hab) hc

/-- Under RH every prefix beyond 1000 has actual Gamma credit 4.24.
Transport the recovered seed through the refined checkpoint and use monotonicity. -/
theorem gamma_prefix1000_recovered (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (106 / 25 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    recovered_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 1000) (recovered_boundary1000 hRH)
      recovered_error1000
  have hm :=
    recovered_prefix_mono (c := 106 / 25) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH every prefix beyond 35000 has actual Gamma credit 5.6377.
The target nodes stay unchanged; only the recovered seed credit enters transport. -/
theorem gamma_prefix35000_recovered (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (56377 / 10000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    recovered_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 35000) (gamma_boundary35000_upper hRH)
      checkpoint35000_error_upper
  have hm :=
    recovered_prefix_mono (c := 56377 / 10000) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Under RH every prefix beyond 50000 has actual Gamma credit 5.7628.
The existing target boundary and error combine with the recovered seed. -/
theorem gamma_prefix50000_recovered (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (14407 / 2500 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    recovered_prefix_at hRH (by norm_num only : (1 : ℝ) ≤ 50000) (boundary50000_refined hRH)
      gamma_tail_error_budget_le
  have hm :=
    recovered_prefix_mono (c := 14407 / 2500) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [h])
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

/-- Transfer an actual Gamma prefix credit to the actual Gaussian prefix with
factor 17/20. The pointwise kernel comparison is independent of RH. -/
theorem recovered_gaussian_prefix {b c : ℝ}
    (hc : c ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m) :
    (17 / 20 : ℝ) * c ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hs :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b⌋₊) (fun n _ ↦ gaussian_gamma_mangoldt_weight_le n)
  rw [← Finset.mul_sum] at hs
  exact (mul_le_mul_of_nonneg_left hc (by norm_num only : (0 : ℝ) ≤ 17 / 20)).trans hs

/-- Under RH, the recovered actual Gaussian prefix beyond 1000 is at least 3.604. -/
theorem gaussian_prefix1000_recovered (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (901 / 250 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have h := recovered_gaussian_prefix (gamma_prefix1000_recovered hRH hb)
  linarith only [h]

/-- Under RH, the recovered actual Gaussian prefix beyond 35000 is at least 4.792045. -/
theorem gaussian_prefix35000_recovered (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (958409 / 200000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have h := recovered_gaussian_prefix (gamma_prefix35000_recovered hRH hb)
  linarith only [h]

/-- Under RH, the recovered actual Gaussian prefix beyond 50000 is at least 4.89838. -/
theorem gaussian_prefix50000_recovered (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (244919 / 50000 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have h := recovered_gaussian_prefix (gamma_prefix50000_recovered hRH hb)
  linarith only [h]

end PseudoPrime.LLS
