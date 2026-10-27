/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLocalBudgetCertificate
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # A complete Gamma local certificate from scale 1936 onward -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Claim: three rational upper bounds hold for log(99/40), log 49 and log 44.
Proof: exact Taylor interval checks in the kernel.
Role: certify the real anchors used on the entire scale half-line. -/
theorem local1936_anchor_logs :
    Real.log (99 / 40 : ℝ) ≤ 91 / 100 ∧
      Real.log (49 : ℝ) ≤ 39 / 10 ∧ Real.log (44 : ℝ) ≤ 19 / 5 := by
  have h1 : rationalLogIntervalCheck (99 / 40) 1 20 0 (91 / 100) = true := by decide +kernel
  have h2 : rationalLogIntervalCheck 49 6 20 0 (39 / 10) = true := by decide +kernel
  have h3 : rationalLogIntervalCheck 44 6 20 0 (19 / 5) = true := by decide +kernel
  have h1R := (rationalLogIntervalCheck_sound h1).2
  have h2R := (rationalLogIntervalCheck_sound h2).2
  have h3R := (rationalLogIntervalCheck_sound h3).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1R h2R h3R
  exact ⟨h1R, h2R, h3R⟩

/-- Input: base p>=3 and scale x>=2401. Claim: the logarithmic ramp allowance is at most 73/400.
Proof: retain log(p)>=549/500 and use the square-root tangent at 49.
Role: control the unbounded part of the scale-1936 certificate. -/
theorem gamma_odd_ramp_large1936 {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 2401 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) / Real.log p + 1) / Real.sqrt x ≤ (73 / 400 : ℝ) := by
  have hraw :=
    log_mul_add_div_sqrt_le_of_anchor (c := (99 / 40 : ℝ)) (a := 49) (b :=
      (549 / 500 : ℝ) * (73 / 400)) (d := 549 / 500) (by norm_num only) (by norm_num only)
      (by
        norm_num only; exact hx)
      (by linarith only [local1936_anchor_logs.1, local1936_anchor_logs.2.1]) (by norm_num only)
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlogp : (549 / 500 : ℝ) ≤ Real.log p := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) hpR
    linarith only [h, Real.log_three_gt_d9]
  have hcut : 0 ≤ Real.log ((99 / 40 : ℝ) * x) := Real.log_nonneg (by nlinarith only [hx])
  have hd := div_le_div_of_nonneg_left hcut (by norm_num only : (0 : ℝ) < 549 / 500) hlogp
  have hm :=
    div_le_div_of_nonneg_right
      (show
        Real.log ((99 / 40 : ℝ) * x) / Real.log p + 1 ≤
          Real.log ((99 / 40 : ℝ) * x) / (549 / 500) + 1
        by linarith only [hd])
      (Real.sqrt_nonneg x)
  have hc : (Real.log ((99 / 40 : ℝ) * x) / (549 / 500) + 1) / Real.sqrt x ≤ (73 / 400 : ℝ) := by
    have ht := Real.sqrt_pos.mpr (by linarith only [hx] : 0 < x)
    have hb := (div_le_iff₀ ht).mp hraw
    apply (div_le_iff₀ ht).mpr
    linarith only [hb]
  exact hm.trans hc

/-- Input: p>1, x>=1 and a strict upper cutoff below p^(k+1).
Claim: the retained prime-power count is at most k.
Proof: compare logarithms and apply the natural floor inequality.
Role: retain exact power counts on short finite scale intervals. -/
theorem gamma_ramp_count_le_of_power {p k : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x)
    (hpow : (99 / 40 : ℝ) * x < (p : ℝ) ^ (k + 1)) : gammaRampPowerCount p x ≤ k := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlogp := Real.log_pos hpR
  have hX : 0 < (99 / 40 : ℝ) * x := by nlinarith only [hx]
  have hlog := Real.log_lt_log hX hpow
  rw [Real.log_pow] at hlog
  have hr : Real.log ((99 / 40 : ℝ) * x) / Real.log p < (k : ℝ) + 1 := by
    apply (div_lt_iff₀ hlogp).mpr
    norm_num only [Nat.cast_add, Nat.cast_one] at hlog
    exact hlog
  have hn : ⌊Real.log ((99 / 40 : ℝ) * x) / Real.log p⌋₊ ≤ k := by
    exact
      Nat.lt_succ_iff.mp
        ((Nat.floor_lt (div_nonneg (Real.log_nonneg (by nlinarith only [hx])) hlogp.le)).mpr
          (by exact_mod_cast hr))
  dsimp only [gammaRampPowerCount]
  exact_mod_cast hn

/-- Input: p>=3 and 1936<=x<=2401. Claim: the count-based ramp allowance is at most 2/11.
Proof: the cutoff is below 3^8, so at most seven powers remain, while sqrt(x)>=44.
Role: bridge the lower scale entrance to the continuous logarithmic estimate. -/
theorem gamma_odd_ramp_small1936 {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1936 ≤ x) (hX : x ≤ 2401) :
    (gammaRampPowerCount p x + 1) / Real.sqrt x ≤ (2 / 11 : ℝ) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (99 / 40 : ℝ) * x < (p : ℝ) ^ (7 + 1) := by
    have hm := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3) hpR 8
    norm_num only at hm
    linarith only [hX, hm]
  have hn :=
    gamma_ramp_count_le_of_power (Nat.lt_of_lt_of_le (by decide : 1 < 3) hp) (by linarith only [hx])
      hpow
  norm_num only at hn
  have hs : (44 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) (by linarith only [hx])).mpr
      (by
        norm_num only; exact hx)
  apply (div_le_iff₀ (by linarith only [hs] : 0 < Real.sqrt x)).mpr
  linarith only [hn, hs]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: an odd prime. Claim: twice its signed odd Euler cost is at most 19/25.
Proof: combine the existing small-prime certificates with the large-prime bound.
Role: isolate the scale-independent Euler contribution. -/
theorem gamma_odd_euler_cost_uniform {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    2 * gammaPrimeOddEulerCost p ≤ (19 / 25 : ℝ) := by
  by_cases hl : 11 ≤ p
  · exact (gamma_large_prime_odd_cost_le (by exact_mod_cast hl)).trans (by norm_num only)
  · have hf : ∀ q ∈ Finset.range 11, q.Prime → 3 ≤ q → q ∈ ([3, 5, 7] : List ℕ) := by decide +kernel
    exact gamma_small_prime_odd_cost_le (hf p (Finset.mem_range.mpr (lt_of_not_ge hl)) hp hp3)

/-- Input: an odd prime and x>=1936. Claim: the combined square cost is at most twice mu.
Proof: use exact counts below 2401 and logarithmic bounds above it.
Role: absorb square-part losses on the lower scale half-line. -/
theorem gamma_odd_square_cost_1936 {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x : ℝ} (hx : 1936 ≤ x) :
    gammaSquareCombinedCost p x ≤ 2 * (11783423 / 25000000 : ℝ) := by
  have he := gamma_odd_euler_cost_uniform hp hp3
  by_cases hX : x ≤ 2401
  · have hr := gamma_odd_ramp_small1936 hp3 hx hX
    dsimp only [gammaSquareCombinedCost]
    linarith only [he, hr]
  · have hr := gamma_odd_ramp_large1936 hp3 (le_of_lt (lt_of_not_ge hX))
    have hc := gamma_square_combined_cost_le_log hp.one_lt (show (1 : ℝ) ≤ x by linarith only [hx])
    linarith only [he, hr, hc]

/-- Input: x>=1936. Claim: the cutoff logarithm with and without the endpoint unit
has square-root bounds 1/4 and 387/2000. Proof: apply the real tangent at 44.
Role: distinguish the minus-one and zero dyadic branches. -/
theorem gamma_cutoff_ramp_1936 {x : ℝ} (hx : 1936 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) + 1) / Real.sqrt x ≤ (1 / 4 : ℝ) ∧
      Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x ≤ (387 / 2000 : ℝ) := by
  constructor
  · exact
      log_mul_add_div_sqrt_le_of_anchor (a := 44) (by norm_num only) (by norm_num only)
        (by
          norm_num only; exact hx)
        (by linarith only [local1936_anchor_logs.1, local1936_anchor_logs.2.2]) (by norm_num only)
  · have h :=
      log_mul_add_div_sqrt_le_of_anchor (c := (99 / 40 : ℝ)) (a := 44) (b := 387 / 2000) (d := 0)
        (by norm_num only) (by norm_num only)
        (by
          norm_num only; exact hx)
        (by linarith only [local1936_anchor_logs.1, local1936_anchor_logs.2.2]) (by norm_num only)
    simpa only [add_zero] using h

/-- Input: x>=1936. Claim: the weighted minus-one dyadic ramp series is at most 1/4.
Proof: retain the signed count comparison and cancel log two.
Role: bound the odd-conductor dyadic correction without a prime-power payload. -/
theorem gamma_dyadic_minus_ramp_1936 {x : ℝ} (hx : 1936 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (1 / 4 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx0 := zero_lt_one.trans_le hx1
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hl1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hr :=
    (gamma_ramp_neg_one_series_le_count (by norm_num only : 1 < (2 : ℕ)) hx0).trans
      (div_le_div_of_nonneg_right
        (add_le_add (gamma_ramp_count_le_log (by norm_num only : 1 < (2 : ℕ)) hx1) le_rfl)
        (Real.sqrt_nonneg x))
  have hw := mul_le_mul_of_nonneg_left hr hl0.le
  have he :
    Real.log 2 * ((Real.log ((99 / 40 : ℝ) * x) / Real.log 2 + 1) / Real.sqrt x) =
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x := by
    rw [← mul_div_assoc, mul_add, mul_one,
      mul_comm (Real.log 2) (Real.log ((99 / 40 : ℝ) * x) / Real.log 2), div_mul_cancel₀ _ hl0.ne']
  norm_num only [Nat.cast_ofNat] at hw
  rw [he] at hw
  exact
    hw.trans
      ((div_le_div_of_nonneg_right (add_le_add le_rfl hl1) (Real.sqrt_nonneg x)).trans
        (gamma_cutoff_ramp_1936 hx).1)

/-- Input: x>=1936. Claim: the weighted zero dyadic ramp series is at most 387/2000.
Proof: use the zero-branch count without the extra endpoint unit.
Role: retain the sharper even-conductor branch. -/
theorem gamma_dyadic_zero_ramp_1936 {x : ℝ} (hx : 1936 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (387 / 2000 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx0 := zero_lt_one.trans_le hx1
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hr :=
    (gamma_ramp_zero_series_le_count (by norm_num only : 1 < (2 : ℕ)) hx0).trans
      (div_le_div_of_nonneg_right (gamma_ramp_count_le_log (by norm_num only : 1 < (2 : ℕ)) hx1)
        (Real.sqrt_nonneg x))
  have hw := mul_le_mul_of_nonneg_left hr hl0.le
  norm_num only [Nat.cast_ofNat] at hw
  have he :
    Real.log 2 * ((Real.log ((99 / 40 : ℝ) * x) / Real.log 2) / Real.sqrt x) =
      Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
    rw [← mul_div_assoc, mul_comm (Real.log 2) (Real.log ((99 / 40 : ℝ) * x) / Real.log 2),
      div_mul_cancel₀ _ hl0.ne']
  rw [he] at hw
  exact hw.trans (gamma_cutoff_ramp_1936 hx).2

/-- Input: a minus-one local value at two, any prefix and x>=1936.
Claim: the adjusted actual dyadic cost is at most 11/20.
Proof: add the signed Euler certificate and the new ramp bound.
Role: discharge the minus-one field of the local certificate. -/
theorem gamma_dyadic_minus_cost_1936 {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = -1)
    (K : Finset ℕ) {x : ℝ} (hx : 1936 ≤ x) :
    gammaActualPrimeLocalCost χ 2 K x - (11783423 / 25000000 : ℝ) * Real.log 4 ≤ (11 / 20 : ℝ) := by
  have he := gamma_minus_one_positive_prime_correction_le_cost χ Nat.prime_two hχ K
  have hr := gamma_dyadic_minus_ramp_1936 hx
  have hc := gamma_dyadic_weighted_euler_bounds.2
  norm_num only [Nat.cast_ofNat] at he
  dsimp only [gammaActualPrimeLocalCost]
  rw [show χ ((2 : ℕ) : ZMod f) = -1 by simpa only [Nat.cast_ofNat] using hχ]
  norm_num only [Nat.cast_ofNat]
  linarith only [he, hr, hc]

/-- Input: a zero local value at two, any prefix and x>=1936.
Claim: the actual dyadic cost is at most 4393/5000.
Proof: combine the complete Euler cost and the zero-branch ramp estimate.
Role: discharge the ramified dyadic field without a finite prefix table. -/
theorem gamma_dyadic_zero_cost_1936 {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = 0)
    (K : Finset ℕ) {x : ℝ} (hx : 1936 ≤ x) :
    gammaActualPrimeLocalCost χ 2 K x ≤ (4393 / 5000 : ℝ) := by
  have he := sum_gammaResolventMangoldtWeight_primePowers_le_cost Nat.prime_two K
  have hr := gamma_dyadic_zero_ramp_1936 hx
  have hc := gamma_dyadic_weighted_euler_bounds.1
  norm_num only [Nat.cast_ofNat] at he
  dsimp only [gammaActualPrimeLocalCost]
  simp only [Nat.cast_ofNat, map_pow, hχ, zero_pow (Nat.succ_ne_zero _), Complex.zero_re, sub_zero,
    one_mul]
  linarith only [he, hr, hc]

/-- Input: x>=1936. Claim: an actual local budget certificate holds with delta=4393/5000.
Proof: assemble the proved odd-prime and two dyadic estimates.
Role: remove all local analytic fields from the new witness entrance. -/
theorem gamma_local_certificate1936 {x : ℝ} (hx : 1936 ≤ x) :
    GammaLocalBudgetCertificate x (4393 / 5000) := by
  refine ⟨by linarith only [hx], by norm_num only, ?_, ?_, ?_⟩
  · intro f χ p hp hp3 K hχ
    exact
      (gamma_actual_minus_one_prime_cost_le χ hp hχ K (by linarith only [hx])).trans
        (mul_le_mul_of_nonneg_left (gamma_odd_square_cost_1936 hp hp3 hx)
          (Real.log_natCast_nonneg p))
  · intro f χ K hχ
    exact (gamma_dyadic_minus_cost_1936 χ hχ K hx).trans (by norm_num only)
  · intro f χ K hχ
    exact gamma_dyadic_zero_cost_1936 χ hχ K hx

end PseudoPrime.Analysis
