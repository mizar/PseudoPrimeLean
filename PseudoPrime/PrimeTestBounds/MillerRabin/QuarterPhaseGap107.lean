/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseMonotone107
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseEndpoints107
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftReflected

/-! # Reflected tail monotonicity and the full section 107 scalar comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem damped_monomial107 {d : ℝ} (k : ℕ) (hd : (k : ℝ) / 7 ≤ d) :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-d * x) * (x - 4) ^ k) (Set.Ici 11) := by
  intro x hx y hy hxy
  have hm := phase_shift_power_antitone107 (b := 4) le_rfl k hx hy hxy
  have he :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hxy (show -d + (k : ℝ) / 7 ≤ 0 by linarith only [hd]))
  have hn : 0 ≤ Real.exp (-(k : ℝ) / 7 * y) * (y - 4) ^ k :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg (by linarith only [Set.mem_Ici.mp hy]) _)
  have h := mul_le_mul he hm hn (Real.exp_pos _).le
  simp only [← mul_assoc, ← Real.exp_add] at h
  have hEq (z : ℝ) : (-d + (k : ℝ) / 7) * z + -(k : ℝ) / 7 * z = -d * z := by ring
  simpa only [hEq] using h

private theorem damped_sum107 {d : ℝ} {N : ℕ} (C : Fin N → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hd : ∀ k : Fin N, (k.val : ℝ) / 7 ≤ d) :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-d * x) * ∑ k : Fin N, C k * (x - 4) ^ k.val)
      (Set.Ici 11) := by
  intro x hx y hy hxy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  simpa only [mul_left_comm] using
    mul_le_mul_of_nonneg_left (damped_monomial107 k.val (hd k) hx hy hxy) (hC k)

private noncomputable def mainRefCoeffs107 : Fin 6 → ℝ :=
  ![164160736894932 / 603351125, 418115594802 / 1856465, 2287737744 / 28561, 33203920 / 2197,
    252800 / 169, 800 / 13]

private theorem main_ref_poly107 (x : ℝ) :
    phaseRefMainPoly107 x = ∑ k : Fin 6, mainRefCoeffs107 k * (x - 4) ^ k.val := by
  unfold phaseRefMainPoly107 mainRefCoeffs107
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, Nat.reduceAdd, Nat.reduceSub, Analysis.logPowerTailPoly, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring

/-- The scaled reflected main cap decreases above log cutoff eleven.
Expanding about four gives a polynomial with nonnegative coefficients. -/
theorem phase_ref_main_antitone107 :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-(77 / 50) * x) * phaseRefMainPoly107 x) (Set.Ici 11) := by
  simp only [main_ref_poly107]
  apply damped_sum107
  · intro k
    fin_cases k <;> norm_num only [mainRefCoeffs107, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · intro k
    fin_cases k <;> norm_num only

private noncomputable def errorRefCoeffs107 : Fin 8 → ℝ :=
  ![5348053026848101230844 / 47674942260834375, 16734968738154459158 / 103866976603125,
    45590854445907596191 / 439907195025000, 389262960547037 / 10147801500,
    1480955127491 / 169130025, 143392742 / 117045, 83930 / 867, 508 / 153]

private theorem error_ref_poly107 (x : ℝ) :
    phaseRefErrorPoly107 x = ∑ k : Fin 8, errorRefCoeffs107 k * (x - 4) ^ k.val := by
  unfold phaseRefErrorPoly107 errorRefCoeffs107 twoShiftSlopeCoeff
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, Nat.reduceAdd, Nat.reduceSub, Analysis.logPowerTailPoly, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring

/-- The scaled reflected error cap decreases above log cutoff eleven.
Expanding about four gives a polynomial with nonnegative coefficients. -/
theorem phase_ref_error_antitone107 :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-(51 / 25) * x) * phaseRefErrorPoly107 x) (Set.Ici 11) := by
  simp only [error_ref_poly107]
  apply damped_sum107
  · intro k
    fin_cases k <;> norm_num only [errorRefCoeffs107, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · intro k
    fin_cases k <;> norm_num only

/-- The closed two-frequency phase remainder is nondecreasing through radius 314. -/
theorem phase_closed_increasing_314 : MonotoneOn phaseClosed107 (Set.Icc 300 314) := by
  intro r hr s hs hrs
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num only) hr.1
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num only) hs.1
  let x := 2 * Real.log r
  let y := 2 * Real.log s
  have hx : x ∈ Set.Icc (2 * Real.log 300) (2 * Real.log 314) :=
    ⟨mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num only) hr.1) (by norm_num only),
      mul_le_mul_of_nonneg_left (Real.log_le_log hr0 hr.2) (by norm_num only)⟩
  have hy : y ∈ Set.Icc (2 * Real.log 300) (2 * Real.log 314) :=
    ⟨mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num only) hs.1) (by norm_num only),
      mul_le_mul_of_nonneg_left (Real.log_le_log hs0 hs.2) (by norm_num only)⟩
  have hxy : x ≤ y := mul_le_mul_of_nonneg_left (Real.log_le_log hr0 hrs) (by norm_num only)
  have hl : 11 ≤ 2 * Real.log 300 := by
    have h := phase_log107_300.1
    rw [← show (300 : ℝ) ^ 2 = 90000 by norm_num only, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  have hf := phase_forward_increasing_314 hx hy hxy
  have hm := phase_ref_main_antitone107 (hl.trans hx.1) (hl.trans hy.1) hxy
  have he := phase_ref_error_antitone107 (hl.trans hx.1) (hl.trans hy.1) hxy
  have hk : 0 ≤ phaseRefCoeff107 :=
    (by norm_num only : (0 : ℝ) ≤ 0.004341453).trans phase_ref_coeff107_bounds.1
  have hcost := mul_le_mul_of_nonneg_left (add_le_add hm he) hk
  rw [phase_closed_log107 hr0, phase_closed_log107 hs0]
  change phaseLog107 x ≤ phaseLog107 y
  unfold phaseForward107 at hf
  unfold phaseLog107
  linarith only [hf, hcost]

/-- Transfer a closed phase lower bound at a left endpoint to any larger
radius in the monotonicity interval from 300 to 314. -/
theorem phase_closed_lower107 {a r c : ℝ} (ha : 300 ≤ a) (har : a ≤ r) (hr : r ≤ 314)
    (hc : c ≤ phaseClosed107 a) : c ≤ phaseClosed107 r := by
  exact hc.trans (phase_closed_increasing_314 ⟨ha, har.trans hr⟩ ⟨ha.trans har, hr⟩ har)

/-- The four certified left endpoints lower-bound the closed phase remainder
throughout the section 107 radius range. -/
theorem phase_remainder_lower107 {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    (if 312 ≤ r then 0.01478
      else if 308 ≤ r then 0.01113 else if 304 ≤ r then 0.00745 else 0.00375) ≤
      phaseClosed107 r := by
  have hmax : r ≤ 314 := hr.2.trans (by norm_num only)
  by_cases h₁ : 312 ≤ r
  · simpa only [ite_eq_left h₁] using
      phase_closed_lower107 (by norm_num only) h₁ hmax phase_remainder107_312
  by_cases h₂ : 308 ≤ r
  · simpa only [ite_eq_right h₁, ite_eq_left h₂] using
      phase_closed_lower107 (by norm_num only) h₂ hmax phase_remainder107_308
  by_cases h₃ : 304 ≤ r
  · simpa only [ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃] using
      phase_closed_lower107 (by norm_num only) h₃ hmax phase_remainder107_304
  simpa only [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃] using
    phase_closed_lower107 (le_refl _) hr.1 hmax phase_remainder107_300

/-- The certified left endpoint bounds the closed two-frequency remainder on [313,314]. -/
theorem phase_remainder_lower_628 {r : ℝ} (hr : r ∈ Set.Icc 313 314) :
    0.01569 ≤ phaseClosed107 r := by
  exact phase_closed_lower107 (by norm_num only) hr.1 hr.2 phase_remainder107_313

/-- On the second radius interval the left endpoint improves the two-frequency bound. -/
theorem phase_remainder_lower_628_right {r : ℝ} (hr : r ∈ Set.Icc (1568 / 5) 314) :
    0.01616 ≤ phaseClosed107 r := by
  exact phase_closed_lower107 (by norm_num only) hr.1 hr.2 phase_remainder107_3136

end PseudoPrime.PrimeTestBounds.MillerRabin
