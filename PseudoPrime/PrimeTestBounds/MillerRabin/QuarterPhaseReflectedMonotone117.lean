/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeShiftReflected117
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseGap107
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeShiftReflected117
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseBoxes117

/-! # Monotonicity of the section 117 reflected caps -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private noncomputable def refMain117 (h x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 6,
    (Nat.choose 5 k : ℝ) * (x - h) ^ (5 - k) * Analysis.logPowerTailPoly (13 / 25) k x

private noncomputable def refError117 (h x : ℝ) : ℝ :=
  x ^ 2 / 24 * (2 * x - h) ^ 5 +
    ∑ k ∈ Finset.range 6,
      twoShiftSlopeCoeff (x - h) k * Analysis.logPowerTailPoly (51 / 50) (k + 2) x

private theorem ref_cap_log_eq117 (h x : ℝ) :
    threeShiftReflectedCap (Real.exp x) h =
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * h)) *
        (Real.exp (-(77 / 50) * x) * refMain117 h x +
          Real.exp (-(51 / 25) * x) * refError117 h x) := by
  have hm (d : ℝ) (k : ℕ) := forward_moment_scale (d := d) (t := Real.exp x) (Real.exp_pos x) k
  simp only [Real.log_exp] at hm
  unfold threeShiftReflectedCap refMain117 refError117 twoShiftReflectedDensity
  simp only [Real.log_exp, hm, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos x)]
  rw [show x + (x - h) = 2 * x - h by ring]
  have hmain :
    (∑ k ∈ Finset.range 6,
        (Nat.choose 5 k : ℝ) * (x - h) ^ (5 - k) *
          (Real.exp (-(13 / 25) * x) * Analysis.logPowerTailPoly (13 / 25) k x)) =
      Real.exp (-(13 / 25) * x) *
        ∑ k ∈ Finset.range 6,
          (Nat.choose 5 k : ℝ) * (x - h) ^ (5 - k) * Analysis.logPowerTailPoly (13 / 25) k x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have herr :
    (∑ k ∈ Finset.range 6,
        twoShiftSlopeCoeff (x - h) k *
          (Real.exp (-(51 / 50) * x) * Analysis.logPowerTailPoly (51 / 50) (k + 2) x)) =
      Real.exp (-(51 / 50) * x) *
        ∑ k ∈ Finset.range 6,
          twoShiftSlopeCoeff (x - h) k * Analysis.logPowerTailPoly (51 / 50) (k + 2) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hB : Real.exp (x * (1 / 2)) * Real.exp (x * -(38 / 25)) = Real.exp (-(51 / 50) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₁ :
    Real.exp (-(51 / 50) * (x - h)) * Real.exp (-(13 / 25) * x) =
      Real.exp ((51 / 50) * h) * Real.exp (-(77 / 50) * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h₂ :
    Real.exp (-(51 / 50) * (x - h)) * Real.exp (-(51 / 50) * x) =
      Real.exp ((51 / 50) * h) * Real.exp (-(51 / 25) * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hmain, herr]
  linear_combination (norm := ring)
    ((51 / 50 : ℝ) ^ 5 / 120) *
      ((∑ k ∈ Finset.range 6,
            (Nat.choose 5 k : ℝ) * (x - h) ^ (5 - k) * Analysis.logPowerTailPoly (13 / 25) k x) *
          h₁ +
        ((x ^ 2 / 24 * (2 * x - h) ^ 5) +
            ∑ k ∈ Finset.range 6,
              twoShiftSlopeCoeff (x - h) k * Analysis.logPowerTailPoly (51 / 50) (k + 2) x) *
          h₂ +
        (Real.exp (-(51 / 50) * (x - h)) * (x ^ 2 / 24) * (2 * x - h) ^ 5) * hB)

private noncomputable def nearRefMainCoeff117 : Fin 6 → ℝ :=
  ![17678878548043170957 / 60335112500000, 2227860271655961 / 9282325000, 300796582953 / 3570125,
    171989876 / 10985, 257480 / 169, 800 / 13]

private theorem near_ref_main_expand117 (x : ℝ) :
    refMain117 (1 / 50) x = ∑ k : Fin 6, nearRefMainCoeff117 k * (x - 4) ^ k.val := by
  unfold refMain117 nearRefMainCoeff117
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, Nat.reduceAdd, Nat.reduceSub, Analysis.logPowerTailPoly, Matrix.cons_val_zero,
    Matrix.cons_val_succ, twoShiftSlopeCoeff]
  ring

private theorem near_ref_main_antitone117 :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-(77 / 50) * x) * refMain117 (1 / 50) x) (Set.Ici 11) := by
  simp only [near_ref_main_expand117]
  apply damped_sum107
  · intro k
    fin_cases k <;>
      norm_num only [nearRefMainCoeff117, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · intro k
    fin_cases k <;> norm_num only

private noncomputable def nearRefErrorCoeff117 : Fin 8 → ℝ :=
  ![294790312575571463021504447 / 2383747113041718750000,
    67548019176403396449479 / 384692505937500000, 4905669329170601699322541 / 43990719502500000000,
    4131664993817110277 / 101478015000000, 1549503384684941 / 169130025000, 7391203231 / 5852250,
    426127 / 4335, 508 / 153]

private theorem near_ref_error_expand117 (x : ℝ) :
    refError117 (1 / 50) x = ∑ k : Fin 8, nearRefErrorCoeff117 k * (x - 4) ^ k.val := by
  unfold refError117 nearRefErrorCoeff117
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, Nat.reduceAdd, Nat.reduceSub, Analysis.logPowerTailPoly, Matrix.cons_val_zero,
    Matrix.cons_val_succ, twoShiftSlopeCoeff]
  ring

private theorem near_ref_error_antitone117 :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-(51 / 25) * x) * refError117 (1 / 50) x) (Set.Ici 11) := by
  simp only [near_ref_error_expand117]
  apply damped_sum107
  · intro k
    fin_cases k <;>
      norm_num only [nearRefErrorCoeff117, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · intro k
    fin_cases k <;> norm_num only

private noncomputable def farRefMainCoeff117 : Fin 6 → ℝ :=
  ![3584103474015507 / 19307236000, 2402711665881 / 14851720, 1755316023 / 28561, 27562180 / 2197,
    229400 / 169, 800 / 13]

private theorem far_ref_main_expand117 (x : ℝ) :
    refMain117 (11 / 10) x = ∑ k : Fin 6, farRefMainCoeff117 k * (x - 4) ^ k.val := by
  unfold refMain117 farRefMainCoeff117
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, Nat.reduceAdd, Nat.reduceSub, Analysis.logPowerTailPoly, Matrix.cons_val_zero,
    Matrix.cons_val_succ, twoShiftSlopeCoeff]
  ring

private theorem far_ref_main_antitone117 :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-(77 / 50) * x) * refMain117 (11 / 10) x) (Set.Ici 11) := by
  simp only [far_ref_main_expand117]
  apply damped_sum107
  · intro k
    fin_cases k <;> norm_num only [farRefMainCoeff117, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · intro k
    fin_cases k <;> norm_num only

private noncomputable def farRefErrorCoeff117 : Fin 8 → ℝ :=
  ![51197244559916952197497 / 762799076173350000, 113350870279384794761 / 1107914417100000,
    990520743318763618391 / 14077030240800000, 4546298486704277 / 162364824000,
    9332808299071 / 1353040200, 244360951 / 234090, 77453 / 867, 508 / 153]

private theorem far_ref_error_expand117 (x : ℝ) :
    refError117 (11 / 10) x = ∑ k : Fin 8, farRefErrorCoeff117 k * (x - 4) ^ k.val := by
  unfold refError117 farRefErrorCoeff117
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, Nat.reduceAdd, Nat.reduceSub, Analysis.logPowerTailPoly, Matrix.cons_val_zero,
    Matrix.cons_val_succ, twoShiftSlopeCoeff]
  ring

private theorem far_ref_error_antitone117 :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-(51 / 25) * x) * refError117 (11 / 10) x) (Set.Ici 11) := by
  simp only [far_ref_error_expand117]
  apply damped_sum107
  · intro k
    fin_cases k <;>
      norm_num only [farRefErrorCoeff117, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · intro k
    fin_cases k <;> norm_num only

/-- The section 117 reflected caps at the near and far shifts decrease
above logarithmic cutoff eleven. The translated polynomial coefficients are positive. -/
theorem ref_cap_antitone117 {h : ℝ} (hh : h = 1 / 50 ∨ h = 11 / 10) :
    AntitoneOn (fun x : ℝ ↦ threeShiftReflectedCap (Real.exp x) h) (Set.Ici 11) := by
  intro x hx y hy hxy
  change threeShiftReflectedCap (Real.exp y) h ≤ threeShiftReflectedCap (Real.exp x) h
  rw [ref_cap_log_eq117, ref_cap_log_eq117]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases hh with rfl | rfl
  · exact add_le_add (near_ref_main_antitone117 hx hy hxy) (near_ref_error_antitone117 hx hy hxy)
  · exact add_le_add (far_ref_main_antitone117 hx hy hxy) (far_ref_error_antitone117 hx hy hxy)

private theorem ref_poly_le117 {N : ℕ} (C : Fin N → ℝ) (hC : ∀ k, 0 ≤ C k) {x u : ℝ} (hx : 4 ≤ x)
    (hu : x ≤ u) : (∑ k : Fin N, C k * (x - 4) ^ k.val) ≤ ∑ k : Fin N, C k * (u - 4) ^ k.val := by
  apply Finset.sum_le_sum
  intro k _
  exact
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hx) (sub_le_sub_right hu _) _)
      (hC k)

private theorem ref_cap_box117 {h x m e M E K : ℝ} (hm : Real.exp (-(77 / 50) * x) ≤ m)
    (he : Real.exp (-(51 / 25) * x) ≤ e) (hM : refMain117 h x ≤ M) (hE : refError117 h x ≤ E)
    (hM0 : 0 ≤ M) (hE0 : 0 ≤ E) (hK : Real.exp ((51 / 50) * h) ≤ K) :
    threeShiftReflectedCap (Real.exp x) h ≤ ((51 / 50 : ℝ) ^ 5 / 120 * K) * (m * M + e * E) := by
  rw [ref_cap_log_eq117]
  have ha :=
    (mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right hm hM0)
  have hb :=
    (mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right he hE0)
  have hsum : 0 ≤ m * M + e * E :=
    add_nonneg (mul_nonneg ((Real.exp_pos _).le.trans hm) hM0)
      (mul_nonneg ((Real.exp_pos _).le.trans he) hE0)
  calc
    _ ≤ _ * (m * M + e * E) := mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by norm_num only)) hsum

/-- Evaluate the near reflected cap with upper bounds for the logarithm and
its two decaying exponential factors. -/
private theorem near_ref_cap_box117 {x u m e M E : ℝ} (hx : 4 ≤ x) (hu : x ≤ u)
    (hm : Real.exp (-(77 / 50) * x) ≤ m) (he : Real.exp (-(51 / 25) * x) ≤ e)
    (hM : refMain117 (1 / 50) u ≤ M) (hE : refError117 (1 / 50) u ≤ E) (hM0 : 0 ≤ M) (hE0 : 0 ≤ E) :
    threeShiftReflectedCap (Real.exp x) (1 / 50) ≤
      ((51 / 50 : ℝ) ^ 5 / 120 * 1.020609504) * (m * M + e * E) := by
  refine ref_cap_box117 hm he ?_ ?_ hM0 hE0 ?_
  · rw [near_ref_main_expand117] at hM ⊢
    apply (ref_poly_le117 _ _ hx hu).trans hM
    intro k
    fin_cases k <;>
      norm_num only [nearRefMainCoeff117, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · rw [near_ref_error_expand117] at hE ⊢
    apply (ref_poly_le117 _ _ hx hu).trans hE
    intro k
    fin_cases k <;>
      norm_num only [nearRefErrorCoeff117, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · have h :=
      Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (1 / 50)) (n := 24)
        (by norm_num only) (by norm_num only)
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one] at h
    linarith only [h]

/-- Evaluate the far reflected cap with upper bounds for the logarithm and
its two decaying exponential factors. -/
private theorem far_ref_cap_box117 {x u m e M E : ℝ} (hx : 4 ≤ x) (hu : x ≤ u)
    (hm : Real.exp (-(77 / 50) * x) ≤ m) (he : Real.exp (-(51 / 25) * x) ≤ e)
    (hM : refMain117 (11 / 10) u ≤ M) (hE : refError117 (11 / 10) u ≤ E) (hM0 : 0 ≤ M)
    (hE0 : 0 ≤ E) :
    threeShiftReflectedCap (Real.exp x) (11 / 10) ≤
      ((51 / 50 : ℝ) ^ 5 / 120 * 3.070990047) * (m * M + e * E) := by
  refine ref_cap_box117 hm he ?_ ?_ hM0 hE0 ?_
  · rw [far_ref_main_expand117] at hM ⊢
    apply (ref_poly_le117 _ _ hx hu).trans hM
    intro k
    fin_cases k <;> norm_num only [farRefMainCoeff117, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · rw [far_ref_error_expand117] at hE ⊢
    apply (ref_poly_le117 _ _ hx hu).trans hE
    intro k
    fin_cases k <;>
      norm_num only [farRefErrorCoeff117, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · have h :=
      Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (11 / 10)) (n := 24)
        (by norm_num only) (by norm_num only)
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one] at h
    linarith only [h]

/-- The near and far reflected caps at radius 314 have rational upper bounds. -/
theorem section117_ref_cap_314 :
    threeShiftReflectedCap ((314 : ℝ) ^ 2) (1 / 50) ≤ 383850 / 10 ^ 8 ∧
      threeShiftReflectedCap ((314 : ℝ) ^ 2) (11 / 10) ≤ 931205 / 10 ^ 8 := by
  have hx := section117_log_box_314
  obtain ⟨_, _, hm, he⟩ := section117_exp_box_314
  have hq : Real.exp (2 * Real.log (314 : ℝ)) = (314 : ℝ) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log (by norm_num only), sq]
  rw [← hq]
  constructor
  · refine
      (near_ref_cap_box117 (M := 19709192) (E := 105700238) (by linarith only [hx.1]) hx.2 hm.2 he.2
            ?_ ?_ (by norm_num only) (by norm_num only)).trans
        ?_
    · rw [near_ref_main_expand117]
      norm_num only [nearRefMainCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · rw [near_ref_error_expand117]
      norm_num only [nearRefErrorCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · norm_num only
  · refine
      (far_ref_cap_box117 (M := 15895982) (E := 83471312) (by linarith only [hx.1]) hx.2 hm.2 he.2
            ?_ ?_ (by norm_num only) (by norm_num only)).trans
        ?_
    · rw [far_ref_main_expand117]
      norm_num only [farRefMainCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · rw [far_ref_error_expand117]
      norm_num only [farRefErrorCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · norm_num only

/-- The near and far reflected caps at radius 314.45 have rational upper bounds. -/
theorem section117_ref_cap_314_45 :
    threeShiftReflectedCap ((6289 / 20 : ℝ) ^ 2) (1 / 50) ≤ 382582 / 10 ^ 8 ∧
      threeShiftReflectedCap ((6289 / 20 : ℝ) ^ 2) (11 / 10) ≤ 928174 / 10 ^ 8 := by
  have hx := section117_log_box_314_45
  obtain ⟨_, _, hm, he⟩ := section117_exp_box_314_45
  have hq : Real.exp (2 * Real.log (6289 / 20 : ℝ)) = (6289 / 20 : ℝ) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log (by norm_num only), sq]
  rw [← hq]
  constructor
  · refine
      (near_ref_cap_box117 (M := 19731220) (E := 105878675) (by linarith only [hx.1]) hx.2 hm.2 he.2
            ?_ ?_ (by norm_num only) (by norm_num only)).trans
        ?_
    · rw [near_ref_main_expand117]
      norm_num only [nearRefMainCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · rw [near_ref_error_expand117]
      norm_num only [nearRefErrorCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · norm_num only
  · refine
      (far_ref_cap_box117 (M := 15914500) (E := 83617097) (by linarith only [hx.1]) hx.2 hm.2 he.2
            ?_ ?_ (by norm_num only) (by norm_num only)).trans
        ?_
    · rw [far_ref_main_expand117]
      norm_num only [farRefMainCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · rw [far_ref_error_expand117]
      norm_num only [farRefErrorCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · norm_num only

/-- The near and far reflected caps at radius 315 have rational upper bounds. -/
theorem section117_ref_cap_315 :
    threeShiftReflectedCap ((315 : ℝ) ^ 2) (1 / 50) ≤ 381041 / 10 ^ 8 ∧
      threeShiftReflectedCap ((315 : ℝ) ^ 2) (11 / 10) ≤ 924488 / 10 ^ 8 := by
  have hx := section117_log_box_315
  obtain ⟨_, _, hm, he⟩ := section117_exp_box_315
  have hq : Real.exp (2 * Real.log (315 : ℝ)) = (315 : ℝ) ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log (by norm_num only), sq]
  rw [← hq]
  constructor
  · refine
      (near_ref_cap_box117 (M := 19758128) (E := 106096769) (by linarith only [hx.1]) hx.2 hm.2 he.2
            ?_ ?_ (by norm_num only) (by norm_num only)).trans
        ?_
    · rw [near_ref_main_expand117]
      norm_num only [nearRefMainCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · rw [near_ref_error_expand117]
      norm_num only [nearRefErrorCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · norm_num only
  · refine
      (far_ref_cap_box117 (M := 15937121) (E := 83795292) (by linarith only [hx.1]) hx.2 hm.2 he.2
            ?_ ?_ (by norm_num only) (by norm_num only)).trans
        ?_
    · rw [far_ref_main_expand117]
      norm_num only [farRefMainCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · rw [far_ref_error_expand117]
      norm_num only [farRefErrorCoeff117, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
        Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · norm_num only

private theorem ref_near_coefficient_box117 :
    0 ≤ 3.124 - 3.143 * Real.exp (-(51 / 50 : ℝ) * (1 / 50)) ∧
      3.124 - 3.143 * Real.exp (-(51 / 50 : ℝ) * (1 / 50)) ≤ 0.04446763 := by
  have hl := Real.add_one_le_exp ((51 / 50 : ℝ) * (1 / 50))
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (1 / 50)) (n := 16) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at hu
  have hE : Real.exp ((51 / 50 : ℝ) * (1 / 50)) ≤ 1.0206095022 := by linarith only [hu]
  rw [neg_mul, Real.exp_neg, ← one_div]
  have hlo := one_div_le_one_div_of_le (Real.exp_pos _) hE
  have hhi := one_div_le_one_div_of_le (show 0 < (_ : ℝ) by norm_num only) hl
  exact ⟨by linarith only [hhi], by linarith only [hlo]⟩

/-- The combined reflected cost at this left endpoint is bounded by one rational number. -/
theorem section117_ref_cost_314 :
    4 * (3.124 - 3.143 * Real.exp (-(51 / 50) * (1 / 50))) *
          threeShiftReflectedCap ((314 : ℝ) ^ 2) (1 / 50) +
        4 * 0.0374 * threeShiftReflectedCap ((314 : ℝ) ^ 2) (11 / 10) ≤
      207585 / 10 ^ 8 := by
  obtain ⟨ha, hb⟩ := section117_ref_cap_314
  obtain ⟨h₀, h₁⟩ := ref_near_coefficient_box117
  have h :=
    (mul_le_mul_of_nonneg_left ha h₀).trans
      (mul_le_mul_of_nonneg_right h₁ (by norm_num only : (0 : ℝ) ≤ 383850 / 10 ^ 8))
  linarith only [h, hb]

/-- The combined reflected cost at this left endpoint is bounded by one rational number. -/
theorem section117_ref_cost_314_45 :
    4 * (3.124 - 3.143 * Real.exp (-(51 / 50) * (1 / 50))) *
          threeShiftReflectedCap ((6289 / 20 : ℝ) ^ 2) (1 / 50) +
        4 * 0.0374 * threeShiftReflectedCap ((6289 / 20 : ℝ) ^ 2) (11 / 10) ≤
      206906 / 10 ^ 8 := by
  obtain ⟨ha, hb⟩ := section117_ref_cap_314_45
  obtain ⟨h₀, h₁⟩ := ref_near_coefficient_box117
  have h :=
    (mul_le_mul_of_nonneg_left ha h₀).trans
      (mul_le_mul_of_nonneg_right h₁ (by norm_num only : (0 : ℝ) ≤ 382582 / 10 ^ 8))
  linarith only [h, hb]

/-- The combined reflected cost at this left endpoint is bounded by one rational number. -/
theorem section117_ref_cost_315 :
    4 * (3.124 - 3.143 * Real.exp (-(51 / 50) * (1 / 50))) *
          threeShiftReflectedCap ((315 : ℝ) ^ 2) (1 / 50) +
        4 * 0.0374 * threeShiftReflectedCap ((315 : ℝ) ^ 2) (11 / 10) ≤
      206081 / 10 ^ 8 := by
  obtain ⟨ha, hb⟩ := section117_ref_cap_315
  obtain ⟨h₀, h₁⟩ := ref_near_coefficient_box117
  have h :=
    (mul_le_mul_of_nonneg_left ha h₀).trans
      (mul_le_mul_of_nonneg_right h₁ (by norm_num only : (0 : ℝ) ≤ 381041 / 10 ^ 8))
  linarith only [h, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
