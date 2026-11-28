/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseBoxes107
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInterval626
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftReflected
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftEuler
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhase107

/-! # Four certified lower endpoints of the section 107 phase remainder -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected main polynomial is bounded by its value at the upper
logarithmic endpoint because all its factors are nonnegative and increasing. -/
theorem phase_ref_main_box107 {x h : ℝ} (hx : 1 / 5 ≤ x) (hh : x ≤ h) :
    phaseRefMainPoly107 x ≤ phaseRefMainPoly107 h := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hz := sub_nonneg.mpr hx
  unfold phaseRefMainPoly107
  apply Finset.sum_le_sum
  intro k _
  exact
    mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz (sub_le_sub_right hh _) _)
        (Nat.cast_nonneg _))
      (Analysis.log_power_tail_poly_mono (by norm_num only) hx0 hh k)
      (Analysis.log_power_tail_poly_nonneg (by norm_num only) hx0 k)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hz.trans (sub_le_sub_right hh _)) _))

/-- The reflected slope coefficient is bounded by evaluating its positive
part at h and its negative part at l. -/
@[expose]
noncomputable def phaseRefSlopeBox107 (l h : ℝ) (k : ℕ) : ℝ :=
  ((38 / 25) * (Nat.choose 5 k : ℝ) * (h - 1 / 5) ^ (5 - k) -
      5 * (Nat.choose 4 k : ℝ) * (l - 1 / 5) ^ (4 - k)) /
    24

/-- The reflected error polynomial is bounded by the endpoint boundary
factor and the six signed moment bounds over the logarithmic interval. -/
theorem phase_ref_error_box107 {l x h : ℝ} (hl : 5 ≤ l) (hx : x ∈ Set.Icc l h) :
    phaseRefErrorPoly107 x ≤
      h ^ 2 / 24 * (2 * h - 1 / 5) ^ 5 +
        ∑ k ∈ Finset.range 6,
          phaseRefSlopeBox107 l h k * Analysis.logPowerTailPoly (51 / 50) (k + 2) h := by
  have hx0 : 0 ≤ x := by linarith only [hl, hx.1]
  have hlz : 0 ≤ l - 1 / 5 := by linarith only [hl]
  have hxz : 0 ≤ x - 1 / 5 := hlz.trans (sub_le_sub_right hx.1 _)
  have hc (k : ℕ) : twoShiftSlopeCoeff (x - 1 / 5) k ≤ phaseRefSlopeBox107 l h k := by
    apply div_le_div_of_nonneg_right _ (by norm_num only)
    exact
      sub_le_sub
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxz (sub_le_sub_right hx.2 _) _)
          (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlz (sub_le_sub_right hx.1 _) _)
          (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)))
  have hb : 0 ≤ 2 * x - 1 / 5 := by linarith only [hl, hx.1]
  unfold phaseRefErrorPoly107
  apply add_le_add
  · exact
      mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ hx0 hx.2 2) (by norm_num only))
        (pow_le_pow_left₀ hb (by linarith only [hx.2]) 5) (pow_nonneg hb _)
        (div_nonneg (sq_nonneg _) (by norm_num only))
  apply Finset.sum_le_sum
  intro k hk
  exact
    mul_le_mul (hc k) (Analysis.log_power_tail_poly_mono (by norm_num only) hx0 hx.2 (k + 2))
      (Analysis.log_power_tail_poly_nonneg (by norm_num only) hx0 (k + 2))
      ((twoShiftSlopeCoeff_nonneg (by linarith only [hl, hx.1]) (Finset.mem_range.mp hk)).trans
        (hc k))

private theorem signed_term_cap {a b A B : ℝ} (ha : a ≤ A) (hb : b ≤ B) (ha0 : 0 ≤ a) (hB : 0 ≤ B) :
    a * b ≤ A * B :=
  (mul_le_mul_of_nonneg_left hb ha0).trans (mul_le_mul_of_nonneg_right ha hB)

private theorem phase_endpoint107 {r l h P Q U V M E F G T c : ℝ} (hr : 0 < r) (hl : 5 ≤ l)
    (hx : Real.log (r ^ 2) ∈ Set.Icc l h) (hp : Real.exp (-(13 / 25) * Real.log (r ^ 2)) ≤ P)
    (hq : Real.exp (-(51 / 50) * Real.log (r ^ 2)) ≤ Q)
    (hu : Real.exp (-(77 / 50) * Real.log (r ^ 2)) ≤ U)
    (hv : Real.exp (-(51 / 25) * Real.log (r ^ 2)) ≤ V)
    (hm : phaseEulerMainPoly107 (Real.log (r ^ 2)) ≤ M)
    (he : phaseEulerErrorPoly107 (Real.log (r ^ 2)) ≤ E)
    (hf : phaseRefMainPoly107 (Real.log (r ^ 2)) ≤ F)
    (hg : phaseRefErrorPoly107 (Real.log (r ^ 2)) ≤ G)
    (ht :
      ((51 / 50 : ℝ) ^ 5 / 30) * ((91 / 200) * 1.22629816 * (h - 1 / 5) ^ 5 - (11 / 25) * l ^ 5) ≤
        T)
    (hM : 0 ≤ M) (hE : 0 ≤ E) (hF : 0 ≤ F) (hG : 0 ≤ G) (hT : 0 ≤ T)
    (hc :
      c ≤
        1.650951366 - 0.000002191 - P * (4 * M + T) - 4 * Q * E + 10.52995361 / r -
          0.004341455 * (U * F + V * G)) :
    c ≤ phaseClosed107 r := by
  let x := Real.log (r ^ 2)
  have hx0 : 0 ≤ x := by linarith only [hl, hx.1]
  have hε := exp_h.2
  have ht₁ :=
    mul_le_mul hε
      (pow_le_pow_left₀ (show 0 ≤ x - 1 / 5 by linarith only [hl, hx.1]) (sub_le_sub_right hx.2 _)
        5)
      (pow_nonneg (by linarith only [hl, hx.1]) _) (by norm_num only)
  have ht₂ := pow_le_pow_left₀ (show 0 ≤ l by linarith only [hl]) hx.1 5
  have ht' : -phaseMainPoly107 x ≤ 4 * M + T := by
    unfold phaseMainPoly107
    linarith only [hm, ht, ht₁, ht₂]
  have hmain := signed_term_cap hp ht' (Real.exp_pos _).le (by positivity)
  have herr := signed_term_cap hq he (Real.exp_pos _).le hE
  have hF' := signed_term_cap hu hf (Real.exp_pos _).le hF
  have hG' := signed_term_cap hv hg (Real.exp_pos _).le hG
  have href :=
    mul_le_mul_of_nonneg_left (add_le_add hF' hG')
      (show 0 ≤ phaseRefCoeff107 from
        (by norm_num only : (0 : ℝ) ≤ 0.004341453).trans phase_ref_coeff107_bounds.1)
  have href' :=
    mul_le_mul_of_nonneg_right phase_ref_coeff107_bounds.2
      (show 0 ≤ U * F + V * G from
        add_nonneg (mul_nonneg ((Real.exp_pos _).le.trans hu) hF)
          (mul_nonneg ((Real.exp_pos _).le.trans hv) hG))
  have hrec := div_le_div_of_nonneg_right phase_recip107_bounds.1 hr.le
  rw [phase_closed_log107 hr, ←
    show x = 2 * Real.log r by
      dsimp only [x]; rw [Real.log_pow]; norm_num only [Nat.cast_ofNat]]
  unfold phaseLog107
  rw [show -x / 2 = -Real.log r by
      dsimp only [x]; rw [Real.log_pow]; norm_num only [Nat.cast_ofNat]; ring,
    Real.exp_neg (Real.log r), Real.exp_log hr, ← div_eq_mul_inv]
  linarith only [hc, phasePole107_lower, hmain, herr, href, href', hrec]

/-- At radius 313 the closed two-frequency remainder is at least 0.01569. -/
theorem phase_remainder107_313 : 0.01569 ≤ phaseClosed107 313 := by
  obtain ⟨hx, hp, hq, hu, hv⟩ := phase_box107_313
  have hX : (313 : ℝ) ^ 2 = 97969 := by norm_num only
  rw [← hX] at hx hp hq hu hv
  have hl : (5 : ℝ) ≤ 11492406369080 / 10 ^ 12 := by norm_num only
  have hm := phase_euler_main_box107 (by linarith only [hl]) hx
  have he := phase_euler_error_box107 hl hx
  have hf := phase_ref_main_box107 (by linarith only [hl, hx.1]) hx.2
  have hg := phase_ref_error_box107 hl hx
  refine
      phase_endpoint107 (M := 32482399 / 10 ^ 6) (E := 183725488 / 10 ^ 6) (F :=
        18979424989102 / 10 ^ 6) (G := 101315402219192 / 10 ^ 6) (T := 524390314 / 10 ^ 6)
        (by norm_num only) hl hx hp.2 hq.2 hu.2 hv.2 (hm.trans ?_) (he.trans ?_) (hf.trans ?_)
        (hg.trans ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    norm_num only [phaseRefMainPoly107, phaseRefSlopeBox107, Analysis.logPowerTailPoly,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]

private theorem phase_3136_exp {p d : ℕ} {u : ℚ}
    (hc : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 98344 0 u p d = true) :
    Real.exp (-(p : ℝ) / d * Real.log ((1568 / 5 : ℝ) ^ 2)) ≤ u := by
  have h := (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat] at h
  rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 98344), mul_comm] at h
  apply le_trans _ h
  apply Real.exp_le_exp.mpr
  exact
    mul_le_mul_of_nonpos_left (Real.log_le_log (by norm_num only) (by norm_num only))
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg p)) (Nat.cast_nonneg d))

/-- At radius 1568/5 the closed two-frequency remainder is at least 0.01616. -/
theorem phase_remainder107_3136 : 0.01616 ≤ phaseClosed107 (1568 / 5) := by
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 98344) (j := 16) (n := 48) (lo :=
        11496226700 / 10 ^ 9) (hi := 12) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 98345) (j := 16) (n := 48) (lo := 11) (hi :=
        11496237100 / 10 ^ 9) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hlo hhi
  have hx : Real.log ((1568 / 5 : ℝ) ^ 2) ∈ Set.Icc (11496226700 / 10 ^ 9) (11496237100 / 10 ^ 9) :=
    ⟨le_trans (show _ ≤ Real.log 98344 by linarith only [hlo])
        (Real.log_le_log (show (0 : ℝ) < 98344 by norm_num only) (by norm_num only)),
      (Real.log_le_log (y := (98345 : ℝ)) (by norm_num only) (by norm_num only)).trans
        (by linarith only [hhi])⟩
  have hp := phase_3136_exp (p := 13) (d := 25) (u := 25337928618289 / 10 ^ 16) (by decide +kernel)
  have hq := phase_3136_exp (p := 51) (d := 50) (u := 80797360614 / 10 ^ 16) (by decide +kernel)
  have hu := phase_3136_exp (p := 77) (d := 50) (u := 204723777 / 10 ^ 16) (by decide +kernel)
  have hv := phase_3136_exp (p := 51) (d := 25) (u := 652823 / 10 ^ 16) (by decide +kernel)
  push_cast only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hp hq hu hv
  simp only [Nat.cast_ofNat, neg_div] at hp hq hu hv
  have hl : (5 : ℝ) ≤ 11496226700 / 10 ^ 9 := by norm_num only
  have hm := phase_euler_main_box107 (by linarith only [hl]) hx
  have he := phase_euler_error_box107 hl hx
  have hf := phase_ref_main_box107 (by linarith only [hl, hx.1]) hx.2
  have hg := phase_ref_error_box107 hl hx
  refine
      phase_endpoint107 (M := 32504247 / 10 ^ 6) (E := 183987210 / 10 ^ 6) (F :=
        19008016820085 / 10 ^ 6) (G := 101545620463190 / 10 ^ 6) (T := 525400731 / 10 ^ 6)
        (by norm_num only) hl hx hp hq hu hv (hm.trans ?_) (he.trans ?_) (hf.trans ?_) (hg.trans ?_)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    norm_num only [phaseRefMainPoly107, phaseRefSlopeBox107, Analysis.logPowerTailPoly,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]

private theorem phase_exp_upper107 {N u : ℚ} {p d : ℕ} (hN : 0 < (N : ℝ))
    (h : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck N 0 u p d = true) :
    Real.exp (-(p : ℝ) / d * Real.log (N : ℝ)) ≤ (u : ℝ) := by
  rw [mul_comm, ← Real.rpow_def_of_pos hN]
  exact (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound h).2

/-- At radius 300, the closed phase remainder exceeds the
lower bound used by the section 107 interval comparison. -/
theorem phase_remainder107_300 : 0.00375 ≤ phaseClosed107 300 := by
  have hx :=
    Analysis.rationalLogIntervalCheck_sound (N := 90000) (j := 16) (n := 48) (lo :=
      11407564919 / 10 ^ 9) (hi := 11407564980 / 10 ^ 9) (by decide +kernel)
  have hp :=
    phase_exp_upper107 (N := 90000) (p := 13) (d := 25) (u := 2653346053845823 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hq :=
    phase_exp_upper107 (N := 90000) (p := 51) (d := 50) (u := 8844486846154 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hu :=
    phase_exp_upper107 (N := 90000) (p := 77) (d := 50) (u := 23467484273 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hv :=
    phase_exp_upper107 (N := 90000) (p := 51) (d := 25) (u := 78224949 / 10 ^ 18) (by norm_num only)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, neg_div] at hx hp hq hu hv
  have hX : (300 : ℝ) ^ 2 = 90000 := by norm_num only
  rw [← hX] at hx hp hq hu hv
  have hl : (5 : ℝ) ≤ 11407564919 / 1000000000 := by norm_num only
  have hm := phase_euler_main_box107 (by linarith only [hl]) hx
  have he := phase_euler_error_box107 hl hx
  have hf := phase_ref_main_box107 (by linarith only [hl, hx.1]) hx.2
  have hg := phase_ref_error_box107 hl hx
  refine
      phase_endpoint107 (by norm_num only) hl hx hp hq hu hv hm he hf hg (le_refl _) ?_ ?_ ?_ ?_ ?_
        ?_ <;>
    norm_num only [phaseRefMainPoly107, phaseRefSlopeBox107, Analysis.logPowerTailPoly,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]

/-- At radius 304, the closed phase remainder exceeds the
lower bound used by the section 107 interval comparison. -/
theorem phase_remainder107_304 : 0.00745 ≤ phaseClosed107 304 := by
  have hx :=
    Analysis.rationalLogIntervalCheck_sound (N := 92416) (j := 16) (n := 48) (lo :=
      11434055372 / 10 ^ 9) (hi := 11434055433 / 10 ^ 9) (by decide +kernel)
  have hp :=
    phase_exp_upper107 (N := 92416) (p := 13) (d := 25) (u := 2617046703324562 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hq :=
    phase_exp_upper107 (N := 92416) (p := 51) (d := 50) (u := 8608706260938 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hu :=
    phase_exp_upper107 (N := 92416) (p := 77) (d := 50) (u := 22529386342 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hv :=
    phase_exp_upper107 (N := 92416) (p := 51) (d := 25) (u := 74109825 / 10 ^ 18) (by norm_num only)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, neg_div] at hx hp hq hu hv
  have hX : (304 : ℝ) ^ 2 = 92416 := by norm_num only
  rw [← hX] at hx hp hq hu hv
  have hl : (5 : ℝ) ≤ 2858513843 / 250000000 := by norm_num only
  have hm := phase_euler_main_box107 (by linarith only [hl]) hx
  have he := phase_euler_error_box107 hl hx
  have hf := phase_ref_main_box107 (by linarith only [hl, hx.1]) hx.2
  have hg := phase_ref_error_box107 hl hx
  refine
      phase_endpoint107 (by norm_num only) hl hx hp hq hu hv hm he hf hg (le_refl _) ?_ ?_ ?_ ?_ ?_
        ?_ <;>
    norm_num only [phaseRefMainPoly107, phaseRefSlopeBox107, Analysis.logPowerTailPoly,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]

/-- At radius 308, the closed phase remainder exceeds the
lower bound used by the section 107 interval comparison. -/
theorem phase_remainder107_308 : 0.01113 ≤ phaseClosed107 308 := by
  have hx :=
    Analysis.rationalLogIntervalCheck_sound (N := 94864) (j := 16) (n := 48) (lo :=
      11460199535 / 10 ^ 9) (hi := 11460199596 / 10 ^ 9) (by decide +kernel)
  have hp :=
    phase_exp_upper107 (N := 94864) (p := 13) (d := 25) (u := 2581708798490955 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hq :=
    phase_exp_upper107 (N := 94864) (p := 51) (d := 50) (u := 8382171423673 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hu :=
    phase_exp_upper107 (N := 94864) (p := 77) (d := 50) (u := 21640325716 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hv :=
    phase_exp_upper107 (N := 94864) (p := 51) (d := 25) (u := 70260799 / 10 ^ 18) (by norm_num only)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, neg_div] at hx hp hq hu hv
  have hX : (308 : ℝ) ^ 2 = 94864 := by norm_num only
  rw [← hX] at hx hp hq hu hv
  have hl : (5 : ℝ) ≤ 2292039907 / 200000000 := by norm_num only
  have hm := phase_euler_main_box107 (by linarith only [hl]) hx
  have he := phase_euler_error_box107 hl hx
  have hf := phase_ref_main_box107 (by linarith only [hl, hx.1]) hx.2
  have hg := phase_ref_error_box107 hl hx
  refine
      phase_endpoint107 (by norm_num only) hl hx hp hq hu hv hm he hf hg (le_refl _) ?_ ?_ ?_ ?_ ?_
        ?_ <;>
    norm_num only [phaseRefMainPoly107, phaseRefSlopeBox107, Analysis.logPowerTailPoly,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]

/-- At radius 312, the closed phase remainder exceeds the
lower bound used by the section 107 interval comparison. -/
theorem phase_remainder107_312 : 0.01478 ≤ phaseClosed107 312 := by
  have hx :=
    Analysis.rationalLogIntervalCheck_sound (N := 97344) (j := 16) (n := 48) (lo :=
      11486006345 / 10 ^ 9) (hi := 11486006406 / 10 ^ 9) (by decide +kernel)
  have hp :=
    phase_exp_upper107 (N := 97344) (p := 13) (d := 25) (u := 2547294877305848 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hq :=
    phase_exp_upper107 (N := 97344) (p := 51) (d := 50) (u := 8164406658033 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hu :=
    phase_exp_upper107 (N := 97344) (p := 77) (d := 50) (u := 20797151258 / 10 ^ 18)
      (by norm_num only) (by decide +kernel)
  have hv :=
    phase_exp_upper107 (N := 97344) (p := 51) (d := 25) (u := 66657538 / 10 ^ 18) (by norm_num only)
      (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, neg_div] at hx hp hq hu hv
  have hX : (312 : ℝ) ^ 2 = 97344 := by norm_num only
  rw [← hX] at hx hp hq hu hv
  have hl : (5 : ℝ) ≤ 2297201269 / 200000000 := by norm_num only
  have hm := phase_euler_main_box107 (by linarith only [hl]) hx
  have he := phase_euler_error_box107 hl hx
  have hf := phase_ref_main_box107 (by linarith only [hl, hx.1]) hx.2
  have hg := phase_ref_error_box107 hl hx
  refine
      phase_endpoint107 (by norm_num only) hl hx hp hq hu hv hm he hf hg (le_refl _) ?_ ?_ ?_ ?_ ?_
        ?_ <;>
    norm_num only [phaseRefMainPoly107, phaseRefSlopeBox107, Analysis.logPowerTailPoly,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]

end PseudoPrime.PrimeTestBounds.MillerRabin
