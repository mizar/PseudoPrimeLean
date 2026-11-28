/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # The combined Euler profile for section 137 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The six exact auxiliary frequencies in (137.11), including the main shift. -/
@[expose]
def quarterFreq663 (i : Fin 6) : ℚ :=
  21 / 8 + (![0, 1 / 10, 185 / 100, 354 / 100, 656 / 100, 666 / 100] : Fin 6 → ℚ) i

/-- The six exact auxiliary coefficients in (137.11). -/
@[expose]
def quarterCoeff663 (i : Fin 6) : ℚ :=
  (![493098778, -516255093, -47978520, -41881026, 154985393, -138841230] i) / 1000000000

/-- The shared Euler polynomial q plus the six-frequency quadratic and linear
terms of (137.12), including every ordered frequency pair. -/
@[expose]
noncomputable def quarterProfile663 (v : ℝ) : ℝ :=
  quarterAuxProfile656 v +
      (∑ i : Fin 6,
          ∑ j : Fin 6,
            (quarterCoeff663 i : ℝ) * (quarterCoeff663 j : ℝ) *
              quarterAuxPair656 ((quarterFreq663 i - quarterFreq663 j : ℚ) : ℝ) v) /
        2 -
    ∑ i : Fin 6, (quarterCoeff663 i : ℝ) * quarterAuxPair656 (quarterFreq663 i : ℝ) v

/-- The rational coefficients of q(x+w), in increasing degree in w. -/
private def shiftedCoeff (j : Fin 3) (x : ℚ) : ℚ :=
  ![3 / 8 + 33 / 80 * x + 121 / 800 * x ^ 2, 33 / 80 + 121 / 400 * x, 121 / 800] j

/-- A shifted quadratic coefficient of the paired profile, with the
exponential factor left as an argument to allow rational approximation. -/
private noncomputable def pairCoeff (j : Fin 3) (s : ℚ) : ℝ :=
  (Real.exp ((-(11 / 10) * |s| : ℚ) : ℝ) * (shiftedCoeff j (23 / 2 + |s|) : ℝ) +
      Real.exp (((11 / 10) * |s| : ℚ) : ℝ) * (shiftedCoeff j (23 / 2 - |s|) : ℝ)) /
    2

/-- The rational Taylor polynomial is shared by positive and negative
exponential arguments in the auxiliary profile. -/
private def profileExpTaylor (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 60, x ^ j / (j.factorial : ℚ)

/-- A uniform remainder of at most 10⁻¹⁶ encloses the signed exponential
arguments in the six-frequency polynomial. -/
private theorem profile_exp_error (x : ℚ) (hx : |(x : ℝ)| ≤ 11) :
    |Real.exp (x : ℝ) - (profileExpTaylor x : ℝ)| ≤ 1 / 10 ^ 16 := by
  have h :=
    Complex.exp_bound' (n := 60) (x := ((x : ℝ) : ℂ))
      (by
        rw [Complex.norm_real, Real.norm_eq_abs]; norm_num only; linarith only [hx])
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  have hc :
    ((profileExpTaylor x : ℚ) : ℂ) =
      ∑ j ∈ Finset.range 60, ((x : ℝ) : ℂ) ^ j / (j.factorial : ℂ) := by
    simp only [profileExpTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
      Complex.ofReal_ratCast]
  rw [← hc, ← Complex.ofReal_ratCast, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact
    h.trans
      ((mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx 60) (by norm_num only))
            (by norm_num only)).trans
        (by norm_num only [Nat.factorial]))

/-- The pair coefficient's exact rational approximation. -/
private def pairApprox (j : Fin 3) (s : ℚ) : ℚ :=
  (profileExpTaylor (-(11 / 10) * |s|) * shiftedCoeff j (23 / 2 + |s|) +
      profileExpTaylor ((11 / 10) * |s|) * shiftedCoeff j (23 / 2 - |s|)) /
    2

/-- An error of 10⁻¹⁶ in each exponential, multiplied by coefficients of
magnitude at most 100, gives an error of at most 10⁻¹⁴. -/
private theorem pair_coeff_error (j : Fin 3) (s : ℚ) (hs : abs ((11 / 10 : ℚ) * |s|) ≤ 11)
    (hp : |shiftedCoeff j (23 / 2 + |s|)| ≤ 100) (hm : |shiftedCoeff j (23 / 2 - |s|)| ≤ 100) :
    |pairCoeff j s - (pairApprox j s : ℝ)| ≤ 1 / 10 ^ 14 := by
  have hneg : |(-(11 / 10 : ℚ) * |s|)| ≤ 11 := by simpa only [neg_mul, abs_neg] using hs
  have h₁ := profile_exp_error (-(11 / 10) * |s|) (by exact_mod_cast hneg)
  have h₂ := profile_exp_error ((11 / 10) * |s|) (by exact_mod_cast hs)
  have hp' : |(shiftedCoeff j (23 / 2 + |s|) : ℝ)| ≤ 100 := by exact_mod_cast hp
  have hm' : |(shiftedCoeff j (23 / 2 - |s|) : ℝ)| ≤ 100 := by exact_mod_cast hm
  unfold pairCoeff pairApprox
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_neg] at h₁ h₂ ⊢
  rw [show
      ∀ a b c d p m : ℝ, (a * p + b * m) / 2 - (c * p + d * m) / 2 = ((a - c) * p + (b - d) * m) / 2
      from fun a b c d p m ↦ by ring,
    abs_div]
  norm_num only
  have h₁' := mul_le_mul h₁ hp' (abs_nonneg _) (by norm_num only)
  have h₂' := mul_le_mul h₂ hm' (abs_nonneg _) (by norm_num only)
  rw [← abs_mul] at h₁' h₂'
  have h := (abs_add_le _ _).trans (add_le_add h₁' h₂')
  linarith only [h]

/-- The real coefficients of the actual centered combined profile. -/
private noncomputable def profileCoeff (k : Fin 3) : ℝ :=
  (shiftedCoeff k (23 / 2) : ℝ) +
      (∑ i : Fin 6,
          ∑ j : Fin 6,
            (quarterCoeff663 i : ℝ) * (quarterCoeff663 j : ℝ) *
              pairCoeff k (quarterFreq663 i - quarterFreq663 j)) /
        2 -
    ∑ i : Fin 6, (quarterCoeff663 i : ℝ) * pairCoeff k (quarterFreq663 i)

/-- The matching exact rational coefficient approximations. -/
private def profileApprox (k : Fin 3) : ℚ :=
  shiftedCoeff k (23 / 2) +
      (∑ i : Fin 6,
          ∑ j : Fin 6,
            quarterCoeff663 i * quarterCoeff663 j *
              pairApprox k (quarterFreq663 i - quarterFreq663 j)) /
        2 -
    ∑ i : Fin 6, quarterCoeff663 i * pairApprox k (quarterFreq663 i)

/-- A uniform bound on the error of each of six summands gives six
times that bound for their sum. -/
private theorem sum_six_error (f g : Fin 6 → ℝ) {e : ℝ} (h : ∀ i, |f i - g i| ≤ e) :
    |(∑ i, f i) - ∑ i, g i| ≤ 6 * e := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |f i - g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 6, e := Finset.sum_le_sum fun i _ ↦ h i
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num only

/-- The coefficient approximation keeps all six linear terms and all
36 ordered cross terms. -/
private theorem profile_coeff_error (k : Fin 3) :
    |profileCoeff k - (profileApprox k : ℝ)| ≤ 1 / 10 ^ 12 := by
  have hpair :
    ∀ (i j : Fin 6) (k : Fin 3),
      let s := quarterFreq663 i - quarterFreq663 j
      abs ((11 / 10 : ℚ) * |s|) ≤ 11 ∧
        |shiftedCoeff k (23 / 2 + |s|)| ≤ 100 ∧ |shiftedCoeff k (23 / 2 - |s|)| ≤ 100 := by
    decide +kernel
  have hsingle :
    ∀ (i : Fin 6) (k : Fin 3),
      let s := quarterFreq663 i
      abs ((11 / 10 : ℚ) * |s|) ≤ 11 ∧
        |shiftedCoeff k (23 / 2 + |s|)| ≤ 100 ∧ |shiftedCoeff k (23 / 2 - |s|)| ≤ 100 := by
    unfold quarterFreq663
    decide +kernel
  have hc : ∀ i : Fin 6, |quarterCoeff663 i| ≤ 1 := by decide +kernel
  have hc' (i : Fin 6) : |(quarterCoeff663 i : ℝ)| ≤ 1 := by exact_mod_cast hc i
  have hweighted (i : Fin 6) {s : ℚ} (h : |pairCoeff k s - (pairApprox k s : ℝ)| ≤ 1 / 10 ^ 14) :
    |(quarterCoeff663 i : ℝ) * pairCoeff k s - (quarterCoeff663 i : ℝ) * (pairApprox k s : ℝ)| ≤
      1 / 10 ^ 14 := by
    rw [← mul_sub, abs_mul]
    exact (mul_le_mul (hc' i) h (abs_nonneg _) (by norm_num only)).trans_eq (one_mul _)
  have hlinear :=
    sum_six_error _ _ fun i ↦
      hweighted i (pair_coeff_error k _ (hsingle i k).1 (hsingle i k).2.1 (hsingle i k).2.2)
  have hinner (i : Fin 6) :=
    sum_six_error _ _ fun j ↦
      hweighted j (pair_coeff_error k _ (hpair i j k).1 (hpair i j k).2.1 (hpair i j k).2.2)
  have hquad :=
    sum_six_error
      (fun i ↦
        (quarterCoeff663 i : ℝ) *
          ∑ j : Fin 6, (quarterCoeff663 j : ℝ) * pairCoeff k (quarterFreq663 i - quarterFreq663 j))
      (fun i ↦
        (quarterCoeff663 i : ℝ) *
          ∑ j : Fin 6,
            (quarterCoeff663 j : ℝ) * (pairApprox k (quarterFreq663 i - quarterFreq663 j) : ℝ))
      fun i ↦ by
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul (hc' i) (hinner i) (abs_nonneg _) (by norm_num only)).trans_eq (one_mul _)
  unfold profileCoeff profileApprox
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_sum, Rat.cast_ofNat,
    mul_assoc, ← Finset.mul_sum]
  rw [show ∀ a b c d e : ℝ, a + b / 2 - c - (a + d / 2 - e) = (b - d) / 2 - (c - e) from
      fun a b c d e ↦ by ring]
  exact
    (abs_sub _ _).trans
      (by
        rw [abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
        linarith only [hlinear, hquad])

/-- Evaluate the centered real quadratic coefficients using exact
rational Taylor sums with the certified error. -/
private theorem profile_coeff_bounds :
    profileCoeff 0 ∈ Set.Icc (-9.917282) (-9.917281) ∧
      profileCoeff 1 ∈ Set.Icc (-5.446822) (-5.446821) ∧
      profileCoeff 2 ∈ Set.Icc 3.549579 3.549580 := by
  have h :
    profileApprox 0 ∈ Set.Icc (-9.917282 + 1 / 10 ^ 12) (-9.917281 - 1 / 10 ^ 12) ∧
      profileApprox 1 ∈ Set.Icc (-5.446822 + 1 / 10 ^ 12) (-5.446821 - 1 / 10 ^ 12) ∧
      profileApprox 2 ∈ Set.Icc (3.549579 + 1 / 10 ^ 12) (3.549580 - 1 / 10 ^ 12) := by
    decide +kernel
  have hb := fun k ↦ abs_le.mp (profile_coeff_error k)
  have cast_box {x l u : ℚ} (hx : x ∈ Set.Icc l u) : (x : ℝ) ∈ Set.Icc (l : ℝ) (u : ℝ) :=
    ⟨(Rat.cast_le (K := ℝ)).mpr hx.1, (Rat.cast_le (K := ℝ)).mpr hx.2⟩
  have h₀ := cast_box h.1
  have h₁ := cast_box h.2.1
  have h₂ := cast_box h.2.2
  norm_num only [Set.mem_Icc, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one, Rat.cast_neg, Rat.cast_ofScientific] at h₀ h₁ h₂
  exact
    ⟨⟨by linarith only [h₀.1, (hb 0).1], by linarith only [h₀.2, (hb 0).2]⟩,
      ⟨by linarith only [h₁.1, (hb 1).1], by linarith only [h₁.2, (hb 1).2]⟩,
      ⟨by linarith only [h₂.1, (hb 2).1], by linarith only [h₂.2, (hb 2).2]⟩⟩

/-- The paired profile is quadratic in the centered variable. -/
private theorem pair_profile_expand (v : ℝ) (s : ℚ) :
    quarterAuxPair656 (s : ℝ) v =
      pairCoeff 0 s + pairCoeff 1 s * (v - 23 / 2) + pairCoeff 2 s * (v - 23 / 2) ^ 2 := by
  unfold quarterAuxPair656 quarterAuxProfile656 pairCoeff shiftedCoeff
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_neg, Rat.cast_abs, Rat.cast_pow]
  ring

/-- The combined profile has the three certified coefficients in the
basis centered at 23/2. -/
private theorem profile_expand (v : ℝ) :
    quarterProfile663 v =
      profileCoeff 0 + profileCoeff 1 * (v - 23 / 2) + profileCoeff 2 * (v - 23 / 2) ^ 2 := by
  unfold quarterProfile663 profileCoeff
  simp_rw [pair_profile_expand, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  simp only [quarterAuxProfile656, shiftedCoeff, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_add, Rat.cast_mul, Rat.cast_pow]
  ring

/-- On the nonnegative displacement half-line, use the lower endpoint
of each coefficient enclosure in the centered quadratic. -/
theorem quarter_profile_lower_663 {v : ℝ} (hv : 23 / 2 ≤ v) :
    -9.917282 - 5.446822 * (v - 23 / 2) + 3.549579 * (v - 23 / 2) ^ 2 ≤ quarterProfile663 v := by
  rw [profile_expand]
  have h := profile_coeff_bounds
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.1 (sub_nonneg.mpr hv)
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.1 (sq_nonneg (v - 23 / 2))
  linarith only [h.1.1, h₁, h₂]

/-- The centered lower quadratic never drops to -20 on its support. -/
theorem quarter_profile_gt_neg20_663 {v : ℝ} (hv : 23 / 2 ≤ v) : -20 < quarterProfile663 v := by
  refine lt_of_lt_of_le ?_ (quarter_profile_lower_663 hv)
  nlinarith only [sq_nonneg (v - 23 / 2 - 0.77)]

/-- The centered quadratic is positive beyond the end of the main
support for all section 137 radii. -/
theorem quarter_profile_pos_663 {v : ℝ} (hv : 14.21 ≤ v) : 0 < quarterProfile663 v := by
  refine lt_of_lt_of_le ?_ (quarter_profile_lower_663 (by linarith only [hv]))
  nlinarith only [hv, sq_nonneg (v - 14.21)]

/-- If the relative logarithm is at least 21/8, the main kernel vanishes
and the reflected quadratic itself remains positive. -/
theorem quarter_profile_beyond_663 {r u : ℝ} (hr : 328 ≤ r) (hu : 21 / 8 ≤ u) :
    0 < quarterProfile663 (2 * Real.log r + u) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr
  apply quarter_profile_pos_663
  linarith only [hl, h, hu]

/-- The positive forward profile after removing the common inverse
power from (137.14). This formula applies on the main support. -/
@[expose]
noncomputable def quarterForward663 (r u : ℝ) : ℝ :=
  (11 / 10) ^ 5 * Real.exp (-(231 / 80)) * r ^ (11 / 5 : ℝ) * Real.exp ((11 / 5) * u) *
      (21 / 8 - u) ^ 5 /
    120

/-- For relative logarithm at most one, the forward profile dominates
the possible negative part of the reflected quadratic. -/
theorem quarter_profile_low_663 {r u : ℝ} (hr : 328 ≤ r) (hu : u ∈ Set.Icc 0 1) :
    0 ≤ quarterProfile663 (2 * Real.log r + u) + quarterForward663 r u := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 23 / 4) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr
  have hF :=
    quarter_profile_gt_neg20_663
      (show 23 / 2 ≤ 2 * Real.log r + u by linarith only [hl, hlog, hu.1])
  have hex :=
    profile_exp_error (-(231 / 80))
      (by norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, abs_neg, abs_of_nonneg])
  have hc : (0.05 : ℚ) + 1 / 10 ^ 16 ≤ profileExpTaylor (-(231 / 80)) := by decide +kernel
  have hc' := (Rat.cast_le (K := ℝ)).mpr hc
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofScientific, Rat.cast_ofNat,
    Rat.cast_neg] at hc' hex
  have he : (0.05 : ℝ) ≤ Real.exp (-(231 / 80)) := by linarith only [hc', (abs_le.mp hex).1]
  have hr₁ : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr
  have hp := Real.rpow_le_rpow_of_exponent_le hr₁ (by norm_num only : (2 : ℝ) ≤ 11 / 5)
  rw [Real.rpow_ofNat] at hp
  have hR := (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 328) hr 2).trans hp
  have hE := Real.one_le_exp (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 11 / 5) hu.1)
  have hP :=
    pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 13 / 8)
      (show (13 / 8 : ℝ) ≤ 21 / 8 - u by linarith only [hu.2]) 5
  have hdecay := mul_le_mul he hR (by norm_num only) (Real.exp_pos _).le
  have hdecay₀ :=
    mul_nonneg (Real.exp_pos (-(231 / 80))).le (Real.rpow_nonneg (zero_le_one.trans hr₁) (11 / 5))
  have hforward := mul_le_mul hdecay hE (by norm_num only) hdecay₀
  have hprod := mul_le_mul hforward hP (by norm_num only) (mul_nonneg hdecay₀ (Real.exp_pos _).le)
  unfold quarterForward663
  nlinarith only [hF, hprod]

/-- The constant multiplying the forward Taylor minorant exceeds 30000
at the least section 137 radius and therefore throughout the range. -/
private theorem forward_scale_lower {r : ℝ} (hr : 328 ≤ r) :
    30000 ≤ (11 / 10 : ℝ) ^ 5 * Real.exp (-(231 / 80)) * r ^ (11 / 5 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000 / 557) (j := 5) (n := 32) (lo := 2.8875)
        (hi := 3) (by decide +kernel)).1
  have hlog : 231 / 80 ≤ Real.log (0.0557 : ℝ)⁻¹ := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h
    norm_num only at h ⊢
    exact h
  rw [Real.log_inv] at hlog
  have he : (0.0557 : ℝ) ≤ Real.exp (-(231 / 80)) :=
    (Real.log_le_iff_le_exp (by norm_num only)).mp (by linarith only [hlog])
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 328) (p := 11) (d := 5)
        (lo := 0) (hi := 1 / 340000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hp
  rw [Real.rpow_neg (by norm_num only : (0 : ℝ) ≤ 328), ← one_div] at hp
  have hpos : 0 < (328 : ℝ) ^ (11 / 5 : ℝ) := Real.rpow_pos_of_pos (by norm_num only) _
  have hb := (one_div_le_one_div_of_le (one_div_pos.mpr hpos) hp)
  rw [one_div_one_div, one_div_one_div] at hb
  have hpow :=
    hb.trans
      (Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ 328) hr
        (by norm_num only : (0 : ℝ) ≤ 11 / 5))
  have hm := mul_le_mul he hpow (by norm_num only) (Real.exp_pos _).le
  nlinarith only [hm]

/-- On the middle interval, a degree-twelve rational minorant uses the
first eight Taylor terms of the positive exponential. -/
theorem quarter_profile_middle_lower {r u : ℝ} (hr : 328 ≤ r) (hu : u ∈ Set.Icc 1 (21 / 8)) :
    -9.917282 - 5.446822 * (0.086 + u) + 3.549579 * (0.086 + u) ^ 2 +
        250 * (21 / 8 - u) ^ 5 * (∑ k ∈ Finset.range 8, ((11 / 5) * u) ^ k / k.factorial) ≤
      quarterProfile663 (2 * Real.log r + u) + quarterForward663 r u := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hc
  have hrlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr
  have hv : 0.086 + u ≤ 2 * Real.log r + u - 23 / 2 := by linarith only [hc, hrlog]
  have hF :=
    quarter_profile_lower_663 (show 23 / 2 ≤ 2 * Real.log r + u by linarith only [hv, hu.1])
  have hm :=
    mul_nonneg (sub_nonneg.mpr hv)
      (show 0 ≤ 3.549579 * (2 * Real.log r + u - 23 / 2 + (0.086 + u)) - 5.446822 by
        linarith only [hv, hu.1])
  have h₀ : 0 ≤ (11 / 5 : ℝ) * u := mul_nonneg (by norm_num only) (zero_le_one.trans hu.1)
  have hE := Real.sum_le_exp_of_nonneg h₀ 8
  have hE₀ : 0 ≤ ∑ k ∈ Finset.range 8, ((11 / 5 : ℝ) * u) ^ k / k.factorial :=
    Finset.sum_nonneg fun k _ ↦ div_nonneg (pow_nonneg h₀ _) (Nat.cast_nonneg _)
  have hscale :=
    mul_le_mul (forward_scale_lower hr) hE hE₀
      ((by norm_num only : (0 : ℝ) ≤ 30000).trans (forward_scale_lower hr))
  have ht := mul_le_mul_of_nonneg_right hscale (pow_nonneg (sub_nonneg.mpr hu.2) 5)
  unfold quarterForward663
  nlinarith only [hF, hm, ht]

end PseudoPrime.PrimeTestBounds.MillerRabin
