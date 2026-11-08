/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaCentral

/-! # Signed baseline and pole-tail budget for the even Gamma term -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The even Gamma baseline is below `-9/2`. The stronger existing signed
quarter-digamma bound supplies the negative term needed to absorb the first
Gamma pole. -/
theorem target028_gamma_baseline :
    (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re - Real.log Real.pi < -(9 / 2 : ℝ) := by
  have h := LLS.PaperStatements.gamma_even_baseline_lt
  linarith only [h]

/-- For positive `c`, the next inverse cube is bounded by a telescoping
inverse-square difference. This is the discrete integral estimate for the
Gamma pole tail. -/
theorem target028_cube_le_telescope {c : ℝ} (hc : 0 < c) :
    1 / (c + 2) ^ 3 ≤ (1 / 4 : ℝ) * (1 / c ^ 2 - 1 / (c + 2) ^ 2) := by
  have hc2 : 0 < c + 2 := by linarith only [hc]
  have hfrac : 1 / (c + 2) ^ 3 ≤ (c + 1) / (c ^ 2 * (c + 2) ^ 2) := by
    apply (div_le_div_iff₀ (pow_pos hc2 3) (mul_pos (sq_pos_of_pos hc) (sq_pos_of_pos hc2))).mpr
    nlinarith only [sq_nonneg c, hc]
  have heq : (c + 1) / (c ^ 2 * (c + 2) ^ 2) = (1 / 4 : ℝ) * (1 / c ^ 2 - 1 / (c + 2) ^ 2) := by
    field_simp (disch :=
      first
      | exact hc.ne'
      | exact hc2.ne'
      | norm_num only)
    ring
  exact hfrac.trans_eq heq

/-- The inverse-square telescope associated with the even Gamma poles.
Its sum controls the tail of the inverse cubes. -/
noncomputable def target028GammaTelescope (n : ℕ) : ℝ :=
  (1 / 16 : ℝ) * (((n : ℝ) + 5 / 4) ^ 2)⁻¹

/-- The Gamma inverse-square telescope is summable by comparison with the
standard shifted inverse-square series. -/
theorem target028_gamma_telescope_summable : Summable target028GammaTelescope := by
  have h := Analysis.summable_shifted_inverse_squares (a := 5 / 4) (by norm_num only)
  have h' := h.mul_left (1 / 16 : ℝ)
  apply h'.congr
  intro n
  dsimp only [target028GammaTelescope]
  congr 2
  ring

/-- Every inverse cube after the first even Gamma pole is bounded by the
corresponding difference of successive telescope values. -/
theorem target028_gamma_tail_term (n : ℕ) :
    1 / (2 * ((n + 1 : ℕ) : ℝ) + 5 / 2) ^ 3 ≤
      target028GammaTelescope n - target028GammaTelescope (n + 1) := by
  let c : ℝ := 2 * n + 5 / 2
  have hc : 0 < c := by
    dsimp only [c]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have h := target028_cube_le_telescope hc
  have hc2 : c + 2 ≠ 0 := (by linarith only [hc] : (0 : ℝ) < c + 2).ne'
  have he :
    target028GammaTelescope n - target028GammaTelescope (n + 1) =
      (1 / 4 : ℝ) * (1 / c ^ 2 - 1 / (c + 2) ^ 2) := by
    dsimp only [target028GammaTelescope, c]
    push_cast
    field_simp (disch :=
      first
      | exact hc.ne'
      | exact hc2
      | norm_num only)
    ring
  rw [he]
  convert h using 1
  dsimp only [c]
  push_cast
  ring

/-- The inverse cubes of all even Gamma poles beginning at `5/2` sum to at
most `13/125`. The first term is `8/125`, and the remaining terms telescope
against an inverse-square tail of size `1/25`. -/
theorem target028_gamma_pole_tail : (∑' n : ℕ, 1 / (2 * (n : ℝ) + 5 / 2) ^ 3) ≤ (13 / 125 : ℝ) := by
  let f : ℕ → ℝ := fun n ↦ 1 / (2 * (n : ℝ) + 5 / 2) ^ 3
  let g := target028GammaTelescope
  have hg : Summable g := target028_gamma_telescope_summable
  have hg1 : Summable (fun n : ℕ ↦ g (n + 1)) := (summable_nat_add_iff 1).mpr hg
  have hd : Summable (fun n : ℕ ↦ g n - g (n + 1)) := hg.sub hg1
  have hf1 : Summable (fun n : ℕ ↦ f (n + 1)) := by
    apply Summable.of_nonneg_of_le _ (fun n ↦ target028_gamma_tail_term n) hd
    intro n
    exact
      div_nonneg (by norm_num only)
        (pow_nonneg
          (add_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (by norm_num only)) _)
  have hf : Summable f := (summable_nat_add_iff 1).mp hf1
  have hsum := Summable.tsum_le_tsum target028_gamma_tail_term hf1 hd
  have ht := hg.tsum_eq_zero_add
  have he : (∑' n : ℕ, (g n - g (n + 1))) = 1 / 25 := by
    rw [hg.tsum_sub hg1]
    have hg0 : g 0 = (1 / 25 : ℝ) := by norm_num only [g, target028GammaTelescope]
    linarith only [ht, hg0]
  rw [he] at hsum
  change (∑' n : ℕ, f (n + 1)) ≤ 1 / 25 at hsum
  change (∑' n : ℕ, f n) ≤ 13 / 125
  have hfirst : f 0 = (8 / 125 : ℝ) := by norm_num only [f]
  have hfull := hf.tsum_eq_zero_add
  rw [hfull, hfirst]
  calc
    _ ≤ (8 / 125 : ℝ) + 1 / 25 := add_le_add (le_refl _) hsum
    _ = 13 / 125 := by norm_num only

/-- The inverse-cube tail of the positive even Gamma poles is summable. Comparison
with the telescoping inverse-square differences supplies the required majorant. -/
theorem target028_gamma_pole_tail_summable :
    Summable (fun n : ℕ ↦ 1 / (2 * (n : ℝ) + 5 / 2) ^ 3) := by
  have hg := target028_gamma_telescope_summable
  have hg1 : Summable (fun n : ℕ ↦ target028GammaTelescope (n + 1)) :=
    (summable_nat_add_iff 1).mpr hg
  have hd := hg.sub hg1
  have hf : Summable (fun n : ℕ ↦ 1 / (2 * ((n + 1 : ℕ) : ℝ) + 5 / 2) ^ 3) := by
    apply Summable.of_nonneg_of_le _ (fun n ↦ target028_gamma_tail_term n) hd
    intro n
    exact
      div_nonneg (by norm_num only)
        (pow_nonneg
          (add_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (by norm_num only)) _)
  exact (summable_nat_add_iff 1).mp hf

/-- Each correction after the first even Gamma pole is bounded by a quadratic
function of the height times the corresponding inverse cube. This estimate is
used with the second moment of the six-pole kernel. -/
theorem target028_gamma_correction_term (t : ℝ) (n : ℕ) :
    (t / 2) ^ 2 / ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2)) ≤
      2 * t ^ 2 * (1 / (2 * (n : ℝ) + 5 / 2) ^ 3) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha : 0 < 1 / 4 + ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith only [hn]
  have hb : 0 < 2 * (n : ℝ) + 5 / 2 := by linarith only [hn]
  have hc : 0 < (1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _)
  have hd : (1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ (1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2 :=
    le_add_of_nonneg_right (sq_nonneg _)
  apply (div_le_iff₀ (mul_pos ha hc)).2
  push_cast at *
  field_simp
  have hp := mul_nonneg (sq_nonneg (t ^ 2)) hb.le
  nlinarith only [hp]

/-- After separating the first pole, the full positive vertical digamma tail
is at most `26/125` times the square of the height. The estimate combines the
termwise inverse-cube bound with the telescoping bound on its sum. -/
theorem target028_gamma_correction_tail (t : ℝ) :
    (∑' n : ℕ,
        (t / 2) ^ 2 /
          ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2))) ≤
      (26 / 125 : ℝ) * t ^ 2 := by
  have hc :=
    AnalyticNumberTheory.Gamma.summable_vertical_digamma_correction (a := (1 / 4 : ℝ)) (t := t / 2)
      (by norm_num only)
  have hcs := (summable_nat_add_iff 1).mpr hc
  have hmajor := target028_gamma_pole_tail_summable.mul_left (2 * t ^ 2)
  have hsum := Summable.tsum_le_tsum (target028_gamma_correction_term t) hcs hmajor
  rw [tsum_mul_left] at hsum
  have hbound :=
    mul_le_mul_of_nonneg_left target028_gamma_pole_tail
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num only) (sq_nonneg t))
  nlinarith only [hsum, hbound]

/-- The real vertical digamma increment at real part `1/4` splits into the
first pole and a tail bounded by `26 t^2 / 125`. Keeping the first pole exact
allows its signed contribution to be combined with the negative baseline. -/
theorem target028_gamma_vertical_upper (t : ℝ) :
    (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
        (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re ≤
      4 - 1 / (1 / 4 + t ^ 2) + (26 / 125 : ℝ) * t ^ 2 := by
  have h :=
    AnalyticNumberTheory.Gamma.digamma_vertical_re_sub_eq_tsum (a := (1 / 4 : ℝ)) (t := t / 2)
      (by norm_num only)
  have hs :=
    AnalyticNumberTheory.Gamma.summable_vertical_digamma_correction (a := (1 / 4 : ℝ)) (t := t / 2)
      (by norm_num only)
  have hfirst :
    (t / 2) ^ 2 / ((1 / 4 : ℝ) * ((1 / 4) ^ 2 + (t / 2) ^ 2)) = 4 - 1 / (1 / 4 + t ^ 2) := by
    have hp : 0 < 1 / 4 + t ^ 2 := by nlinarith only [sq_nonneg t]
    field_simp
    ring
  rw [hs.tsum_eq_zero_add] at h
  simp only [Nat.cast_zero, add_zero] at h
  rw [hfirst] at h
  have hle := h.le.trans (add_le_add (le_refl _) (target028_gamma_correction_tail t))
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hle

/-- The real vertical digamma increment contains the first pole plus a
nonnegative tail. Together with the upper bound this controls the tail's
absolute contribution against a kernel of changing sign. -/
theorem target028_gamma_vertical_lower (t : ℝ) :
    4 - 1 / (1 / 4 + t ^ 2) ≤
      (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
        (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re := by
  have h :=
    AnalyticNumberTheory.Gamma.digamma_vertical_re_sub_eq_tsum (a := (1 / 4 : ℝ)) (t := t / 2)
      (by norm_num only)
  have hs :=
    AnalyticNumberTheory.Gamma.summable_vertical_digamma_correction (a := (1 / 4 : ℝ)) (t := t / 2)
      (by norm_num only)
  have hfirst :
    (t / 2) ^ 2 / ((1 / 4 : ℝ) * ((1 / 4) ^ 2 + (t / 2) ^ 2)) = 4 - 1 / (1 / 4 + t ^ 2) := by
    have hp : 0 < 1 / 4 + t ^ 2 := by nlinarith only [sq_nonneg t]
    field_simp
    ring
  rw [hs.tsum_eq_zero_add] at h
  simp only [Nat.cast_zero, add_zero] at h
  rw [hfirst] at h
  have htail :
    0 ≤
      ∑' n : ℕ,
        (t / 2) ^ 2 /
          ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2)) := by
    apply tsum_nonneg
    intro n
    apply div_nonneg (sq_nonneg _)
    apply mul_nonneg
    · positivity
    · exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hle :
    4 - 1 / (1 / 4 + t ^ 2) ≤
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re -
        (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re := by
    linarith only [h, htail]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hle

/-- An integrable error dominated by the even-Gamma tail times the six-pole
kernel has normalized integral at most `13(27/25)^2/1000`. The exact kernel
second moment makes this estimate independent of the oscillatory phase. -/
theorem target028_gamma_tail_integral_bound (F : ℝ → ℝ) (hF : MeasureTheory.Integrable F)
    (hbound :
      ∀ t : ℝ, F t ≤ (26 / 125 : ℝ) * (t ^ 2 * ‖refinedSixPoleKernel.function (Complex.I * t)‖)) :
    (∫ t : ℝ, F t) / (2 * Real.pi) ≤ (13 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 := by
  have hi := refined_six_pole_second_integrable.const_mul (26 / 125 : ℝ)
  have h := MeasureTheory.integral_mono hF hi hbound
  rw [MeasureTheory.integral_const_mul, refined_six_pole_second_moment] at h
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  apply (div_le_iff₀ hp).2
  nlinarith only [h, Real.pi_pos]

end PseudoPrime.PrimeTestBounds.MillerRabin
