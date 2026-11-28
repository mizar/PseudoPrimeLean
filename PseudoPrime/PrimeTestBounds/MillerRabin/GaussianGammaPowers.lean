/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaCoefficients
public import PseudoPrime.Analysis.EulerCorrectionTailBounds

/-! # Rational bounds for the Gaussian gamma reciprocal powers -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The integral-test remainder for the gamma reciprocal powers has an
exact rational expression at a rational cutoff. -/
theorem gamma_pole_power_integral {d x : ℝ} (hx : 0 < d + 2 * x) (j : ℕ) :
    (∫ t in Set.Ioi x, (1 : ℝ) / (d + 2 * t) ^ (j + 2)) =
      1 / (2 * (j + 1) * (d + 2 * x) ^ (j + 1)) := by
  let a := d + 2 * x
  let F := fun v : ℝ ↦ (1 : ℝ) / v ^ (j + 2)
  let G := fun t : ℝ ↦ F (a + t)
  rw [← integral_translate_Ioi _ x]
  have h (t : ℝ) : (1 : ℝ) / (d + 2 * (x + t)) ^ (j + 2) = G (2 * t) := by
    dsimp only [G, F, a]
    rw [show d + 2 * (x + t) = d + 2 * x + 2 * t by ring]
  simp only [h]
  rw [MeasureTheory.integral_comp_mul_left_Ioi G 0 (by norm_num only : (0 : ℝ) < 2), mul_zero,
    smul_eq_mul]
  change (2 : ℝ)⁻¹ * (∫ t in Set.Ioi (0 : ℝ), F (a + t)) = _
  rw [integral_translate_Ioi F a]
  have he : (∫ v in Set.Ioi a, F v) = ∫ v in Set.Ioi a, v ^ (-((j : ℝ) + 2)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only [F]
    have hc : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by norm_num only [Nat.cast_add, Nat.cast_ofNat]
    rw [Real.rpow_neg (hx.trans hv).le, ← hc, Real.rpow_natCast, one_div]
  rw [he, integral_Ioi_rpow_of_lt (by linarith only [Nat.cast_nonneg (α := ℝ) j]) hx]
  rw [show -((j : ℝ) + 2) + 1 = -((j : ℝ) + 1) by ring, Real.rpow_neg hx.le, ←
    (show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by norm_num only [Nat.cast_add, Nat.cast_one]),
    Real.rpow_natCast, div_neg, neg_div, neg_neg]
  simp only [div_eq_mul_inv, mul_inv, one_mul]
  ring

/-- Bracket a gamma power series by its first `N + 1` terms plus
the lower and upper integral-test remainders. -/
theorem gamma_pole_power_bounds {d : ℝ} (hd : 0 < d) (j N : ℕ) :
    let P := ∑ n ∈ Finset.range (N + 1), (1 : ℝ) / (d + 2 * n) ^ (j + 2)
    let S := ∑' n : ℕ, (1 : ℝ) / (d + 2 * n) ^ (j + 2)
    P + 1 / (2 * (j + 1) * (d + 2 * (N + 1)) ^ (j + 1)) ≤ S ∧
      S ≤ P + 1 / (2 * (j + 1) * (d + 2 * N) ^ (j + 1)) := by
  intro P S
  let f := fun t : ℝ ↦ (1 : ℝ) / (d + 2 * t) ^ (j + 2)
  have hh (t : ℝ) (ht : 0 ≤ t) : 0 < d + 2 * t := by linarith only [hd, ht]
  have ha : AntitoneOn f (Set.Ici 0) := by
    intro x hx y _ hxy
    exact
      one_div_le_one_div_of_le (pow_pos (hh x hx) _)
        (pow_le_pow_left₀ (hh x hx).le
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (by norm_num only : (0 : ℝ) ≤ 2))) _)
  have hn (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ioi (m : ℝ)) : 0 ≤ f t :=
    div_nonneg zero_le_one (pow_nonneg (hh t ((Nat.cast_nonneg m).trans ht.le)).le _)
  have hs : Summable (fun n : ℕ ↦ f n) := gamma_pole_power_summable hd (Nat.zero_lt_succ j)
  have haN (m : ℕ) : AntitoneOn f (Set.Ici (m : ℝ)) :=
    ha.mono (Set.Ici_subset_Ici.mpr (Nat.cast_nonneg m))
  have hInt :=
    (haN N).integrableOn_Ioi_of_summable_comp_add ((summable_nat_add_iff N).mpr hs) (hn N)
  have hl := (haN (N + 1)).integral_le_tsum_comp_add (N + 1) hs (hn (N + 1))
  have hu := (haN N).tsum_comp_add_le_integral N hInt (hn N)
  have hf (m : ℕ) : (∫ t in Set.Ioi (m : ℝ), f t) = 1 / (2 * (j + 1) * (d + 2 * m) ^ (j + 1)) :=
    gamma_pole_power_integral (hh m (Nat.cast_nonneg m)) j
  rw [hf (N + 1)] at hl
  rw [hf N] at hu
  have hsplit := hs.sum_add_tsum_nat_add (N + 1)
  change P + (∑' n : ℕ, f (↑(n + (N + 1) : ℕ))) = S at hsplit
  have hupper : (∑' n : ℕ, f (↑(n + (N + 1) : ℕ))) ≤ 1 / (2 * (j + 1) * (d + 2 * N) ^ (j + 1)) := by
    simpa only [Nat.add_assoc] using hu
  rw [← hsplit]
  exact
    ⟨add_le_add le_rfl (by simpa only [Nat.cast_add, Nat.cast_one] using hl),
      add_le_add le_rfl hupper⟩

/-- Compute the lower and upper integral-test bounds for a positive pole
spacing parameter, derivative order `j + 1`, and prefix of length `N + 1`. -/
@[expose]
def gammaPolePowerBounds (d : ℚ) (j N : ℕ) : ℚ × ℚ :=
  let p := ∑ n ∈ Finset.range (N + 1), (1 : ℚ) / (d + 2 * n) ^ (j + 2)
  (p + 1 / (2 * (j + 1) * (d + 2 * (N + 1)) ^ (j + 1)),
    p + 1 / (2 * (j + 1) * (d + 2 * N) ^ (j + 1)))

/-- The exact rational endpoints enclose the corresponding real series. -/
theorem gamma_pole_power_bounds_cast {d : ℚ} (hd : 0 < d) (j N : ℕ) :
    let S := ∑' n : ℕ, (1 : ℝ) / ((d : ℝ) + 2 * n) ^ (j + 2)
    ((gammaPolePowerBounds d j N).1 : ℝ) ≤ S ∧ S ≤ ((gammaPolePowerBounds d j N).2 : ℝ) := by
  simpa only [gammaPolePowerBounds, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_sum] using
    gamma_pole_power_bounds (Rat.cast_pos.mpr hd) j N

/-- Enclose the pole-power prefix by summing integer grid endpoints.
The integrated tail endpoint is rounded on the same grid before addition. -/
@[expose]
def gammaPolePowerGrid (d : ℚ) (j N D : ℕ) : ℤ × ℤ :=
  let f := fun n : ℕ ↦ (D : ℚ) * (1 / (d + 2 * n) ^ (j + 2))
  let t := fun n : ℕ ↦ (D : ℚ) * (1 / (2 * (j + 1) * (d + 2 * n) ^ (j + 1)))
  ((∑ n ∈ Finset.range (N + 1), ⌊f n⌋) + ⌊t (N + 1)⌋, (∑ n ∈ Finset.range (N + 1), ⌈f n⌉) + ⌈t N⌉)

/-- Dividing the integer endpoints by a positive grid denominator
encloses both exact rational integral-test endpoints. -/
theorem gamma_pole_power_grid_sound (d : ℚ) (j N D : ℕ) (hD : 0 < D) :
    ((gammaPolePowerGrid d j N D).1 : ℚ) / D ≤ (gammaPolePowerBounds d j N).1 ∧
      (gammaPolePowerBounds d j N).2 ≤ ((gammaPolePowerGrid d j N D).2 : ℚ) / D := by
  have hD' : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  simp only [gammaPolePowerGrid, gammaPolePowerBounds, Int.cast_add, Int.cast_sum, Nat.cast_add,
    Nat.cast_one]
  constructor
  · apply (div_le_iff₀ hD').mpr
    rw [add_mul, Finset.sum_mul]
    simp only [mul_comm _ (D : ℚ)]
    exact add_le_add (Finset.sum_le_sum (fun _ _ ↦ Int.floor_le _)) (Int.floor_le _)
  · apply (le_div_iff₀ hD').mpr
    rw [add_mul, Finset.sum_mul]
    simp only [mul_comm _ (D : ℚ)]
    exact add_le_add (Finset.sum_le_sum (fun _ _ ↦ Int.le_ceil _)) (Int.le_ceil _)

/-- The integer grid endpoints enclose the infinite real pole-power sum
after division by the grid denominator. -/
theorem gamma_pole_power_grid_cast {d : ℚ} (hd : 0 < d) (j N D : ℕ) (hD : 0 < D) :
    let S := ∑' n : ℕ, (1 : ℝ) / ((d : ℝ) + 2 * n) ^ (j + 2)
    (↑(gammaPolePowerGrid d j N D).1 : ℝ) / D ≤ S ∧
      S ≤ (↑(gammaPolePowerGrid d j N D).2 : ℝ) / D := by
  obtain ⟨hl, hu⟩ := gamma_pole_power_grid_sound d j N D hD
  obtain ⟨hl', hu'⟩ := gamma_pole_power_bounds_cast hd j N
  have h₁ := (Rat.cast_le (K := ℝ)).mpr hl
  have h₂ := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at h₁ h₂
  exact ⟨h₁.trans hl', hu'.trans h₂⟩

/-- For the even middle-kernel Gamma terms, bound the forward derivative
powers after two head terms and the reflected powers from index zero. -/
theorem middle_gamma_power_bounds {a : ℚ} (ha : -(1 / 2) < a) (ha' : a < 9 / 2) (j N D : ℕ)
    (hD : 0 < D) :
    let f := 9 / 2 - a
    let r := a + 1 / 2
    let F := ∑' n : ℕ, (1 : ℝ) / ((f : ℝ) + 2 * n) ^ (j + 2)
    let R := ∑' n : ℕ, (1 : ℝ) / ((r : ℝ) + 2 * n) ^ (j + 2)
    (↑(gammaPolePowerGrid f j N D).1 : ℝ) / D ≤ F ∧
      F ≤ (↑(gammaPolePowerGrid f j N D).2 : ℝ) / D ∧
      (↑(gammaPolePowerGrid r j N D).1 : ℝ) / D ≤ R ∧
      R ≤ (↑(gammaPolePowerGrid r j N D).2 : ℝ) / D := by
  intro f r F R
  have hf : 0 < f := sub_pos.mpr ha'
  have hr : 0 < r := neg_lt_iff_pos_add.mp ha
  obtain ⟨hf₀, hf₁⟩ := gamma_pole_power_grid_cast hf j N D hD
  obtain ⟨hr₀, hr₁⟩ := gamma_pole_power_grid_cast hr j N D hD
  exact ⟨hf₀, hf₁, hr₀, hr₁⟩

/-- The signed coefficient of derivative order `j + 1` for the even Gamma
contours after separating the first two forward terms. -/
noncomputable def gammaHigherCoeff (a : ℚ) (j : ℕ) : ℝ :=
  -((-1 : ℝ) ^ (j + 1) * (∑' n : ℕ, 1 / (((9 / 2 - a : ℚ) : ℝ) + 2 * n) ^ (j + 2))) -
    ∑' n : ℕ, 1 / (((a + 1 / 2 : ℚ) : ℝ) + 2 * n) ^ (j + 2)

/-- Combine the forward and reflected grid endpoints, accounting for the
alternating forward sign at derivative order `j + 1`. -/
@[expose]
def gammaHigherGrid (a : ℚ) (j N D : ℕ) : ℤ × ℤ :=
  let F := gammaPolePowerGrid (9 / 2 - a) j N D
  let R := gammaPolePowerGrid (a + 1 / 2) j N D
  let p := (-1 : ℤ) ^ (j + 1)
  (-max (p * F.1) (p * F.2) - R.2, -min (p * F.1) (p * F.2) - R.1)

/-- For positive forward and reflected rates, the combined grid encloses
the signed derivative coefficient. -/
theorem gamma_higher_grid {a : ℚ} (ha : -(1 / 2) < a) (ha' : a < 9 / 2) (j N D : ℕ) (hD : 0 < D) :
    (↑(gammaHigherGrid a j N D).1 : ℝ) / D ≤ gammaHigherCoeff a j ∧
      gammaHigherCoeff a j ≤ (↑(gammaHigherGrid a j N D).2 : ℝ) / D := by
  obtain ⟨hf₀, hf₁, hr₀, hr₁⟩ := middle_gamma_power_bounds ha ha' j N D hD
  let p := (-1 : ℝ) ^ (j + 1)
  have hD' : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  simp only [gammaHigherGrid, gammaHigherCoeff, Int.cast_sub, Int.cast_neg, Int.cast_max,
    Int.cast_min, Int.cast_mul, Int.cast_pow, Int.cast_one, sub_div, neg_div,
    ← max_div_div_right hD', ← min_div_div_right hD', mul_div_assoc, Rat.cast_sub, Rat.cast_add,
    Rat.cast_one, Rat.cast_div, Rat.cast_ofNat]
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_one, Rat.cast_div,
    Rat.cast_ofNat] at hf₀ hf₁ hr₀ hr₁
  by_cases hp : 0 ≤ p
  · exact
      ⟨sub_le_sub (neg_le_neg ((mul_le_mul_of_nonneg_left hf₁ hp).trans (le_max_right _ _))) hr₁,
        sub_le_sub (neg_le_neg ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left hf₀ hp))) hr₀⟩
  · exact
      ⟨sub_le_sub
          (neg_le_neg ((mul_le_mul_of_nonpos_left hf₀ (le_of_not_ge hp)).trans (le_max_left _ _)))
          hr₁,
        sub_le_sub
          (neg_le_neg ((min_le_right _ _).trans (mul_le_mul_of_nonpos_left hf₁ (le_of_not_ge hp))))
          hr₀⟩

/-- A bound on the width of a reciprocal-power grid interval. The
common finite prefix cancels, leaving just the tail width and rounding. -/
@[expose]
def gammaPoleGridWidth (d : ℚ) (j N D : ℕ) : ℚ :=
  (1 / (2 * (j + 1) * (d + 2 * N) ^ (j + 1))) - (1 / (2 * (j + 1) * (d + 2 * (N + 1)) ^ (j + 1))) +
    2 * ((N : ℚ) + 2) / D

/-- The grid width is bounded without computing any prefix reciprocal
powers. Each lower/upper rounding pair costs at most two ticks. -/
theorem gamma_pole_grid_width_le (d : ℚ) (j N D : ℕ) (hD : 0 < D) :
    ((gammaPolePowerGrid d j N D).2 - (gammaPolePowerGrid d j N D).1 : ℤ) / (D : ℚ) ≤
      gammaPoleGridWidth d j N D := by
  let f := fun n : ℕ ↦ (D : ℚ) * (1 / (d + 2 * n) ^ (j + 2))
  let t := fun n : ℕ ↦ 1 / (2 * (j + 1) * (d + 2 * n) ^ (j + 1))
  have hp : (∑ n ∈ Finset.range (N + 1), ((⌈f n⌉ : ℚ) - (⌊f n⌋ : ℚ))) ≤ 2 * ((N : ℚ) + 1) := by
    have h (n : ℕ) : (⌈f n⌉ : ℚ) - (⌊f n⌋ : ℚ) ≤ 2 := by
      linarith only [Int.ceil_lt_add_one (f n), Int.sub_one_lt_floor (f n)]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      mul_comm (2 : ℚ)] using (Finset.sum_le_sum (s := Finset.range (N + 1)) fun n _ ↦ h n)
  have ht :
    (⌈(D : ℚ) * t N⌉ : ℚ) - (⌊(D : ℚ) * t (N + 1)⌋ : ℚ) ≤ (D : ℚ) * (t N - t (N + 1)) + 2 := by
    linarith only [Int.ceil_lt_add_one ((D : ℚ) * t N), Int.sub_one_lt_floor ((D : ℚ) * t (N + 1))]
  have hD' : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  apply (div_le_iff₀ hD').mpr
  simp only [gammaPolePowerGrid, gammaPoleGridWidth, Int.cast_sub, Int.cast_add, Int.cast_sum]
  have h := add_le_add hp ht
  rw [Finset.sum_sub_distrib] at h
  rw [add_mul, div_mul_cancel₀ _ hD'.ne']
  dsimp only [f, t] at h
  simp only [Nat.cast_add, Nat.cast_one] at h ⊢
  linear_combination h

/-- Applying the forward parity sign and subtracting the reflected interval
preserves the sum of the two interval widths. -/
theorem gamma_higher_grid_width (a : ℚ) (j N D : ℕ) (hD : 0 < D) (ha : a < 9 / 2) :
    ((gammaHigherGrid a j N D).2 - (gammaHigherGrid a j N D).1 : ℤ) / (D : ℚ) ≤
      gammaPoleGridWidth (9 / 2 - a) j N D + gammaPoleGridWidth (a + 1 / 2) j N D := by
  let F := gammaPolePowerGrid (9 / 2 - a) j N D
  let R := gammaPolePowerGrid (a + 1 / 2) j N D
  let p := (-1 : ℤ) ^ (j + 1)
  have h :=
    add_le_add (gamma_pole_grid_width_le (9 / 2 - a) j N D hD)
      (gamma_pole_grid_width_le (a + 1 / 2) j N D hD)
  have hF := gamma_pole_power_grid_cast (sub_pos.mpr ha) j N D hD
  have hD' : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hle : F.1 ≤ F.2 := by
    have hc : (F.1 : ℝ) ≤ F.2 := (div_le_div_iff_of_pos_right hD').mp (hF.1.trans hF.2)
    exact_mod_cast hc
  change ((-min (p * F.1) (p * F.2) - R.1 - (-max (p * F.1) (p * F.2) - R.2) : ℤ) : ℚ) / (D : ℚ) ≤ _
  have he : max (p * F.1) (p * F.2) - min (p * F.1) (p * F.2) = F.2 - F.1 := by
    by_cases ho : Odd (j + 1)
    · simp only [p, ho.neg_one_pow, neg_one_mul, max_eq_left (neg_le_neg hle),
        min_eq_right (neg_le_neg hle)]
      ring
    · have hEven : Even (j + 1) := Nat.not_odd_iff_even.mp ho
      simp only [p, hEven.neg_one_pow, one_mul, max_eq_right hle, min_eq_left hle]
  have he' :
    -min (p * F.1) (p * F.2) - R.1 - (-max (p * F.1) (p * F.2) - R.2) =
      (F.2 - F.1) + (R.2 - R.1) := by
    linear_combination he
  rw [he', Int.cast_add, add_div]
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
