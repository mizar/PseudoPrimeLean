/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalHeightRectangle
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TrivialZeroSeriesLimit

/-! # Unconditional trivial-zero corrections for logarithmic contours -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- At positive height and left-edge parameter at least two, a real point belongs
to the closed contour rectangle exactly when its real coordinate lies between
the two vertical edges. Compute coordinates explicitly. This removes the height
sequence and GRH from trivial-zero support identification. -/
theorem real_mem_unconditionalHeightRectangle_iff (A : ℕ) (hA : 2 ≤ A) (T : ℝ) (hT : 0 < T)
    (r : ℝ) :
    (r : ℂ) ∈
        Rectangle.rectangleClosedBox (unconditionalHeightLowerCorner A T)
          (unconditionalHeightUpperCorner T) ↔
      -(A : ℝ) - 1 / 2 ≤ r ∧ r ≤ 2 := by
  obtain ⟨hreL, himL, hreU, himU, hre, _⟩ := unconditionalHeightRectangleFacts A hA T hT
  have hleft : -(A : ℝ) - 1 / 2 ≤ 2 := by
    rw [hreL, hreU] at hre; exact hre.le
  simp only [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Complex.ofReal_re,
    Complex.ofReal_im, hreL, himL, hreU, himU, Set.uIcc_of_le hleft,
    Set.uIcc_of_le (neg_le_self hT.le), Set.mem_Icc]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, neg_nonpos.mpr hT.le, hT.le⟩⟩

/-- For either parity location and a positive height, the negative integer location
belongs to the rectangle with left edge minus twice the cutoff minus one half
exactly when its natural index is below the cutoff. Reduce to real coordinate
inequalities. This fixes the finite trivial-zero support without RH. -/
theorem trivialLocation_mem_unconditionalHeightRectangle_iff (m : ℕ) (T : ℝ) (hT : 0 < T) (j a : ℕ)
    (hm : 1 ≤ m) (ha : a ≤ 1) :
    (-2 * ((j : ℂ) + 1) + (a : ℂ)) ∈
        Rectangle.rectangleClosedBox (unconditionalHeightLowerCorner (2 * m) T)
          (unconditionalHeightUpperCorner T) ↔
      j < m := by
  have hA : 2 ≤ 2 * m := Nat.mul_le_mul_left 2 hm
  have hc : (-2 * ((j : ℂ) + 1) + (a : ℂ)) = ((-2 * ((j : ℝ) + 1) + (a : ℝ) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_natCast, Complex.ofReal_one]
  rw [hc, real_mem_unconditionalHeightRectangle_iff (2 * m) hA T hT]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  have han : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have ha1 : (a : ℝ) ≤ 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_le.mpr ha : (a : ℝ) ≤ (1 : ℕ))
  have hjn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  constructor
  · intro h
    have hjm : (j : ℝ) < m := by linarith only [h.1, ha1]
    exact Nat.cast_lt.mp hjm
  · intro h
    have hjm : (j : ℝ) + 1 ≤ m := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_le.mpr (Nat.succ_le_of_lt h) : ((j + 1 : ℕ) : ℝ) ≤ m)
    exact ⟨by linarith only [hjm, han], by linarith only [hjn, ha1]⟩

/-- For an even nonprincipal character and positive height, the nonzero gamma-forced
zeros in the contour rectangle are precisely the first negative even integer
locations. Use gamma zero classification and the explicit rectangle coordinates.
This identifies the even trivial correction independently of any height sequence. -/
theorem even_trivialZeros_unconditionalRectangle_eq_image {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (he : χ.Even) (m : ℕ) (hm : 1 ≤ m) (T : ℝ)
    (hT : 0 < T) :
    (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner (2 * m) T)
            (unconditionalHeightUpperCorner T)).filter
        (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0) =
      (Finset.range m).image (fun j : ℕ => -2 * ((j : ℂ) + 1)) := by
  classical
  ext ρ
  constructor
  · intro h
    obtain ⟨hZ, hΓ, hρ⟩ := Finset.mem_filter.mp h
    obtain ⟨j, hj⟩ := exists_nat_trivial_location_of_even he hΓ hρ
    have hb := (mem_dirichletLFunctionZerosInRectangle_iff.mp hZ).1
    have hmem :=
      (trivialLocation_mem_unconditionalHeightRectangle_iff m T hT j 0 hm (Nat.zero_le 1)).mp
        (by
          simpa only [dirichletCompletedLFunctionRectangleBox, Nat.cast_zero, add_zero, ← hj] using
            hb)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hmem, hj.symm⟩
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have hΓ : DirichletCharacter.gammaFactor χ (-2 * ((j : ℂ) + 1)) = 0 := by
      rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
      exact ⟨j + 1, by rw [Nat.cast_add, Nat.cast_one, neg_mul]⟩
    have hz : -2 * ((j : ℂ) + 1) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero j)
    refine Finset.mem_filter.mpr ⟨mem_dirichletLFunctionZerosInRectangle_iff.mpr ⟨?_, ?_⟩, hΓ, hz⟩
    · simpa only [dirichletCompletedLFunctionRectangleBox, Nat.cast_zero, add_zero] using
        (trivialLocation_mem_unconditionalHeightRectangle_iff m T hT j 0 hm (Nat.zero_le 1)).mpr
          (Finset.mem_range.mp hj)
    · rw [dirichletLFunction_eq_completed_div_gammaFactor χ _
          (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne)),
        hΓ, div_zero]

/-- For an odd nonprincipal character and positive height, the gamma-forced zeros
in the contour rectangle are precisely the first negative odd integer locations.
Use gamma zero classification and the explicit rectangle coordinates.
This identifies the odd trivial correction independently of any height sequence. -/
theorem odd_trivialZeros_unconditionalRectangle_eq_image {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (ho : χ.Odd) (m : ℕ) (hm : 1 ≤ m) (T : ℝ)
    (hT : 0 < T) :
    (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner (2 * m) T)
            (unconditionalHeightUpperCorner T)).filter
        (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0) =
      (Finset.range m).image (fun j : ℕ => -2 * ((j : ℂ) + 1) + 1) := by
  classical
  ext ρ
  constructor
  · intro h
    obtain ⟨hZ, hΓ, _⟩ := Finset.mem_filter.mp h
    obtain ⟨j, hj⟩ := exists_nat_trivial_location_of_odd ho hΓ
    have hb := (mem_dirichletLFunctionZerosInRectangle_iff.mp hZ).1
    have hmem :=
      (trivialLocation_mem_unconditionalHeightRectangle_iff m T hT j 1 hm (Nat.le_refl 1)).mp
        (by simpa only [dirichletCompletedLFunctionRectangleBox, Nat.cast_one, ← hj] using hb)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hmem, hj.symm⟩
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    have hΓ : DirichletCharacter.gammaFactor χ (-2 * ((j : ℂ) + 1) + 1) = 0 := by
      rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
      exact ⟨j, by ring⟩
    have hz : -2 * ((j : ℂ) + 1) + 1 ≠ 0 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.natCast_re, Complex.one_re, Complex.zero_re, Complex.neg_im] at hre
      linarith only [hre, Nat.cast_nonneg (α := ℝ) j]
    refine Finset.mem_filter.mpr ⟨mem_dirichletLFunctionZerosInRectangle_iff.mpr ⟨?_, ?_⟩, hΓ, hz⟩
    · simpa only [dirichletCompletedLFunctionRectangleBox, Nat.cast_one] using
        (trivialLocation_mem_unconditionalHeightRectangle_iff m T hT j 1 hm (Nat.le_refl 1)).mpr
          (Finset.mem_range.mp hj)
    · rw [dirichletLFunction_eq_completed_div_gammaFactor χ _
          (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne)),
        hΓ, div_zero]

/-- For an even primitive nonprincipal character and positive contour height, the
finite logarithmic trivial-zero contribution equals the negative cast of the
first even inverse-power terms. Use the exact finite support and multiplicity-one
residue formula. This makes the correction independent of height without RH. -/
theorem sum_even_log_trivialZeros_unconditionalRectangle_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) (x : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (T : ℝ) (hT : 0 < T) :
    (∑
        ρ ∈
          (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner (2 * m) T)
                (unconditionalHeightUpperCorner T)).filter
            (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
        dirichletLFunctionLogZeroContribution x χ ρ) =
      -((∑ j ∈ Finset.range m, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [even_trivialZeros_unconditionalRectangle_eq_image hne he m hm T hT,
    Finset.sum_image
      (fun a _ b _ h =>
        Nat.cast_injective (R := ℂ)
          (add_right_cancel (mul_left_cancel₀ (neg_ne_zero.mpr two_ne_zero) h))),
    Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hloc : -2 * ((j : ℂ) + 1) = -((2 * (j + 1) : ℕ) : ℂ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, neg_mul]
  have hΓ : DirichletCharacter.gammaFactor χ (-((2 * (j + 1) : ℕ) : ℂ)) = 0 := by
    rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
    exact ⟨j + 1, by rw [Nat.cast_mul, Nat.cast_ofNat]⟩
  rw [hloc]
  exact log_trivialZeroContribution_neg_nat hp hne x (2 * (j + 1)) hΓ

/-- For an odd primitive nonprincipal character and positive contour height, the
finite logarithmic trivial-zero contribution equals the negative cast of the
first odd inverse-power terms. Use the exact finite support and multiplicity-one
residue formula. This makes the correction independent of height without RH. -/
theorem sum_odd_log_trivialZeros_unconditionalRectangle_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (ho : χ.Odd) (x : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (T : ℝ) (hT : 0 < T) :
    (∑
        ρ ∈
          (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner (2 * m) T)
                (unconditionalHeightUpperCorner T)).filter
            (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
        dirichletLFunctionLogZeroContribution x χ ρ) =
      -((∑ j ∈ Finset.range m, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [odd_trivialZeros_unconditionalRectangle_eq_image hne ho m hm T hT,
    Finset.sum_image
      (fun a _ b _ h =>
        Nat.cast_injective (R := ℂ)
          (add_right_cancel (mul_left_cancel₀ (neg_ne_zero.mpr two_ne_zero) (add_right_cancel h)))),
    Complex.ofReal_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hloc : -2 * ((j : ℂ) + 1) + 1 = -((2 * j + 1 : ℕ) : ℂ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have hΓ : DirichletCharacter.gammaFactor χ (-((2 * j + 1 : ℕ) : ℂ)) = 0 := by
    rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff]
    exact
      ⟨j, by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]; ring⟩
  rw [hloc]
  exact log_trivialZeroContribution_neg_nat hp hne x (2 * j + 1) hΓ

/-- For an even primitive nonprincipal character and scale greater than one, the
trivial logarithmic sums tend to the full even correction along any positive
height selection as the left edge expands. Use the exact partial sums and the
summable even subsequence. This removes RH from the trivial-zero limit. -/
theorem tendsto_sum_even_log_trivialZeros_unconditionalRectangle {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (he : χ.Even) {x : ℝ}
    (hx : 1 < x) (g : ℕ → ℝ) (hg : ∀ m : ℕ, 0 < g m) :
    Filter.Tendsto
      (fun m =>
        ∑
          ρ ∈
            (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner (2 * m) (g m))
                  (unconditionalHeightUpperCorner (g m))).filter
              (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
          dirichletLFunctionLogZeroContribution x χ ρ)
      Filter.atTop
      (nhds (-((∑' j : ℕ, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))) := by
  have hi : Function.Injective (fun j : ℕ => 2 * (j + 1)) := by
    intro a b h
    exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left (of_decide_eq_true rfl : 0 < 2) h)
  have hs := (summable_log_inversePower_nat hx).comp_injective hi
  have ht :
    Filter.Tendsto
      (fun m =>
        -((∑ j ∈ Finset.range m, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))
      Filter.atTop
      (nhds (-((∑' j : ℕ, x⁻¹ ^ (2 * (j + 1)) / ((2 * (j + 1) : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))) := by
    simpa only [Complex.ofReal_neg, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp hs.hasSum.tendsto_sum_nat.neg
  exact
    ht.congr'
      (by
        filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        exact
          (sum_even_log_trivialZeros_unconditionalRectangle_eq hp hne he x m hm (g m) (hg m)).symm)

/-- For an odd primitive nonprincipal character and scale greater than one, the
trivial logarithmic sums tend to the full odd correction along any positive
height selection as the left edge expands. Use the exact partial sums and the
summable odd subsequence. This removes RH from the trivial-zero limit. -/
theorem tendsto_sum_odd_log_trivialZeros_unconditionalRectangle {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (ho : χ.Odd) {x : ℝ}
    (hx : 1 < x) (g : ℕ → ℝ) (hg : ∀ m : ℕ, 0 < g m) :
    Filter.Tendsto
      (fun m =>
        ∑
          ρ ∈
            (dirichletLFunctionZerosInRectangle χ hne (unconditionalHeightLowerCorner (2 * m) (g m))
                  (unconditionalHeightUpperCorner (g m))).filter
              (fun ρ => DirichletCharacter.gammaFactor χ ρ = 0 ∧ ρ ≠ 0),
          dirichletLFunctionLogZeroContribution x χ ρ)
      Filter.atTop
      (nhds (-((∑' j : ℕ, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))) := by
  have hi : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b h
    exact Nat.eq_of_mul_eq_mul_left (of_decide_eq_true rfl : 0 < 2) (Nat.add_right_cancel h)
  have hs := (summable_log_inversePower_nat hx).comp_injective hi
  have ht :
    Filter.Tendsto
      (fun m => -((∑ j ∈ Finset.range m, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))
      Filter.atTop
      (nhds (-((∑' j : ℕ, x⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))) := by
    simpa only [Complex.ofReal_neg, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto _).comp hs.hasSum.tendsto_sum_nat.neg
  exact
    ht.congr'
      (by
        filter_upwards [Filter.eventually_ge_atTop 1] with m hm
        exact
          (sum_odd_log_trivialZeros_unconditionalRectangle_eq hp hne ho x m hm (g m) (hg m)).symm)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
