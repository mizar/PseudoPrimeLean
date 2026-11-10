/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularDualScaleGeneral

/-! # Variable-width triangular support at the quarter cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The transform of a positive-width triangular kernel vanishes at a
positive argument whose logarithm is at least twice the width. The explicit
profile and reality of the Mellin transform give both complex components.
This supplies support bounds at scale one and at inverse scale. -/
theorem quarter_triangular_transform_zero {a u : ℝ} (ha : 0 < a) (hu : 0 < u)
    (hbound : 2 * a ≤ Real.log u) :
    (LLS.PaperStatements.triangularMellinKernel ha).transform u = 0 := by
  have hz : 0 ≤ Real.log u := by linarith only [ha, hbound]
  have hprof : LLS.PaperStatements.triangularKernelProfile a u = 0 := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [abs_of_nonneg hz]
    exact max_eq_left (by linarith only [hbound])
  let K := LLS.PaperStatements.triangularMellinKernel ha
  have ht : K.transform u = 0 := by
    apply Complex.ext
    · change (K.transform u).re = 0
      rw [LLS.PaperStatements.triangular_transform_of_function K ha rfl hu, hprof]
    · change (Analysis.inverseMellin K.function 0 u).im = 0
      exact K.mellin_real _ hu
  exact ht

/-- A positive-index scale-one triangular term is zero once the logarithm
of its index reaches twice the width. The profile support gives the vanishing
used to replace the full scale-one series by a finite cutoff sum. -/
theorem quarter_triangular_scale_one_term {a : ℝ} (ha : 0 < a) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n ≠ 0) (hbound : 2 * a ≤ Real.log n) :
    (LLS.PaperStatements.triangularMellinKernel ha).summand χ 1 n = 0 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have ht := quarter_triangular_transform_zero ha hn0 hbound
  simp only [LLS.PaperStatements.MellinKernel.summand, hn, ite_false, div_one, ht, mul_zero]

/-- When `X ≥ 1` lies at or beyond the triangular support endpoint, the full
scale-one arithmetic series equals the finite sum through `floor X` for every
character. Terms outside the cutoff vanish by the explicit transform support.
This identifies the scale-one credit in the high-index comparison. -/
theorem quarter_triangular_scale_one_sum {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : 2 * a ≤ Real.log X) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, (LLS.PaperStatements.triangularMellinKernel ha).summand χ 1 n) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (LLS.PaperStatements.triangularMellinKernel ha).summand χ 1 n := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true]
  · have hnlo : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnhi : ⌊X⌋₊ < n := by
      by_contra h
      exact hn (Finset.mem_Icc.mpr ⟨hnlo, Nat.le_of_not_gt h⟩)
    have hXn : X < (n : ℝ) := (Nat.floor_lt (zero_le_one.trans hX)).mp hnhi
    have hl := Real.log_le_log (zero_lt_one.trans_le hX) hXn.le
    exact quarter_triangular_scale_one_term ha χ hn0 (hbound.trans hl)

/-- At a positive scale, a cutoff whose logarithmic ratio is at least twice
the kernel width contains the entire triangular arithmetic series. The
transform vanishes beyond the cutoff, including at its support endpoint. -/
theorem quarter_triangular_forward_sum {a X Y : ℝ} (ha : 0 < a) (hX : 0 < X) (hY : 1 ≤ Y)
    (hbound : 2 * a ≤ Real.log (Y / X)) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, (LLS.PaperStatements.triangularMellinKernel ha).summand χ X n) =
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (LLS.PaperStatements.triangularMellinKernel ha).summand χ X n := by
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true]
  · have hnlo : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnhi : ⌊Y⌋₊ < n := by
      by_contra h
      exact hn (Finset.mem_Icc.mpr ⟨hnlo, Nat.le_of_not_gt h⟩)
    have hYn : Y < (n : ℝ) := (Nat.floor_lt (zero_le_one.trans hY)).mp hnhi
    have hratio : Y / X ≤ (n : ℝ) / X := div_le_div_of_nonneg_right hYn.le hX.le
    have hlog := Real.log_le_log (div_pos (zero_lt_one.trans_le hY) hX) hratio
    have ht :=
      quarter_triangular_transform_zero ha (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)) hX)
        (hbound.trans hlog)
    simp only [LLS.PaperStatements.MellinKernel.summand, hn0, ite_false, ht, mul_zero]

/-- At inverse scale `x⁻¹`, every triangular arithmetic term vanishes when
`x ≥ 1` and `log x ≥ 2a`. The logarithmic support ends at `exp (2a)`; the
endpoint is included. This removes the inverse arithmetic sum in the
variable-width high-index argument. -/
theorem quarter_triangular_inverse_term {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x)
    (hbound : 2 * a ≤ Real.log x) {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (LLS.PaperStatements.triangularMellinKernel ha).summand χ x⁻¹ n = 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hu : 0 < (n : ℝ) / x⁻¹ := div_pos (by linarith only [hn1]) (inv_pos.mpr hx0)
    have hux : x ≤ (n : ℝ) / x⁻¹ := by
      rw [div_inv_eq_mul]
      nlinarith only [hn1, hx0]
    have hlog := Real.log_le_log hx0 hux
    have ht := quarter_triangular_transform_zero ha hu (hbound.trans hlog)
    simp only [LLS.PaperStatements.MellinKernel.summand, hn, ite_false, ht, mul_zero]

/-- At inverse scale `x⁻¹`, the full triangular arithmetic series vanishes
when `log x ≥ 2a`. Termwise support vanishing applies to every character and
is used in the variable-width dual-scale identity. -/
theorem quarter_triangular_inverse_sum {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x)
    (hbound : 2 * a ≤ Real.log x) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑' n : ℕ, (LLS.PaperStatements.triangularMellinKernel ha).summand χ x⁻¹ n) = 0 := by
  simp only [quarter_triangular_inverse_term ha hx hbound, tsum_zero]

/-- At or beyond the triangular support endpoint, the GRH dual-scale formula
contains neither the inverse-scale arithmetic sum nor the conductor term.
Both vanish by support, leaving the forward arithmetic sum, oscillating zero
sum, and the two central Gamma terms used by the high-index comparison. -/
theorem quarter_triangular_dual_boundary {a : ℝ} (ha : 0 < a) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x)
    (hbound : 2 * a ≤ Real.log x) :
    let K := LLS.PaperStatements.triangularMellinKernel ha
    let G := fun (ψ : DirichletCharacter ℂ q) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor (Complex.I * t + 1 / 2) *
            (K.function (Complex.I * t) * (y : ℂ) ^ (Complex.I * t)))
    (∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) = G χ x + G χ⁻¹ x⁻¹ := by
  have hz : 0 ≤ Real.log x := by linarith only [ha, hbound]
  have hp0 : LLS.PaperStatements.triangularKernelProfile a x = 0 := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [abs_of_nonneg hz]
    exact max_eq_left (by linarith only [hbound])
  have h := LLS.PaperStatements.triangular_dual_signed_central ha hq hGRH hp hne hinv hx
  dsimp only at h ⊢
  rw [quarter_triangular_inverse_sum ha hx hbound χ⁻¹, add_zero, hp0] at h
  simpa only [Complex.ofReal_zero, mul_zero, zero_add] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
