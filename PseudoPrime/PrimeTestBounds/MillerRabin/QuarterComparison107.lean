/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiBoundary107
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseGap107
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInterval600
import all PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Right-endpoint comparisons for section 107 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem section107_coord_one {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    14 ≤ quarterCoord570 (r ^ 2) 1 ∧ quarterCoord570 (r ^ 2) 1 ≤ 15 := by
  have hl := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 300) hr.1 2
  have hp : 0 < r := by linarith only [hr.1]
  have hu := pow_le_pow_left₀ hp.le hr.2 2
  have hlo :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 90000)
      ((by norm_num only : (90000 : ℝ) = 300 ^ 2) ▸ hl)
  have hhi := Real.log_le_log (sq_pos_of_pos hp) ((by norm_num only : (97969 : ℝ) = 313 ^ 2) ▸ hu)
  unfold quarterCoord570
  rw [one_div, Real.log_inv, sub_neg_eq_add]
  norm_num only
  exact ⟨by linarith only [hlo, phase_log107_300.1], by linarith only [hhi, phase_box107_313.1.2]⟩

/-- The section 99 centered error budget also holds on the full section 107
radius interval. The trivial-zero estimate uses the certified coordinates. -/
theorem section107_principal_error (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    -0.0273 ≤ section99PrincipalError r := by
  have hl : 292 ≤ r := (by norm_num only : (292 : ℝ) ≤ 300).trans hr.1
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ (by linarith only [hl]) (n := 2)
  have hc := section107_coord_one hr
  apply section99_error_of_abel hl
  rw [section99_abel_zero_split hx]
  linarith only [section99_nontrivial_lower hRH hl, quarter_trivial_upper_coord hl hc.1 hc.2]

/-- Under RH the principal term on the section 107 interval retains the
signed Chebyshev boundary and the positive log term. The centered error
uses the section 99 budget, which leaves room in the right-endpoint tests. -/
theorem section107_principal_budget (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.717289 * r - 0.0273 + 0.002137 + 4 * quarterWeight570 X X * (Chebyshev.psi X - X) -
        3 * Real.log (2 * Real.pi) * quarterWeight570 X 1 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  have hp :=
    quarter_principal_signed ((by norm_num only : (292 : ℝ) ≤ 300).trans hr.1)
      (section107_principal_error hRH hr)
  have hb := quarter_log_boundary_107 (by linarith only [hr.1]) hr.2
  dsimp only at hp ⊢
  rw [mul_add] at hp
  linarith only [hp, hb]

private theorem conductor_313_lower : 3 ≤ section99Conductor 313 := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000 / 57) (j := 4) (n := 24) (lo := 357 / 125)
        (hi := 3) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have he : (57 / 1000 : ℝ) ≤ Real.exp (-(51 / 50) * (14 / 5)) := by
    rw [show -(51 / 50 : ℝ) * (14 / 5) = -(357 / 125) by norm_num only, Real.exp_neg]
    have h := (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 1000 / 57)).mp hlog
    exact
      (by norm_num only : (57 / 1000 : ℝ) = (1000 / 57)⁻¹).trans_le
        ((inv_le_inv₀ (by norm_num only) (Real.exp_pos _)).mpr h)
  have hX : Real.log 97969 = 2 * Real.log 313 := by
    rw [show (97969 : ℝ) = 313 ^ 2 by norm_num only, Real.log_pow, Nat.cast_ofNat]
  have hv : (11.49 : ℝ) ≤ 2 * Real.log 313 := by linarith only [hX, phase_box107_313.1.1]
  have hp : (0.002538 : ℝ) ≤ (313 : ℝ) ^ (-(26 / 25 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num only), ←
      show -(13 / 25 : ℝ) * Real.log 97969 = Real.log 313 * -(26 / 25 : ℝ) by
        rw [hX]; ring]
    exact
      (by norm_num only : (0.002538 : ℝ) ≤ 253883156349754752 / 10 ^ 20).trans
        phase_box107_313.2.1.1
  unfold section99Conductor
  have hv' :=
    pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 14 / 5 + 11.49) (add_le_add_right hv (14 / 5)) 5
  have ha := mul_le_mul hp hv' (by norm_num only) ((by norm_num only : (0 : ℝ) ≤ 0.002538).trans hp)
  have hb := mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ 4 * (51 / 50) ^ 5)
  have hc := div_le_div_of_nonneg_right hb (by norm_num only : (0 : ℝ) ≤ 120)
  exact
    (by norm_num only :
          (3 : ℝ) ≤
            (4 * (51 / 50) ^ 5 * (57 / 1000) / 120) * (0.002538 * (14 / 5 + 11.49) ^ 5)).trans
      (mul_le_mul hc ha (by norm_num only) (by positivity))

private theorem section107_euler_row {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    section99Conductor r + 4 * positiveTail570 (r ^ 2) ≤ 3.78087 + 0.0162 * (313 - r) := by
  let E := fun t : ℝ ↦ section99Conductor t + 4 * positiveTail570 (t ^ 2)
  have ht {t : ℝ} (h : t ∈ Set.Icc (300 : ℝ) 313) : 292 ≤ t :=
    (by norm_num only : (292 : ℝ) ≤ 300).trans h.1
  have hd (t : ℝ) (h : t ∈ Set.Icc (300 : ℝ) 313) : DifferentiableAt ℝ E t :=
    (quarter_euler_deriv_nonpos (ht h)).1
  have hm :=
    antitoneOn_of_deriv_nonpos (convex_Icc (300 : ℝ) 313)
      (fun t h ↦ (hd t h).continuousAt.continuousWithinAt)
      (fun t h ↦ (hd t (interior_subset h)).differentiableWithinAt)
      (fun t h ↦ (quarter_euler_deriv_nonpos (ht (interior_subset h))).2)
  have hcd (t : ℝ) (h : t ∈ Set.Icc (300 : ℝ) 313) : DifferentiableAt ℝ section99Conductor t :=
    (section99_conductor_deriv (by linarith only [h.1])).differentiableAt
  have hc : AntitoneOn section99Conductor (Set.Icc (300 : ℝ) 313) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun t h ↦ (hcd t h).continuousAt.continuousWithinAt)
      (fun t h ↦ (hcd t (interior_subset h)).differentiableWithinAt)
      (fun t h ↦ (section99_conductor_slope (ht (interior_subset h))).2)
  have hs (t : ℝ) (h : t ∈ interior (Set.Icc (300 : ℝ) 313)) : -0.0162 ≤ deriv E t := by
    have hi := interior_subset h
    have hE := (hm (by norm_num only [Set.mem_Icc, and_self]) hi hi.1).trans section99_euler_300
    have hC := conductor_313_lower.trans (hc hi (by norm_num only [Set.mem_Icc, and_self]) hi.2)
    apply le_of_mul_le_mul_left (a := t) _ (by linarith only [hi.1])
    linarith only [hE, hC, hi.1, quarter_euler_slope_sharp (ht hi)]
  have h :=
    (convex_Icc (300 : ℝ) 313).mul_sub_le_image_sub_of_le_deriv
      (fun t hi ↦ (hd t hi).continuousAt.continuousWithinAt)
      (fun t hi ↦ (hd t (interior_subset hi)).differentiableWithinAt) hs r hr 313
      (by norm_num only [Set.mem_Icc, and_self]) hr.2
  dsimp only [E] at h
  linarith only [h, section107_euler_313]

private theorem section107_linear_lower {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    3 / 200 * (r - 313) + 239 / 10000 ≤
      phaseClosed107 r +
        4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  have hU := hr.2.trans (by norm_num only : (313 : ℝ) ≤ 314)
  by_cases h₁ : r ≤ 304
  · have hp := phase_closed_lower107 (le_refl _) hr.1 hU phase_remainder107_300
    linarith only [h₁, hp, quarter_psi_boundary_304 hr.1 h₁]
  have hl := le_of_not_ge h₁
  by_cases h₂ : r ≤ 308
  · have hp := phase_closed_lower107 (by norm_num only) hl hU phase_remainder107_304
    linarith only [h₂, hp, quarter_psi_boundary_308 hl h₂]
  have hl := le_of_not_ge h₂
  by_cases h₃ : r ≤ 312
  · have hp := phase_closed_lower107 (by norm_num only) hl hU phase_remainder107_308
    linarith only [h₃, hp, quarter_psi_boundary_312 hl h₃]
  have hl := le_of_not_ge h₃
  have hp := phase_closed_lower107 (by norm_num only) hl hU phase_remainder107_312
  linarith only [hr.2, hp, quarter_psi_boundary_313 hl hr.2]

/-- The section 107 gap clears the residual budget over radii 300 to 313.
A linear lower bound for the combined phase and signed boundary leaves
one final comparison at radius 313. -/
theorem section107_gap_margin {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    0.002045924 <
      -0.0315745 * r + 13.642245167 - (section99Conductor r + 4 * positiveTail570 (r ^ 2)) +
        phaseClosed107 r +
        4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  linarith only [section107_linear_lower hr, section107_euler_row hr, hr.2]

/-- The positive section 107 gap after paying the additional 0.00095
of the certified centered principal error budget. -/
theorem section107_gap_with_error {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    0 <
      -0.0315745 * r + 13.641295167 - (section99Conductor r + 4 * positiveTail570 (r ^ 2)) +
        phaseClosed107 r +
        4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  linarith only [section107_gap_margin hr]

/-- The original section 107 comparison is positive on the same interval. -/
theorem section107_gap_pos {r : ℝ} (hr : r ∈ Set.Icc 300 313) :
    0 <
      -0.0315745 * r + 13.642245167 - (section99Conductor r + 4 * positiveTail570 (r ^ 2)) +
        phaseClosed107 r +
        4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  linarith only [section107_gap_margin hr]

end PseudoPrime.PrimeTestBounds.MillerRabin
