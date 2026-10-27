/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularKernel
public import PseudoPrime.LLS.MellinKernelContour
public import PseudoPrime.Analysis.TriangularDigammaMoments

/-! # Absolute first resolvent moment of the triangular kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive c and any real u, bound u by its inverse square-root constant
plus its square times sqrt c. A square nonnegativity identity gives the inequality.
This replaces a Holder estimate by an explicit integrable majorant. -/
theorem resolvent_first_moment_am_bound {c : ℝ} (hc : 0 < c) (u : ℝ) :
    u ≤ 1 / Real.sqrt c + Real.sqrt c * u ^ 2 := by
  have hy := Real.sqrt_pos.mpr hc
  have h : u * Real.sqrt c ≤ 1 + (Real.sqrt c) ^ 2 * u ^ 2 := by
    nlinarith only [sq_nonneg (Real.sqrt c * u - 1 / 2)]
  apply (mul_le_mul_iff_left₀ hy).mp
  calc
    _ ≤ 1 + (Real.sqrt c) ^ 2 * u ^ 2 := h
    _ = _ := by
      rw [add_mul, div_mul_cancel₀ 1 hy.ne']
      ring

/-- For positive c and any triangular parameter and real height, bound the absolute
first resolvent moment by the kernel norm and its height-square Cauchy moment.
Apply the scalar quadratic inequality to the normalized height. This supplies domination. -/
theorem triangular_resolvent_first_moment_majorant {a c : ℝ} (hc : 0 < c) (t : ℝ) :
    |t| * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / Real.sqrt (c ^ 2 + t ^ 2) ≤
      (1 / Real.sqrt c) * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ +
        Real.sqrt c *
          (t ^ 2 * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2)) := by
  have hd : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have h := resolvent_first_moment_am_bound hc (|t| / Real.sqrt (c ^ 2 + t ^ 2))
  rw [div_pow, sq_abs, Real.sq_sqrt hd.le] at h
  have hm :=
    mul_le_mul_of_nonneg_right h (norm_nonneg (Analysis.triangularMellinFunction a (Complex.I * t)))
  convert hm using 1 <;> ring

/-- For positive triangular parameter and positive c, the absolute first resolvent
moment is integrable and its normalized integral is at most 2a/sqrt c plus 2sqrt c/c.
Integrate the scalar majorant using mass 2a and the height-square moment bound.
This supplies integrated norm bounds for the digamma reciprocal-difference series. -/
theorem triangular_resolvent_first_moment_integrable_and_bound {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    MeasureTheory.Integrable
        (fun t : ℝ ↦
          |t| * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / Real.sqrt (c ^ 2 + t ^ 2)) ∧
      (∫ t : ℝ,
            |t| * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ /
              Real.sqrt (c ^ 2 + t ^ 2)) /
          (2 * Real.pi) ≤
        2 * a / Real.sqrt c + 2 * Real.sqrt c / c := by
  let K := triangularMellinKernel ha
  let w := fun t : ℝ ↦ ‖Analysis.triangularMellinFunction a (Complex.I * t)‖
  let M := fun t : ℝ ↦ t ^ 2 * w t / (c ^ 2 + t ^ 2)
  let F := fun t : ℝ ↦ |t| * w t / Real.sqrt (c ^ 2 + t ^ 2)
  let G := fun t : ℝ ↦ (1 / Real.sqrt c) * w t + Real.sqrt c * M t
  have hd (t : ℝ) : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have hw : MeasureTheory.Integrable w := by
    have h :=
      MellinKernel.integrable_line_in_strip K (c := 0)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < 0; norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only)
    simp only [Complex.ofReal_zero, zero_add] at h
    exact h.norm
  have hm := (Analysis.triangular_digamma_moment_integrable_and_bound ha.ne' hc).1
  have hG : MeasureTheory.Integrable G := (hw.const_mul _).add (hm.const_mul _)
  have hK : Continuous w :=
    ((Analysis.differentiable_triangularMellinFunction a).continuous.comp
        (continuous_const.mul Complex.continuous_ofReal)).norm
  have hF : Continuous F :=
    (continuous_abs.mul hK).div ((continuous_const.add (continuous_id.pow 2)).sqrt)
      (fun t ↦ (Real.sqrt_pos.mpr (hd t)).ne')
  have hb (t : ℝ) : F t ≤ G t := triangular_resolvent_first_moment_majorant hc t
  have hI : MeasureTheory.Integrable F :=
    hG.mono' hF.aestronglyMeasurable
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          rw [Real.norm_eq_abs,
            abs_of_nonneg
              (div_nonneg (mul_nonneg (abs_nonneg t) (norm_nonneg _)) (Real.sqrt_nonneg _))]
          exact hb t))
  have hi := MeasureTheory.integral_mono hI hG hb
  have hmass : (∫ t : ℝ, w t) / (2 * Real.pi) = 2 * a := triangular_mass_of_function K ha rfl
  have hM := Analysis.triangular_digamma_normalized_moment_le ha.ne' hc
  change (∫ t : ℝ, M t) / (2 * Real.pi) ≤ 2 / c at hM
  have hN := div_le_div_of_nonneg_right hi (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).le
  change (∫ t : ℝ, F t) / (2 * Real.pi) ≤ (∫ t : ℝ, G t) / (2 * Real.pi) at hN
  dsimp only [G] at hN
  rw [MeasureTheory.integral_add (hw.const_mul _) (hm.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, add_div, mul_div_assoc,
    mul_div_assoc, hmass] at hN
  change
    (∫ t : ℝ, F t) / (2 * Real.pi) ≤
      (1 / Real.sqrt c) * (2 * a) + Real.sqrt c * ((∫ t : ℝ, M t) / (2 * Real.pi)) at hN
  have hB := mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg c)
  refine ⟨hI, ?_⟩
  change (∫ t : ℝ, F t) / (2 * Real.pi) ≤ _
  simp only [div_eq_mul_inv] at hN hB ⊢
  linarith only [hN, hB]

/-- For positive triangular parameter and c, the normalized absolute first
resolvent moment is at most (2a+2)/sqrt c. Simplify the integrable moment budget with
the square-root identity. This gives inverse square-root decay in the shifted pole index. -/
theorem triangular_resolvent_normalized_first_moment_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (∫ t : ℝ,
          |t| * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / Real.sqrt (c ^ 2 + t ^ 2)) /
        (2 * Real.pi) ≤
      (2 * a + 2) / Real.sqrt c := by
  have h := (triangular_resolvent_first_moment_integrable_and_bound ha hc).2
  have hy := Real.sqrt_pos.mpr hc
  have he : Real.sqrt c / c = 1 / Real.sqrt c :=
    (div_eq_div_iff hc.ne' hy.ne').mpr
      (by
        rw [one_mul]
        simpa only [pow_two] using Real.sq_sqrt hc.le)
  rw [mul_div_assoc 2 (Real.sqrt c) c, he] at h
  have hr : 2 * a / Real.sqrt c + 2 * (1 / Real.sqrt c) = (2 * a + 2) / Real.sqrt c := by ring
  exact h.trans_eq hr

end PseudoPrime.LLS.PaperStatements
