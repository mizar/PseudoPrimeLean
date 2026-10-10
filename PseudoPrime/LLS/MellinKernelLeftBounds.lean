/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelVerticalIntegrability

/-!
# Uniform conductor bounds for left Mellin integrals

The primitive functional equation isolates the conductor logarithm.
Kernel decay makes the reflected logarithmic majorant integrable.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open AnalyticNumberTheory.DirichletLFunction in
/-- For a fixed allowed left line between minus three halves and minus one half, a
positive constant bounds the normalized completed integral by (log N + 1) times x^a.
It works for every primitive nonprincipal character with nonprincipal inverse and every
positive scale. Reflect the completed logarithmic derivative, isolate the conductor term,
and integrate its uniform logarithmic majorant against the kernel's quadratic decay.
This supplies the conductor error in the arithmetic Mellin formula. -/
theorem exists_norm_left_completedIntegral_le_log_rpow (K : MellinKernel) {a : ℝ}
    (ha : -1 / 2 - K.delta < a) (hal : a < -1 / 2) (ha2 : -3 / 2 ≤ a) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          1 ≤ N →
            χ.IsPrimitive →
            χ ≠ 1 →
            χ⁻¹ ≠ 1 →
            ∀ {x : ℝ},
              0 < x →
                ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                      (∫ t : ℝ,
                        -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
                          (K.function ((a : ℂ) + Complex.I * t) *
                            (x : ℂ) ^ ((a : ℂ) + Complex.I * t)))‖ ≤
                  C * (Real.log N + 1) * x ^ a := by
  obtain ⟨A, hA, hbA⟩ :=
    exists_uniform_norm_completed_vertical_left_le_log (σ := a + 1 / 2) (by linarith only [hal])
      (by linarith only [ha2])
  have hu : a ≤ 1 / 2 + K.delta := by linarith only [hal, K.delta_pos]
  obtain ⟨B, hB, hbB⟩ := exists_norm_line_le_inverseSquare K ha hu hal.ne
  let H := fun t : ℝ => (Real.log (4 + |t|) + 1) / (1 + t ^ 2)
  let D := (B * (A + 1)) * (∫ t : ℝ, H t)
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  refine ⟨1 + ‖d‖ * max D 0, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (norm_nonneg _) (le_max_right _ _))
  · intro N _ χ hN hp hne hinv x hx
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlog : 0 ≤ Real.log N := Real.log_nonneg hNr
    have hnlog : ‖Complex.log (N : ℂ)‖ = Real.log N := by
      rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    let E : ℝ := (Real.log N + 1) * x ^ a
    have hE : 0 ≤ E := mul_nonneg (by linarith only [hlog]) (Real.rpow_nonneg hx.le a)
    let F := fun t : ℝ =>
      -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
        (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t))
    have hiF : MeasureTheory.Integrable F :=
      integrable_completed_left_line K hp hne hinv ha hal ha2 hx
    have hb (t : ℝ) : ‖F t‖ ≤ (E * (B * (A + 1))) * H t := by
      have hL : 1 ≤ Real.log (4 + |t|) + 1 := by
        have hl := Real.log_nonneg (show (1 : ℝ) ≤ 4 + |t| from by linarith only [abs_nonneg t])
        linarith only [hl]
      have hγ := hbA N χ hp hne hinv t
      have he : (((a + 1 / 2 : ℝ) : ℂ) + Complex.I * t) = ((a : ℂ) + Complex.I * t) + 1 / 2 := by
        rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
        ring
      rw [he, hnlog] at hγ
      have hg :
        ‖logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2)‖ ≤
          ((Real.log N + 1) * (A + 1)) * (Real.log (4 + |t|) + 1) := by
        calc
          _ ≤ Real.log N + A * (Real.log (4 + |t|) + 1) := hγ
          _ ≤ (Real.log N + A) * (Real.log (4 + |t|) + 1) := by nlinarith only [hL, hlog]
          _ ≤ _ :=
            mul_le_mul_of_nonneg_right
              (by nlinarith only [hlog, hA] : Real.log N + A ≤ (Real.log N + 1) * (A + 1))
              (zero_le_one.trans hL)
      dsimp only [F]
      rw [norm_mul, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      calc
        _ ≤
            (((Real.log N + 1) * (A + 1)) * (Real.log (4 + |t|) + 1)) *
              ((B / (1 + t ^ 2)) * x ^ a) :=
          mul_le_mul hg (mul_le_mul_of_nonneg_right (hbB t) (Real.rpow_nonneg hx.le a))
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.le a))
            (mul_nonneg (mul_nonneg (by linarith only [hlog]) (by linarith only [hA]))
              (zero_le_one.trans hL))
        _ = _ := by
          dsimp only [H, E]; ring
    have hiH : MeasureTheory.Integrable (fun t : ℝ => (E * (B * (A + 1))) * H t) :=
      PseudoPrime.Analysis.integrable_log_add_abs_div_one_add_sq.const_mul _
    have hi :=
      (MeasureTheory.norm_integral_le_integral_norm F).trans
        (MeasureTheory.integral_mono hiF.norm hiH hb)
    rw [MeasureTheory.integral_const_mul] at hi
    have hi' : ‖∫ t : ℝ, F t‖ ≤ E * D := by simpa only [D, mul_assoc] using hi
    have hb' : ‖d * ∫ t : ℝ, F t‖ ≤ (1 + ‖d‖ * max D 0) * E := by
      rw [norm_mul]
      calc
        _ ≤ ‖d‖ * (E * D) := mul_le_mul_of_nonneg_left hi' (norm_nonneg _)
        _ ≤ ‖d‖ * (E * max D 0) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_left D 0) hE) (norm_nonneg _)
        _ ≤ _ := by nlinarith only [hE]
    simpa only [d, E, mul_assoc] using hb'

/-- On a fixed allowed left line, the normalized completed integral for primitive
nonprincipal data has norm at most C log N / sqrt x for N at least two and x at least one.
The positive constant depends only on the kernel and line. Absorb the constant part into
log N using log 2, and compare x^a with the inverse square root. This is the conductor
error required in the general Mellin explicit formula. -/
theorem exists_norm_left_completedIntegral_le_log_div_sqrt (K : MellinKernel) {a : ℝ}
    (ha : -1 / 2 - K.delta < a) (hal : a < -1 / 2) (ha2 : -3 / 2 ≤ a) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          2 ≤ N →
            χ.IsPrimitive →
            χ ≠ 1 →
            χ⁻¹ ≠ 1 →
            ∀ {x : ℝ},
              1 ≤ x →
                ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                      (∫ t : ℝ,
                        -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
                          (K.function ((a : ℂ) + Complex.I * t) *
                            (x : ℂ) ^ ((a : ℂ) + Complex.I * t)))‖ ≤
                  C * Real.log N / Real.sqrt x := by
  obtain ⟨C, hC, hb⟩ := exists_norm_left_completedIntegral_le_log_rpow K ha hal ha2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  refine
    ⟨C * (1 + 1 / Real.log 2),
      mul_pos hC (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg zero_le_one h2.le)), ?_⟩
  intro N _ χ hN hp hne hinv x hx
  have hN1 : 1 ≤ N := (by norm_num only : 1 ≤ 2).trans hN
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num only) hNr
  have hlog : 0 ≤ Real.log N := h2.le.trans hlog2
  have hunit : 1 ≤ Real.log N / Real.log 2 :=
    (le_div_iff₀ h2).mpr (by simpa only [one_mul] using hlog2)
  have hl : Real.log N + 1 ≤ (1 + 1 / Real.log 2) * Real.log N := by
    simp only [div_eq_mul_inv, one_mul] at hunit ⊢
    nlinarith only [hunit]
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hxpow : x ^ a ≤ 1 / Real.sqrt x := by
    calc
      _ ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hal.le
      _ = _ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow,
          one_div]
  calc
    _ ≤ C * (Real.log N + 1) * x ^ a := hb N χ hN1 hp hne hinv hxpos
    _ ≤ (C * ((1 + 1 / Real.log 2) * Real.log N)) * (1 / Real.sqrt x) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hl hC.le) hxpow (Real.rpow_nonneg hxpos.le a)
        (mul_nonneg hC.le (mul_nonneg (by positivity : 0 ≤ 1 + 1 / Real.log 2) hlog))
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements.MellinKernel
