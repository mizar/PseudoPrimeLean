/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelZetaVerticalIntegrability
public import PseudoPrime.LLS.MellinKernelZetaContourLimits

/-! # Uniform xi contributions in the principal Mellin formula

The left xi integral and the kernel-pole residue are bounded at scales at least one.
The infinite xi contour identity transfers these bounds to the right integral.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- On a fixed admissible left line in `[-1,-1/2)`, a positive constant bounds
the normalized ξ integral for every `x ≥ 1`. The logarithmic ξ majorant and
inverse-square kernel majorant are integrable, and the Mellin power has norm at
most one. This controls the left integral in the principal explicit formula. -/
theorem exists_norm_xi_leftIntegral_le (K : MellinKernel) {a : ℝ} (ha : -1 / 2 - K.delta < a)
    (hal : a < -1 / 2) (ha2 : -1 ≤ a) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {x : ℝ},
          1 ≤ x →
            ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi
                          (((a : ℂ) + Complex.I * t) + 1 / 2) *
                      (K.function ((a : ℂ) + Complex.I * t) *
                        (x : ℂ) ^ ((a : ℂ) + Complex.I * t)))‖ ≤
              C := by
  obtain ⟨A, hA, hbA⟩ :=
    AnalyticNumberTheory.RiemannXi.exists_norm_logDeriv_vertical_left_le_log (σ := a + 1 / 2)
      (by linarith only [hal]) (by linarith only [ha2])
  have hu : a ≤ 1 / 2 + K.delta := by linarith only [hal, K.delta_pos]
  obtain ⟨B, hB, hbB⟩ := exists_norm_line_le_inverseSquare K ha hu hal.ne
  let H := fun t : ℝ => (Real.log (4 + |t|) + 1) / (1 + t ^ 2)
  let D := (A * B) * (∫ t : ℝ, H t)
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  refine ⟨1 + ‖d‖ * max D 0, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (norm_nonneg _) (le_max_right _ _))
  · intro x hx
    have hxp : 0 < x := zero_lt_one.trans_le hx
    let F := fun t : ℝ =>
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (((a : ℂ) + Complex.I * t) + 1 / 2) *
        (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t))
    have hiF : MeasureTheory.Integrable F := integrable_xi_left_line K ha hal ha2 hxp
    have hb (t : ℝ) : ‖F t‖ ≤ (A * B) * H t := by
      have hL : 0 ≤ Real.log (4 + |t|) + 1 := by
        have hl := Real.log_nonneg (show (1 : ℝ) ≤ 4 + |t| from by linarith only [abs_nonneg t])
        linarith only [hl]
      have hγ := hbA t
      have he : (((a + 1 / 2 : ℝ) : ℂ) + Complex.I * t) = ((a : ℂ) + Complex.I * t) + 1 / 2 := by
        rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
        ring
      rw [he] at hγ
      dsimp only [F]
      rw [norm_mul, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxp]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      calc
        _ ≤ (A * (Real.log (4 + |t|) + 1)) * ((B / (1 + t ^ 2)) * 1) :=
          mul_le_mul hγ
            (mul_le_mul (hbB t) (Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith only [hal]))
              (Real.rpow_nonneg hxp.le a) (div_nonneg hB.le (by positivity)))
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hxp.le a)) (mul_nonneg hA.le hL)
        _ = _ := by
          dsimp only [H]; ring
    have hiH : MeasureTheory.Integrable (fun t : ℝ => (A * B) * H t) :=
      Analysis.integrable_log_add_abs_div_one_add_sq.const_mul (A * B)
    have hi :=
      (MeasureTheory.norm_integral_le_integral_norm F).trans
        (MeasureTheory.integral_mono hiF.norm hiH hb)
    rw [MeasureTheory.integral_const_mul] at hi
    change ‖∫ t : ℝ, F t‖ ≤ D at hi
    change ‖d * ∫ t : ℝ, F t‖ ≤ _
    rw [norm_mul]
    exact
      (mul_le_mul_of_nonneg_left (hi.trans (le_max_left D 0)) (norm_nonneg d)).trans
        (le_add_of_nonneg_left zero_le_one)

/-- The shifted ξ kernel-pole residue is uniformly bounded for `x ≥ 1`.
Its scale factor has norm `x^(-1/2) ≤ 1`; the logarithmic derivative and
regularized kernel values are fixed. This bounds the remaining pole contribution
in the principal ξ contour identity. -/
theorem exists_norm_xi_poleResidue_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {x : ℝ},
          1 ≤ x →
            ‖weightedResidue K (fun t : ℂ => AnalyticNumberTheory.RiemannXi.riemannXi (t + 1 / 2)) x
                  (-1 / 2)‖ ≤
              C := by
  let F := fun t : ℂ => AnalyticNumberTheory.RiemannXi.riemannXi (t + 1 / 2)
  let A := ‖logDeriv F (-1 / 2)‖ * ‖K.regularized (-1 / 2)‖
  have hA : 0 ≤ A := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨A + 1, add_pos_of_nonneg_of_pos hA zero_lt_one, ?_⟩
  intro x hx
  rw [weightedResidue, ite_eq_left rfl, norm_mul, norm_neg, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
  simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re]
  rw [← mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num only : -(1 : ℝ) / 2 ≤ 0)) hA).trans
      (by simpa only [mul_one] using le_add_of_nonneg_right zero_le_one (a := A))

open AnalyticNumberTheory.RiemannXi in
/-- Under RH, on fixed admissible contour lines around the kernel pole and critical
line, the normalized right ξ integral is uniformly bounded for `x ≥ 1`.
The infinite contour identity writes it as the left integral plus the kernel-pole
residue minus the oscillatory zero sum. Apply their three uniform bounds.
This isolates the bounded xi contribution in the principal Mellin formula. -/
theorem exists_norm_xi_rightIntegral_le (K : MellinKernel) (hRH : RiemannHypothesis) {a b : ℝ}
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -1 ≤ a) (hb' : b ≤ 1)
    (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {x : ℝ},
          1 ≤ x →
            ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    -logDeriv riemannXi (((b : ℂ) + Complex.I * t) + 1 / 2) *
                      (K.function ((b : ℂ) + Complex.I * t) *
                        (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
              C := by
  obtain ⟨A, hA, hbA⟩ := exists_norm_xi_leftIntegral_le K ha haleft ha'
  obtain ⟨B, hB, hbB⟩ := exists_norm_xi_poleResidue_le K
  obtain ⟨C, hC, hbC⟩ := exists_norm_tsum_zetaOscillatingZeroTerm_le K hRH
  refine ⟨A + B + C, add_pos (add_pos hA hB) hC, ?_⟩
  intro x hx
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let R :=
    ∫ t : ℝ,
      -logDeriv riemannXi (((b : ℂ) + Complex.I * t) + 1 / 2) *
        (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t))
  let L :=
    ∫ t : ℝ,
      -logDeriv riemannXi (((a : ℂ) + Complex.I * t) + 1 / 2) *
        (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t))
  let P := weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x (-1 / 2)
  let Z := ∑' ρ, K.zetaOscillatingZeroTerm x ρ
  have he : Complex.I * (R - L) = 2 * Real.pi * Complex.I * (P - Z) := by
    simpa only [R, L, P, Z, mul_comm Complex.I] using
      xiContourIdentity K hRH ha hb ha' hb' haleft hbright hx
  have hi : Complex.I * (R - L) = Complex.I * (2 * (Real.pi : ℂ) * (P - Z)) := by
    rw [he]
    ring
  have hdif := mul_left_cancel₀ Complex.I_ne_zero hi
  have hd : d * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp only [d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  have hR : d * R = d * L + P - Z := by
    rw [eq_add_of_sub_eq hdif, mul_add, ← mul_assoc, hd, one_mul]
    ring
  change ‖d * R‖ ≤ A + B + C
  rw [hR]
  exact
    (norm_sub_le (d * L + P) Z).trans
      (add_le_add ((norm_add_le (d * L) P).trans (add_le_add (hbA hx) (hbB hx)))
        (hbC (zero_lt_one.trans_le hx)))

end PseudoPrime.LLS.PaperStatements.MellinKernel
