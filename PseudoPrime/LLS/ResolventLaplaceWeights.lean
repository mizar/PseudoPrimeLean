/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaResolventFubini

/-! # Kernel-independent Laplace and Fubini representation of vertical resolvents -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The norm of a Laplace factor times any complex value separates into real exponential
decay and the value norm. Compute the real exponent explicitly.
This identity provides product-measure domination independently of the Mellin kernel. -/
theorem norm_resolvent_laplace_mul (c r t : ℝ) (z : ℂ) :
    ‖Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) * z‖ =
      Real.exp (-c * r) * ‖z‖ := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, zero_div, add_zero]

/-- For c>0 and any continuous integrable complex weight W, the resolvent Laplace product
is integrable on the positive half-line times the real line. Its norm separates into
two integrable factors. This discharges Fubini without a kernel-specific decay premise. -/
theorem integrable_resolvent_laplace_mul_weight {c : ℝ} (hc : 0 < c) (W : ℝ → ℂ) (hW : Continuous W)
    (hiW : MeasureTheory.Integrable W) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦ Complex.exp (-((c : ℂ) + Complex.I * (p.2 : ℂ) / 2) * (p.1 : ℂ)) * W p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod MeasureTheory.volume) := by
  have hC :
    Continuous (fun p : ℝ × ℝ ↦ Complex.exp (-((c : ℂ) + Complex.I * (p.2 : ℂ) / 2) * (p.1 : ℂ))) :=
    ((continuous_const.add
            ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)).div_const
              (2 : ℂ))).neg.mul
        (Complex.continuous_ofReal.comp continuous_fst)).cexp
  apply
    (MeasureTheory.integrable_norm_iff (hC.mul (hW.comp continuous_snd)).aestronglyMeasurable).mp
  have hR := integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) (0 : ℝ)
  exact
    (hR.mul_prod hiW.norm).congr
      (MeasureTheory.ae_of_all _ (fun p ↦ (norm_resolvent_laplace_mul c p.1 p.2 (W p.2)).symm))

/-- For c>0 and any continuous integrable weight, its reciprocal-factor integral equals
the iterated Laplace integral. Substitute the half-line resolvent representation and
apply absolute Fubini. This remains valid when poles in a rational weight coincide. -/
theorem resolvent_integral_eq_laplace_weight {c : ℝ} (hc : 0 < c) (W : ℝ → ℂ) (hW : Continuous W)
    (hiW : MeasureTheory.Integrable W) :
    (∫ t : ℝ, (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * W t) =
      ∫ r : ℝ in Set.Ioi 0,
        ∫ t : ℝ, Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) * W t := by
  calc
    _ =
        ∫ t : ℝ,
          ∫ r : ℝ in Set.Ioi 0,
            Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) * W t :=
      by
      apply MeasureTheory.integral_congr_ae
      exact
        MeasureTheory.ae_of_all _
          (fun t ↦ by
            dsimp only
            rw [central_resolvent_eq_laplace hc t, MeasureTheory.integral_mul_const])
    _ = _ :=
      (MeasureTheory.integral_integral_swap
          (integrable_resolvent_laplace_mul_weight hc W hW hiW)).symm

end PseudoPrime.LLS.PaperStatements
