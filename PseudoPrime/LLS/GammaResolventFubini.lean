/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaResolventLaplace
public import PseudoPrime.LLS.GammaCentralDigammaSeries
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Absolute integrability for the Gamma resolvent Laplace representation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For any real parameters, the Laplace phase has norm one. The norm of
the product therefore separates into an exponential decay and the Gamma weight.
This identity is the domination used for the product-measure integral. -/
theorem norm_central_resolvent_laplace_mul_weight (c x r t : ℝ) :
    ‖Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) * gammaCentralMellinWeight x t‖ =
      Real.exp (-c * r) * ‖gammaCentralMellinWeight x t‖ := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, zero_div, add_zero]

/-- Positive decay and a positive Mellin scale make the actual two-variable
Gamma-Laplace integrand absolutely integrable on the product measure.
The proof uses the separated norm identity and the two one-variable integrals.
This discharges the Fubini premise without assuming it as an extra hypothesis. -/
theorem integrable_central_resolvent_laplace_mul_weight {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦
        Complex.exp (-((c : ℂ) + Complex.I * (p.2 : ℂ) / 2) * (p.1 : ℂ)) *
          gammaCentralMellinWeight x p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod MeasureTheory.volume) := by
  have hC :
    Continuous (fun p : ℝ × ℝ ↦ Complex.exp (-((c : ℂ) + Complex.I * (p.2 : ℂ) / 2) * (p.1 : ℂ))) :=
    ((continuous_const.add
            ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)).div_const
              (2 : ℂ))).neg.mul
        (Complex.continuous_ofReal.comp continuous_fst)).cexp
  have hW : Continuous (fun p : ℝ × ℝ ↦ gammaCentralMellinWeight x p.2) :=
    (continuous_gammaCentralMellinWeight hx).comp continuous_snd
  apply (MeasureTheory.integrable_norm_iff (hC.mul hW).aestronglyMeasurable).mp
  have hR := integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) (0 : ℝ)
  have hT := (integrable_gammaCentralMellinWeight hx).norm
  exact
    (hR.mul_prod hT).congr
      (MeasureTheory.ae_of_all _
        (fun p ↦ (norm_central_resolvent_laplace_mul_weight c x p.1 p.2).symm))

/-- For positive decay and Mellin scale, substitute the proved Laplace
representation and exchange the actual Gamma integral with the half-line integral.
All absolute-integrability conditions follow from the preceding theorem.
This identity is the input to evaluating the inner Mellin integral. -/
theorem gamma_central_resolvent_integral_eq_laplace {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (∫ t : ℝ, (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t) =
      ∫ r : ℝ in Set.Ioi 0,
        ∫ t : ℝ,
          Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
            gammaCentralMellinWeight x t := by
  calc
    _ =
        ∫ t : ℝ,
          ∫ r : ℝ in Set.Ioi 0,
            Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
              gammaCentralMellinWeight x t :=
      by
      apply MeasureTheory.integral_congr_ae
      exact
        MeasureTheory.ae_of_all _
          (fun t ↦ by
            dsimp only
            rw [central_resolvent_eq_laplace hc t, MeasureTheory.integral_mul_const])
    _ = _ :=
      (MeasureTheory.integral_integral_swap
          (integrable_central_resolvent_laplace_mul_weight hc hx)).symm

/-- The Laplace phase changes the positive Mellin scale by exp(-r/2),
while its real decay remains exp(-c r). The identity holds at every real height
and prepares the inner integral for the certified Gamma inverse Mellin formula. -/
theorem central_resolvent_laplace_mul_weight_eq_shift {x : ℝ} (hx : 0 < x) (c r t : ℝ) :
    Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) * gammaCentralMellinWeight x t =
      (Real.exp (-c * r) : ℂ) * gammaCentralMellinWeight (x * Real.exp (-r / 2)) t := by
  have hs : 0 < x * Real.exp (-r / 2) := mul_pos hx (Real.exp_pos _)
  unfold gammaCentralMellinWeight
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne'), ← Complex.ofReal_log hx.le, ←
    Complex.ofReal_log hs.le, Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp]
  simp only [Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  have he :
    -((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ) + (Real.log x : ℂ) * (Complex.I * (t : ℂ)) =
      -(c : ℂ) * (r : ℂ) + ((Real.log x : ℂ) + -(r : ℂ) / 2) * (Complex.I * (t : ℂ)) := by
    ring
  calc
    _ =
        gammaMellinKernel.function (Complex.I * (t : ℂ)) *
          (Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
            Complex.exp ((Real.log x : ℂ) * (Complex.I * (t : ℂ)))) :=
      by ring
    _ = _ := by
      rw [← Complex.exp_add, he, Complex.exp_add]; ring

/-- At a positive Mellin scale, the normalized inner Gamma-Laplace integral
equals a real exponential decay times the certified shifted Gamma density.
No GRH assumption enters this inverse Mellin evaluation.
The result gives the scalar integrand for the archimedean resolvent terms. -/
theorem gamma_central_laplace_inner_integral_eq_density {x : ℝ} (hx : 0 < x) (c r : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
            gammaCentralMellinWeight x t) =
      ((Real.exp (-c * r) * Real.sqrt ((x * Real.exp (-r / 2))⁻¹) *
            Real.exp (-(x * Real.exp (-r / 2))⁻¹) :
          ℝ) :
        ℂ) := by
  have hI :
    (∫ t : ℝ,
        Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
          gammaCentralMellinWeight x t) =
      (Real.exp (-c * r) : ℂ) * (∫ t : ℝ, gammaCentralMellinWeight (x * Real.exp (-r / 2)) t) := by
    rw [← MeasureTheory.integral_const_mul]
    exact
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_of_all _ (fun t ↦ central_resolvent_laplace_mul_weight_eq_shift hx c r t))
  rw [hI, mul_left_comm, gamma_central_kernel_integral_eq_density (mul_pos hx (Real.exp_pos _))]
  simp only [Complex.ofReal_mul, mul_assoc]

/-- The normalized Gamma resolvent integral has an exact scalar half-line
representation at every positive decay parameter and positive Mellin scale.
The proof combines absolute Fubini exchange with the evaluated inner integral.
This is the scalar representation needed for the signed archimedean series. -/
theorem gamma_central_resolvent_integral_eq_scalar {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / ((c : ℂ) + Complex.I * (t : ℂ) / 2)) * gammaCentralMellinWeight x t) =
      ∫ r : ℝ in Set.Ioi 0,
        ((Real.exp (-c * r) * Real.sqrt ((x * Real.exp (-r / 2))⁻¹) *
              Real.exp (-(x * Real.exp (-r / 2))⁻¹) :
            ℝ) :
          ℂ) := by
  rw [gamma_central_resolvent_integral_eq_laplace hc hx, ← MeasureTheory.integral_const_mul]
  exact
    MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_of_all _ (fun r ↦ gamma_central_laplace_inner_integral_eq_density hx c r))

end PseudoPrime.LLS.PaperStatements
