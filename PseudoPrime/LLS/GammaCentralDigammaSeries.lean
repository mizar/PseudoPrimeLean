/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaKernel
public import PseudoPrime.LLS.GammaDigammaIntegralExchange
public import PseudoPrime.Analysis.GammaCentralFirstMoment

/-! # Weighted digamma exchange for the actual Gamma central kernel

Discharge measurability and first-moment conditions for every positive Mellin scale.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The actual Gamma central-line weight with its Mellin phase.
Input: real scale x and real height t.
Output: Gamma(I t+1/2) times x to the power I t.
Role: retain the exact kernel and phase during the archimedean series exchange. -/
noncomputable def gammaCentralMellinWeight (x t : ℝ) : ℂ :=
  gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)

/-- Input: positive scale and any real height.
Claim: the Mellin phase has unit norm, leaving the positive half-line Gamma norm.
Proof: evaluate the complex-power norm at real part zero.
Role: transfer central Gamma integrability to the actual weighted kernel. -/
theorem norm_gammaCentralMellinWeight {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖gammaCentralMellinWeight x t‖ = ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + Complex.I * t)‖ := by
  change ‖Complex.Gamma (Complex.I * t + 1 / 2) * (x : ℂ) ^ (Complex.I * t)‖ = _
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hr : (Complex.I * (t : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero]
  rw [hr, Real.rpow_zero, mul_one]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [add_comm (Complex.I * (t : ℂ)) (1 / 2)]

/-- Input: positive real scale.
Claim: the actual Gamma central weight is continuous.
Proof: continuity of Gamma on the positive line and the pole-free complex phase.
Role: provide measurability for the weighted digamma integral. -/
theorem continuous_gammaCentralMellinWeight {x : ℝ} (hx : 0 < x) :
    Continuous (gammaCentralMellinWeight x) := by
  have hG : Continuous (fun t : ℝ ↦ Complex.Gamma (Complex.I * t + 1 / 2)) := by
    have h := Analysis.continuous_Gamma_vertical (by norm_num only : (0 : ℝ) < 1 / 2)
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, add_comm] using h
  have hP : Continuous (fun t : ℝ ↦ (x : ℂ) ^ (Complex.I * t)) :=
    (continuous_const.mul Complex.continuous_ofReal).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  exact hG.mul hP

/-- Input: positive real scale.
Claim: the actual central Gamma weight has integrable absolute first moment.
Proof: its phase has unit norm and the positive Gamma vertical-line moment is integrable.
Role: discharge the analytic premise of the digamma series-integral exchange. -/
theorem integrable_abs_mul_norm_gammaCentralMellinWeight {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable (fun t : ℝ ↦ |t| * ‖gammaCentralMellinWeight x t‖) := by
  have h := Analysis.integrable_abs_mul_norm_Gamma_vertical (by norm_num only : (0 : ℝ) < 1 / 2)
  exact
    h.congr (MeasureTheory.ae_of_all _ (fun t ↦ by simp only [norm_gammaCentralMellinWeight hx t]))

/-- Input: positive real scale.
Claim: the central Gamma weight itself is integrable.
Proof: transfer the Gamma vertical norm integral through the unit-norm phase.
Role: permit separating the digamma baseline in the archimedean identity. -/
theorem integrable_gammaCentralMellinWeight {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable (gammaCentralMellinWeight x) := by
  apply
    (MeasureTheory.integrable_norm_iff
        (continuous_gammaCentralMellinWeight hx).aestronglyMeasurable).mp
  have h := (Analysis.integrable_Gamma_vertical (by norm_num only : (0 : ℝ) < 1 / 2)).norm
  exact
    h.congr (MeasureTheory.ae_of_all _ (fun t ↦ by simp only [norm_gammaCentralMellinWeight hx t]))

/-- Input: positive digamma base and positive Mellin scale.
Claim: the actual Gamma-weighted vertical digamma difference is the sum of the term integrals.
Proof: apply the proved weighted exchange after discharging its actual kernel conditions.
Role: series representation for the signed Gamma archimedean integral. -/
theorem gamma_central_digamma_vertical_sub_integral_eq_tsum {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    (∫ t : ℝ,
        (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
          gammaCentralMellinWeight x t) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
            gammaCentralMellinWeight x t := by
  exact
    integral_weighted_digamma_vertical_sub_eq_tsum hb (gammaCentralMellinWeight x)
      (continuous_gammaCentralMellinWeight hx).aestronglyMeasurable
      (integrable_abs_mul_norm_gammaCentralMellinWeight hx)

/-- Input: a positive Mellin scale.
Claim: the normalized actual Gamma central integral is sqrt(1/x) times exp(-1/x).
Proof: specialize the certified shifted-Gamma inverse Mellin formula.
Role: evaluate the baseline in the signed archimedean series. -/
theorem gamma_central_kernel_integral_eq_density {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, gammaCentralMellinWeight x t) =
      ((Real.sqrt (x⁻¹) * Real.exp (-x⁻¹) : ℝ) : ℂ) := by
  have hm := inverseMellin_gamma (c := 0) (u := x⁻¹) (by norm_num only) (inv_pos.mpr hx)
  unfold inverseMellin at hm
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] at hm
  exact hm

end PseudoPrime.LLS.PaperStatements
