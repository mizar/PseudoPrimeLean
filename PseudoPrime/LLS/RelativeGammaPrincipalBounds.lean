/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeChebyshevLowerBounds
public import PseudoPrime.LLS.GammaTruncatedBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.AffineChebyshevSmoothing

/-! # Relative-loss principal Gamma cutoff bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH, any relative width in (0,1/2] gives a finite Gamma cutoff lower
bound with relative main loss h, constant error 1/(10h), and inverse-square-root
error. Apply the global Chebyshev envelope before Abel smoothing and normalize
by sqrt(x). This supplies a lower input without a growing quarter-power error. -/
theorem gamma_level_one_sum_lower_relative (hRH : RiemannHypothesis) {h x lambda : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hx : 0 < x) (hl : 0 ≤ lambda) :
    (1 - h) * Real.sqrt x * (1 - Real.exp (-lambda)) - 1 / (10 * h) -
        (21 / (10 * h) + 1839 / 1000) / Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊lambda * x⌋₊,
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have hp (t : ℝ) (ht : 0 ≤ t) :
    (1 - h) * t - (1 / (10 * h)) * Real.sqrt t - (21 / (10 * h) + 1839 / 1000) ≤
      Chebyshev.psi t := by
    have hb := LLS.psi_lower_relative_log_shift hRH hh hh1 ht
    have he : (Real.sqrt t / 10 + 21 / 10) / h = (1 / (10 * h)) * Real.sqrt t + 21 / (10 * h) := by
      field_simp [hh.ne']
    rw [he] at hb
    linarith only [hb]
  have hb :=
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum_lower_of_sqrt_psi
      (by positivity : 0 ≤ 1 / (10 * h)) hx (mul_nonneg hl hx.le) hp
  have hd := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg x)
  rw [gamma_level_one_sum_eq_exponential hx]
  have he :
    ((1 - h) * x * (1 - Real.exp (-(lambda * x) / x)) - 1 / (10 * h) * Real.sqrt x -
          (21 / (10 * h) + 1839 / 1000)) /
        Real.sqrt x =
      (1 - h) * Real.sqrt x * (1 - Real.exp (-lambda)) - 1 / (10 * h) -
        (21 / (10 * h) + 1839 / 1000) / Real.sqrt x := by
    rw [neg_div, mul_div_cancel_right₀ _ hx.ne']
    rw [sub_div, sub_div, mul_div_assoc, mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hx).ne']
    rw [show
        (1 - h) * x * ((1 - Real.exp (-lambda)) / Real.sqrt x) =
          (1 - h) * (1 - Real.exp (-lambda)) * (x / Real.sqrt x)
        by ring,
      Real.div_sqrt]
    ring
  exact he ▸ hd

end PseudoPrime.LLS.PaperStatements
