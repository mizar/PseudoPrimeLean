/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScale43
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Chebyshev error after bounding the scaled zero terms -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `L ≥ 43`, the selected dimensionless width lies in `(0, 1/2]`,
the averaging width is at least one, and the width, cutoff and logarithms
have the forms used in the normalized Chebyshev estimate. -/
theorem scale43_identities {L : ℝ} (hL : 43 ≤ L) :
    let δ := L / (Real.pi * Real.exp (L / 2))
    let h := Real.exp (L / 2) * L / Real.pi
    0 < δ ∧
      δ ≤ 1 / 2 ∧
      1 ≤ h ∧
      h = Real.exp L * δ ∧
      2 / δ = 2 * Real.pi * Real.exp (L / 2) / L ∧
      Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log L ∧
      Real.log (2 / δ) = L / 2 - Real.log L + Real.log (2 * Real.pi) := by
  dsimp only
  have hl : 0 < L := by linarith only [hL]
  have hp : 0 < Real.pi := Real.pi_pos
  have he : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hδ : 0 < L / (Real.pi * Real.exp (L / 2)) := div_pos hl (mul_pos hp he)
  have hu : L / (Real.pi * Real.exp (L / 2)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos hp he)).2
    have hh := exp_half_lower hL
    nlinarith only [hL, hh, hp, Real.pi_gt_three]
  have he1 : (1 : ℝ) ≤ Real.exp (L / 2) := by
    have hh := exp_half_lower hL
    linarith only [hh, hL]
  have hw : 1 ≤ Real.exp (L / 2) * L / Real.pi := by
    apply (le_div_iff₀ hp).2
    have hm := mul_le_mul_of_nonneg_left hL he.le
    nlinarith only [hm, he1, Real.pi_lt_four]
  have hs : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hwid : Real.exp (L / 2) * L / Real.pi = Real.exp L * (L / (Real.pi * Real.exp (L / 2))) := by
    rw [hs]
    field_simp
  have hT : 2 / (L / (Real.pi * Real.exp (L / 2))) = 2 * Real.pi * Real.exp (L / 2) / L := by
    field_simp
  have hTpi : (2 / (L / (Real.pi * Real.exp (L / 2)))) / (2 * Real.pi) = Real.exp (L / 2) / L := by
    rw [hT]
    field_simp
  have hlog1 :
    Real.log ((2 / (L / (Real.pi * Real.exp (L / 2)))) / (2 * Real.pi)) = L / 2 - Real.log L := by
    rw [hTpi, Real.log_div he.ne' hl.ne', Real.log_exp]
  have hlog2 :
    Real.log (2 / (L / (Real.pi * Real.exp (L / 2)))) =
      L / 2 - Real.log L + Real.log (2 * Real.pi) := by
    rw [hT]
    have heq : 2 * Real.pi * Real.exp (L / 2) / L = (2 * Real.pi) * (Real.exp (L / 2) / L) := by
      ring
    rw [heq, Real.log_mul (ne_of_gt (mul_pos (by norm_num only) hp)) (ne_of_gt (div_pos he hl)),
      Real.log_div he.ne' hl.ne', Real.log_exp]
    ring
  exact ⟨hδ, hu, hw, hwid, hT, hlog1, hlog2⟩

/-- Under RH and the stated Rosser-type zero-count hypothesis, bound the
Chebyshev error using linear estimates for the low- and high-zero factors.
The width is `xδ`, with `0 ≤ δ ≤ 1/2`, and the cutoff is at least 1000. -/
theorem psi_error_scaled (hRH : RiemannHypothesis) {x h T δ : ℝ} (hx0 : 0 < x) (hh : 0 < h)
    (hx : 1 < x - h) (hT : 1000 ≤ T) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) (hwidth : h = x * δ)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        (Real.sqrt x * (1 + δ / 2)) * ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
        (x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
        1 / h := by
  have hb := psi_error_of_rosser hRH hT hh hx hQ
  have hp := scale_power_bounds hx0 hδ hδ2
  rw [← hwidth] at hp
  have ht0 : 0 ≤ T := by linarith only [hT]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT])
  have hc : 0 ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1 := by
    have h :=
      div_nonneg (sq_nonneg (Real.log (T / (2 * Real.pi))))
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num only) Real.pi_pos.le)
    linarith only [h]
  have hf : 0 ≤ Real.log T / (Real.pi * T) := div_nonneg hlog (mul_nonneg Real.pi_pos.le ht0)
  have hl := mul_le_mul_of_nonneg_right hp.1 hc
  have hhpow :
    (x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ) ≤ x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ) :=
    add_le_add hp.2 le_rfl
  have hhdiv := div_le_div_of_nonneg_right hhpow hh.le
  have hhigh := mul_le_mul_of_nonneg_right hhdiv hf
  linarith only [hb, hl, hhigh]

/-- Under RH and the stated zero-count hypothesis, normalize the Chebyshev
error by `sqrt x` when the width is `xδ` and the cutoff is `2/δ`. The
inverse-width factor is retained until the cutoff is substituted. -/
theorem psi_error_normalized (hRH : RiemannHypothesis) {x h δ : ℝ} (hx0 : 0 < x) (hh : 0 < h)
    (hx : 1 < x - h) (hT : 1000 ≤ 2 / δ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hwidth : h = x * δ)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ / 2) * ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
        (1 + δ) * Real.log (2 / δ) / Real.pi +
        1 / (h * Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hxp : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have hr := Real.rpow_add hx0 (1 : ℝ) (1 / 2 : ℝ)
    convert hr using 1
    · norm_num only
    · rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hb := psi_error_scaled hRH hx0 hh hx hT hδ.le hδ2 hwidth hQ
  have hhdiv := div_le_div_of_nonneg_right hb hs.le
  have heq :
    (h / 2 + Real.log (2 * Real.pi) +
          (Real.sqrt x * (1 + δ / 2)) *
            ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
          (x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ)) / h *
            (Real.log (2 / δ) / (Real.pi * (2 / δ))) +
          1 / h) /
        Real.sqrt x =
      h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ / 2) * ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
        (1 + δ) * Real.log (2 / δ) / Real.pi +
        1 / (h * Real.sqrt x) := by
    have hxne : x ≠ 0 := hx0.ne'
    have hdne : δ ≠ 0 := hδ.ne'
    have hsne : Real.sqrt x ≠ 0 := hs.ne'
    have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [hxp, hwidth]
    field_simp
    ring
  rw [heq] at hhdiv
  exact hhdiv

/-- Under RH and the stated Rosser-type zero-count bound, the normalized
Chebyshev error satisfies the explicit logarithmic-scale estimate for
`L ≥ 43`. The last term absorbs the constant and inverse-width terms. -/
theorem psi_error_log_scale (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    let δ := L / (Real.pi * Real.exp (L / 2))
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      L / (2 * Real.pi) + (1 + δ / 2) * ((L / 2 - Real.log L) ^ 2 / (2 * Real.pi) + 1) +
        (1 + δ) * (L / 2 - Real.log L + Real.log (2 * Real.pi)) / Real.pi +
        3 / Real.exp (L / 2) := by
  dsimp only
  let δ := L / (Real.pi * Real.exp (L / 2))
  let h := Real.exp (L / 2) * L / Real.pi
  have hi := scale43_identities hL
  change
    0 < δ ∧
      δ ≤ 1 / 2 ∧
      1 ≤ h ∧
      h = Real.exp L * δ ∧
      2 / δ = 2 * Real.pi * Real.exp (L / 2) / L ∧
      Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log L ∧
      Real.log (2 / δ) = L / 2 - Real.log L + Real.log (2 * Real.pi) at hi
  obtain ⟨hd, hd2, hw1, hwid, hT, hlog1, hlog2⟩ := hi
  have hc := scale43_conditions hL
  change 0 < h ∧ 1 < Real.exp L - h ∧ 1000 ≤ 2 * Real.pi * Real.exp (L / 2) / L at hc
  have ht : 1000 ≤ 2 / δ := by
    rw [hT]; exact hc.2.2
  have hb := psi_error_normalized hRH (Real.exp_pos L) hc.1 hc.2.1 ht hd hd2 hwid hQ
  rw [hlog1, hlog2] at hb
  have he : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hs : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    have heq : Real.exp L = Real.exp (L / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos he]
  rw [hs] at hb
  have hh : h / (2 * Real.exp (L / 2)) = L / (2 * Real.pi) := by
    dsimp only [h]
    have he0 : Real.exp (L / 2) ≠ 0 := he.ne'
    have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hh] at hb
  have hconst : Real.log (2 * Real.pi) + 1 / h ≤ 3 := by
    have hinv : 1 / h ≤ 1 := (div_le_one₀ (lt_of_lt_of_le (by norm_num only) hw1)).2 hw1
    have hp := Analysis.log_two_mul_pi_lt
    norm_num only at hp
    linarith only [hinv, hp]
  have hconst' := div_le_div_of_nonneg_right hconst he.le
  have heq :
    (Real.log (2 * Real.pi) + 1 / h) / Real.exp (L / 2) =
      Real.log (2 * Real.pi) / Real.exp (L / 2) + 1 / (h * Real.exp (L / 2)) := by
    have he0 : Real.exp (L / 2) ≠ 0 := he.ne'
    have hh0 : h ≠ 0 := ne_of_gt hc.1
    field_simp
  rw [heq] at hconst'
  exact le_trans hb (by linarith only [hconst'])

/-- Under RH and the stated Rosser-type zero-count hypothesis, split the
normalized logarithmic-scale Chebyshev bound into its main expression and
the explicit exponentially small remainder. -/
theorem psi_error_main_remainder (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    let a := L / 2 - Real.log L
    let c := Real.log (2 * Real.pi)
    let δ := L / (Real.pi * Real.exp (L / 2))
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      (a ^ 2 + 2 * a + 2 * c + L) / (2 * Real.pi) + 1 +
        (δ * a ^ 2 / (4 * Real.pi) + δ / 2 + δ * (a + c) / Real.pi + 3 / Real.exp (L / 2)) := by
  dsimp only
  have h := psi_error_log_scale hRH hL hQ
  dsimp only at h
  convert h using 1
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
