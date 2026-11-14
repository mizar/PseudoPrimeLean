/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Jensen
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.EulerLog
import PseudoPrime.Analysis.ExponentialAbsoluteIntegral
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Exponential decay of the zeta Dirichlet tail -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For x at least two and exponent at least two, an inverse power is
bounded by a telescoping reciprocal times a decaying power of two.
This pointwise comparison supports the zeta tail estimate. -/
theorem inverse_rpow_le_telescoping {x σ : ℝ} (hx : 2 ≤ x) (hσ : 2 ≤ σ) :
    x ^ (-σ) ≤ (2 : ℝ) ^ (2 - σ) / (x * (x - 1)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 0 < x - 1 := by linarith only [hx]
  have hpow :=
    Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 2 by norm_num only) hx
      (show 2 - σ ≤ 0 by linarith only [hσ])
  have he : x ^ (-σ) = x ^ (2 - σ) / x ^ 2 := by
    have h := Real.rpow_add hx0 (-σ) 2
    rw [Real.rpow_two] at h
    have h2 : -σ + 2 = 2 - σ := by ring
    rw [h2] at h
    exact (eq_div_iff (ne_of_gt (sq_pos_of_pos hx0))).2 h.symm
  rw [he]
  have hstep := div_le_div_of_nonneg_right hpow (sq_nonneg x)
  have hden : x * (x - 1) ≤ x ^ 2 := by nlinarith only [hx]
  have hpos : 0 ≤ (2 : ℝ) ^ (2 - σ) := Real.rpow_nonneg (by norm_num only) _
  have hstep2 := div_le_div_of_nonneg_left hpos (mul_pos hx0 hx1) hden
  exact hstep.trans hstep2

/-- For real part at least two, the zeta Dirichlet tail decays as
`2 ^ (2 - re s)`. Bound each term by a telescoping reciprocal and sum;
the estimate holds uniformly at every complex height. -/
theorem norm_zeta_sub_one_decay {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ (2 : ℝ) ^ (2 - s.re) := by
  have hs1 : 1 < s.re := by linarith only [hs]
  have hsumm1 : Summable (fun n : ℕ ↦ (1 : ℂ) / (n + 1 : ℂ) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs1)
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using h
  have heq : riemannZeta s - 1 = ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 2) ^ s := by
    have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
    rw [hz, hsumm1.tsum_eq_zero_add]
    have h0 : (1 : ℂ) / (((0 : ℕ) : ℂ) + 1) ^ s = 1 := by norm_num only [Complex.one_cpow]
    rw [h0]
    have hcongr :
      (∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℕ) : ℂ) + 1) ^ s) =
        ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 2) ^ s := by
      apply tsum_congr
      intro n
      push_cast
      ring_nf
    rw [hcongr]
    ring
  have hsummR : Summable (fun n : ℕ ↦ ‖(1 : ℂ) / ((n : ℂ) + 2) ^ s‖) := by
    have h := (summable_nat_add_iff 1).mpr hsumm1
    have h2 : Summable (fun n : ℕ ↦ (1 : ℂ) / ((n : ℂ) + 2) ^ s) := by
      apply h.congr
      intro n
      push_cast
      ring_nf
    exact h2.norm
  have hsummB : Summable (fun n : ℕ ↦ (2 : ℝ) ^ (2 - s.re) * (1 / ((n + 1) * (n + 2)))) :=
    hasSum_inv_succ_mul_succ_succ.summable.mul_left _
  have hbound :
    ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, (2 : ℝ) ^ (2 - s.re) * (1 / ((n + 1) * (n + 2))) := by
    rw [heq]
    refine (norm_tsum_le_tsum_norm hsummR).trans ?_
    apply hsummR.tsum_le_tsum _ hsummB
    intro n
    rw [norm_div, norm_one]
    have hcast : ((n : ℂ) + 2) = (((n : ℝ) + 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith only [hn]
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn2, one_div, ← Real.rpow_neg hn2.le]
    have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have h := Nat.cast_nonneg (α := ℝ) n
      linarith only [h]
    have h := inverse_rpow_le_telescoping hn hs
    have he : ((n : ℝ) + 2) * ((n : ℝ) + 2 - 1) = ((n : ℝ) + 1) * ((n : ℝ) + 2) := by ring
    rw [he] at h
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, mul_one_div] using h
  rw [tsum_mul_left, tsum_inv_succ_mul_succ_succ, mul_one] at hbound
  exact hbound

/-- For a real argument at least two, the logarithm of zeta is nonnegative
and bounded by the exponentially decaying Dirichlet tail. The Euler-log
majorant supplies nonnegativity and log x ≤ x - 1 supplies the upper bound. -/
theorem log_zeta_real_le_decay {σ : ℝ} (hσ : 2 ≤ σ) :
    0 ≤ Real.log (riemannZeta (σ : ℂ)).re ∧
      Real.log (riemannZeta (σ : ℂ)).re ≤ (2 : ℝ) ^ (2 - σ) := by
  have hσ1 : 1 < σ := by linarith only [hσ]
  have hs : 1 < (σ : ℂ).re := by simpa only [Complex.ofReal_re] using hσ1
  have hz : 0 < (riemannZeta (σ : ℂ)).re := (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hσ1)).1
  have hnon := (norm_nonneg (backlundZetaLog (σ : ℂ))).trans (norm_backlundZetaLog_le hs)
  have hlog := Real.log_le_sub_one_of_pos hz
  have hdec := norm_zeta_sub_one_decay (s := (σ : ℂ)) (by simpa only [Complex.ofReal_re] using hσ)
  have hreal := Complex.re_le_norm (riemannZeta (σ : ℂ) - 1)
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hreal hdec
  constructor
  · simpa only [Complex.ofReal_re] using hnon
  · linarith only [hlog, hreal, hdec]

/-- The decaying power majorant for the horizontal offset is integrable
above 3/2. Rewriting it as a constant times an exponential gives an
integrable negative exponential on the half-line. -/
theorem integrable_zeta_decay :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ (2 : ℝ) ^ (3 / 2 - u)) (Set.Ioi (3 / 2 : ℝ)) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hi :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hl) (3 / 2)).const_mul
      (Real.exp (Real.log 2 * (3 / 2)))
  have he :
    (fun u : ℝ ↦ (2 : ℝ) ^ (3 / 2 - u)) =
      (fun u : ℝ ↦ Real.exp (Real.log 2 * (3 / 2)) * Real.exp (-Real.log 2 * u)) := by
    funext u
    rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 2), ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact hi

/-- The integral of the decaying power majorant above 3/2 equals the
reciprocal of log 2. The exponential integral is evaluated exactly. -/
theorem integral_zeta_decay :
    (∫ u in Set.Ioi (3 / 2 : ℝ), (2 : ℝ) ^ (3 / 2 - u)) = (Real.log 2)⁻¹ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have he :
    (fun u : ℝ ↦ (2 : ℝ) ^ (3 / 2 - u)) =
      (fun u : ℝ ↦ Real.exp (Real.log 2 * (3 / 2)) * Real.exp (-Real.log 2 * u)) := by
    funext u
    rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 2), ← Real.exp_add]
    congr 1
    ring
  rw [he, MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hl)]
  have hc : Real.exp (Real.log 2 * (3 / 2)) * Real.exp (-Real.log 2 * (3 / 2)) = 1 := by
    rw [← Real.exp_add]
    have h : Real.log 2 * (3 / 2) + -Real.log 2 * (3 / 2) = 0 := by ring
    rw [h, Real.exp_zero]
  rw [neg_div_neg_eq, ← mul_div_assoc, hc, one_div]

/-- The real-axis zeta logarithm on the horizontal tail is integrable.
Its continuity follows from zeta nonvanishing for real part greater than
one, and the decaying power bounds its norm. -/
theorem integrable_log_zeta_real_tail :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.log (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re)
      (Set.Ioi (3 / 2 : ℝ)) := by
  have hc :
    ContinuousOn (fun u : ℝ ↦ Real.log (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re)
      (Set.Ioi (3 / 2 : ℝ)) := by
    intro u hu
    change (3 / 2 : ℝ) < u at hu
    have hσ : 1 < 1 / 2 + u := by linarith only [hu]
    have hs : (((1 / 2 + u : ℝ) : ℂ)) ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.one_re] at hr
      linarith only [hσ, hr]
    have hp : 0 < (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re :=
      (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hσ)).1
    have hlin : ContinuousAt (fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ))) u :=
      (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).continuousAt
    have hf : ContinuousAt (fun v : ℝ ↦ riemannZeta (((1 / 2 + v : ℝ) : ℂ))) u :=
      ContinuousAt.comp (f := fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ)))
        (differentiableAt_riemannZeta hs).continuousAt hlin
    exact ((Complex.continuous_re.continuousAt.comp hf).log hp.ne').continuousWithinAt
  apply integrable_zeta_decay.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  change (3 / 2 : ℝ) < u at hu
  have hσ : 2 ≤ 1 / 2 + u := by linarith only [hu]
  have h := log_zeta_real_le_decay hσ
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  have he : (2 : ℝ) - (1 / 2 + u) = 3 / 2 - u := by ring
  rw [he] at h
  exact h.2

/-- The real-axis zeta logarithm has tail integral at most two. Its
exponential majorant integrates to 1/log 2, which is below two. -/
theorem integral_log_zeta_real_tail_le_two :
    (∫ u in Set.Ioi (3 / 2 : ℝ), Real.log (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re) ≤ 2 := by
  have h :=
    MeasureTheory.integral_mono_ae integrable_log_zeta_real_tail integrable_zeta_decay
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
        change (3 / 2 : ℝ) < u at hu
        have hσ : 2 ≤ 1 / 2 + u := by linarith only [hu]
        have hv := (log_zeta_real_le_decay hσ).2
        have he : (2 : ℝ) - (1 / 2 + u) = 3 / 2 - u := by ring
        rwa [he] at hv)
  rw [integral_zeta_decay] at h
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hi : (Real.log 2)⁻¹ ≤ 2 := by
    have hrec := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hl
    norm_num only [one_div, inv_div, inv_one] at hrec
    exact hrec
  exact h.trans hi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
