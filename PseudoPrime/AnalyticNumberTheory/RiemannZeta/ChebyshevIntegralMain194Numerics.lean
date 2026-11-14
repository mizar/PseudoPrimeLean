/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegralMain194
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Endpoint comparison for the integrated ψ main term -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Rational logarithm certificates and a lower bound for π show that the
integrated main-term gap at 97/5 is greater than 19/2000. -/
theorem integrated_main_gap_at_194 :
    (19 / 2000 : ℝ) < leeNosalPsiLog (97 / 5) - integratedPsiMain (97 / 5) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (97 / 5) 4 64 (296527 / 100000) (296528 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hk :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck (6 / 5) 0 64 (18232 / 100000) (18233 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hk
  have ha0 : 0 ≤ (97 / 10 : ℝ) - Real.log (97 / 5) + Real.log (6 / 5) := by
    linarith only [hL.2, hk.1]
  have hau :
    (97 / 10 : ℝ) - Real.log (97 / 5) + Real.log (6 / 5) ≤
      (97 / 10 : ℝ) - 296527 / 100000 + 18233 / 100000 := by
    linarith only [hL.1, hk.2]
  have hasq := pow_le_pow_left₀ ha0 hau 2
  rw [integrated_main_gap_eq (by norm_num only : (0 : ℝ) < 97 / 5)]
  apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 8) Real.pi_pos)).2
  nlinarith only [hL.2, hk.2, hau, hasq, Real.pi_gt_d4]

/-- The integrated main-term gap exceeds 19/2000 for every L at least
97/5, by the endpoint calculation and the established monotonicity. -/
theorem integrated_main_gap_above_194 {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    (19 / 2000 : ℝ) < leeNosalPsiLog L - integratedPsiMain L := by
  have h :=
    integratedPsiMain_gap_mono.monotoneOn (Set.mem_Ici.mpr (le_rfl : (97 / 5 : ℝ) ≤ 97 / 5))
      (Set.mem_Ici.mpr hL) hL
  exact integrated_main_gap_at_194.trans_le h

/-- Above 97/5, a cubic polynomial bounds the exponential coefficient
of the integrated ψ envelope. The proof uses π ≥ 3 and elementary log bounds. -/
theorem integrated_remainder_coeff_le {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    let q := 5 * L / (6 * Real.pi)
    let a := L / 2 - Real.log (5 * L / 6)
    q * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 317 / 10000) + Real.log (2 * Real.pi) ≤
      5 * L ^ 3 / 432 - 5 * L ^ 2 / 108 + 5 * L / 54 + 2 := by
  dsimp only
  let q := 5 * L / (6 * Real.pi)
  let a := L / 2 - Real.log (5 * L / 6)
  let u := L / 2 - 2
  have hL0 : 0 < L := by linarith only [hL]
  have hlogupper : Real.log (5 * L / 6) ≤ Real.log L := by
    apply Real.log_le_log
    · exact div_pos (mul_pos (by norm_num only) hL0) (by norm_num only)
    · linarith only [hL0]
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    have hh := (log_bounds_194 hL).2
    linarith only [hh, hlogupper, hL]
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have he : (16 : ℝ) = 2 ^ 4 := by norm_num only
    rw [he, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hloglower : (2 : ℝ) ≤ Real.log (5 * L / 6) := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 16)
        (show (16 : ℝ) ≤ 5 * L / 6 by linarith only [hL])
    linarith only [h, hlog16, Real.log_two_gt_d9]
  have hau : a ≤ u := by
    dsimp only [a, u]; linarith only [hloglower]
  have hu0 : 0 ≤ u := by
    dsimp only [u]; linarith only [hL]
  have hasq := mul_le_mul hau hau ha0 hu0
  have hnum0 : 0 ≤ a ^ 2 + 2 * a + 2 := by nlinarith only [sq_nonneg a, ha0]
  have hnum : a ^ 2 + 2 * a + 2 ≤ u ^ 2 + 2 * u + 2 := by nlinarith only [hasq, hau]
  have hp3 : (3 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d4]
  have hp0 : 0 < Real.pi := Real.pi_pos
  have hcoeff : q / (2 * Real.pi) ≤ 5 * L / 108 := by
    dsimp only [q]
    have hh : (1 / Real.pi : ℝ) ≤ 1 / 3 := by
      apply (div_le_div_iff₀ hp0 (by norm_num only : (0 : ℝ) < 3)).2
      linarith only [hp3]
    have hq :=
      mul_le_mul hh hh (div_nonneg (by norm_num only) hp0.le) (by norm_num only : (0 : ℝ) ≤ 1 / 3)
    have hm := mul_le_mul_of_nonneg_left hq hL0.le
    simp only [div_eq_mul_inv, mul_inv_rev] at hm ⊢
    nlinarith only [hm]
  have hpnum : 0 ≤ u ^ 2 + 2 * u + 2 := by nlinarith only [sq_nonneg u, hu0]
  have hm := mul_le_mul hcoeff hnum hnum0 (by nlinarith only [hpnum, hL0])
  have hq0 : 0 ≤ q := div_nonneg (by nlinarith only [hL0]) (by nlinarith only [hp0])
  have hpi2 : Real.log (2 * Real.pi) ≤ 2 := by
    have h :=
      Analysis.rationalLogIntervalCheck_sound
        (show
          Analysis.rationalLogIntervalCheck (62832 / 10000) 2 64 (1837 / 1000) (1838 / 1000) = true
          from by decide +kernel)
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    have hp : (2 * Real.pi : ℝ) ≤ 62832 / 10000 := by linarith only [Real.pi_lt_d4]
    have hlog := Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) hp
    linarith only [hlog, h.2]
  change q * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 317 / 10000) + Real.log (2 * Real.pi) ≤ _
  dsimp only [u] at hm
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hm, hq0, hpi2]

/-- The exponential at 97/10 is at least 16000, by a finite Taylor sum. -/
theorem exp_97_over_10_ge_16000 : (16000 : ℝ) ≤ Real.exp (97 / 10) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 97 / 10) 30
  have hc : (16000 : ℝ) ≤ ∑ k ∈ Finset.range 30, (97 / 10 : ℝ) ^ k / k.factorial := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  exact hc.trans h

/-- Differentiate the cubic remainder majorant multiplied by exp(-L/2). -/
theorem integrated_remainder_poly_deriv {t : ℝ} :
    HasDerivAt
      (fun x : ℝ ↦ (5 * x ^ 3 / 432 - 5 * x ^ 2 / 108 + 5 * x / 54 + 2) * Real.exp (-x / 2))
      ((5 * t ^ 2 / 144 - 5 * t / 54 + 5 / 54 -
          (5 * t ^ 3 / 432 - 5 * t ^ 2 / 108 + 5 * t / 54 + 2) / 2) *
        Real.exp (-t / 2))
      t := by
  have hi := hasDerivAt_id t
  have hp1 := ((hi.pow 3).const_mul 5).div_const 432
  have hp2 := ((hi.pow 2).const_mul 5).div_const 108
  have hp3 := (hi.const_mul 5).div_const 54
  have hp := ((hp1.sub hp2).add hp3).add_const 2
  have he := (Real.hasDerivAt_exp (-t / 2)).comp t ((hi.neg).div_const 2)
  have hh := hp.mul he
  convert hh using 1
  · funext x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Pi.neg_apply,
      Function.comp_apply, id_eq]
  · simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Pi.neg_apply, Function.comp_apply, id_eq,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

/-- Above 97/5, the cubic-exponential remainder majorant is at most
443/100000. Its derivative is nonpositive and the endpoint exponential
exceeds 16000. -/
theorem integrated_remainder_poly_le {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    (5 * L ^ 3 / 432 - 5 * L ^ 2 / 108 + 5 * L / 54 + 2) * Real.exp (-L / 2) ≤ 443 / 100000 := by
  have hmono :
    AntitoneOn
      (fun x : ℝ ↦ (5 * x ^ 3 / 432 - 5 * x ^ 2 / 108 + 5 * x / 54 + 2) * Real.exp (-x / 2))
      (Set.Ici (97 / 5 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro t ht
      exact integrated_remainder_poly_deriv.continuousAt.continuousWithinAt
    · intro t ht
      exact integrated_remainder_poly_deriv.differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : (97 / 5 : ℝ) ≤ t := interior_subset ht
      rw [integrated_remainder_poly_deriv.deriv]
      have h1 : 0 ≤ t - 97 / 5 := by linarith only [ht']
      have h2 : 0 ≤ (t - 97 / 5) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ (t - 97 / 5) ^ 3 := pow_nonneg h1 _
      have hq :
        (5 * t ^ 2 / 144 - 5 * t / 54 + 5 / 54) -
            (5 * t ^ 3 / 432 - 5 * t ^ 2 / 108 + 5 * t / 54 + 2) / 2 ≤
          0 := by
        nlinarith only [h1, h2, h3]
      exact mul_nonpos_of_nonpos_of_nonneg hq (Real.exp_pos _).le
  have hm := hmono (Set.mem_Ici.mpr (le_rfl : (97 / 5 : ℝ) ≤ 97 / 5)) (Set.mem_Ici.mpr hL) hL
  have he0 : Real.exp (-(97 / 5 : ℝ) / 2) ≤ 1 / 16000 := by
    rw [show (-(97 / 5 : ℝ) / 2) = -(97 / 10) by norm_num only, Real.exp_neg, one_div]
    exact
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num only : (0 : ℝ) < 16000)).2 exp_97_over_10_ge_16000
  have hP :
    0 ≤ (5 * (97 / 5 : ℝ) ^ 3 / 432 - 5 * (97 / 5 : ℝ) ^ 2 / 108 + 5 * (97 / 5 : ℝ) / 54 + 2) := by
    norm_num only
  have hmul := mul_le_mul_of_nonneg_left he0 hP
  nlinarith only [hm, hmul]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
