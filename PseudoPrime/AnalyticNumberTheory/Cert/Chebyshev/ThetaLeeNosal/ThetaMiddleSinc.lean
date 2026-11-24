/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaMomentIntegral
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPhaseRealBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincSmoothingWidth
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevThetaPhaseCell
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPhaseDefect

/-! # Additive smoothing on the middle theta band -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- At the middle-band smoothing width the signed midpoint and certified
sinc tail jointly bound the width-scaled lower psi error. -/
theorem middlePsi_width_le (hRH : RiemannHypothesis) {L : ℝ} (hl : 35 / 2 ≤ L) (hu : L ≤ 53 / 2) :
    let x := Real.exp L
    let q := 2 * L / 7 - 2 / 3
    let d := q / Real.exp (L / 2)
    let a := x * (1 - d)
    let h := x - a
    let β := -Real.log (1 - d) / 2
    let A := L / 2 - Real.log (Real.pi * q)
    let H := RiemannZeta.lowerMidpointSum ((a + x) / 2) + 3640 * a ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24
    h * (x - Chebyshev.psi x) ≤
      h * (h / 2 + Real.log (2 * Real.pi) + H) +
        x ^ (3 / 2 : ℝ) * d *
          ((A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) - 748 / 625 + 19164 / 10 * β ^ 2) +
        1 := by
  intro x q d a h β A H
  have hd : 0 < d ∧ d ≤ 13 / 18300 := RiemannZeta.sinc_relative_width hl
  have hx : 2 < x :=
    lt_of_lt_of_le (by linarith only [Real.exp_one_gt_d9] : 2 < Real.exp 1)
      (Real.exp_le_exp.mpr (by linarith only [hl]))
  have hx0 : 0 < x := Real.exp_pos L
  have ha : 1 < a := by
    dsimp only [a]
    nlinarith only [hx,
      mul_pos (by linarith only [hx] : 0 < x) (by linarith only [hd.2] : 0 < 1 / 2 - d)]
  have hax : a < x := by
    dsimp only [a]; nlinarith only [mul_pos hx0 hd.1]
  apply RiemannZeta.psi_lower_of_finite_tail hRH ha hax
  intro U hz hr hy
  have ht := middleIntegratedTail_le hRH U hz hr hy (by linarith only [hx] : 0 < x) hl hu
  simpa only [a, d, q, β, A, neg_neg, Real.exp_log (by linarith only [hd.2] : 0 < 1 - d),
    sub_sub_cancel] using ht

/-- Dividing by the width and square root cancels the entire tail prefactor.
The half-width becomes q/2 and the explicit-formula remainder becomes 1/(q x). -/
theorem middlePsi_normalized (hRH : RiemannHypothesis) {L : ℝ} (hl : 35 / 2 ≤ L) (hu : L ≤ 53 / 2) :
    let x := Real.exp L
    let s := Real.exp (L / 2)
    let q := 2 * L / 7 - 2 / 3
    let d := q / s
    let a := x * (1 - d)
    let β := -Real.log (1 - d) / 2
    let A := L / 2 - Real.log (Real.pi * q)
    let H :=
      RiemannZeta.lowerMidpointSum ((a + x) / 2) + 3640 * a ^ (-(3 / 2 : ℝ)) * (x - a) ^ 2 / 24
    (x - Chebyshev.psi x) / s ≤
      q / 2 + (Real.log (2 * Real.pi) + H) / s +
        ((A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) - 748 / 625 + 19164 / 10 * β ^ 2) +
        1 / (q * x) := by
  intro x s q d a β A H
  have hs : 0 < s := Real.exp_pos _
  have hq : 0 < q := by
    dsimp only [q]; linarith only [hl]
  have hsq : x = s ^ 2 := by
    dsimp only [x, s]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hh : x - a = q * s := by
    dsimp only [a, d]; rw [hsq]; field_simp [hs.ne']; ring
  have hp : x ^ (3 / 2 : ℝ) * d = q * s ^ 2 := by
    dsimp only [x, s, d]
    rw [← Real.exp_mul, sq, ← Real.exp_add]
    have he : L * (3 / 2) = (L / 2 + L / 2) + L / 2 := by ring
    rw [he, Real.exp_add (L / 2 + L / 2)]
    field_simp [(Real.exp_pos (L / 2)).ne']
  let B := (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) - 748 / 625 + 19164 / 10 * β ^ 2
  have hw :
    (x - a) * (x - Chebyshev.psi x) ≤
      (x - a) * ((x - a) / 2 + Real.log (2 * Real.pi) + H) + x ^ (3 / 2 : ℝ) * d * B + 1 :=
    middlePsi_width_le hRH hl hu
  rw [hh, hp] at hw
  change _ ≤ q / 2 + (Real.log (2 * Real.pi) + H) / s + B + 1 / (q * x)
  apply (div_le_iff₀ hs).mpr
  apply le_of_mul_le_mul_left (a := q * s) _ (mul_pos hq hs)
  apply hw.trans_eq
  rw [hsq]
  field_simp [hs.ne', hq.ne']
  ring

/-- The generated phase inequality removes the signed midpoint and the quadratic
tail term from the normalized psi bound, leaving only the smoothing errors. -/
theorem middlePsi_phase_le (hRH : RiemannHypothesis) {L : ℝ} (hl : 35 / 2 ≤ L) (hu : L ≤ 53 / 2) :
    let x := Real.exp L
    let s := Real.exp (L / 2)
    let q := 2 * L / 7 - 2 / 3
    let d := q / s
    let a := x * (1 - d)
    let β := -Real.log (1 - d) / 2
    (x - Chebyshev.psi x) / s ≤
      L * (L - Real.log L) / (8 * Real.pi) - 1081 / 1000 + Real.log (2 * Real.pi) / s +
        (3640 * a ^ (-(3 / 2 : ℝ)) * (x - a) ^ 2 / 24) / s +
        19164 / 10 * β ^ 2 +
        1 / (q * x) := by
  intro x s q d a β
  have he : Real.sqrt x = s := by
    dsimp only [x, s]
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hp := phaseBand_midpoint hRH hl hu
  have hn := middlePsi_normalized hRH hl hu
  dsimp only at hp hn
  change Real.sqrt (Real.exp L) = Real.exp (L / 2) at he
  rw [he] at hp
  simp only [add_div] at hn hp
  dsimp only [x, s, q, d, a, β]
  linarith only [hp, hn]

/-- The four smoothing errors cost at most one thousandth on the whole band,
leaving 27/25 of normalized slack for the prime-power correction. -/
theorem middlePsi_le (hRH : RiemannHypothesis) {L : ℝ} (hl : 35 / 2 ≤ L) (hu : L ≤ 53 / 2) :
    (Real.exp L - Chebyshev.psi (Real.exp L)) / Real.exp (L / 2) ≤
      L * (L - Real.log L) / (8 * Real.pi) - 27 / 25 := by
  let s := Real.exp (L / 2)
  let x := Real.exp L
  let q := 2 * L / 7 - 2 / 3
  let d := q / s
  let a := x * (1 - d)
  let β := -Real.log (1 - d) / 2
  have hs : 0 < s := Real.exp_pos _
  have hx : 0 < x := Real.exp_pos _
  have hq : 4 ≤ q := by
    dsimp only [q]; linarith only [hl]
  have hd : 0 < d ∧ d ≤ 13 / 18300 := RiemannZeta.sinc_relative_width hl
  have hb : 1 / 300000 ≤ β ∧ β ≤ 1 / 1998 := RiemannZeta.sinc_beta_bounds hl hu
  have hs0 : 6000 ≤ s := by
    apply le_trans _ (Real.exp_le_exp.mpr (by linarith only [hl] : 35 / 4 ≤ L / 2))
    linarith only [RiemannZeta.exp_lower_cutoff]
  have hsq : s ^ 2 = x := by
    dsimp only [s, x]; rw [sq, ← Real.exp_add]; congr 1; ring
  have hroot : Real.sqrt x = s := by rw [← hsq, Real.sqrt_sq hs.le]
  have hk := RiemannZeta.small_width_curvature hx hd.1.le (by linarith only [hd.2] : d ≤ 1 / 1000)
  change 3640 * (x - x * d) ^ (-(3 / 2 : ℝ)) * (x - (x - x * d)) ^ 2 / 24 / Real.sqrt x ≤ _ at hk
  rw [←
    show a = x - x * d by
      dsimp only [a]; ring,
    hroot] at hk
  have he := RiemannZeta.sinc_small_errors (by linarith only [hb.1] : 0 ≤ β) hb.2 hs0
  have hlog :=
    div_le_div_of_nonneg_right
      (by linarith only [Analysis.log_two_mul_pi_lt] : Real.log (2 * Real.pi) ≤ 2) hs.le
  have hrem :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 1)
      (mul_pos (by norm_num only : (0 : ℝ) < 4) hx) (mul_le_mul_of_nonneg_right hq hx.le)
  rw [hsq] at he
  have hp := middlePsi_phase_le hRH hl hu
  change
    (x - Chebyshev.psi x) / s ≤
      _ - 1081 / 1000 + Real.log (2 * Real.pi) / s +
        (3640 * a ^ (-(3 / 2 : ℝ)) * (x - a) ^ 2 / 24) / s +
        19164 / 10 * β ^ 2 +
        1 / (q * x) at hp
  change (x - Chebyshev.psi x) / s ≤ _
  linarith only [hp, hk, he, hlog, hrem]

/-- Under RH the normalized lower theta error on the entire closed middle band
satisfies the Lee–Nosal envelope using the sinc tail and the generated phase cells. -/
theorem middleTheta_le (hRH : RiemannHypothesis) {L : ℝ} (hl : 35 / 2 ≤ L) (hu : L ≤ 53 / 2) :
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have he : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hp := middlePsi_le hRH hl hu
  rw [← he] at hp
  have h := add_le_add hp (Arithmetic.sinc_prime_power_bound hl hu)
  simpa only [← add_div, sub_add_sub_cancel, sub_add_cancel] using h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
