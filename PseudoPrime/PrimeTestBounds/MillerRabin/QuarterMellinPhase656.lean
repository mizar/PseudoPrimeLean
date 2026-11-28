/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhasePairs656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowPhase

/-! # Critical-line Mellin coefficient in section 132 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The six logarithmic moments at a positive endpoint y form the
polynomial in inverse powers of the effective exponent s. -/
noncomputable def quarterMoment656 (s : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ s *
    ∑ j ∈ Finset.range 6,
      (((5 : ℕ).choose j : ℂ) * ((21 / 8 - Real.log y : ℝ) : ℂ) ^ (5 - j)) *
        ((j.factorial : ℂ) / s ^ (j + 1))

/-- At the exponential endpoint the logarithmic shift vanishes and only
the highest inverse power contributes to the full-support Mellin moment. -/
theorem quarter_moment_support_656 (s : ℂ) :
    quarterMoment656 s (Real.exp (21 / 8)) = (Real.exp (21 / 8) : ℂ) ^ s * (120 / s ^ 6) := by
  unfold quarterMoment656
  norm_num only [Real.log_exp, sub_self, Complex.ofReal_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceSub, Nat.reduceAdd, zero_pow, pow_zero, Nat.factorial,
    Nat.choose_self, Nat.cast_one, Nat.cast_ofNat, zero_mul, mul_zero, one_mul, zero_add,
    Nat.reduceMul]

/-- The radius-independent coefficient multiplying the critical-line
cutoff phase. The two full moments and the upper boundary enter together. -/
noncomputable def quarterMellinPhase656 (ρ : ℂ) : ℂ :=
  let s := ρ + (3 / 5 : ℂ)
  let C := ((11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120 : ℝ)
  4 * (quarterWeight656 1 1 : ℂ) / ρ -
    (C : ℂ) * (4 * quarterMoment656 s 1 - quarterMoment656 s (Real.exp (21 / 8)))

private theorem rational_phase_identity {w s : ℂ} (hw : w ≠ 0) (hs : s ≠ 0) (he : s = w + 3 / 5) :
    (21 / 8 : ℂ) ^ 5 / w - quarterMoment656 s 1 =
      ∑ j ∈ Finset.range 6, (quarterPhaseCoeff656 j : ℂ) / (w * s ^ (j + 1)) := by
  unfold quarterMoment656 quarterPhaseCoeff656
  norm_num only [Complex.ofReal_one, Complex.one_cpow, one_mul, Real.log_one, sub_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
    ite_true, ite_false, Nat.choose, Nat.factorial, Nat.reduceMul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, zero_add, add_zero, zero_mul, mul_zero, pow_zero, pow_one, mul_one,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat, Complex.ofReal_zero, Complex.ofReal_one]
  field_simp [hw, hs]
  rw [he]
  ring

private theorem support_phase_identity (t : ℝ) :
    (Real.exp (21 / 8) : ℂ) ^ ((11 / 10 : ℂ) + Complex.I * t) =
      (Real.exp ((11 / 10) * (21 / 8)) : ℂ) * Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)), ←
    Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- On the critical line, the exact Mellin phase coefficient equals the
kernel used by the certified four-interval lower bounds. The rational
parts share the derivative coefficients and the support term gives the
shift by `21/8`. -/
theorem quarter_mellin_phase_eq_656 (t : ℝ) :
    quarterMellinPhase656 ((1 / 2 : ℂ) + Complex.I * t) = quarterPhaseKernel656 t := by
  let w : ℂ := 1 / 2 + Complex.I * t
  let s : ℂ := 11 / 10 + Complex.I * t
  let C : ℝ := (11 / 10) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120
  have hws : s = w + 3 / 5 := by
    dsimp only [s, w]; ring
  have hw : w ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num only [w, Complex.add_re, Complex.div_ofNat_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re,
      Complex.one_re, ← Complex.ofReal_ofNat, Complex.ofReal_re] at h'
  have hs : s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num only [s, Complex.add_re, Complex.div_ofNat_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re,
      Complex.one_re, ← Complex.ofReal_ofNat, Complex.ofReal_re] at h'
    rw [← Complex.ofReal_ofNat (n := 11), Complex.ofReal_re] at h'
    norm_num only at h'
  have hu : quarterWeight656 1 1 = C * (21 / 8) ^ 5 := by
    unfold quarterWeight656
    simp only [div_self one_ne_zero, Real.sqrt_one, Real.log_one, sub_zero, one_mul]
    dsimp only [C]
    ring_nf
  have hS :
    (C : ℂ) * quarterMoment656 s (Real.exp (21 / 8)) =
      (11 / 10 : ℂ) ^ 5 * Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ)) / s ^ 6 := by
    rw [quarter_moment_support_656, show s = _ from rfl, support_phase_identity]
    dsimp only [C]
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_neg, Complex.ofReal_ofNat, neg_mul]
    let z : ℂ := (11 / 10) * (21 / 8)
    have hz : Complex.exp (-z) * Complex.exp z = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    change
      (11 / 10 : ℂ) ^ 5 * Complex.exp (-z) / 120 * (Complex.exp z * Complex.exp _ * (120 / s ^ 6)) =
        _
    calc
      _ =
          (Complex.exp (-z) * Complex.exp z) *
            ((11 / 10 : ℂ) ^ 5 * Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ)) / s ^ 6) :=
        by
        simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
        ring
      _ = _ := by
        rw [hz, one_mul]
        simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  unfold quarterMellinPhase656 quarterPhaseKernel656
  dsimp only
  rw [mul_comm (21 / 8 : ℝ) (11 / 10), ← neg_mul]
  change
    4 * (quarterWeight656 1 1 : ℂ) / w -
        (C : ℂ) *
          (4 * quarterMoment656 (w + 3 / 5) 1 - quarterMoment656 (w + 3 / 5) (Real.exp (21 / 8))) =
      ((4 * C : ℝ) : ℂ) * (∑ j ∈ Finset.range 6, (quarterPhaseCoeff656 j : ℂ) / (w * s ^ (j + 1))) +
        (11 / 10 : ℂ) ^ 5 * Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ)) / s ^ 6
  rw [← hws, hu, mul_sub, sub_sub_eq_add_sub, hS]
  rw [← rational_phase_identity hw hs hws]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- On the critical line, the normalized cutoff power times the Mellin
coefficient is exactly the oscillating summand used by the phase bounds. -/
theorem quarter_mellin_cutoff_phase_656 {r : ℝ} (hr : 0 < r) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    (((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * quarterMellinPhase656 ρ =
      Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel656 ρ.im := by
  have hρ' : ρ = (1 / 2 : ℂ) + Complex.I * ρ.im := by
    apply Complex.ext <;>
      simp only [hρ, Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
        Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_add,
        add_zero, zero_div]
  have hK := quarter_mellin_phase_eq_656 ρ.im
  rw [← hρ'] at hK
  have he :
    ((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ) =
      Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) := by
    conv_lhs => rw [hρ']
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_comm] using
      quarter_cutoff_phase_exp (t := ρ.im) hr
  rw [he, hK]

/-- Under RH, the normalized Mellin zero sum at every complete height
truncation has the certified section 132 lower bound after the scalar allowance. -/
theorem quarter_mellin_truncations_656 (hRH : RiemannHypothesis) {r T : ℝ}
    (hr : r ∈ Set.Icc 322 328) (hT : 100 ≤ T) :
    -(201 / 40000 : ℝ) ≤
      (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ((((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ)) * quarterMellinPhase656 ρ).re) -
        quarterPhaseRem656 r := by
  have h := quarter_phase_with_rem_656 hRH hr hT
  apply h.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hzero :=
    (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo
          (show 0 ≤ T from (by norm_num only : (0 : ℝ) ≤ 100).trans hT)).mp
      hρ
  have hxi := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hzero.1 hzero.2.1
  rw [quarter_mellin_cutoff_phase_656 ((by norm_num only : (0 : ℝ) < 322).trans_le hr.1)
      (AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi)]

end PseudoPrime.PrimeTestBounds.MillerRabin
