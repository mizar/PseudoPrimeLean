/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledRationalPhase

/-! # Rounded phase rotations on an arithmetic logarithmic grid -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Multiply rational complex pairs and round both components to the grid. -/
def rationalRotationStep (G : ℕ) (rot z : ℚ × ℚ) : ℚ × ℚ :=
  rationalComplexRound G (rationalComplexMul z rot)

/-- A rounded rotation increases the error by at most twice the rotation
error plus 2/G, provided the prior error is at most one. -/
theorem norm_rationalRotationStep_error {G : ℕ} (hG : 0 < G) (rot z : ℚ × ℚ) (r w : ℂ)
    (hr : ‖r‖ = 1) (hw : ‖w‖ = 1) {e d : ℝ} (he : ‖rationalComplexCast z - w‖ ≤ e) (he1 : e ≤ 1)
    (hd : ‖rationalComplexCast rot - r‖ ≤ d) :
    ‖rationalComplexCast (rationalRotationStep G rot z) - w * r‖ ≤ e + 2 * d + 2 / (G : ℝ) := by
  have hz : ‖rationalComplexCast z‖ ≤ 1 + e := by
    have h := norm_le_norm_sub_add (rationalComplexCast z) w
    rw [hw] at h
    linarith only [h, he]
  have hz2 : ‖rationalComplexCast z‖ ≤ 2 := by linarith only [hz, he1]
  have hround := norm_rationalComplexRound_error hG (rationalComplexMul z rot)
  rw [rationalComplexCast_mul] at hround
  have hnorm :=
    norm_add_le
      (rationalComplexCast (rationalRotationStep G rot z) -
        rationalComplexCast z * rationalComplexCast rot)
      (rationalComplexCast z * (rationalComplexCast rot - r) + (rationalComplexCast z - w) * r)
  have hsecond :=
    norm_add_le (rationalComplexCast z * (rationalComplexCast rot - r))
      ((rationalComplexCast z - w) * r)
  have hmul : ‖rationalComplexCast z * (rationalComplexCast rot - r)‖ ≤ 2 * d := by
    rw [norm_mul]
    exact mul_le_mul hz2 hd (norm_nonneg _) (by norm_num only)
  have hprev : ‖(rationalComplexCast z - w) * r‖ ≤ e := by
    rw [norm_mul, hr, mul_one]
    exact he
  have heq :
    rationalComplexCast (rationalRotationStep G rot z) - w * r =
      (rationalComplexCast (rationalRotationStep G rot z) -
          rationalComplexCast z * rationalComplexCast rot) +
        (rationalComplexCast z * (rationalComplexCast rot - r) +
          (rationalComplexCast z - w) * r) := by
    ring
  rw [heq]
  have hfirst :
    ‖rationalComplexCast (rationalRotationStep G rot z) -
          rationalComplexCast z * rationalComplexCast rot‖ ≤
      2 / (G : ℝ) :=
    hround
  linarith only [hnorm, hsecond, hmul, hprev, hfirst]

/-- Repeatedly apply the rounded rational rotation starting from a seed. -/
def rationalRotationIter (G : ℕ) (rot seed : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => seed
  | n + 1 => rationalRotationStep G rot (rationalRotationIter G rot seed n)

/-- Rounded rotations have a linear error budget when each prior budget
is at most one. -/
theorem norm_rationalRotationIter_error {G : ℕ} (hG : 0 < G) (rot seed : ℚ × ℚ) (r w : ℂ)
    (hr : ‖r‖ = 1) (hw : ‖w‖ = 1) {e d : ℝ} (he : ‖rationalComplexCast seed - w‖ ≤ e)
    (hd : ‖rationalComplexCast rot - r‖ ≤ d) {N : ℕ}
    (hsmall : ∀ j < N, e + (j : ℝ) * (2 * d + 2 / (G : ℝ)) ≤ 1) {n : ℕ} (hn : n ≤ N) :
    ‖rationalComplexCast (rationalRotationIter G rot seed n) - w * r ^ n‖ ≤
      e + (n : ℝ) * (2 * d + 2 / (G : ℝ)) := by
  induction n with
  | zero =>
    simpa only [rationalRotationIter, pow_zero, mul_one, Nat.cast_zero, zero_mul, add_zero] using he
  | succ n ih =>
    have hlt : n < N := Nat.lt_of_succ_le hn
    have hprev := ih (Nat.le_of_lt hlt)
    have hw' : ‖w * r ^ n‖ = 1 := by rw [norm_mul, norm_pow, hw, hr, one_pow, mul_one]
    have hs :=
      norm_rationalRotationStep_error hG rot (rationalRotationIter G rot seed n) r (w * r ^ n) hr
        hw' hprev (hsmall n hlt) hd
    rw [rationalRotationIter, pow_succ, ← mul_assoc]
    have heq :
      e + ((n + 1 : ℕ) : ℝ) * (2 * d + 2 / (G : ℝ)) =
        (e + (n : ℝ) * (2 * d + 2 / (G : ℝ))) + 2 * d + 2 / (G : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [heq]
    exact hs

/-- Generate a rational approximation at a log grid node by repeated rounded phase rotations. -/
def rationalPhaseRotation (G : ℕ) (q A : ℚ) (p k n : ℕ) : ℚ × ℚ :=
  rationalRotationIter G (rationalScaledPhase G (q / 250) p k) (rationalScaledPhase G (A * q) p k) n

/-- Seed and rotation errors imply a linear error bound for each node
in the rational logarithmic grid. -/
theorem norm_rationalPhaseRotation_error {G : ℕ} (hG : 0 < G) (q A : ℚ) (p k : ℕ) {e d : ℝ}
    (he :
      ‖rationalComplexCast (rationalScaledPhase G (A * q) p k) -
            Complex.exp (Complex.I * ((A * q : ℚ) : ℂ))‖ ≤
        e)
    (hd :
      ‖rationalComplexCast (rationalScaledPhase G (q / 250) p k) -
            Complex.exp (Complex.I * ((q / 250 : ℚ) : ℂ))‖ ≤
        d)
    {N : ℕ} (hsmall : ∀ j < N, e + (j : ℝ) * (2 * d + 2 / (G : ℝ)) ≤ 1) {n : ℕ} (hn : n ≤ N) :
    ‖rationalComplexCast (rationalPhaseRotation G q A p k n) -
          Complex.exp (Complex.I * ((A : ℂ) + (n : ℂ) / 250) * (q : ℂ))‖ ≤
      e + (n : ℝ) * (2 * d + 2 / (G : ℝ)) := by
  have h :=
    norm_rationalRotationIter_error hG (rationalScaledPhase G (q / 250) p k)
      (rationalScaledPhase G (A * q) p k) (Complex.exp (Complex.I * ((q / 250 : ℚ) : ℂ)))
      (Complex.exp (Complex.I * ((A * q : ℚ) : ℂ)))
      (by rw [← Complex.ofReal_ratCast, Complex.norm_exp_I_mul_ofReal])
      (by rw [← Complex.ofReal_ratCast, Complex.norm_exp_I_mul_ofReal]) he hd hsmall hn
  have heq :
    Complex.exp (Complex.I * ((A * q : ℚ) : ℂ)) *
        Complex.exp (Complex.I * ((q / 250 : ℚ) : ℂ)) ^ n =
      Complex.exp (Complex.I * ((A : ℂ) + (n : ℂ) / 250) * (q : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
    ring
  rw [heq] at h
  exact h

/-- For phase magnitude at most 2100, the 10^20 grid, 24 Taylor terms,
and 12 squarings have the stated explicit error. -/
theorem norm_scaled_phase_grid20_error (v : ℚ) (hv : |(v : ℝ)| ≤ 2100) :
    ‖Complex.exp (Complex.I * (v : ℂ)) -
          rationalComplexCast (rationalScaledPhase (10 ^ 20) v 24 12)‖ ≤
      (2125763 / 100000000000000000000 : ℝ) := by
  have hred : |((v / (2 : ℚ) ^ 12 : ℚ) : ℝ)| ≤ 3 / 5 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hv]
  have hp := pow_le_pow_left₀ (abs_nonneg ((v / (2 : ℚ) ^ 12 : ℚ) : ℝ)) hred 24
  have h :=
    norm_scaled_phase_error (by norm_num only : 0 < 10 ^ 20) v 24 12
      (by
        norm_num only; linarith only [hred])
      (by
        norm_num only [Nat.factorial] at hp ⊢; nlinarith only [hp])
      (by
        intro j hj
        interval_cases j <;>
          norm_num only [roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
            Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast])
  norm_num only [roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_natCast] at h
  exact h

/-- For ordinates at most 100 and starting log height at most 21,
up to 1600 rounded rotations have error at most 10^-8. -/
theorem norm_rationalPhaseRotation20_error (q A : ℚ) (hq : |(q : ℝ)| ≤ 100) (hA : |(A : ℝ)| ≤ 21)
    {n : ℕ} (hn : n ≤ 1600) :
    ‖rationalComplexCast (rationalPhaseRotation (10 ^ 20) q A 24 12 n) -
          Complex.exp (Complex.I * ((A : ℂ) + (n : ℂ) / 250) * (q : ℂ))‖ ≤
      (1 / 100000000 : ℝ) := by
  have hprod : |((A * q : ℚ) : ℝ)| ≤ 2100 := by
    rw [Rat.cast_mul, abs_mul]
    have h := mul_le_mul hA hq (abs_nonneg (q : ℝ)) (by norm_num only : (0 : ℝ) ≤ 21)
    norm_num only at h
    exact h
  have hrot : |((q / 250 : ℚ) : ℝ)| ≤ 2100 := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hq]
  have hseed := norm_scaled_phase_grid20_error (A * q) hprod
  have hstep := norm_scaled_phase_grid20_error (q / 250) hrot
  rw [norm_sub_rev] at hseed hstep
  have hn' : (n : ℝ) ≤ 1600 := by exact (Nat.cast_le).2 hn
  have h :=
    norm_rationalPhaseRotation_error (by norm_num only : 0 < 10 ^ 20) q A 24 12 hseed hstep (N :=
      1600)
      (by
        intro j hj
        have hj' : (j : ℝ) ≤ 1600 := by exact (Nat.cast_le).2 (Nat.le_of_lt hj)
        norm_num only
        nlinarith only [hj'])
      hn
  norm_num only at h
  have hb :
    (2125763 / 100000000000000000000 : ℝ) +
        (n : ℝ) * (2 * (2125763 / 100000000000000000000 : ℝ) + 2 / 100000000000000000000) ≤
      1 / 100000000 := by
    norm_num only
    nlinarith only [hn']
  norm_num only at hb
  exact h.trans hb

end PseudoPrime.Analysis
