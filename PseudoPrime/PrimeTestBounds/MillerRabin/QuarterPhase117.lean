/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeShiftMain117
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeShiftEuler117
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeShiftReflected117
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Phase lower bound with the section 117 residual -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem three_shift_g_eq {s : ℝ} (hs : 0 ≤ s) :
    threeShiftG s = 4 * twoShiftSymmetricProfile (Real.exp s)⁻¹ := by
  rw [twoShift_conductor_profile hs]
  unfold threeShiftG
  rw [neg_mul]
  ring

/-- Finite remainder after extracting the linear gain from the three-frequency
phase comparison. It keeps the signed conductor and pole terms and both Euler costs. -/
noncomputable def threeShiftRemainder117 (r : ℝ) : ℝ :=
  let X := r ^ 2
  let x := 2 * Real.log r
  let B := fun s : ℝ ↦ -6 * ((51 / 50 : ℝ) ^ 5 / ((51 / 50) ^ 2 - 1 / 4) ^ 3) * Real.cosh (s / 2)
  (3.143 * B (14 / 5) + (-3.124) * B (141 / 50) + (-0.0374) * B (39 / 10) +
          (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2)) * B 0 +
          (3.143 * 3.124) * B (1 / 50) +
          (3.143 * 0.0374) * B (11 / 10) +
          (-(3.124 * 0.0374)) * B (27 / 25)) -
        0.00003249 -
        4 *
          (threeShiftEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * threeShiftEulerDensity X +
            threeShiftEulerError X) +
      ((51 / 50 : ℝ) ^ 5 / 30) * Real.exp (-(13 / 25) * x) *
        (3.143 * x ^ 5 - 3.124 * Real.exp ((51 / 50) * (1 / 50)) * (x - 1 / 50) ^ 5 -
          0.0374 * Real.exp ((51 / 50) * (11 / 10)) * (x - 11 / 10) ^ 5) -
    (3 * (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6) *
        (3.143 - 3.124 * Real.exp (1 / 100) - 0.0374 * Real.exp (11 / 20)) /
      r -
    4 * (3.124 - 3.143 * Real.exp (-(51 / 50) * (1 / 50))) * threeShiftReflectedCap X (1 / 50) -
    4 * 0.0374 * threeShiftReflectedCap X (11 / 10)

/-- Under GRH, the phase sum of the three pair characters of a passing
uniform Korselt triple dominates the section 117 linear gain and finite remainder. -/
theorem three_shift_passing_phase_117 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 300 ≤ R)
    (hL : Real.log n = 2 * R) (hprod : n = p * q * r)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    0.00120516 * R + threeShiftRemainder117 R ≤
      twoShiftZeroPhase a (R ^ 2) + twoShiftZeroPhase b (R ^ 2) + twoShiftZeroPhase c (R ^ 2) := by
  intro a b c
  let X := R ^ 2
  have hR0 : 0 < R := by linarith only [hR]
  have hX : 85264 ≤ X :=
    (by norm_num only : (85264 : ℝ) ≤ 300 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hR 2)
  have hx : 0 < X := sq_pos_of_pos hR0
  have hRlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 20) (lo := 5) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hRlog
  have hl := hRlog.trans (Real.log_le_log (by norm_num only) hR)
  have hXlog : 6 ≤ Real.log X := by
    dsimp only [X]
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hl]
  have hT : 1 ≤ X * Real.exp (-(39 / 10)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    rw [← Real.exp_natCast_mul] at he
    norm_num only [Nat.cast_ofNat, mul_one] at he
    exact
      (Real.exp_le_exp.mpr (show (39 / 10 : ℝ) ≤ 4 by norm_num only)).trans
        (he.trans (by linarith only [hX]))
  have oneAt {i j : ℕ} [NeZero i] [NeZero j] [Fact i.Prime] [Fact j.Prime] [Fact (2 < i)]
    [Fact (2 < j)] (hi : Odd i) (hj : Odd j) (hd : i * j ∣ n) (hik : i - 1 ∣ n - 1)
    (hjk : j - 1 ∣ n - 1) (hv : padicValNat 2 (j - 1) = padicValNat 2 (i - 1)) (k : ℕ)
    (hk : k.Prime) (hkX : (k : ℝ) ≤ X) :=
    pair_character_nat_eq_one hn ho hi hj ((dvd_mul_right _ _).trans hd)
      ((dvd_mul_left _ _).trans hd) hd hik hjk hv k (hpass k hk hkX)
  have contourAt {i j : ℕ} [NeZero i] [NeZero j] [Fact i.Prime] [Fact j.Prime] [Fact (2 < i)]
    [Fact (2 < j)] (hi : Odd i) (hj : Odd j) (hd : i * j ∣ n) (hik : i - 1 ∣ n - 1)
    (hjk : j - 1 ∣ n - 1) (hv : padicValNat 2 (j - 1) = padicValNat 2 (i - 1)) (s : ℝ)
    (hs : 0 ≤ s) :=
    twoShift_contour_eq_tail (pair_character_primitive hsq hd (hi.mul hj))
      (pair_character_ne_one hsq hd (hi.mul hj)
        ((Fact.out : i.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)))
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hi hj hik hjk hv) hx.le hs (oneAt hi hj hd hik hjk hv)
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hcos (s : ℝ) (hs : 0 ≤ s) :=
    twoShift_cosine_decompose hprod a b c X s (contourAt hp hq hpq hpk hqk hvq s hs)
      (contourAt hp hr hpr hpk hrk hvr s hs) (contourAt hq hr hqr hqk hrk (hvr.trans hvq.symm) s hs)
  have hy (s : ℝ) := mul_pos hx (Real.exp_pos (-s))
  have hphase :=
    three_shift_triple_117 hsq hn ho hp hq hr hpq hpr hqr hpk hqk hrk hvq hvr hG hX hpass
  dsimp only at hphase
  rw [hcos (14 / 5) (by norm_num only), hcos (141 / 50) (by norm_num only),
    hcos (39 / 10) (by norm_num only), hcos 0 (by norm_num only), hcos (1 / 50) (by norm_num only),
    hcos (11 / 10) (by norm_num only), hcos (27 / 25) (by norm_num only),
    weighted_residue_decompose hprod a b c (hy (14 / 5)),
    weighted_residue_decompose hprod a b c (hy (141 / 50)),
    weighted_residue_decompose hprod a b c (hy (39 / 10)), hL] at hphase
  have htail :=
    three_shift_cosine_tail_lower a b c hX (show 5 ≤ Real.log X by linarith only [hXlog]) hG.riemann
      ht
  have href :=
    three_shift_reflected_lower a b c (by linarith only [hX]) hT hXlog hG.riemann ht
      (oneAt hp hq hpq hpk hqk hvq) (oneAt hp hr hpr hpk hrk hvr)
      (oneAt hq hr hqr hqk hrk (hvr.trans hvq.symm))
  have hz := three_shift_zeta_lower hG.riemann (hy (14 / 5)) (hy (141 / 50)) (hy (39 / 10))
  have hslope := mul_le_mul_of_nonneg_right three_shift_gain_lower.le hR0.le
  unfold threeShiftGain at hslope
  rw [three_shift_g_eq (s := (14 / 5)) (by norm_num only),
    three_shift_g_eq (s := (141 / 50)) (by norm_num only),
    three_shift_g_eq (s := (39 / 10)) (by norm_num only),
    three_shift_g_eq (s := 0) (by norm_num only),
    three_shift_g_eq (s := (1 / 50)) (by norm_num only),
    three_shift_g_eq (s := (11 / 10)) (by norm_num only),
    three_shift_g_eq (s := (27 / 25)) (by norm_num only)] at hslope
  have hlog : 6 ≤ 2 * Real.log R := by
    dsimp only [X] at hXlog
    rw [Real.log_pow, Nat.cast_ofNat] at hXlog
    exact hXlog
  have h₀ := three_shift_real_main_eq n hR0 (h := 0) (by linarith only [hlog]) hL
  have h₁ := three_shift_real_main_eq n hR0 (h := 1 / 50) (by linarith only [hlog]) hL
  have h₂ := three_shift_real_main_eq n hR0 (h := 11 / 10) (by linarith only [hlog]) hL
  norm_num only [add_zero, sub_zero, zero_div, neg_zero, Real.exp_zero, mul_one] at h₀
  rw [show (14 / 5 + 1 / 50 : ℝ) = 141 / 50 by norm_num only,
    show (1 / 50 : ℝ) / 2 = 1 / 100 by norm_num only] at h₁
  rw [show (14 / 5 + 11 / 10 : ℝ) = 39 / 10 by norm_num only,
    show (11 / 10 : ℝ) / 2 = 11 / 20 by norm_num only] at h₂
  dsimp only at href hz htail
  dsimp only [X] at hphase href hz htail
  rw [h₀, h₁, h₂] at hphase
  dsimp only [threeShiftRemainder117]
  linear_combination hphase + htail + href + hz + hslope

end PseudoPrime.PrimeTestBounds.MillerRabin
