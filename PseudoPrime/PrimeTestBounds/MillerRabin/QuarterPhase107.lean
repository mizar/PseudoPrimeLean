/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedReflected
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftEuler
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass101
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Explicit phase recovery at the section 107 cutoff -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the quarter-square cutoff, independent weights on the two real main
terms give the conductor density, reciprocal pole and linear pole of section 101. -/
theorem weighted_real_main_difference (n : ℕ) {r : ℝ} (hr : 0 < r) (hu : 1 / 5 ≤ 2 * Real.log r)
    (hn : Real.log n = 2 * r) (u v : ℝ) :
    u * twoShiftRealMain n (r ^ 2 * Real.exp (-(14 / 5))) -
        v * twoShiftRealMain n (r ^ 2 * Real.exp (-3)) =
      ((51 / 50 : ℝ) ^ 5 / 30) * Real.exp (-(13 / 25) * (2 * Real.log r)) *
            (u * (2 * Real.log r) ^ 5 -
              v * Real.exp ((51 / 50) * (1 / 5)) * (2 * Real.log r - 1 / 5) ^ 5) +
          (3 * (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6) * (v * Real.exp (1 / 10) - u) / r -
        (3 * (51 / 50 : ℝ) ^ 5 / (38 / 25) ^ 6) * (u - v * Real.exp (-(1 / 10))) * r := by
  have h₀ := twoShift_main_at_shift n hr ((by norm_num only : (0 : ℝ) ≤ 1 / 5).trans hu)
  have h₁ := twoShift_main_at_shift n hr hu
  norm_num only [add_zero, sub_zero, zero_div, neg_zero, Real.exp_zero, div_div, mul_one] at h₀
  rw [show -(14 / 5 + 1 / 5 : ℝ) = -3 by norm_num only,
    show (1 / 5 : ℝ) / 2 = 1 / 10 by norm_num only] at h₁
  rw [h₀, h₁, hn]
  have hshift :
    Real.exp (-(51 / 50 : ℝ) * (2 * Real.log r - 1 / 5)) =
      Real.exp (-(51 / 50) * (2 * Real.log r)) * Real.exp ((51 / 50) * (1 / 5)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscale :
    r * Real.exp (-(51 / 50 : ℝ) * (2 * Real.log r)) =
      Real.exp (-(13 / 25) * (2 * Real.log r)) := by
    calc
      _ = Real.exp (Real.log r) * Real.exp (-(51 / 50) * (2 * Real.log r)) := by
        rw [Real.exp_log hr]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [hshift]
  linear_combination (norm := ring)
    ((51 / 50 : ℝ) ^ 5 / 30 *
        (u * (2 * Real.log r) ^ 5 -
          v * Real.exp ((51 / 50) * (1 / 5)) * (2 * Real.log r - 1 / 5) ^ 5)) *
      hscale

/-- The linear coefficient of the section 107 phase gain, in radius units. -/
noncomputable def phaseSlope107 : ℝ :=
  let u : ℝ := 11 / 25
  let v : ℝ := 91 / 200
  let B := fun s : ℝ ↦ 4 * twoShiftSymmetricProfile (Real.exp s)⁻¹
  u * B (14 / 5) - v * B 3 - ((u ^ 2 + v ^ 2) / 2) * B 0 + (u * v) * B (1 / 5) -
    (3 * (51 / 50 : ℝ) ^ 5 / (38 / 25) ^ 6) * (u - v * Real.exp (-(1 / 10)))

/-- The section 107 linear phase recovery per unit radius exceeds 0.0011365. -/
theorem phaseSlope107_lower : 0.0011365 < phaseSlope107 := by
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (1 / 10 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hu
  have hsmall : Real.exp (1 / 10 : ℝ) ≤ 110517092 / 100000000 := by linarith only [hu]
  unfold phaseSlope107
  dsimp only
  rw [twoShift_conductor_profile (by norm_num only : (0 : ℝ) ≤ 14 / 5),
    twoShift_conductor_profile (by norm_num only : (0 : ℝ) ≤ 3),
    twoShift_conductor_profile (le_refl (0 : ℝ)),
    twoShift_conductor_profile (by norm_num only : (0 : ℝ) ≤ 1 / 5)]
  simp only [neg_mul, mul_zero, Real.exp_zero, Real.exp_neg, ← one_div]
  linarith only [one_div_le_one_div_of_le (Real.exp_pos _) exp_b.2,
    one_div_le_one_div_of_le (by norm_num only) exp_t.1,
    one_div_le_one_div_of_le (Real.exp_pos _) exp_h.2,
    one_div_le_one_div_of_le (Real.exp_pos _) hsmall]

/-- The constant phase recovery from the two symmetric poles before the
zeta and Euler tail costs are charged. -/
noncomputable def phasePole107 : ℝ :=
  let u : ℝ := 11 / 25
  let v : ℝ := 91 / 200
  6 * (51 / 50 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 - 1 / 4) ^ 3 *
    (v * Real.cosh (3 / 2) - u * Real.cosh (7 / 5) + (u ^ 2 + v ^ 2) / 2 -
      (u * v) * Real.cosh (1 / 10))

/-- A fixed rational lower bound on the symmetric pole recovery in section 107. -/
theorem phasePole107_lower : 1.650951366 < phasePole107 := by
  have ht := (cosh_taylor_box (3 / 2) (by norm_num only) (by norm_num only)).1
  have hb := (cosh_taylor_box (7 / 5) (by norm_num only) (by norm_num only)).2
  have hh := (cosh_taylor_box (1 / 10) (by norm_num only) (by norm_num only)).2
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat] at ht hb hh
  unfold phasePole107
  linarith only [ht, hb, hh]

/-- The explicit section 107 phase remainder at radius r. It combines the
constant pole recovery, both Euler tail costs, and the two decaying main terms. -/
noncomputable def phaseRemainder107 (r : ℝ) : ℝ :=
  let u : ℝ := 11 / 25
  let v : ℝ := 91 / 200
  let x := r ^ 2
  let l := 2 * Real.log r
  phasePole107 - 0.000002191 -
        4 *
          (weightedEulerMain x + Real.sqrt x * (Real.log x ^ 2 / 24) * weightedEulerDensity x +
            weightedEulerError x) +
      ((51 / 50 : ℝ) ^ 5 / 30) * Real.exp (-(13 / 25) * l) *
        (u * l ^ 5 - v * Real.exp ((51 / 50) * (1 / 5)) * (l - 1 / 5) ^ 5) +
      (3 * (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6) * (v * Real.exp (1 / 10) - u) / r -
    4 * (v - u * Real.exp (-(51 / 50) * (1 / 5))) *
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5))) *
      twoShiftReflectedTail x

/-- Passing all prime bases through the quarter-square cutoff forces the
three zero phases to dominate the section 107 linear gain and explicit remainder. -/
theorem weighted_passing_phase_107 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
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
    0.0011365 * R + phaseRemainder107 R ≤
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
  have hXlog : 5 ≤ Real.log X := by
    dsimp only [X]
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hl]
  have hT : 1 ≤ X * Real.exp (-3) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
    rw [← Real.exp_natCast_mul] at he
    norm_num only [Nat.cast_ofNat, mul_one] at he
    linarith only [he, hX]
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
  have hb := mul_pos hx (Real.exp_pos (-(14 / 5 : ℝ)))
  have htp := mul_pos hx (Real.exp_pos (-3))
  have hphase :=
    twoShift_weighted_triple hsq hn ho hp hq hr hpq hpr hqr hpk hqk hrk hvq hvr hG hX hpass
      (11 / 25) (91 / 200)
  dsimp only at hphase
  rw [hcos (14 / 5) (by norm_num only), hcos 3 (by norm_num only), hcos 0 (le_refl 0),
    hcos (1 / 5) (by norm_num only), weighted_residue_decompose hprod a b c hb,
    weighted_residue_decompose hprod a b c htp, hL] at hphase
  have htail := weighted_cosine_tail_lower a b c hX hXlog hG.riemann ht
  have href :=
    weighted_reflected_lower a b c (by linarith only [hX]) hT ht (oneAt hp hq hpq hpk hqk hvq)
      (oneAt hp hr hpr hpk hrk hvr) (oneAt hq hr hqr hqk hrk (hvr.trans hvq.symm))
  have hz := section107_zeta_lower hG.riemann hb htp
  have hmain := weighted_real_main_difference n hR0 (by linarith only [hl]) hL (11 / 25) (91 / 200)
  have hslope := mul_le_mul_of_nonneg_right phaseSlope107_lower.le hR0.le
  dsimp only [phaseSlope107] at hslope
  dsimp only [phaseRemainder107, phasePole107]
  dsimp only at href hz htail
  dsimp only [X] at hphase href hz htail
  rw [zero_div, Real.cosh_zero] at hphase
  norm_num only [show (14 / 5 : ℝ) / 2 = 7 / 5 by norm_num only, show (3 : ℝ) / 2 = 3 / 2 by rfl,
    show (1 / 5 : ℝ) / 2 = 1 / 10 by norm_num only] at hphase
  linarith only [hphase, htail, href, hz, hmain, hslope]

end PseudoPrime.PrimeTestBounds.MillerRabin
