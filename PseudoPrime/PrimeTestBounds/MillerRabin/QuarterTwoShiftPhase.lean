/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftIntervals
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Two-shift phase bound at the quarter-square cutoff -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If all prime bases through the quarter-square cutoff pass, the three
pair phases retain the full two-shift leading coefficient and the signed
Euler and reflected remainder. The radius is at least 292. -/
theorem twoShift_passing_phase_lower {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hprod : n = p * q * r) (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n)
    (hpk : p - 1 ∣ n - 1) (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 292 ≤ R)
    (hL : Real.log n = 2 * R)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    twoShiftPhaseCoeff * R + twoShiftSignedRemainder p q r hp hq hr R (R ^ 2) ≤
      twoShiftZeroPhase a (R ^ 2) + twoShiftZeroPhase b (R ^ 2) + twoShiftZeroPhase c (R ^ 2) := by
  intro a b c
  have h₀ : 0 < R := by linarith only [hR]
  have hX : 85264 ≤ R ^ 2 :=
    (by norm_num only : (85264 : ℝ) ≤ 292 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hR 2)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 20) (lo := 5) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlog
  have hu : (1 / 5 : ℝ) ≤ 2 * Real.log R := by
    linarith only [hlog, Real.log_le_log (by norm_num only) hR]
  have oneAt {i j : ℕ} [NeZero i] [NeZero j] [Fact i.Prime] [Fact j.Prime] [Fact (2 < i)]
    [Fact (2 < j)] (hi : Odd i) (hj : Odd j) (hd : i * j ∣ n) (hik : i - 1 ∣ n - 1)
    (hjk : j - 1 ∣ n - 1) (hv : padicValNat 2 (j - 1) = padicValNat 2 (i - 1)) (l : ℕ)
    (hl : l.Prime) (hlX : (l : ℝ) ≤ R ^ 2) :=
    pair_character_nat_eq_one hn ho hi hj ((dvd_mul_right _ _).trans hd)
      ((dvd_mul_left _ _).trans hd) hd hik hjk hv l (hpass l hl hlX)
  have contourAt {i j : ℕ} [NeZero i] [NeZero j] [Fact i.Prime] [Fact j.Prime] [Fact (2 < i)]
    [Fact (2 < j)] (hi : Odd i) (hj : Odd j) (hd : i * j ∣ n) (hik : i - 1 ∣ n - 1)
    (hjk : j - 1 ∣ n - 1) (hv : padicValNat 2 (j - 1) = padicValNat 2 (i - 1)) (s : ℝ)
    (hs : 0 ≤ s) :=
    twoShift_contour_eq_tail (pair_character_primitive hsq hd (hi.mul hj))
      (pair_character_ne_one hsq hd (hi.mul hj)
        ((Fact.out : i.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)))
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hi hj hik hjk hv) (sq_nonneg R) hs
      (oneAt hi hj hd hik hjk hv)
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hcos :=
    twoShift_cosine_combination hprod a b c hX hG.riemann (contourAt hp hq hpq hpk hqk hvq)
      (contourAt hp hr hpr hpk hrk hvr) (contourAt hq hr hqr hqk hrk (hvr.trans hvq.symm))
  have hres :=
    twoShift_residue_signed_lower hprod a b c hG.riemann hX ht (oneAt hp hq hpq hpk hqk hvq)
      (oneAt hp hr hpr hpk hrk hvr) (oneAt hq hr hqr hqk hrk (hvr.trans hvq.symm))
  have hphase :=
    twoShift_triple_phase_components hsq hn ho hp hq hr hpq hpr hqr hpk hqk hrk hvq hvr hG hX hpass
  have hζ := (abs_lt.mp (twoShift_zeta_cosine_bound hG.riemann)).2
  have hcoef := congrArg (fun t : ℝ ↦ t * R) twoShift_phaseCoeff_formula
  dsimp only at hcos hres hphase hcoef
  rw [hL, twoShift_conductor_profile (by norm_num only : (0 : ℝ) ≤ 14 / 5),
    twoShift_conductor_profile (by norm_num only : (0 : ℝ) ≤ 3),
    twoShift_conductor_profile (le_refl (0 : ℝ)),
    twoShift_conductor_profile (by norm_num only : (0 : ℝ) ≤ 1 / 5)] at hcos
  rw [twoShift_real_main_difference n h₀ hu hL] at hres
  dsimp only [twoShiftSignedRemainder]
  dsimp only [a, b, c] at hcos hres ⊢
  linarith only [hcos, hres, hphase, hζ, hcoef]

end PseudoPrime.PrimeTestBounds.MillerRabin
