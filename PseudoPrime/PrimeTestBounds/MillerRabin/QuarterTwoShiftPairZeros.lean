/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZeroTwoFrequency
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticPairSign

/-! # Two-frequency contour comparison for the three Jacobi characters -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The mass plus the real oscillating zero sum at cutoff X for one character. -/
@[expose]
noncomputable def twoShiftZeroPhase {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) : ℝ :=
  quarterMass570 χ + (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ X ρ).re

/-- Character-dependent part of the lower bound in (96.8), retaining the
two cosine frequencies, their Gram correction, and both shifted contour terms. -/
@[expose]
noncomputable def twoShiftContourPart {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) : ℝ :=
  let W := fun s : ℝ ↦ ∑' ρ : ℂ, ‖quarterKernel570.oscillatingZeroTerm χ X ρ‖ * Real.cos (s * ρ.im)
  let C := fun y : ℝ ↦ contourNonEuler570 χ y - reflectedIntegral570 χ y
  (W (14 / 5) - W 3 + (C (X * Real.exp (-(14 / 5))) - C (X * Real.exp (-3)))) / 2 -
    (quarterMass570 χ - W (1 / 5)) / 4

/-- The forward principal contribution subtracted once per character. -/
@[expose]
noncomputable def twoShiftPrincipalDiff (X : ℝ) : ℝ :=
  let S := fun y : ℝ ↦ (∑' n : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) y n).re
  (S (X * Real.exp (-(14 / 5))) - S (X * Real.exp (-3))) / 2

private theorem pair_contour_lower {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q] [Fact p.Prime]
    [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hd : p * q ∣ n) (hpk : p - 1 ∣ n - 1) (hqk : q - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hx : 0 < X)
    (hcut : 1 ≤ X * Real.exp (-3))
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    twoShiftContourPart χ X - twoShiftPrincipalDiff X ≤ twoShiftZeroPhase χ X := by
  intro χ
  have hpq : 2 ≤ p * q :=
    ((Fact.out : p.Prime).two_le).trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hne := pair_character_ne_one hsq hd (hp.mul hq) hpq
  have h :=
    twoShift_zero_contour_lower hpq hG (pair_character_primitive hsq hd (hp.mul hq)) hne
      (inv_ne_one.mpr hne) hx hcut
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hp hq ((dvd_mul_right p q).trans hd)
          ((dvd_mul_left q p).trans hd) hd hpk hqk hv l (hpass l hl hlX))
  dsimp only at h
  unfold twoShiftContourPart twoShiftPrincipalDiff twoShiftZeroPhase
  dsimp only [χ]
  linarith only [h]

/-- Under GRH and universal prime-base passage, the mass plus oscillating zero sums
of the three pair characters dominate their contour corrections minus three copies
of one principal difference. Pair primitivity follows from squarefreeness. -/
theorem twoShift_pair_zero_lower {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    twoShiftContourPart a X + twoShiftContourPart b X + twoShiftContourPart c X -
        3 * twoShiftPrincipalDiff X ≤
      twoShiftZeroPhase a X + twoShiftZeroPhase b X + twoShiftZeroPhase c X := by
  intro a b c
  have hx : 0 < X := by linarith only [hX]
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
  have hex : Real.exp 3 ≤ X := by
    rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [he, hX]
  have hcut : 1 ≤ X * Real.exp (-3) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    exact hex
  have ha := pair_contour_lower hsq hn ho hp hq hpq hpk hqk hvq hG hx hcut hpass
  have hb := pair_contour_lower hsq hn ho hp hr hpr hpk hrk hvr hG hx hcut hpass
  have hc := pair_contour_lower hsq hn ho hq hr hqr hqk hrk (hvr.trans hvq.symm) hG hx hcut hpass
  dsimp only at ha hb hc
  dsimp only [a, b, c]
  linarith only [ha, hb, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
