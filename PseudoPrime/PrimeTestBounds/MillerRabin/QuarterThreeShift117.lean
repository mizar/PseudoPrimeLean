/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedPhase
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedPhase
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZeroThreeFrequency

/-! # The section 117 three-shift contour comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The section 117 phase estimate for one even primitive quadratic character,
with all three mixed cosine contours and all three shifted residues. -/
theorem three_shift_contour_117 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ = χ) (he : χ.Even) {X : ℝ} (hx : 0 < X) (ht : 1 ≤ X * Real.exp (-(39 / 10)))
    (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let W := twoShiftContourValue χ
    let R := twoShiftResidueValue χ
    3.143 * (W (14 / 5) + R (X * Real.exp (-(14 / 5)))) -
            3.124 * (W (141 / 50) + R (X * Real.exp (-(141 / 50)))) -
            0.0374 * (W (39 / 10) + R (X * Real.exp (-(39 / 10)))) -
            ((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2) * W 0 +
          3.143 * 3.124 * W (1 / 50) +
          3.143 * 0.0374 * W (11 / 10) -
        3.124 * 0.0374 * W (27 / 25) ≤
      twoShiftZeroPhase χ X := by
  intro W R
  have hi' : χ⁻¹ ≠ 1 := inv_ne_one.mpr hn
  have cut {s : ℝ} (hs : s ≤ 39 / 10) : 1 ≤ X * Real.exp (-s) :=
    ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hs)) hx.le)
  have res {s : ℝ} (hs : 14 / 5 ≤ s) (hy : 1 ≤ X * Real.exp (-s)) :
    (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ (X * Real.exp (-s)) ρ).re =
      twoShiftResidueValue χ (X * Real.exp (-s)) := by
    rw [zero_re_eq_contour_sub_prime hq hG hp hn hi' hy,
      twoShift_forward_eq_principal χ hx hs hpass,
      twoShift_unshifted_contour_eq χ hn hi he hG.riemann hy, add_sub_cancel_left]
  have h :=
    quarter_zero_three_frequency hq hG hp hn hi' hx (39 / 10) (141 / 50) (14 / 5) (-0.0374) (-3.124)
      3.143
  dsimp only at h
  rw [show (39 / 10 : ℝ) - 141 / 50 = 27 / 25 by norm_num only,
    show (39 / 10 : ℝ) - 14 / 5 = 11 / 10 by norm_num only,
    show (141 / 50 : ℝ) - 14 / 5 = 1 / 50 by norm_num only] at h
  rw [twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 39 / 10),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 141 / 50),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 14 / 5),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 27 / 25),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 11 / 10),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 1 / 50),
    res (by norm_num only) ht, res (by norm_num only) (cut (by norm_num only)),
    res le_rfl (cut (by norm_num only)), twoShift_mass_eq_zero_contour hq hG hp hn] at h
  dsimp only [W, R, twoShiftZeroPhase]
  rw [twoShift_mass_eq_zero_contour hq hG hp hn]
  linarith only [h]

/-- For a passing uniform Korselt product, summing the three pair-character
inequalities retains the full section 117 contour and residue expression. -/
theorem three_shift_triple_117 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
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
    let W := fun s ↦ twoShiftContourValue a s + twoShiftContourValue b s + twoShiftContourValue c s
    let R := fun x ↦ twoShiftResidueValue a x + twoShiftResidueValue b x + twoShiftResidueValue c x
    3.143 * (W (14 / 5) + R (X * Real.exp (-(14 / 5)))) -
            3.124 * (W (141 / 50) + R (X * Real.exp (-(141 / 50)))) -
            0.0374 * (W (39 / 10) + R (X * Real.exp (-(39 / 10)))) -
            ((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2) * W 0 +
          3.143 * 3.124 * W (1 / 50) +
          3.143 * 0.0374 * W (11 / 10) -
        3.124 * 0.0374 * W (27 / 25) ≤
      twoShiftZeroPhase a X + twoShiftZeroPhase b X + twoShiftZeroPhase c X := by
  intro a b c W R
  have hx : 0 < X := by linarith only [hX]
  have ht : 1 ≤ X * Real.exp (-(39 / 10)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
    rw [← Real.exp_natCast_mul] at he
    norm_num only [Nat.cast_ofNat, mul_one] at he
    exact
      (Real.exp_le_exp.mpr (show (39 / 10 : ℝ) ≤ 4 by norm_num only)).trans
        (he.trans (by linarith only [hX]))
  have H {i j : ℕ} [NeZero i] [NeZero j] [Fact i.Prime] [Fact j.Prime] [Fact (2 < i)] [Fact (2 < j)]
    (hi : Odd i) (hj : Odd j) (hd : i * j ∣ n) (hik : i - 1 ∣ n - 1) (hjk : j - 1 ∣ n - 1)
    (hv : padicValNat 2 (j - 1) = padicValNat 2 (i - 1)) :=
    three_shift_contour_117
      ((Fact.out : i.Prime).two_le.trans (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)) hG
      (pair_character_primitive hsq hd (hi.mul hj))
      (pair_character_ne_one hsq hd (hi.mul hj)
        ((Fact.out : i.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)))
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hi hj hik hjk hv) hx ht
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hi hj ((dvd_mul_right _ _).trans hd)
          ((dvd_mul_left _ _).trans hd) hd hik hjk hv l (hpass l hl hlX))
  dsimp only [W, R, a, b, c]
  linarith only [H hp hq hpq hpk hqk hvq, H hp hr hpr hpk hrk hvr,
    H hq hr hqr hqk hrk (hvr.trans hvq.symm)]

/-- Collect the seven cosine-tail contributions in a single sum over prime powers
above the cutoff, retaining the common trace factor. -/
theorem three_shift_weighted_tail {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ) :
    let S := twoShiftCosineTail a b c X
    let P := fun (k s : ℝ) ↦
      twoShiftSymmetricProfile (k * Real.exp (-s)) + twoShiftSymmetricProfile (k⁻¹ * Real.exp (-s))
    (3.143) * S (14 / 5) + (-3.124) * S (141 / 50) + (-0.0374) * S (39 / 10) +
        (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2)) * S 0 +
        ((3.143 * 3.124)) * S (1 / 50) +
        ((3.143 * 0.0374)) * S (11 / 10) +
        (-(3.124 * 0.0374)) * S (27 / 25) =
      ∑' k : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
          (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val) *
          ((3.143) * P k.val (14 / 5) + (-3.124) * P k.val (141 / 50) +
            (-0.0374) * P k.val (39 / 10) +
            (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2)) * P k.val 0 +
            ((3.143 * 3.124)) * P k.val (1 / 50) +
            ((3.143 * 0.0374)) * P k.val (11 / 10) +
            (-(3.124 * 0.0374)) * P k.val (27 / 25)) := by
  intro S P
  let F := fun (y : ℝ) (k : { n : ℕ // ⌊X⌋₊ < n }) ↦
    (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
      (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
        twoShiftSymmetricProfile (k.val / y))
  have hs (s : ℝ) : HasSum (fun k ↦ F (Real.exp s)⁻¹ k + F (Real.exp s) k) (S s) :=
    (twoShift_trace_tail_hasSum a b c X (inv_pos.mpr (Real.exp_pos s))).summable.hasSum.add
      (twoShift_trace_tail_hasSum a b c X (Real.exp_pos s)).summable.hasSum
  have h0 := (hs (14 / 5)).mul_left (3.143)
  have h1 := (hs (141 / 50)).mul_left (-3.124)
  have h2 := (hs (39 / 10)).mul_left (-0.0374)
  have h3 := (hs 0).mul_left (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2))
  have h4 := (hs (1 / 50)).mul_left ((3.143 * 3.124))
  have h5 := (hs (11 / 10)).mul_left ((3.143 * 0.0374))
  have h6 := (hs (27 / 25)).mul_left (-(3.124 * 0.0374))
  have hh := (((((h0.add h1).add h2).add h3).add h4).add h5).add h6
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro k
  dsimp only [F, P]
  let A := 3 - ((a k.val).re + (b k.val).re + (c k.val).re)
  let B := ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val
  linear_combination
    (3.143 * A * B) * twoShift_tail_profile_pair (k.val : ℝ) (14 / 5) +
      (-3.124 * A * B) * twoShift_tail_profile_pair (k.val : ℝ) (141 / 50) +
      (-0.0374 * A * B) * twoShift_tail_profile_pair (k.val : ℝ) (39 / 10) +
      (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2) * A * B) *
        twoShift_tail_profile_pair (k.val : ℝ) 0 +
      ((3.143 * 3.124) * A * B) * twoShift_tail_profile_pair (k.val : ℝ) (1 / 50) +
      ((3.143 * 0.0374) * A * B) * twoShift_tail_profile_pair (k.val : ℝ) (11 / 10) +
      (-(3.124 * 0.0374) * A * B) * twoShift_tail_profile_pair (k.val : ℝ) (27 / 25)

/-- The Euler weight of the section 117 comparison is the negative of the
signed sum of shifted quadratic polynomials, after factoring out the common decay. -/
@[expose]
noncomputable def threeShiftEulerPoly (x : ℝ) : ℝ :=
  -(3.143 * weightedShiftPoly (14 / 5) x - 3.124 * weightedShiftPoly (141 / 50) x -
          0.0374 * weightedShiftPoly (39 / 10) x -
          ((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2) * weightedShiftPoly 0 x +
        (3.143 * 3.124) * weightedShiftPoly (1 / 50) x +
        (3.143 * 0.0374) * weightedShiftPoly (11 / 10) x -
      (3.124 * 0.0374) * weightedShiftPoly (27 / 25) x)

private theorem three_shift_euler_term {k : ℕ} (hk : 0 < k) (hl : 4 ≤ Real.log k) :
    let P := fun s : ℝ ↦
      twoShiftSymmetricProfile ((k : ℝ) * Real.exp (-s)) +
        twoShiftSymmetricProfile ((k : ℝ)⁻¹ * Real.exp (-s))
    ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        ((3.143) * P (14 / 5) + (-3.124) * P (141 / 50) + (-0.0374) * P (39 / 10) +
          (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2)) * P 0 +
          ((3.143 * 3.124)) * P (1 / 50) +
          ((3.143 * 0.0374)) * P (11 / 10) +
          (-(3.124 * 0.0374)) * P (27 / 25)) =
      -(ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ (38 / 25 : ℝ) *
          threeShiftEulerPoly (Real.log k)) := by
  intro P
  have hp : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  dsimp only [P]
  have h (s : ℝ) (hs : 0 ≤ s) (hu : s ≤ 4) := profile_pair_weighted hp hs (hu.trans hl)
  rw [h (14 / 5) (by norm_num only) (by norm_num only),
    h (141 / 50) (by norm_num only) (by norm_num only),
    h (39 / 10) (by norm_num only) (by norm_num only), h 0 (by norm_num only) (by norm_num only),
    h (1 / 50) (by norm_num only) (by norm_num only),
    h (11 / 10) (by norm_num only) (by norm_num only),
    h (27 / 25) (by norm_num only) (by norm_num only)]
  have hd : (k : ℝ) ^ (38 / 25 : ℝ) = (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (51 / 50 : ℝ) := by
    rw [← Real.rpow_add hp]
    norm_num only
  rw [mul_comm (-(51 / 50)) (Real.log k), ← Real.rpow_def_of_pos hp, Real.rpow_neg hp.le,
    Real.sqrt_eq_rpow, hd]
  simp only [threeShiftEulerPoly, div_eq_mul_inv, mul_inv_rev]
  ring

/-- For cutoffs at least 85264, the combined Euler tail has a common quadratic
weight and trace deficit, with one factor of the inverse power 38/25. -/
theorem three_shift_euler_eq {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 85264 ≤ X) :
    let S := twoShiftCosineTail a b c X
    (3.143) * S (14 / 5) + (-3.124) * S (141 / 50) + (-0.0374) * S (39 / 10) +
        (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2)) * S 0 +
        ((3.143 * 3.124)) * S (1 / 50) +
        ((3.143 * 0.0374)) * S (11 / 10) +
        (-(3.124 * 0.0374)) * S (27 / 25) =
      -(∑' k : { n : ℕ // ⌊X⌋₊ < n },
          (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
            (ArithmeticFunction.vonMangoldt k.val / (k.val : ℝ) ^ (38 / 25 : ℝ) *
              threeShiftEulerPoly (Real.log k.val))) := by
  intro S
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
  have hx : Real.exp 4 ≤ X := by
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [he, hX]
  dsimp only [S]
  rw [three_shift_weighted_tail, ← tsum_neg]
  apply tsum_congr
  intro k
  have hk : 0 < k.val := (Nat.zero_le _).trans_lt k.property
  have hl :=
    (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hk)).mpr (hx.trans (Nat.lt_of_floor_lt k.property).le)
  rw [mul_assoc, three_shift_euler_term hk hl, mul_neg]

end PseudoPrime.PrimeTestBounds.MillerRabin
