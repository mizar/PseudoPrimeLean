/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZeroTwoFrequency
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Weighted two-shift phase comparison for the three pair characters -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and prime-prefix triviality, a primitive even quadratic character
satisfies the weighted two-shift comparison with both forward sums cancelled. -/
theorem twoShift_weighted_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ = χ) (he : χ.Even) {X : ℝ} (hx : 0 < X) (ht : 1 ≤ X * Real.exp (-3))
    (hpass : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) (u v : ℝ) :
    u * (twoShiftContourValue χ (14 / 5) + twoShiftResidueValue χ (X * Real.exp (-(14 / 5)))) -
          v * (twoShiftContourValue χ 3 + twoShiftResidueValue χ (X * Real.exp (-3))) -
          ((u ^ 2 + v ^ 2) / 2) * twoShiftContourValue χ 0 +
        (u * v) * twoShiftContourValue χ (1 / 5) ≤
      twoShiftZeroPhase χ X := by
  have hi' : χ⁻¹ ≠ 1 := inv_ne_one.mpr hn
  have hb : 1 ≤ X * Real.exp (-(14 / 5)) :=
    ht.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only : (-3 : ℝ) ≤ -(14 / 5)))
        hx.le)
  have res {s : ℝ} (hs : 14 / 5 ≤ s) (hy : 1 ≤ X * Real.exp (-s)) :
    (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ (X * Real.exp (-s)) ρ).re =
      twoShiftResidueValue χ (X * Real.exp (-s)) := by
    rw [zero_re_eq_contour_sub_prime hq hG hp hn hi' hy,
      twoShift_forward_eq_principal χ hx hs hpass,
      twoShift_unshifted_contour_eq χ hn hi he hG.riemann hy, add_sub_cancel_left]
  have h := quarter_zero_weighted_lower hq hG hp hn hi' hx (14 / 5) 3 u v
  dsimp only at h
  rw [show (3 : ℝ) - 14 / 5 = 1 / 5 by norm_num only,
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 14 / 5),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 3),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 1 / 5),
    twoShift_mass_eq_zero_contour hq hG hp hn, res le_rfl hb, res (by norm_num only) ht] at h
  unfold twoShiftZeroPhase
  rw [twoShift_mass_eq_zero_contour hq hG hp hn]
  exact h

/-- If all prime bases through X pass for an odd squarefree Korselt triple
with equal two-adic valuations, summing the three weighted contour comparisons
gives the section 101 lower bound in terms of the cosine and residue values. -/
theorem twoShift_weighted_triple {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n))
    (u v : ℝ) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let W := fun s ↦ twoShiftContourValue a s + twoShiftContourValue b s + twoShiftContourValue c s
    let R := fun x ↦ twoShiftResidueValue a x + twoShiftResidueValue b x + twoShiftResidueValue c x
    u * (W (14 / 5) + R (X * Real.exp (-(14 / 5)))) - v * (W 3 + R (X * Real.exp (-3))) -
          ((u ^ 2 + v ^ 2) / 2) * W 0 +
        (u * v) * W (1 / 5) ≤
      twoShiftZeroPhase a X + twoShiftZeroPhase b X + twoShiftZeroPhase c X := by
  intro a b c W R
  have hx : 0 < X := by linarith only [hX]
  have ht : 1 ≤ X * Real.exp (-3) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
    rw [← Real.exp_natCast_mul] at he
    norm_num only [Nat.cast_ofNat, mul_one] at he
    linarith only [he, hX]
  have H {i j : ℕ} [NeZero i] [NeZero j] [Fact i.Prime] [Fact j.Prime] [Fact (2 < i)] [Fact (2 < j)]
    (hi : Odd i) (hj : Odd j) (hd : i * j ∣ n) (hik : i - 1 ∣ n - 1) (hjk : j - 1 ∣ n - 1)
    (hv : padicValNat 2 (j - 1) = padicValNat 2 (i - 1)) :=
    twoShift_weighted_contour
      ((Fact.out : i.Prime).two_le.trans (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)) hG
      (pair_character_primitive hsq hd (hi.mul hj))
      (pair_character_ne_one hsq hd (hi.mul hj)
        ((Fact.out : i.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)))
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hi hj hik hjk hv) hx ht
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hi hj ((dvd_mul_right _ _).trans hd)
          ((dvd_mul_left _ _).trans hd) hd hik hjk hv l (hpass l hl hlX))
      u v
  dsimp only [W, R, a, b, c]
  linarith only [H hp hq hpq hpk hqk hvq, H hp hr hpr hpk hrk hvr,
    H hq hr hqr hqk hrk (hvr.trans hvq.symm)]

/-- For a passing triple, the cosine contour sum at a nonnegative frequency
decomposes into the common zeta contour, conductor, poles, and shared Euler tail. -/
theorem twoShift_cosine_decompose {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) (X s : ℝ)
    (ha : twoShiftContourValue a s = twoShiftXiContourValue s + twoShiftTailDifference a X s)
    (hb : twoShiftContourValue b s = twoShiftXiContourValue s + twoShiftTailDifference b X s)
    (hc : twoShiftContourValue c s = twoShiftXiContourValue s + twoShiftTailDifference c X s) :
    twoShiftContourValue a s + twoShiftContourValue b s + twoShiftContourValue c s =
      3 * twoShiftXiContourValue s + 2 * Real.log n * twoShiftSymmetricProfile (Real.exp s)⁻¹ -
          6 * ((51 / 50 : ℝ) ^ 5 / ((51 / 50) ^ 2 - 1 / 4) ^ 3) * Real.cosh (s / 2) +
        twoShiftCosineTail a b c X s := by
  linarith only [ha, hb, hc, twoShift_three_cosine_tail hn a b c X s]

/-- The four weighted cosine tails share one series over prime powers above X.
Collect the frequency coefficients inside that series before bounding the trace. -/
theorem twoShift_weighted_tail {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (X u v : ℝ) :
    let S := twoShiftCosineTail a b c X
    let P := fun (k s : ℝ) ↦
      twoShiftSymmetricProfile (k * Real.exp (-s)) + twoShiftSymmetricProfile (k⁻¹ * Real.exp (-s))
    u * S (14 / 5) - v * S 3 - ((u ^ 2 + v ^ 2) / 2) * S 0 + (u * v) * S (1 / 5) =
      ∑' k : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
          (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val) *
          (u * P k.val (14 / 5) - v * P k.val 3 - ((u ^ 2 + v ^ 2) / 2) * P k.val 0 +
            (u * v) * P k.val (1 / 5)) := by
  intro S P
  let F := fun (y : ℝ) (k : { n : ℕ // ⌊X⌋₊ < n }) ↦
    (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
      (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
        twoShiftSymmetricProfile (k.val / y))
  have hs (s : ℝ) : HasSum (fun k ↦ F (Real.exp s)⁻¹ k + F (Real.exp s) k) (S s) :=
    (twoShift_trace_tail_hasSum a b c X (inv_pos.mpr (Real.exp_pos s))).summable.hasSum.add
      (twoShift_trace_tail_hasSum a b c X (Real.exp_pos s)).summable.hasSum
  have h :=
    ((((hs (14 / 5)).mul_left u).sub ((hs 3).mul_left v)).sub
          ((hs 0).mul_left ((u ^ 2 + v ^ 2) / 2))).add
      ((hs (1 / 5)).mul_left (u * v))
  rw [← h.tsum_eq]
  apply tsum_congr
  intro k
  dsimp only [F, P]
  let A := 3 - ((a k.val).re + (b k.val).re + (c k.val).re)
  let B := ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val
  linear_combination
    (A * B * u) * twoShift_tail_profile_pair (k.val : ℝ) (14 / 5) -
        (A * B * v) * twoShift_tail_profile_pair (k.val : ℝ) 3 -
        (A * B * ((u ^ 2 + v ^ 2) / 2)) * twoShift_tail_profile_pair (k.val : ℝ) 0 +
      (A * B * (u * v)) * twoShift_tail_profile_pair (k.val : ℝ) (1 / 5)

/-- The frequency-s coefficient Q_s(x) in section 101.9, obtained by
factoring the common exponential from the two symmetric profiles. -/
@[expose]
noncomputable def weightedShiftPoly (s x : ℝ) : ℝ :=
  let a := (51 / 50 : ℝ)
  let Q := fun z : ℝ ↦ 3 / 8 + 3 * a / 8 * z + a ^ 2 / 8 * z ^ 2
  (Real.exp (-a * s) * Q (x + s) + Real.exp (a * s) * Q (x - s)) / 2

/-- The common Euler polynomial in section 101.9 for the auxiliary
coefficients u and v. The trace deficit is multiplied by this combined weight. -/
@[expose]
noncomputable def weightedEulerPoly (u v x : ℝ) : ℝ :=
  ((u ^ 2 + v ^ 2) / 2) * weightedShiftPoly 0 x - (u * v) * weightedShiftPoly (1 / 5) x -
      u * weightedShiftPoly (14 / 5) x +
    v * weightedShiftPoly 3 x

private theorem profile_pair_weighted {k s : ℝ} (hk : 0 < k) (hs : 0 ≤ s) (hx : s ≤ Real.log k) :
    twoShiftSymmetricProfile (k * Real.exp (-s)) + twoShiftSymmetricProfile (k⁻¹ * Real.exp (-s)) =
      Real.exp (-(51 / 50) * Real.log k) * weightedShiftPoly s (Real.log k) := by
  conv_lhs => rw [← Real.exp_log hk, ← Real.exp_neg]
  unfold weightedShiftPoly twoShiftSymmetricProfile
  rw [← Real.exp_add, ← Real.exp_add, Real.log_exp, Real.log_exp,
    abs_of_nonneg (by linarith only [hx]), abs_of_nonpos (by linarith only [hs, hx])]
  dsimp only
  rw [show -(51 / 50 : ℝ) * (Real.log k + -s) = -(51 / 50) * Real.log k + (51 / 50) * s by ring,
    show -(51 / 50 : ℝ) * -(-Real.log k + -s) = -(51 / 50) * Real.log k + -(51 / 50) * s by ring,
    Real.exp_add, Real.exp_add]
  ring

private theorem weighted_euler_term {k : ℕ} (hk : 0 < k) (hl : 3 ≤ Real.log k) (u v : ℝ) :
    let P := fun s : ℝ ↦
      twoShiftSymmetricProfile ((k : ℝ) * Real.exp (-s)) +
        twoShiftSymmetricProfile ((k : ℝ)⁻¹ * Real.exp (-s))
    ArithmeticFunction.vonMangoldt k / Real.sqrt k *
        (u * P (14 / 5) - v * P 3 - ((u ^ 2 + v ^ 2) / 2) * P 0 + (u * v) * P (1 / 5)) =
      -(ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ (38 / 25 : ℝ) *
          weightedEulerPoly u v (Real.log k)) := by
  intro P
  have hp : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  dsimp only [P]
  rw [profile_pair_weighted hp (by norm_num only) (by linarith only [hl]),
    profile_pair_weighted hp (by norm_num only) hl,
    profile_pair_weighted hp (le_refl 0) (by linarith only [hl]),
    profile_pair_weighted hp (by norm_num only) (by linarith only [hl])]
  have hd : (k : ℝ) ^ (38 / 25 : ℝ) = (k : ℝ) ^ (1 / 2 : ℝ) * (k : ℝ) ^ (51 / 50 : ℝ) := by
    rw [← Real.rpow_add hp]
    norm_num only
  rw [mul_comm (-(51 / 50)) (Real.log k), ← Real.rpow_def_of_pos hp, Real.rpow_neg hp.le,
    Real.sqrt_eq_rpow, hd]
  simp only [weightedEulerPoly, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Above a cutoff of at least 85264, the four weighted Euler tails combine
into the negative trace-deficit sum with the section 101 polynomial. -/
theorem twoShift_weighted_euler_eq {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 85264 ≤ X) (u v : ℝ) :
    let S := twoShiftCosineTail a b c X
    u * S (14 / 5) - v * S 3 - ((u ^ 2 + v ^ 2) / 2) * S 0 + (u * v) * S (1 / 5) =
      -(∑' k : { n : ℕ // ⌊X⌋₊ < n },
          (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
            (ArithmeticFunction.vonMangoldt k.val / (k.val : ℝ) ^ (38 / 25 : ℝ) *
              weightedEulerPoly u v (Real.log k.val))) := by
  intro S
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
  have hx : Real.exp 3 ≤ X := by
    rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [he, hX]
  dsimp only [S]
  rw [twoShift_weighted_tail, ← tsum_neg]
  apply tsum_congr
  intro k
  have hk : 0 < k.val := (Nat.zero_le _).trans_lt k.property
  have hl :=
    (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hk)).mpr (hx.trans (Nat.lt_of_floor_lt k.property).le)
  rw [mul_assoc, weighted_euler_term hk hl, mul_neg]

end PseudoPrime.PrimeTestBounds.MillerRabin
