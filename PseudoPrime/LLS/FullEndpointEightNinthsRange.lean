/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEightyOneRange

/-! # A tighter logarithmic chord for finite-scale endpoint witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For 8<=y<=18 the endpoint polynomial at L=(9/8)y is positive on the
tighter logarithmic lower line 81y/1000+1431/1000. Shift by eight and bound
the quadratic using the interval length; retain the nonnegative higher powers. -/
theorem fullEndpoint_eightNinths_base_pos {y : ℝ} (ha : (8 : ℝ) ≤ y) (hb : y ≤ (18 : ℝ)) :
    0 <
      fullEndpointPolynomial ((9 / 8 : ℝ) * y) (2096 / 1831) y
        ((81 / 1000 : ℝ) * y + 1431 / 1000) := by
  have ht : 0 ≤ y - 8 := by linarith only [ha]
  have hu : y - 8 ≤ (10 : ℝ) := by linarith only [hb]
  have hs : (y - 8) ^ 2 ≤ (10 : ℝ) * (y - 8) := by nlinarith only [ht, hu]
  dsimp only [fullEndpointPolynomial]
  nlinarith only [ht, hu, hs, pow_nonneg ht 3, pow_nonneg ht 4]

/-- For 8<=y<=18, log y is at least 81y/1000+1431/1000. Use concavity and
the certified logarithms of two and three at both endpoints. This improves
the older chord over the smaller finite-scale radius interval. -/
theorem fullEndpoint_log_chord_eight_eighteen {y : ℝ} (ha : 8 ≤ y) (hb : y ≤ 18) :
    (81 / 1000 : ℝ) * y + 1431 / 1000 ≤ Real.log y := by
  have h8 : (2079 / 1000 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have h18 : (2889 / 1000 : ℝ) ≤ Real.log 18 := by
    rw [show (18 : ℝ) = 2 * 3 ^ 2 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (3 : ℝ) ^ 2 ≠ 0),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hwa : 0 ≤ (18 - y) / 10 := div_nonneg (sub_nonneg.mpr hb) (by norm_num only)
  have hwb : 0 ≤ (y - 8) / 10 := div_nonneg (sub_nonneg.mpr ha) (by norm_num only)
  have hw : (18 - y) / 10 + (y - 8) / 10 = 1 := by ring
  have hc :=
    strictConcaveOn_log_Ioi.concaveOn.2 (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num only [Set.mem_Ioi])
      (show (18 : ℝ) ∈ Set.Ioi 0 by norm_num only [Set.mem_Ioi]) hwa hwb hw
  simp only [smul_eq_mul] at hc
  have he : (18 - y) / 10 * 8 + (y - 8) / 10 * 18 = y := by ring
  rw [he] at hc
  have hA := mul_le_mul_of_nonneg_left h8 hwa
  have hB := mul_le_mul_of_nonneg_left h18 hwb
  linarith only [hc, hA, hB]

/-- The coefficient of a logarithm shift in the full endpoint polynomial.
Inputs are conductor log L, pi-log endpoint P, radius y and log value z.
The exact shift identity uses this coefficient before any positivity estimate. -/
noncomputable def fullEndpointLogSlope (L P y z : ℝ) : ℝ :=
  -(y - 1) ^ 2 * (L + 1089 / 500) -
      2 * ((1 / 2 : ℝ) * (y ^ 2 - 1) * (L - P) + (26551 / 20000 : ℝ) * y ^ 2) +
    4 * (y + 1) * y ^ 2 +
    8 * y ^ 2 * z

/-- For arbitrary real parameters, shifting the logarithm by t changes the
endpoint polynomial by t times its named slope plus 4y^2t^2. Expand and
normalize algebraically. This permits reuse with other chord certificates. -/
theorem fullEndpointPolynomial_log_shift (L P y z t : ℝ) :
    fullEndpointPolynomial L P y (z + t) =
      fullEndpointPolynomial L P y z + t * fullEndpointLogSlope L P y z + 4 * y ^ 2 * t ^ 2 := by
  dsimp only [fullEndpointPolynomial, fullEndpointLogSlope]
  ring

/-- For 8<=y<=18 and z above the tighter chord, the endpoint polynomial at
L=(9/8)y is positive. The slope is nonnegative and the quadratic log slack
is nonnegative. This removes any upper bound on the actual radius logarithm. -/
theorem fullEndpoint_eightNinths_polynomial_pos {y z : ℝ} (ha : 8 ≤ y) (hb : y ≤ 18)
    (hz : (81 / 1000 : ℝ) * y + 1431 / 1000 ≤ z) :
    0 < fullEndpointPolynomial ((9 / 8 : ℝ) * y) (2096 / 1831) y z := by
  let a := (81 / 1000 : ℝ) * y + 1431 / 1000
  have hp := fullEndpoint_eightNinths_base_pos ha hb
  have hy0 : 0 ≤ y := by linarith only [ha]
  have hc : 0 ≤ fullEndpointLogSlope ((9 / 8 : ℝ) * y) (2096 / 1831) y a := by
    dsimp only [fullEndpointLogSlope, a]
    nlinarith only [ha, pow_nonneg hy0 3, sq_nonneg y]
  have hm := mul_nonneg (sub_nonneg.mpr hz) hc
  have hs :=
    mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (sq_nonneg y)) (sq_nonneg (z - a))
  have he := fullEndpointPolynomial_log_shift ((9 / 8 : ℝ) * y) (2096 / 1831) y a (z - a)
  rw [add_sub_cancel] at he
  dsimp only [a] at hm hs he
  linarith only [hp, hm, hs, he]

/-- For every real 9<=L<=81/4 the endpoint polynomial at y=(8/9)L is positive.
Insert the radius interval and the tighter log chord. This certifies a
continuous interval without enumerating integer moduli. -/
theorem fullEndpoint_polynomial_pos_eightNinths_log_interval {L : ℝ} (hL : 9 ≤ L)
    (hU : L ≤ (81 / 4 : ℝ)) :
    0 < fullEndpointPolynomial L (2096 / 1831) ((8 / 9 : ℝ) * L) (Real.log ((8 / 9 : ℝ) * L)) := by
  let y := (8 / 9 : ℝ) * L
  have ha : (8 : ℝ) ≤ y := by
    dsimp only [y]; linarith only [hL]
  have hb : y ≤ (18 : ℝ) := by
    dsimp only [y]; linarith only [hU]
  have hp :=
    fullEndpoint_eightNinths_polynomial_pos ha hb (fullEndpoint_log_chord_eight_eighteen ha hb)
  have he : (9 / 8 : ℝ) * y = L := by
    dsimp only [y]; ring
  rw [he] at hp
  exact hp

/-- For a nonprincipal character under GRH and 9<=log q<=81/4, a prime p
with value different from one exists through (64/81)(log q)^2. Apply the
original-level endpoint criterion. Nonunit and even primes remain admissible. -/
theorem exists_prime_ne_one_le_eightNinths_log_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 9 ≤ Real.log q) (hU : Real.log q ≤ (81 / 4 : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log q) ^ 2 ∧ χ p ≠ 1 := by
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_fullEndpointPolynomial_original χ hne hGRH
      (by linarith only [hL] : (8 : ℝ) ≤ (8 / 9 : ℝ) * Real.log q)
      (fullEndpoint_polynomial_pos_eightNinths_log_interval hL hU)
  exact ⟨p, hp, by nlinarith only [hb], hv⟩

/-- For positive L the coefficient-64/81 bound is strictly smaller than the
coefficient-81/100 bound. Multiply the rational coefficient inequality by L^2.
This supplies the comparison on the common applicability interval. -/
theorem fullEndpoint_eightNinths_lt_eightyOne {L : ℝ} (hL : 0 < L) :
    (64 / 81 : ℝ) * L ^ 2 < (81 / 100 : ℝ) * L ^ 2 := by
  exact mul_lt_mul_of_pos_right (by norm_num only : (64 / 81 : ℝ) < 81 / 100) (sq_pos_of_pos hL)

end PseudoPrime.LLS.PaperStatements
