/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftReflected

/-! # Seven radius intervals for the two-frequency remainder -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem cap_certificate (A lo hi P Q : ℚ) (j : ℕ) (m b e cap : ℝ)
    (hlog : Analysis.rationalLogIntervalCheck A j 24 lo hi = true)
    (hp : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck A 0 P 13 25 = true)
    (hq : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck A 0 Q 51 50 = true)
    (hA : 0 < (A : ℝ)) (hl : 4 ≤ (lo : ℝ))
    (hm :
      (711631 * Analysis.logPowerTailPoly (13 / 25) 0 hi -
              619250 * Analysis.logPowerTailPoly (13 / 25) 1 lo +
            126937 * Analysis.logPowerTailPoly (13 / 25) 2 hi) /
          1000000 ≤
        m)
    (hb :
      (hi : ℝ) ^ 2 / 24 * ((26562 + 39625 * ((hi : ℝ) - 4) + 12694 * ((hi : ℝ) - 4) ^ 2) / 100000) ≤
        b)
    (he :
      (70873 * Analysis.logPowerTailPoly (51 / 50) 2 hi -
              49797 * Analysis.logPowerTailPoly (51 / 50) 3 lo +
            8040 * Analysis.logPowerTailPoly (51 / 50) 4 hi) /
          1000000 ≤
        e)
    (hm0 : 0 ≤ m) (hbe : 0 ≤ b + e) (hc : (P : ℝ) * m + Q * (b + e) ≤ cap) :
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      cap := by
  have hlh := Analysis.rationalLogIntervalCheck_sound hlog
  have hP := (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hp).2
  have hQ := (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hq).2
  norm_num only [Nat.cast_ofNat] at hP hQ
  exact (twoShiftEuler_cap_box hA hl hlh.1 hlh.2 hP hQ hm hb he hm0 hbe).trans hc

private theorem cap_1169_4 :
    let A := ((1169 / 4) : ℝ) ^ 2
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      (819349 / 10000000) := by
  intro A
  have hA : A = ((1366561 / 16) : ℚ) := by norm_num only [A, Rat.cast_div, Rat.cast_ofNat]
  rw [hA]
  apply
    cap_certificate (1366561 / 16) (1135521919 / 100000000) (1135521931 / 100000000)
      (2726561509 / 1000000000000) (932955179 / 100000000000000) 16 (2949838 / 100000)
      (5398055 / 100000) (10740208 / 100000)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals norm_num only [Analysis.logPowerTailPoly, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]

private theorem cap_294 :
    let A := (294 : ℝ) ^ 2
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      (25499 / 312500) := by
  intro A
  have hA : A = (86436 : ℚ) := by norm_num only [A, Rat.cast_div, Rat.cast_ofNat]
  rw [hA]
  apply
    cap_certificate 86436 (22734319 / 2000000) (28417899 / 2500000) (338710601 / 125000000000)
      (1843323 / 200000000000) 16 (2956159 / 100000) (5423973 / 100000) (10787629 / 100000)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals norm_num only [Analysis.logPowerTailPoly, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]

private theorem cap_299 :
    let A := (299 : ℝ) ^ 2
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      (806487 / 10000000) := by
  intro A
  have hA : A = (89401 : ℚ) := by norm_num only [A, Rat.cast_div, Rat.cast_ofNat]
  rw [hA]
  apply
    cap_certificate 89401 (114008871 / 10000000) (14251109 / 1250000) (2662575701 / 1000000000000)
      (445246773 / 50000000000000) 16 (594811 / 20000) (5497689 / 100000) (2184487 / 20000)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals norm_num only [Analysis.logPowerTailPoly, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]

private theorem cap_300 :
    let A := (300 : ℝ) ^ 2
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      (402311 / 5000000) := by
  intro A
  have hA : A = (90000 : ℚ) := by norm_num only [A, Rat.cast_div, Rat.cast_ofNat]
  rw [hA]
  apply
    cap_certificate 90000 (114075649 / 10000000) (2281513 / 200000) (1326673027 / 500000000000)
      (176889737 / 20000000000000) 16 (595521 / 20000) (1378093 / 25000) (437971 / 4000)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals norm_num only [Analysis.logPowerTailPoly, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]

private theorem cap_307 :
    let A := (307 : ℝ) ^ 2
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      (791837 / 10000000) := by
  intro A
  have hA : A = (94249 : ℚ) := by norm_num only [A, Rat.cast_div, Rat.cast_ofNat]
  rw [hA]
  apply
    cap_certificate 94249 (57268477 / 5000000) (22907391 / 2000000) (1295227611 / 500000000000)
      (84379649 / 10000000000000) 17 (1501093 / 50000) (1122921 / 20000) (2784011 / 25000)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals norm_num only [Analysis.logPowerTailPoly, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]

private theorem cap_350 :
    let A := (350 : ℝ) ^ 2
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      (361269 / 5000000) := by
  intro A
  have hA : A = (122500 : ℚ) := by norm_num only [A, Rat.cast_div, Rat.cast_ofNat]
  rw [hA]
  apply
    cap_certificate 122500 (117158663 / 10000000) (14644833 / 1250000) (2260316389 / 1000000000000)
      (645804683 / 100000000000000) 17 (3143861 / 100000) (248909 / 4000) (1224341 / 10000)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  all_goals norm_num only [Analysis.logPowerTailPoly, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]

/-- The signed finite remainder with the normalized reflected majorant for three odd levels. -/
@[expose]
noncomputable def twoShiftSignedRemainder (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (R X : ℝ) : ℝ :=
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let f := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) +
      twoShiftConductor (2 * Real.log R) +
      twoShiftReciprocalCoeff / R -
    2 * ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) * twoShiftReflectedTail X)

/-- Under RH the signed remainder exceeds -13 / 100 throughout the closed radius
interval from 292 to 299. Each Euler cap is certified at the left endpoint. -/
theorem twoShiftRemainder_low (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p) (hq : Odd q)
    (hr : Odd r) {R X : ℝ} (hlo : 292 ≤ R) (hhi : R ≤ 299) (hX : R ^ 2 ≤ X)
    (hRH : RiemannHypothesis) : (-13 / 100 : ℝ) < twoShiftSignedRemainder p q r hp hq hr R X := by
  by_cases h₀ : R ≤ 1169 / 4
  · exact pair_twoShift_first_interval p q r hp hq hr hlo h₀ hX hRH
  by_cases h1 : R ≤ 294
  · have hu : (1169 / 4 : ℝ) ≤ R := by linarith only [h₀]
    have h :=
      pair_twoShift_interval_remainder p q r hp hq hr (by norm_num only : (292 : ℝ) ≤ 1169 / 4) hu
        h1 hX hRH
    have hc := twoShiftConductor_lower (r := 1169 / 4) (by norm_num only)
    have he := cap_1169_4
    dsimp only at h he
    unfold twoShiftSignedRemainder
    linarith only [h, hc, he]
  have hu : (294 : ℝ) ≤ R := by linarith only [h1]
  have h :=
    pair_twoShift_interval_remainder p q r hp hq hr (by norm_num only : (292 : ℝ) ≤ 294) hu hhi hX
      hRH
  have hc := twoShiftConductor_lower (r := 294) (by norm_num only)
  have he := cap_294
  dsimp only at h he
  unfold twoShiftSignedRemainder
  linarith only [h, hc, he]

/-- Under RH the signed remainder exceeds -1 / 8 throughout the closed radius
interval from 299 to 475. Each Euler cap is certified at the left endpoint. -/
theorem twoShiftRemainder_middle (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {R X : ℝ} (hlo : 299 ≤ R) (hhi : R ≤ 475) (hX : R ^ 2 ≤ X)
    (hRH : RiemannHypothesis) : (-1 / 8 : ℝ) < twoShiftSignedRemainder p q r hp hq hr R X := by
  by_cases h1 : R ≤ 300
  · have hu : (299 : ℝ) ≤ R := by linarith only [hlo]
    have h :=
      pair_twoShift_interval_remainder p q r hp hq hr (by norm_num only : (292 : ℝ) ≤ 299) hu h1 hX
        hRH
    have hc := twoShiftConductor_lower_299 (r := 299) (by norm_num only)
    have he := cap_299
    dsimp only at h he
    unfold twoShiftSignedRemainder
    linarith only [h, hc, he]
  by_cases h2 : R ≤ 307
  · have hu : (300 : ℝ) ≤ R := by linarith only [h1]
    have h :=
      pair_twoShift_interval_remainder p q r hp hq hr (by norm_num only : (292 : ℝ) ≤ 300) hu h2 hX
        hRH
    have hc := twoShiftConductor_lower_299 (r := 300) (by norm_num only)
    have he := cap_300
    dsimp only at h he
    unfold twoShiftSignedRemainder
    linarith only [h, hc, he]
  by_cases h3 : R ≤ 350
  · have hu : (307 : ℝ) ≤ R := by linarith only [h2]
    have h :=
      pair_twoShift_interval_remainder p q r hp hq hr (by norm_num only : (292 : ℝ) ≤ 307) hu h3 hX
        hRH
    have hc := twoShiftConductor_lower_299 (r := 307) (by norm_num only)
    have he := cap_307
    dsimp only at h he
    unfold twoShiftSignedRemainder
    linarith only [h, hc, he]
  have hu : (350 : ℝ) ≤ R := by linarith only [h3]
  have h :=
    pair_twoShift_interval_remainder p q r hp hq hr (by norm_num only : (292 : ℝ) ≤ 350) hu hhi hX
      hRH
  have hc := twoShiftConductor_lower_299 (r := 350) (by norm_num only)
  have he := cap_350
  dsimp only at h he
  unfold twoShiftSignedRemainder
  linarith only [h, hc, he]

/-- Under RH the signed remainder exceeds −1/8 on the entire half-line from 299. -/
theorem twoShiftRemainder_from299 (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {R X : ℝ} (hR : 299 ≤ R) (hX : R ^ 2 ≤ X) (hRH : RiemannHypothesis) :
    (-1 / 8 : ℝ) < twoShiftSignedRemainder p q r hp hq hr R X := by
  by_cases h : R ≤ 475
  · exact twoShiftRemainder_middle p q r hp hq hr hR h hX hRH
  have hl : 950 ≤ 2 * R := by linarith only [h]
  have hc : (2 * R) ^ 2 / 4 ≤ X := by linarith only [hX]
  have ht := pair_twoShift_reflected_remainder p q r hp hq hr hl hc hRH
  dsimp only at ht
  rw [show 2 * R / 2 = R by ring] at ht
  exact ht

/-- Under RH the signed remainder exceeds −0.13 for every radius at least 292. -/
theorem twoShiftRemainder_from292 (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {R X : ℝ} (hR : 292 ≤ R) (hX : R ^ 2 ≤ X) (hRH : RiemannHypothesis) :
    (-13 / 100 : ℝ) < twoShiftSignedRemainder p q r hp hq hr R X := by
  by_cases h : R ≤ 299
  · exact twoShiftRemainder_low p q r hp hq hr hR h hX hRH
  exact
    lt_trans (by norm_num only : (-13 / 100 : ℝ) < -1 / 8)
      (twoShiftRemainder_from299 p q r hp hq hr (le_of_not_ge h) hX hRH)

/-- The explicit phase-recovery lower expression exceeds 0.000988 times the radius
throughout the half-line in (96.4), using the conductor coefficient and signed remainder. -/
theorem twoShiftPhase_lower (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p) (hq : Odd q)
    (hr : Odd r) {R X : ℝ} (hR : 292 ≤ R) (hX : R ^ 2 ≤ X) (hRH : RiemannHypothesis) :
    (988 / 1000000 : ℝ) * R <
      twoShiftPhaseCoeff * R + twoShiftSignedRemainder p q r hp hq hr R X := by
  have hc := mul_lt_mul_of_pos_right twoShiftPhaseCoeff_lower (show 0 < R by linarith only [hR])
  linarith only [hc, hR, twoShiftRemainder_from292 p q r hp hq hr hR hX hRH]

end PseudoPrime.PrimeTestBounds.MillerRabin
