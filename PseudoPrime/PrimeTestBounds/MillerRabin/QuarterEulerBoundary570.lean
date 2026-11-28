/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMoments570
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion

/-! # Boundary estimates for the finite section 31 Euler tail -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A certified dyadic logarithm enclosure at the lower cutoff controls its polynomial factors. -/
private theorem log2701_bounds :
    7901377 / 1000000 ≤ Real.log 2701 ∧ Real.log 2701 ≤ 7901378 / 1000000 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 2701) (j := 11) (n := 32) (lo :=
      7901377 / 1000000) (hi := 7901378 / 1000000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at h
  exact ⟨h.1, by linarith only [h.2]⟩

/-- At 2701 the section 31 density is bounded by rational power and logarithm enclosures. -/
private theorem density2701_upper : eulerDensity570 2701 ≤ 701 / 10000000 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 38) (d :=
        25) (lo := 0) (hi := 608251 / 100000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  unfold eulerDensity570
  have hp : (2701 : ℝ) ^ (-(38 / 25 : ℝ)) ≤ 608251 / 100000000000 := by simpa only [neg_div] using h
  calc
    _ ≤
        (608251 / 100000000000 : ℝ) *
          (3 / 8 + 153 / 400 * (7901378 / 1000000) + 2601 / 20000 * (7901378 / 1000000) ^ 2) :=
      by gcongr <;> exact log2701_bounds.2
    _ ≤ _ := by norm_num only

/-- The finite psi certificate and the Euler density bound control the lower boundary at 2701. -/
theorem euler570_boundary_2701 :
    (Chebyshev.psi 2701 - 2701) * eulerDensity570 2701 ≤ 292 / 100000 := by
  have he :=
    (abs_le.mp
        (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
          (by norm_num only : (1423 : ℝ) ≤ 2701) (by norm_num only))).2
  have hs : Real.sqrt 2701 ≤ 52 := (Real.sqrt_le_iff).2 ⟨by norm_num only, by norm_num only⟩
  have hf : 0 ≤ eulerDensity570 2701 := by
    unfold eulerDensity570; positivity
  have h :=
    mul_le_mul (he.trans (mul_le_mul_of_nonneg_left hs (by norm_num only))) density2701_upper hf
      (by norm_num only)
  linarith only [h]

/-- The logarithm of the upper endpoint is bounded using the certified logarithm of ten. -/
private theorem log_large_upper : Real.log ((10 : ℝ) ^ 50) ≤ 150 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10) (j := 3) (n := 8) (lo := 0) (hi := 3)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Nat.cast_ofNat] at h
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h]

/-- At the truncation point ten to the fiftieth, the RH psi bound and power decay limit
the negative Euler boundary contribution to one millionth. -/
theorem euler570_boundary_large (hRH : RiemannHypothesis) :
    -(1 / 1000000 : ℝ) ≤ (Chebyshev.psi ((10 : ℝ) ^ 50) - 10 ^ 50) * eulerDensity570 (10 ^ 50) := by
  let b : ℝ := 10 ^ 50
  have hb : 1000000 ≤ b := by
    dsimp only [b]; norm_num only
  have he := (abs_le.mp (euler570_psi_high hRH hb)).1
  have hs : Real.sqrt b ≤ 10 ^ 25 :=
    Real.sqrt_le_iff.mpr
      ⟨by norm_num only, by
        dsimp only [b]; norm_num only⟩
  have hl : Real.log b ≤ 150 := log_large_upper
  have hn : 0 ≤ Real.log b :=
    Real.log_nonneg
      (by
        dsimp only [b]; norm_num only)
  have hp : b ^ (-(38 / 25 : ℝ)) = (10 : ℝ) ^ (-76 : ℝ) := by
    dsimp only [b]
    rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 10)]
    norm_num only
  have hd :
    eulerDensity570 b ≤
      (10 : ℝ) ^ (-76 : ℤ) * (3 / 8 + 153 / 400 * 150 + 2601 / 20000 * 150 ^ 2) := by
    unfold eulerDensity570
    rw [hp, ← Real.rpow_intCast]
    gcongr <;> norm_num only [Int.cast_neg, Int.cast_ofNat]
  have hf : 0 ≤ eulerDensity570 b := by
    unfold eulerDensity570; positivity
  have hE : Real.sqrt b * (Real.log b ^ 2 / 24) ≤ (10 : ℝ) ^ 25 * (150 ^ 2 / 24) := by gcongr
  have h := mul_le_mul hE hd hf (by norm_num only)
  have hh := mul_le_mul_of_nonneg_right he hf
  change _ ≤ (Chebyshev.psi b - b) * eulerDensity570 b
  linarith only [hh, h]

/-- The endpoint expression for the main integral, formed from its three logarithmic moments. -/
noncomputable def eulerMainTail570 (x : ℝ) : ℝ :=
  3 / 8 * eulerMomentValue570 (13 / 25) 0 x + 153 / 400 * eulerMomentValue570 (13 / 25) 1 x +
    2601 / 20000 * eulerMomentValue570 (13 / 25) 2 x

/-- Subtract the two main endpoint expressions to obtain the exact main integral. -/
private theorem mainDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, eulerDensity570 t) = eulerMainTail570 a - eulerMainTail570 b := by
  rw [euler570_main_interval ha hab, Fin.sum_univ_three]
  unfold eulerMainTail570
  change
    (3 / 8 : ℝ) * (eulerMomentValue570 (13 / 25) 0 a - eulerMomentValue570 (13 / 25) 0 b) +
        (153 / 400 : ℝ) * (eulerMomentValue570 (13 / 25) 1 a - eulerMomentValue570 (13 / 25) 1 b) +
        (2601 / 20000 : ℝ) *
          (eulerMomentValue570 (13 / 25) 2 a - eulerMomentValue570 (13 / 25) 2 b) =
      _
  ring

/-- The endpoint expression for the finite square-root error envelope. -/
noncomputable def eulerLowError570 (x : ℝ) : ℝ :=
  3 / 20 * eulerMomentValue570 (51 / 50) 0 x + 3213 / 12500 * eulerMomentValue570 (51 / 50) 1 x +
    49419 / 312500 * eulerMomentValue570 (51 / 50) 2 x

/-- Subtract the finite-error endpoint expressions to evaluate the low error integral. -/
private theorem lowDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, (4 / 5 : ℝ) * Real.sqrt t * -eulerSlope570 t) =
      eulerLowError570 a - eulerLowError570 b := by
  rw [euler570_low_interval ha hab, Fin.sum_univ_three]
  unfold eulerLowError570
  change
    ((4 / 5 : ℝ) * (3 / 16)) *
          (eulerMomentValue570 (51 / 50) 0 a - eulerMomentValue570 (51 / 50) 0 b) +
        ((4 / 5 : ℝ) * (3213 / 10000)) *
          (eulerMomentValue570 (51 / 50) 1 a - eulerMomentValue570 (51 / 50) 1 b) +
        ((4 / 5 : ℝ) * (49419 / 250000)) *
          (eulerMomentValue570 (51 / 50) 2 a - eulerMomentValue570 (51 / 50) 2 b) =
      _
  ring

/-- The endpoint expression for the RH logarithmic error envelope. -/
noncomputable def eulerHighError570 (x : ℝ) : ℝ :=
  1 / 128 * eulerMomentValue570 (51 / 50) 2 x + 1071 / 80000 * eulerMomentValue570 (51 / 50) 3 x +
    16473 / 2000000 * eulerMomentValue570 (51 / 50) 4 x

/-- Subtract the RH-error endpoint expressions to evaluate the high error integral. -/
private theorem highDiff {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -eulerSlope570 t) =
      eulerHighError570 a - eulerHighError570 b := by
  rw [euler570_high_interval ha hab, Fin.sum_univ_three]
  unfold eulerHighError570
  change
    ((1 / 24 : ℝ) * (3 / 16)) *
          (eulerMomentValue570 (51 / 50) 2 a - eulerMomentValue570 (51 / 50) 2 b) +
        ((1 / 24 : ℝ) * (3213 / 10000)) *
          (eulerMomentValue570 (51 / 50) 3 a - eulerMomentValue570 (51 / 50) 3 b) +
        ((1 / 24 : ℝ) * (49419 / 250000)) *
          (eulerMomentValue570 (51 / 50) 4 a - eulerMomentValue570 (51 / 50) 4 b) =
      _
  ring

/-- Upper enclosures for the power and logarithm bound their nonnegative moment product. -/
private theorem momentUpper {d x p z : ℝ} (k : ℕ) (hd : 0 < d) (hx : 1 ≤ x) (hp : x ^ (-d) ≤ p)
    (hz : Real.log x ≤ z) : eulerMomentValue570 d k x ≤ p * Analysis.logPowerTailPoly d k z := by
  exact
    mul_le_mul hp (Analysis.log_power_tail_poly_mono hd (Real.log_nonneg hx) hz k)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg hx) k)
      ((Real.rpow_nonneg (zero_le_one.trans hx) _).trans hp)

/-- Lower enclosures for the power and logarithm bound their nonnegative moment product. -/
private theorem momentLower {d x p z : ℝ} (k : ℕ) (hd : 0 < d) (hx : 1 ≤ x) (hp : p ≤ x ^ (-d))
    (hz0 : 0 ≤ z) (hz : z ≤ Real.log x) :
    p * Analysis.logPowerTailPoly d k z ≤ eulerMomentValue570 d k x := by
  exact
    mul_le_mul hp (Analysis.log_power_tail_poly_mono hd hz0 hz k)
      (Analysis.log_power_tail_poly_nonneg hd hz0 k) (Real.rpow_nonneg (zero_le_one.trans hx) _)

/-- Certified power and logarithm bounds give the main contribution at 2701. -/
private theorem mainLower : 54234 / 100000 ≤ eulerMainTail570 2701 := by
  have hp : 16428851 / 1000000000 ≤ (2701 : ℝ) ^ (-(13 / 25 : ℝ)) := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 13) (d :=
          25) (lo := 16428851 / 1000000000) (hi := 1) (by decide +kernel)).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    linarith only [h]
  have hz : 7901377 / 1000000 ≤ Real.log 2701 := log2701_bounds.1
  have h0 :=
    momentLower 0 (by norm_num only : (0 : ℝ) < 13 / 25) (by norm_num only : (1 : ℝ) ≤ 2701) hp
      (by norm_num only) hz
  have h1 :=
    momentLower 1 (by norm_num only : (0 : ℝ) < 13 / 25) (by norm_num only : (1 : ℝ) ≤ 2701) hp
      (by norm_num only) hz
  have h2 :=
    momentLower 2 (by norm_num only : (0 : ℝ) < 13 / 25) (by norm_num only : (1 : ℝ) ≤ 2701) hp
      (by norm_num only) hz
  unfold eulerMainTail570
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at h0 h1 h2
  linarith only [h0, h1, h2]

/-- Certified power and logarithm bounds control the square-root error at 2701. -/
private theorem lowUpper : eulerLowError570 2701 ≤ 4668 / 1000000 := by
  have hp : (2701 : ℝ) ^ (-(51 / 50 : ℝ)) ≤ 316115 / 1000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 2701) (p := 51) (d :=
          50) (lo := 0) (hi := 316115 / 1000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    linarith only [h]
  have hz : Real.log 2701 ≤ 7901378 / 1000000 := log2701_bounds.2
  have h0 :=
    momentUpper 0 (by norm_num only : (0 : ℝ) < 51 / 50) (by norm_num only : (1 : ℝ) ≤ 2701) hp hz
  have h1 :=
    momentUpper 1 (by norm_num only : (0 : ℝ) < 51 / 50) (by norm_num only : (1 : ℝ) ≤ 2701) hp hz
  have h2 :=
    momentUpper 2 (by norm_num only : (0 : ℝ) < 51 / 50) (by norm_num only : (1 : ℝ) ≤ 2701) hp hz
  unfold eulerLowError570
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at h0 h1 h2
  linarith only [h0, h1, h2]

/-- The logarithm of ten bounds the RH error polynomial at one million. -/
theorem eulerHighError_million_le : eulerHighError570 1000000 ≤ 33605 / 100000000 := by
  have hp : (1000000 : ℝ) ^ (-(51 / 50 : ℝ)) ≤ 75858 / 100000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 51)
          (d := 50) (lo := 0) (hi := 75858 / 100000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    linarith only [h]
  have hz : Real.log 1000000 ≤ 13816 / 1000 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 10) (j := 3) (n := 16) (lo := 0) (hi :=
          23026 / 10000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at h
    rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [h]
  have h0 :=
    momentUpper 2 (by norm_num only : (0 : ℝ) < 51 / 50) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  have h1 :=
    momentUpper 3 (by norm_num only : (0 : ℝ) < 51 / 50) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  have h2 :=
    momentUpper 4 (by norm_num only : (0 : ℝ) < 51 / 50) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  unfold eulerHighError570
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at h0 h1 h2
  linarith only [h0, h1, h2]

private theorem highUpper : eulerHighError570 1000000 ≤ 337 / 1000000 :=
  eulerHighError_million_le.trans (by norm_num only)

/-- The exact power at the truncation point bounds the omitted main integral. -/
private theorem mainUpper : eulerMainTail570 ((10 : ℝ) ^ 50) ≤ 1 / 1000000 := by
  have hp : (((10 : ℝ) ^ 50) : ℝ) ^ (-(13 / 25 : ℝ)) ≤ 1 / (10 ^ 26) := by
    rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 10)]
    norm_num only
  have hz : Real.log ((10 : ℝ) ^ 50) ≤ 150 := log_large_upper
  have h0 :=
    momentUpper 0 (by norm_num only : (0 : ℝ) < 13 / 25)
      (by norm_num only : (1 : ℝ) ≤ ((10 : ℝ) ^ 50)) hp hz
  have h1 :=
    momentUpper 1 (by norm_num only : (0 : ℝ) < 13 / 25)
      (by norm_num only : (1 : ℝ) ≤ ((10 : ℝ) ^ 50)) hp hz
  have h2 :=
    momentUpper 2 (by norm_num only : (0 : ℝ) < 13 / 25)
      (by norm_num only : (1 : ℝ) ≤ ((10 : ℝ) ^ 50)) hp hz
  unfold eulerMainTail570
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at h0 h1 h2
  linarith only [h0, h1, h2]

/-- Endpoint moments are nonnegative above one by positivity of the tail polynomial. -/
private theorem moment_nonneg {d x : ℝ} (hd : 0 < d) (hx : 1 ≤ x) (k : ℕ) :
    0 ≤ eulerMomentValue570 d k x := by
  exact
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg hx) k)

/-- Under RH, the section 31 Euler mass is at least 3.7275. Sum through ten to the fiftieth,
combine the two Abel intervals and their boundary estimates, then use positivity of the tail. -/
theorem euler570_total_lower (hRH : RiemannHypothesis) :
    37275 / 10000 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  let b : ℝ := 10 ^ 50
  have hb : 1000000 ≤ b := by
    dsimp only [b]; norm_num only
  have h := euler570_tail_split hRH hb
  dsimp only at h
  rw [mainDiff (by norm_num only) (by norm_num only), mainDiff (by norm_num only) hb,
    lowDiff (by norm_num only) (by norm_num only), highDiff (by norm_num only) hb] at h
  have hm (k : ℕ) :=
    moment_nonneg (by norm_num only : 0 < (51 / 50 : ℝ)) (show 1 ≤ b by linarith only [hb]) k
  have hv (k : ℕ) :=
    moment_nonneg (by norm_num only : 0 < (51 / 50 : ℝ)) (by norm_num only : (1 : ℝ) ≤ 1000000) k
  have hl : 0 ≤ eulerLowError570 1000000 := by
    unfold eulerLowError570
    linarith only [hv 0, hv 1, hv 2]
  have hh : 0 ≤ eulerHighError570 b := by
    unfold eulerHighError570; linarith only [hm 2, hm 3, hm 4]
  have ht :
    (1335906798741 / 2500000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc ⌊(2701 : ℝ)⌋₊ ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
    dsimp only [b] at h hh ⊢
    calc
      _ ≤
          (54234 / 100000 : ℝ) - 1 / 1000000 - 1 / 1000000 - 292 / 100000 - 4668 / 1000000 -
            337 / 1000000 :=
        by norm_num only
      _ ≤ _ := by
        linear_combination
          h + mainLower + mainUpper + lowUpper + highUpper + hl + hh + euler570_boundary_2701 +
            euler570_boundary_large hRH
  apply euler570_total_of_interval (N := ⌊b⌋₊)
  · exact
      Nat.le_floor
        (by
          dsimp only [b]; norm_num only [Nat.cast_ofNat])
  · simpa only [Nat.floor_ofNat] using ht

/-- The explicit upper bound for the complementary Euler weight at a variable cutoff
between 2701 and one million. It includes both psi error integrals and the lower boundary. -/
noncomputable def positiveTail570 (x : ℝ) : ℝ :=
  eulerMainTail570 x + (4 / 5) * Real.sqrt x * eulerDensity570 x + eulerLowError570 x +
    eulerHighError570 1000000

/-- Centered Abel summation on both sides of one million gives a finite upper bound
with the upper psi boundary retained for the infinite limit. -/
private theorem finite_tail_upper (hRH : RiemannHypothesis) {a b : ℝ} (ha : 2701 ≤ a)
    (hav : a ≤ 1000000) (hb : 1000000 ≤ b) :
    let w := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, w n) ≤
      positiveTail570 a + (Chebyshev.psi b - b) * eulerDensity570 b := by
  intro w
  have ha1 : 1 ≤ a := by linarith only [ha]
  have lo := euler570_abel (zero_lt_one.trans_le ha1) hav
  have hi := euler570_abel (by norm_num only) hb
  have el := (abs_le.mp (euler570_error_million (by linarith only [ha]) hav (le_refl 1000000))).1
  have eh := (abs_le.mp (euler570_error_high hRH (le_refl 1000000) hb)).1
  rw [mainDiff ha1 hav] at lo
  rw [mainDiff (by norm_num only) hb] at hi
  rw [lowDiff ha1 hav] at el
  rw [highDiff (by norm_num only) hb] at eh
  have hfa : 0 ≤ eulerDensity570 a := by
    have hl := Real.log_nonneg ha1
    have hp := zero_le_one.trans ha1
    unfold eulerDensity570
    positivity
  have he :=
    mul_le_mul_of_nonneg_right
      (abs_le.mp
          (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (by linarith only [ha])
            hav)).1
      hfa
  have hbm (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 13 / 25) (show 1 ≤ b by linarith only [hb]) k
  have hbe (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 51 / 50) (show 1 ≤ b by linarith only [hb]) k
  have hve (k : ℕ) :=
    moment_nonneg (by norm_num only : (0 : ℝ) < 51 / 50) (by norm_num only : (1 : ℝ) ≤ 1000000) k
  have hmb : 0 ≤ eulerMainTail570 b := by
    unfold eulerMainTail570
    linarith only [hbm 0, hbm 1, hbm 2]
  have heb : 0 ≤ eulerHighError570 b := by
    unfold eulerHighError570
    linarith only [hbe 2, hbe 3, hbe 4]
  have hev : 0 ≤ eulerLowError570 1000000 := by
    unfold eulerLowError570
    linarith only [hve 0, hve 1, hve 2]
  unfold positiveTail570
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.floor_mono hav) (Nat.floor_mono hb),
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  dsimp only [w]
  linear_combination lo + hi + el + eh + he + hmb + heb + hev

/-- The RH log-square bound and power decay force the upper Euler boundary to vanish. -/
private theorem upper_boundary_zero (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun t ↦ (Chebyshev.psi t - t) * eulerDensity570 t) Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm' _
      (Analysis.log_pow_mul_neg_rpow_tendsto (by norm_num only : (0 : ℝ) < 51 / 50) 4)
  filter_upwards [Filter.eventually_ge_atTop (1000000 : ℝ)] with t ht
  have hp : 0 < t := by linarith only [ht]
  have hl : 1 ≤ Real.log t :=
    (Real.le_log_iff_exp_le hp).mpr (Real.exp_one_lt_d9.le.trans (by linarith only [ht]))
  have hlog := zero_le_one.trans hl
  have hd : 0 ≤ eulerDensity570 t := by
    unfold eulerDensity570; positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd]
  apply (mul_le_mul_of_nonneg_right (euler570_psi_high hRH ht) hd).trans
  have hz :
    3 / 8 + 153 / 400 * Real.log t + 2601 / 20000 * Real.log t ^ 2 ≤ 24 * Real.log t ^ 2 := by
    nlinarith only [hl, sq_nonneg (Real.log t - 1)]
  have he : Real.sqrt t * t ^ (-(38 / 25 : ℝ)) = t ^ (-(51 / 50 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  unfold eulerDensity570
  have hw : 0 ≤ Real.sqrt t * t ^ (-(38 / 25 : ℝ)) * (Real.log t ^ 2 / 24) := by positivity
  linear_combination mul_le_mul_of_nonneg_left hz hw + Real.log t ^ 4 * he

/-- Under RH the positive Euler tail above a real cutoff between 2701 and one million
is bounded by the explicit section 31 expression. Pass the finite upper bound to infinity
using summability and decay of the centered upper boundary. -/
theorem positive_tail_upper_570 (hRH : RiemannHypothesis) {a : ℝ} (ha : 2701 ≤ a)
    (hav : a ≤ 1000000) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) ≤
      positiveTail570 a := by
  have ht :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix _
      (by simp only [ArithmeticFunction.map_zero, zero_mul]) quarter_euler_weight_summable_570 a
  have hb :=
    (upper_boundary_zero hRH).comp
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  have hr := hb.const_add (positiveTail570 a)
  rw [add_zero] at hr
  apply le_of_tendsto_of_tendsto ht hr
  filter_upwards [Filter.eventually_ge_atTop (1000000 : ℕ)] with n hn
  have h := finite_tail_upper hRH ha hav (b := (n : ℝ)) (by exact_mod_cast hn)
  simpa only [Nat.floor_natCast, Function.comp_apply] using h

/-- On radii from 278 through 285, monotone power and logarithm bounds at opposite endpoints
bound the positive Euler remainder by 0.1592 throughout the interval. -/
theorem radius_tail_numeric {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    positiveTail570 (r ^ 2) ≤ 1592 / 10000 := by
  let x := r ^ 2
  have hr : 0 ≤ r := by linarith only [hl]
  have hx : 77284 ≤ x :=
    (by norm_num only : (77284 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2)
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hz : Real.log x ≤ 11305 / 1000 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 285) (j := 8) (n := 24) (lo := 5) (hi :=
          56525 / 10000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h, Real.log_le_log (by linarith only [hl]) hu]
  have hm : x ^ (-(13 / 25 : ℝ)) ≤ 287206 / 100000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 77284) (p := 13) (d :=
          25) (lo := 0) (hi := 287206 / 100000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 77284) hx
          (by norm_num only : -(13 / 25 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hl' : x ^ (-(51 / 50 : ℝ)) ≤ 103312 / 10000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 77284) (p := 51) (d :=
          50) (lo := 0) (hi := 103312 / 10000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 77284) hx
          (by norm_num only : -(51 / 50 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hb : x ^ (-(38 / 25 : ℝ)) ≤ 371625 / 10000000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 77284) (p := 38) (d :=
          25) (lo := 0) (hi := 371625 / 10000000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 77284) hx
          (by norm_num only : -(38 / 25 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hmain (j : ℕ) := momentUpper j (by norm_num only) hx1 hm hz
  have herr (j : ℕ) := momentUpper j (by norm_num only) hx1 hl' hz
  have hD :
    eulerDensity570 x ≤
      (371625 / 10000000000000 : ℝ) *
        (3 / 8 + 153 / 400 * (11305 / 1000) + 2601 / 20000 * (11305 / 1000) ^ 2) := by
    unfold eulerDensity570
    have hlog := Real.log_nonneg hx1
    gcongr
  have hn : 0 ≤ eulerDensity570 x := by
    have hlog := Real.log_nonneg hx1
    have hp := zero_le_one.trans hx1
    unfold eulerDensity570
    positivity
  have hs : Real.sqrt x ≤ 285 := (Real.sqrt_sq hr).le.trans hu
  have hB := mul_le_mul hs hD hn (by norm_num only)
  have hM0 := hmain 0
  have hM1 := hmain 1
  have hM2 := hmain 2
  have hE0 := herr 0
  have hE1 := herr 1
  have hE2 := herr 2
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at hM0 hM1 hM2 hE0 hE1 hE2
  change positiveTail570 x ≤ _
  unfold positiveTail570 eulerMainTail570 eulerLowError570
  linarith only [hM0, hM1, hM2, hE0, hE1, hE2, hB, highUpper]

/-- Across section 62 the positive Euler tail is at most 0.1556, by bounding the
negative powers at radius 285 and logarithms at radius 287. -/
theorem radius_tail_numeric_574 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287) :
    positiveTail570 (r ^ 2) ≤ 1556 / 10000 := by
  let x := r ^ 2
  have hr : 0 ≤ r := by linarith only [hl]
  have hx : 81225 ≤ x :=
    (by norm_num only : (81225 : ℝ) ≤ 285 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2)
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hz : Real.log x ≤ 11319 / 1000 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 287) (j := 8) (n := 24) (lo := 5) (hi :=
          56595 / 10000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h, Real.log_le_log (by linarith only [hl]) hu]
  have hm : x ^ (-(13 / 25 : ℝ)) ≤ 279874 / 100000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 81225) (p := 13) (d :=
          25) (lo := 0) (hi := 279874 / 100000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 81225) hx
          (by norm_num only : -(13 / 25 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hl' : x ^ (-(51 / 50 : ℝ)) ≤ 98202 / 10000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 81225) (p := 51) (d :=
          50) (lo := 0) (hi := 98202 / 10000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 81225) hx
          (by norm_num only : -(51 / 50 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hb : x ^ (-(38 / 25 : ℝ)) ≤ 344566 / 10000000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 81225) (p := 38) (d :=
          25) (lo := 0) (hi := 344566 / 10000000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 81225) hx
          (by norm_num only : -(38 / 25 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hmain (j : ℕ) := momentUpper j (by norm_num only) hx1 hm hz
  have herr (j : ℕ) := momentUpper j (by norm_num only) hx1 hl' hz
  have hD :
    eulerDensity570 x ≤
      (344566 / 10000000000000 : ℝ) *
        (3 / 8 + 153 / 400 * (11319 / 1000) + 2601 / 20000 * (11319 / 1000) ^ 2) := by
    unfold eulerDensity570
    have hlog := Real.log_nonneg hx1
    gcongr
  have hn : 0 ≤ eulerDensity570 x := by
    have hlog := Real.log_nonneg hx1
    have hp := zero_le_one.trans hx1
    unfold eulerDensity570
    positivity
  have hs : Real.sqrt x ≤ 287 := (Real.sqrt_sq hr).le.trans hu
  have hB := mul_le_mul hs hD hn (by norm_num only)
  have hM0 := hmain 0
  have hM1 := hmain 1
  have hM2 := hmain 2
  have hE0 := herr 0
  have hE1 := herr 1
  have hE2 := herr 2
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at hM0 hM1 hM2 hE0 hE1 hE2
  change positiveTail570 x ≤ _
  unfold positiveTail570 eulerMainTail570 eulerLowError570
  linarith only [hM0, hM1, hM2, hE0, hE1, hE2, hB, highUpper]

/-- On the section 86 radius interval, positive Euler tail moments at the squared radius
are bounded by their endpoint rational power and logarithm enclosures. -/
theorem radius_tail_numeric_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    positiveTail570 (r ^ 2) ≤ 1546 / 10000 := by
  let x := r ^ 2
  have hr : 0 ≤ r := by linarith only [hl]
  have hx : 82369 ≤ x :=
    (by norm_num only : (82369 : ℝ) ≤ 287 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2)
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hz : Real.log x ≤ 11326 / 1000 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 288) (j := 8) (n := 24) (lo := 5) (hi :=
          56630 / 10000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h, Real.log_le_log (by linarith only [hl]) hu]
  have hm : x ^ (-(13 / 25 : ℝ)) ≤ 277846 / 100000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 82369) (p := 13) (d :=
          25) (lo := 0) (hi := 277846 / 100000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 82369) hx
          (by norm_num only : -(13 / 25 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hl' : x ^ (-(51 / 50 : ℝ)) ≤ 96811 / 10000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 82369) (p := 51) (d :=
          50) (lo := 0) (hi := 96811 / 10000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 82369) hx
          (by norm_num only : -(51 / 50 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hb : x ^ (-(38 / 25 : ℝ)) ≤ 337318 / 10000000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 82369) (p := 38) (d :=
          25) (lo := 0) (hi := 337318 / 10000000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    apply
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 82369) hx
          (by norm_num only : -(38 / 25 : ℝ) ≤ 0)).trans
    linarith only [h]
  have hmain (j : ℕ) := momentUpper j (by norm_num only) hx1 hm hz
  have herr (j : ℕ) := momentUpper j (by norm_num only) hx1 hl' hz
  have hD :
    eulerDensity570 x ≤
      (337318 / 10000000000000 : ℝ) *
        (3 / 8 + 153 / 400 * (11326 / 1000) + 2601 / 20000 * (11326 / 1000) ^ 2) := by
    unfold eulerDensity570
    have hlog := Real.log_nonneg hx1
    gcongr
  have hn : 0 ≤ eulerDensity570 x := by
    have hlog := Real.log_nonneg hx1
    have hp := zero_le_one.trans hx1
    unfold eulerDensity570
    positivity
  have hs : Real.sqrt x ≤ 288 := (Real.sqrt_sq hr).le.trans hu
  have hB := mul_le_mul hs hD hn (by norm_num only)
  have hM0 := hmain 0
  have hM1 := hmain 1
  have hM2 := hmain 2
  have hE0 := herr 0
  have hE1 := herr 1
  have hE2 := herr 2
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at hM0 hM1 hM2 hE0 hE1 hE2
  change positiveTail570 x ≤ _
  unfold positiveTail570 eulerMainTail570 eulerLowError570
  linarith only [hM0, hM1, hM2, hE0, hE1, hE2, hB, highUpper]

end PseudoPrime.PrimeTestBounds.MillerRabin
