/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Gram
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineCore663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663

/-! # Certified constants of the K197 mixed cosine core -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem k197_weighted_error (i : Fin 6) {a b e : ℝ} (h : |a - b| ≤ e) :
    |(gaussianCoeff197 i : ℝ) * a - (gaussianCoeff197 i : ℝ) * b| ≤ e := by
  have hc : ∀ i : Fin 6, |gaussianCoeff197 i| ≤ 1 := by decide +kernel
  have hcR : |(gaussianCoeff197 i : ℝ)| ≤ 1 := by exact_mod_cast hc i
  rw [← mul_sub, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hcR).trans h

private theorem k197_mix_error (f g : ℚ → ℝ) {e : ℝ}
    (hs : ∀ i, |f (quarterFreq663 i) - g (quarterFreq663 i)| ≤ e)
    (hp :
      ∀ i j,
        |f (quarterFreq663 i - quarterFreq663 j) - g (quarterFreq663 i - quarterFreq663 j)| ≤ e) :
    |gaussianAuxMix197 f - gaussianAuxMix197 g| ≤ 24 * e := by
  have hl := sum_six_error _ _ fun i ↦ k197_weighted_error i (hs i)
  have hq :=
    sum_six_error _ _ fun i ↦
      k197_weighted_error i (sum_six_error _ _ fun j ↦ k197_weighted_error j (hp i j))
  unfold gaussianAuxMix197
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [show ∀ a b c d : ℝ, a / 2 - b - (c / 2 - d) = (a - c) / 2 - (b - d) from fun a b c d ↦ by
      ring]
  exact
    (abs_sub _ _).trans
      (by
        rw [abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
        linarith only [hl, hq])

/-- Factor out the outer coefficient before checking a row of the
rational mixed profile. -/
private def mixRowRat197 (F : ℚ → ℚ) (i : Fin 6) : ℚ :=
  (∑ j, gaussianCoeff197 i * gaussianCoeff197 j * F (quarterFreq663 i - quarterFreq663 j)) / 2 -
    gaussianCoeff197 i * F (quarterFreq663 i)

private theorem cast_mix_rows (F : ℚ → ℚ) :
    ((∑ i, mixRowRat197 F i : ℚ) : ℝ) = gaussianAuxMix197 (fun t ↦ (F t : ℝ)) := by
  simp only [mixRowRat197, gaussianAuxMix197, Rat.cast_sum, Rat.cast_sub, Rat.cast_div,
    Rat.cast_mul, Rat.cast_ofNat, Finset.sum_sub_distrib, Finset.sum_div]

private def residueRowLower (i : Fin 6) : ℚ :=
  (![(-20379643649 : ℤ), 22256461874, 4589993620, 9519223490, -130939354279, 122508145258] i : ℤ) /
    10 ^ 10

private def conductorRowUpper (i : Fin 6) : ℚ :=
  (![(-1495525184 : ℤ), 1487326994, 55235393, 21462888, -3391965, 2563028] i : ℤ) / 10 ^ 10

private theorem residue_row_check (i : Fin 6) : residueRowLower i ≤ mixRowRat197 residueRat i := by
  fin_cases i <;> decide +kernel

private theorem conductor_row_check (i : Fin 6) :
    mixRowRat197 conductorApprox i ≤ conductorRowUpper i := by fin_cases i <;> decide +kernel

/-- The symmetric half-point contribution gives a certified gain of
at least 4.125679 after the three-character normalization. -/
theorem gaussian_residue_lower_197 :
    (4.125679 : ℝ) ≤
      3 * ((11 / 10 : ℝ) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3) *
        gaussianAuxMix197 (fun s ↦ quarterAuxResidue656 (s : ℝ)) := by
  have hs :
    ∀ i,
      let s := quarterFreq663 i
      |(-|s| / 2 : ℚ)| ≤ 11 ∧ |(|s| / 2 : ℚ)| ≤ 11 := by
    decide +kernel
  have hp :
    ∀ i j,
      let s := quarterFreq663 i - quarterFreq663 j
      |(-|s| / 2 : ℚ)| ≤ 11 ∧ |(|s| / 2 : ℚ)| ≤ 11 := by
    decide +kernel
  have he :=
    k197_mix_error (fun s ↦ quarterAuxResidue656 (s : ℝ)) (fun s ↦ (residueRat s : ℝ))
      (fun i ↦ residue_error _ (hs i).1 (hs i).2) (fun i j ↦ residue_error _ (hp i j).1 (hp i j).2)
  have hc :=
    (Rat.cast_le (K := ℝ)).mpr
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ residue_row_check i))
  rw [cast_mix_rows] at hc
  have hn :
    (4.125679 : ℚ) ≤
      3 * ((11 / 10 : ℚ) ^ 5 / ((11 / 10 : ℚ) ^ 2 - 1 / 4) ^ 3) *
        ((∑ i, residueRowLower i) - 48 / 10 ^ 16) := by
    decide +kernel
  have h := (Rat.cast_le (K := ℝ)).mpr hn
  norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofScientific] at h
  linarith only [h, hc, (abs_le.mp he).1]

/-- The K197 conductor coefficient is bounded above by its six
rational row enclosures and the Taylor approximation error. -/
theorem gaussian_conductor_upper_197 :
    gaussianAuxMix197 quarterConductorProfile663 ≤ 0.00676712 := by
  have hs :
    ∀ i,
      let s := quarterFreq663 i
      |(-(11 / 10) * |s| : ℚ)| ≤ 11 ∧ |shiftedCoeff 0 (|s|)| ≤ 50 := by
    decide +kernel
  have hp :
    ∀ i j,
      let s := quarterFreq663 i - quarterFreq663 j
      |(-(11 / 10) * |s| : ℚ)| ≤ 11 ∧ |shiftedCoeff 0 (|s|)| ≤ 50 := by
    decide +kernel
  have he :=
    k197_mix_error quarterConductorProfile663 (fun s ↦ (conductorApprox s : ℝ))
      (fun i ↦ conductor_error _ (hs i).1 (hs i).2)
      (fun i j ↦ conductor_error _ (hp i j).1 (hp i j).2)
  have hc :=
    (Rat.cast_le (K := ℝ)).mpr
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ conductor_row_check i))
  rw [cast_mix_rows] at hc
  have hn : (∑ i, conductorRowUpper i) + (24 / 10 ^ 14 : ℚ) ≤ 0.00676712 := by decide +kernel
  have h := (Rat.cast_le (K := ℝ)).mpr hn
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofScientific] at h
  linarith only [h, hc, (abs_le.mp he).2]

/-- The mixed xi allowance is 72 millionths after summing the three characters. -/
theorem gaussian_core_xi_cap_197 (hRH : RiemannHypothesis) :
    |3 * gaussianAuxMix197 (fun s ↦ quarterCosineXi656 |(s : ℝ)|)| ≤ 0.000072 := by
  have h :=
    k197_mix_error (fun s ↦ quarterCosineXi656 |(s : ℝ)|) (fun _ ↦ 0)
      (fun i ↦ by
        simpa only [sub_zero] using
          quarter_xi_cosine_abs_656 hRH (abs_nonneg (quarterFreq663 i : ℝ)))
      (fun i j ↦ by
        simpa only [sub_zero] using
          quarter_xi_cosine_abs_656 hRH
            (abs_nonneg ((quarterFreq663 i - quarterFreq663 j : ℚ) : ℝ)))
  simp only [gaussianAuxMix197, mul_zero, Finset.sum_const_zero, zero_div, sub_zero] at h
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)]
  unfold gaussianAuxMix197
  linarith only [h]

/-- The mixed cosine core has a uniform residue gain after paying its xi error. -/
theorem gaussian_core_cap_197 (hRH : RiemannHypothesis) (r : ℝ) :
    gaussianAuxMix197 (fun s ↦ quarterCosineCore656 (4 * r) (s : ℝ)) ≤
      gaussianAuxMix197 quarterConductorProfile663 * r - 4.125607 := by
  rw [gaussian_core_eq_197]
  linarith only [gaussian_residue_lower_197, (abs_le.mp (gaussian_core_xi_cap_197 hRH)).2]

private def halfApprox197 : ℚ :=
  ∑ i, gaussianCoeff197 i * profileExpTaylor (-quarterShift663 i / 2)

/-- The positive half-point term has a negative signed coefficient,
certified by Taylor enclosures at the six auxiliary shifts. -/
theorem gaussian_half_upper_197 : gaussianHalfCoeff197 ≤ -0.00692794 := by
  have hv : ∀ i : Fin 6, |(-quarterShift663 i / 2 : ℚ)| ≤ 11 := by decide +kernel
  have he :=
    sum_six_error (fun i ↦ (gaussianCoeff197 i : ℝ) * Real.exp ((-quarterShift663 i / 2 : ℚ) : ℝ))
      (fun i ↦ (gaussianCoeff197 i : ℝ) * (profileExpTaylor (-quarterShift663 i / 2) : ℝ))
      (fun i ↦ k197_weighted_error i (profile_exp_error _ (by exact_mod_cast hv i)))
  have hc :
    (halfApprox197 : ℝ) =
      ∑ i, (gaussianCoeff197 i : ℝ) * (profileExpTaylor (-quarterShift663 i / 2) : ℝ) := by
    simp only [halfApprox197, Rat.cast_sum, Rat.cast_mul]
  rw [← hc] at he
  have hn :
    (3 * (11 / 10) ^ 5 / (8 / 5) ^ 6 : ℚ) * (halfApprox197 + 6 / 10 ^ 16) ≤ -0.00692794 := by
    decide +kernel
  have hcast := (Rat.cast_le (K := ℝ)).mpr hn
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofScientific, Rat.cast_neg] at hcast
  have hh := (abs_le.mp he).2
  simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hh
  unfold gaussianHalfCoeff197
  linarith only [hh, hcast]

/-- Combine the three K197 forward inequalities with the certified
mixed-core allowance, keeping the signed Euler tail explicit. -/
theorem gaussian_scaled_forward_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r t : ℝ} (hr : 328 ≤ r)
    (hL : Real.log p + Real.log q + Real.log k = 4 * t)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    (∑' n, quarterKernel656.summand a (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand b (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand c (r ^ 2) n).re +
        (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        4.125607 ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) +
        gaussianAuxMix197 quarterConductorProfile663 * t +
        ∑' n : { n : ℕ // ⌊r ^ 2⌋₊ < n },
          (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (8 / 5 : ℝ)) *
            (gaussianProfile197 (Real.log n.val) - quarterAuxProfile656 (Real.log n.val)) := by
  have h := gaussian_three_gram_197 ha hb hc hp hq hk hG hr hpa hpb hpc
  rw [hL] at h
  linarith only [h, gaussian_core_cap_197 hG.riemann t]

end PseudoPrime.PrimeTestBounds.MillerRabin
