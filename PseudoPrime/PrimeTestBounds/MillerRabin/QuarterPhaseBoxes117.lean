/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Rational logarithm and exponential enclosures for the section 117 endpoints -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational enclosure of twice the logarithm at radius 314. -/
theorem section117_log_box_314 :
    2 * Real.log (314) ∈ Set.Icc (114987859598 / 10 ^ 10) (114987859840 / 10 ^ 10) := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 314) (j := 8) (n := 40) (lo :=
      57493929799 / 10 ^ 10) (hi := 57493929920 / 10 ^ 10) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h
  exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

/-- Rational enclosure of twice the logarithm at radius 314.45. -/
theorem section117_log_box_314_45 :
    2 * Real.log (6289 / 20) ∈ Set.Icc (115016501498 / 10 ^ 10) (115016501740 / 10 ^ 10) := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 6289 / 20) (j := 8) (n := 40) (lo :=
      57508250749 / 10 ^ 10) (hi := 57508250870 / 10 ^ 10) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h
  exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

/-- Rational enclosure of twice the logarithm at radius 315. -/
theorem section117_log_box_315 :
    2 * Real.log (315) ∈ Set.Icc (115051452656 / 10 ^ 10) (115051452898 / 10 ^ 10) := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 315) (j := 8) (n := 40) (lo :=
      57525726328 / 10 ^ 10) (hi := 57525726449 / 10 ^ 10) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h
  exact ⟨by linarith only [h.1], by linarith only [h.2]⟩

/-- At a positive rational radius, a rational power certificate also bounds
the exponential in the logarithmic coordinate of the phase. -/
theorem section117_exp_of_power {b L U : ℚ} {p d : ℕ} (hb : 0 < b)
    (hc : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck b L U p d = true) :
    Real.exp (-(p : ℝ) / d * Real.log (b : ℝ)) ∈ Set.Icc (L : ℝ) (U : ℝ) := by
  have h := AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hc
  rw [Real.rpow_def_of_pos ((Rat.cast_pos (K := ℝ)).mpr hb), mul_comm] at h
  exact h

/-- Four exponential factors at radius 314, certified by exact rational powers. -/
theorem section117_exp_box_314 :
    Real.exp (-(13 / 25) * (2 * Real.log (314))) ∈
        Set.Icc (2530423230768361 / 10 ^ 18) (2530423230768366 / 10 ^ 18) ∧
      Real.exp (-(51 / 50) * (2 * Real.log (314))) ∈
        Set.Icc (8058672709451 / 10 ^ 18) (8058672709456 / 10 ^ 18) ∧
      Real.exp (-(77 / 50) * (2 * Real.log (314))) ∈
        Set.Icc (20391852631 / 10 ^ 18) (20391852636 / 10 ^ 18) ∧
      Real.exp (-(51 / 25) * (2 * Real.log (314))) ∈
        Set.Icc (64942203 / 10 ^ 18) (64942208 / 10 ^ 18) := by
  have h0 :=
    section117_exp_of_power (b := 314) (p := 26) (d := 25) (L := 2530423230768361 / 10 ^ 18) (U :=
      2530423230768366 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h0
  rw [show -((26 : ℝ) / 25) * Real.log (314) = -(13 / 25) * (2 * Real.log (314)) by ring] at h0
  have h1 :=
    section117_exp_of_power (b := 314) (p := 51) (d := 25) (L := 8058672709451 / 10 ^ 18) (U :=
      8058672709456 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h1
  rw [show -((51 : ℝ) / 25) * Real.log (314) = -(51 / 50) * (2 * Real.log (314)) by ring] at h1
  have h2 :=
    section117_exp_of_power (b := 314) (p := 77) (d := 25) (L := 20391852631 / 10 ^ 18) (U :=
      20391852636 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h2
  rw [show -((77 : ℝ) / 25) * Real.log (314) = -(77 / 50) * (2 * Real.log (314)) by ring] at h2
  have h3 :=
    section117_exp_of_power (b := 314) (p := 102) (d := 25) (L := 64942203 / 10 ^ 18) (U :=
      64942208 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h3
  rw [show -((102 : ℝ) / 25) * Real.log (314) = -(51 / 25) * (2 * Real.log (314)) by ring] at h3
  norm_num only
  exact ⟨h0, h1, h2, h3⟩

/-- Four exponential factors at radius 314.45, certified by exact rational powers. -/
theorem section117_exp_box_314_45 :
    Real.exp (-(13 / 25) * (2 * Real.log (6289 / 20))) ∈
        Set.Icc (2526657277001745 / 10 ^ 18) (2526657277001750 / 10 ^ 18) ∧
      Real.exp (-(51 / 50) * (2 * Real.log (6289 / 20))) ∈
        Set.Icc (8035163863892 / 10 ^ 18) (8035163863897 / 10 ^ 18) ∧
      Real.exp (-(77 / 50) * (2 * Real.log (6289 / 20))) ∈
        Set.Icc (20302105246 / 10 ^ 18) (20302105251 / 10 ^ 18) ∧
      Real.exp (-(51 / 25) * (2 * Real.log (6289 / 20))) ∈
        Set.Icc (64563856 / 10 ^ 18) (64563861 / 10 ^ 18) := by
  have h0 :=
    section117_exp_of_power (b := 6289 / 20) (p := 26) (d := 25) (L := 2526657277001745 / 10 ^ 18)
      (U := 2526657277001750 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h0
  rw [show -((26 : ℝ) / 25) * Real.log (6289 / 20) = -(13 / 25) * (2 * Real.log (6289 / 20)) by
      ring] at h0
  have h1 :=
    section117_exp_of_power (b := 6289 / 20) (p := 51) (d := 25) (L := 8035163863892 / 10 ^ 18)
      (U := 8035163863897 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h1
  rw [show -((51 : ℝ) / 25) * Real.log (6289 / 20) = -(51 / 50) * (2 * Real.log (6289 / 20)) by
      ring] at h1
  have h2 :=
    section117_exp_of_power (b := 6289 / 20) (p := 77) (d := 25) (L := 20302105246 / 10 ^ 18) (U :=
      20302105251 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h2
  rw [show -((77 : ℝ) / 25) * Real.log (6289 / 20) = -(77 / 50) * (2 * Real.log (6289 / 20)) by
      ring] at h2
  have h3 :=
    section117_exp_of_power (b := 6289 / 20) (p := 102) (d := 25) (L := 64563856 / 10 ^ 18) (U :=
      64563861 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h3
  rw [show -((102 : ℝ) / 25) * Real.log (6289 / 20) = -(51 / 25) * (2 * Real.log (6289 / 20)) by
      ring] at h3
  norm_num only
  exact ⟨h0, h1, h2, h3⟩

/-- Four exponential factors at radius 315, certified by exact rational powers. -/
theorem section117_exp_box_315 :
    Real.exp (-(13 / 25) * (2 * Real.log (315))) ∈
        Set.Icc (2522069348540647 / 10 ^ 18) (2522069348540651 / 10 ^ 18) ∧
      Real.exp (-(51 / 50) * (2 * Real.log (315))) ∈
        Set.Icc (8006569360444 / 10 ^ 18) (8006569360449 / 10 ^ 18) ∧
      Real.exp (-(77 / 50) * (2 * Real.log (315))) ∈
        Set.Icc (20193123168 / 10 ^ 18) (20193123173 / 10 ^ 18) ∧
      Real.exp (-(51 / 25) * (2 * Real.log (315))) ∈
        Set.Icc (64105150 / 10 ^ 18) (64105155 / 10 ^ 18) := by
  have h0 :=
    section117_exp_of_power (b := 315) (p := 26) (d := 25) (L := 2522069348540647 / 10 ^ 18) (U :=
      2522069348540651 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h0
  rw [show -((26 : ℝ) / 25) * Real.log (315) = -(13 / 25) * (2 * Real.log (315)) by ring] at h0
  have h1 :=
    section117_exp_of_power (b := 315) (p := 51) (d := 25) (L := 8006569360444 / 10 ^ 18) (U :=
      8006569360449 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h1
  rw [show -((51 : ℝ) / 25) * Real.log (315) = -(51 / 50) * (2 * Real.log (315)) by ring] at h1
  have h2 :=
    section117_exp_of_power (b := 315) (p := 77) (d := 25) (L := 20193123168 / 10 ^ 18) (U :=
      20193123173 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h2
  rw [show -((77 : ℝ) / 25) * Real.log (315) = -(77 / 50) * (2 * Real.log (315)) by ring] at h2
  have h3 :=
    section117_exp_of_power (b := 315) (p := 102) (d := 25) (L := 64105150 / 10 ^ 18) (U :=
      64105155 / 10 ^ 18) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h3
  rw [show -((102 : ℝ) / 25) * Real.log (315) = -(51 / 25) * (2 * Real.log (315)) by ring] at h3
  norm_num only
  exact ⟨h0, h1, h2, h3⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
