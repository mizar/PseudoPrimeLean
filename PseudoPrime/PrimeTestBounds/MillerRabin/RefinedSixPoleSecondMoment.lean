/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePrincipalWeight
public import PseudoPrime.Analysis.ScaledLogMoments
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Logarithmic moments of the refined second Abel density -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive arguments, a real power times the exponential and square-root factor
reduces to a single real power. Expand both powers as exponentials and combine exponents. -/
theorem refined_second_power_factor {u : ℝ} (hu : 0 < u) (p : ℝ) :
    u ^ p * Real.exp (-refinedCoord u) / (u * Real.sqrt u) =
      Real.exp (-(567 / 200 : ℝ)) * u ^ (p - 21 / 50) := by
  calc
    _ =
        (Real.exp (Real.log u * p) * Real.exp (-refinedCoord u)) /
          (Real.exp (Real.log u) * Real.exp (Real.log u * (1 / 2))) :=
      by rw [Real.rpow_def_of_pos hu, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, Real.exp_log hu]
    _ = Real.exp (-(567 / 200 : ℝ)) * Real.exp (Real.log u * (p - 21 / 50)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      dsimp only [refinedCoord]
      ring
    _ = _ := by rw [Real.rpow_def_of_pos hu]

/-- For every positive moment parameter, the selected logarithmic coordinate has
integrable moments on the full support with the displayed exact value.
Factor the coordinate into (27/25)(21/8-log u) and reuse the general scaled log moment.
This provides all polynomial terms in the second-density evaluation. -/
theorem refined_coord_moment (n : ℕ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * refinedCoord u ^ n)
        (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) ∧
      (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), u ^ (s - 1) * refinedCoord u ^ n) =
        (27 / 25 : ℝ) ^ n * Real.exp ((21 / 8 : ℝ) * s) * ((n.factorial : ℝ) / s ^ (n + 1)) := by
  have h := Analysis.scaled_log_moment n (21 / 8) hs
  have he :
    (fun u : ℝ ↦ u ^ (s - 1) * refinedCoord u ^ n) =
      (fun u : ℝ ↦ (27 / 25 : ℝ) ^ n * (u ^ (s - 1) * (21 / 8 - Real.log u) ^ n)) := by
    funext u
    have hv : refinedCoord u = (27 / 25 : ℝ) * (21 / 8 - Real.log u) := by
      dsimp only [refinedCoord]
      ring
    rw [hv, mul_pow]
    ring
  rw [he]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [intervalIntegral.integral_const_mul, h.2]
  ring

/-- A power-weighted term of the refined second density is integrable when p+29/50 is positive.
Its exact integral follows from the preceding power factor and coordinate moment.
The cases p=0, p=1/2 and p=1 control integrability, error variation and the main term. -/
theorem refined_density_moment (n : ℕ) (p : ℝ) (hp : 0 < p + (29 / 50 : ℝ)) :
    MeasureTheory.IntegrableOn
        (fun u : ℝ ↦
          u ^ p * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ n)
        (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)),
          u ^ p * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ n) =
        (Real.exp (-(567 / 200 : ℝ)) / 120) *
          ((27 / 25 : ℝ) ^ n * Real.exp ((21 / 8 : ℝ) * (p + 29 / 50)) *
            ((n.factorial : ℝ) / (p + 29 / 50) ^ (n + 1))) := by
  have h := refined_coord_moment n hp
  rw [intervalIntegral.integral_of_le (Real.exp_pos _).le] at h
  have he :
    (fun u : ℝ ↦
        u ^ p * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
          refinedCoord u ^ n) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 (Real.exp (21 / 8 : ℝ)))]
      (fun u : ℝ ↦
        (Real.exp (-(567 / 200 : ℝ)) / 120) * (u ^ (p + 29 / 50 - 1) * refinedCoord u ^ n)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have hf := refined_second_power_factor hu.1 p
    have hexp : p + (29 / 50 : ℝ) - 1 = p - 21 / 50 := by ring
    rw [hexp]
    calc
      _ = (u ^ p * Real.exp (-refinedCoord u) / (u * Real.sqrt u)) / 120 * refinedCoord u ^ n := by
        ring
      _ = _ := by
        rw [hf]; ring
  refine ⟨(h.1.const_mul (Real.exp (-(567 / 200 : ℝ)) / 120)).congr he.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae he, MeasureTheory.integral_const_mul, h.2]

/-- The actual second Abel density is integrable on its positive support. Express it
as a linear combination of three integrable logarithmic moments at exponent zero. -/
theorem refined_second_integrable :
    MeasureTheory.IntegrableOn refinedSecondDensity (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
  have h3 := refined_density_moment 3 0 (by norm_num only)
  have h4 := refined_density_moment 4 0 (by norm_num only)
  have h5 := refined_density_moment 5 0 (by norm_num only)
  simp only [Real.rpow_zero, one_mul] at h3 h4 h5
  have he :
    refinedSecondDensity =
      (fun u : ℝ ↦
        (29 / 50 : ℝ) ^ 2 *
              (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 5) -
            (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ)) *
              (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 4) +
          (20 * (27 / 25 : ℝ) ^ 2) *
            (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 3)) := by
    funext u
    dsimp only [refinedSecondDensity]
    ring
  rw [he]
  exact ((h5.1.const_mul _).sub (h4.1.const_mul _)).add (h3.1.const_mul _)

end PseudoPrime.PrimeTestBounds.MillerRabin
