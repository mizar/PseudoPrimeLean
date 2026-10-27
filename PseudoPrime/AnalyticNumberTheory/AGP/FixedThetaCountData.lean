/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionCountConstruction
public import PseudoPrime.AnalyticNumberTheory.AGP.UniformProgressionFixed

/-! # Progression count data from fixed-scale theta estimates

This module combines the initial modulus-one Proposition 1.5 count with a
fixed-scale theta supply. It uses the unconditional coarse progression sieve
bound and the stronger reciprocal-prime-sum estimate carried by the auxiliary
data to construct the final progression-count interface.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: an initial modulus-one uniform count and the fixed-scale theta supply.

Claim: these analytic inputs imply `AGPProgressionCountDataExists`.

Proof: decrease the initial count coefficient to absorb the uniform
exceptional-modulus loss, construct the P2 auxiliary data with reciprocal
prime sum at most `1/1024`, obtain the exceptional set at its fifth-power
scale, and apply the finite theta endpoint with the unconditional coarse sieve
bound.

Role: this connects the initial Proposition 1.5 count and paper95 Theorem 2.1
to the AGP prime-supply construction. The initial count and theta supply remain
analytic hypotheses.
-/
theorem agp_progression_count_data_exists_of_initial_count_and_fixed_theta (c₂ : ℝ) (xSeed : ℕ)
    (hc₂ : 0 < c₂) (hseed : ReliableProp15UniformCount c₂ 1 1 xSeed)
    (hTheta : AGPFixedThetaSupply) : AGPProgressionCountDataExists := by
  classical
  obtain ⟨Dexc, Xtheta, hThetaFour⟩ := agpFixedThetaSupply_four hTheta
  let beta : ℝ := agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024)
  have hbetaQuarter : (1 / 4 : ℝ) < beta := by
    simpa only [beta] using agp_fifth_power_average_coefficient_640_1024_gt_quarter
  have hbeta : 0 < beta := lt_trans (by norm_num only : (0 : ℝ) < 1 / 4) hbetaQuarter
  have hpowPos : 0 < (2 ^ Dexc : ℝ) := by exact_mod_cast Nat.pow_pos (by norm_num only : 0 < 2)
  let c₁ : ℝ := min c₂ (beta / (32 * (2 ^ Dexc : ℝ)))
  have hc₁ : 0 < c₁ := by
    dsimp only [c₁]
    exact lt_min hc₂ (div_pos hbeta (mul_pos (by norm_num only : (0 : ℝ) < 32) hpowPos))
  have hc₁c₂ : c₁ ≤ c₂ := by
    dsimp only [c₁]
    exact min_le_left _ _
  have hscaled : 16 * (2 ^ Dexc : ℝ) * c₁ ≤ beta / 2 := by
    dsimp only [c₁]
    calc
      16 * (2 ^ Dexc : ℝ) * min c₂ (beta / (32 * (2 ^ Dexc : ℝ))) ≤
          16 * (2 ^ Dexc : ℝ) * (beta / (32 * (2 ^ Dexc : ℝ))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (le_of_lt (mul_pos (by norm_num only : (0 : ℝ) < 16) hpowPos))
      _ = beta / 2 := by
        field_simp [ne_of_gt hpowPos]
        ring
  have hmargin : 16 * (2 ^ Dexc : ℝ) * c₁ < beta := by
    exact lt_of_le_of_lt hscaled (by nlinarith only [hbeta])
  let x₀ : ℕ := max 2 (Xtheta ^ 5)
  have hx₀ : 2 ≤ x₀ := le_max_left _ _
  have hseed' : ReliableProp15UniformCount c₁ 1 1 xSeed :=
    reliableProp15UniformCount_mono hc₁c₂ hseed
  have hauxExists := agp_progression_auxiliary_data_exists_of_uniform_count c₁ xSeed x₀
  refine ⟨c₁, hc₁, x₀, hx₀, ?_⟩
  intro W C hWpos
  obtain ⟨X, aux, hX, hScale, hqleX⟩ := hauxExists hc₁ hseed' W C hWpos
  have hXthetaPow : Xtheta ^ 5 ≤ X ^ 5 := by
    calc
      Xtheta ^ 5 ≤ x₀ := le_max_right _ _
      _ ≤ aux.x := aux.hLargeEnough
      _ = X ^ 5 := hScale
  have hXtheta : Xtheta ≤ X := by
    by_contra hnot
    have hlt : X < Xtheta := Nat.lt_of_not_ge hnot
    exact (not_lt_of_ge hXthetaPow) (Nat.pow_lt_pow_left hlt (by norm_num only : 5 ≠ 0))
  obtain ⟨E, hEcard, hElog, hthetaAll⟩ := hThetaFour X hXtheta
  let y : ℕ := reliableProp15DivisorCutoff (X ^ 5)
  let T : ℕ :=
    Nat.floor (reliableProp15Coefficient c₁ 4 (X ^ 5) * ((restrictedDivisors aux.L y).card : ℝ)) + 1
  have hLpos : 0 < aux.L := lt_trans (by norm_num only : 0 < 2) aux.hL
  have hLne : aux.L ≠ 0 := Nat.ne_of_gt hLpos
  have hL'div : exceptionalFreePartForModulus aux.L E 4 ∣ aux.L :=
    (exceptionalFreePartForModulus_properties aux.L E 4 hLne aux.hProp15Input.1).2.2.1
  have hL'pos : 0 < exceptionalFreePartForModulus aux.L E 4 := Nat.pos_of_dvd_of_pos hL'div hLpos
  have hL'ne : exceptionalFreePartForModulus aux.L E 4 ≠ 0 := Nat.ne_of_gt hL'pos
  have hEconditions :=
    paper95_exceptional_moduli_conditions_for_four_of_nat_fifth_power_scale E X hX hElog
  have hDmem :
    ∀ d,
      d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q →
        d ∣ exceptionalFreePartForModulus aux.L E 4 ∧ d ≤ y ∧ aux.q < d := by
    intro d hdD
    exact (mem_largeRestrictedDivisors hL'ne).mp hdD
  have hpos :
    ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q, 0 < d := by
    intro d hdD
    exact Nat.pos_of_dvd_of_pos (hDmem d hdD).1 hL'pos
  have hd :
    ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q, d ≤ X ^ 2 := by
    intro d hdD
    exact le_trans ((hDmem d hdD).2.1) (reliableProp15DivisorCutoff_fifth_power_le_square X)
  have hdm :
    ∀ d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q,
      Nat.Coprime d 4 := by
    intro d hdD
    exact Nat.Coprime.coprime_dvd_left (dvd_trans (hDmem d hdD).1 hL'div) aux.hProp15Input.2.1
  have htheta :
    ∀ d,
      ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q,
        ((d * X ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * 4) : ℝ)) ≤
          thetaInProgressionReal ((d * X ^ 3 : ℕ) : ℝ) (d * 4)
            (progressionCoprimeResidue d 4 3 (hdm d hdD)) := by
    intro d hdD
    have havoid : ∀ e ∈ E, ¬e ∣ d * 4 :=
      exceptionalFreePartForModulus_divisors_avoid aux.L E 4 hLne aux.hProp15Input.1 hEconditions.1
        hEconditions.2 aux.hProp15Input.2.1 d (hDmem d hdD).1
    exact hthetaAll d (hdm d hdD) (hpos d hdD) (hd d hdD) havoid
  have hrecip : (∑ r ∈ aux.L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ) := aux.hReciprocal1024
  have hcoeffmargin :
    16 * (2 ^ Dexc : ℝ) * c₁ <
      agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024) := by
    simpa only [beta] using hmargin
  have hBTbound :
    ∀ d,
      ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q,
        ∀ r : { r // r ∈ aux.L.primeFactors },
          (primeCountInProgression (d * X ^ 3) (d * r.val * 4)
                (progressionCoprimeResidue (d * r.val) 4 3
                  (Nat.Coprime.mul_left (hdm d hdD)
                    (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp r.property).2.1
                      aux.hProp15Input.2.1))) :
              ℝ) ≤
            (640 / 3) * (r.val : ℝ)⁻¹ *
              (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
    intro d hdD r
    have hrprop := Nat.mem_primeFactors.mp r.property
    have hrd4 : Nat.Coprime (d * r.val) 4 :=
      Nat.Coprime.mul_left (hdm d hdD) (Nat.Coprime.of_dvd_left hrprop.2.1 aux.hProp15Input.2.1)
    have hclass :=
      progressionCoprimeResidue_spec (d * r.val) 4 3 hrd4 (by norm_num only : Nat.Coprime 3 4)
    have hX32 : 32 ≤ X := le_trans (by norm_num only : 32 ≤ 2 ^ 56) hX
    exact
      agp_coarse_sieve_bound hX32 (hpos d hdD) hrprop.1
        (le_trans (aux.hfactor r.val hrprop.2.1 hrprop.1) hqleX)
        (Nat.Coprime.of_dvd_left hrprop.2.1 aux.hProp15Input.2.1) hclass.2.2
  let data :=
    agpProgressionCountData_of_fifth_power_theta_and_brun_titchmarsh W C c₁ x₀ X 2 y Dexc T E
      (640 / 3) (1 / 1024) (by norm_num only) aux hX hx₀ hbeta hEconditions hEcard hScale rfl rfl
      hpos hd hdm htheta hrecip hBTbound hcoeffmargin
  refine ⟨X, data, hX, ?_, ?_⟩
  · rfl
  · change aux.q ≤ X
    exact hqleX

end PseudoPrime.AnalyticNumberTheory.AGP
