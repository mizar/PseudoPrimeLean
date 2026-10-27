/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.FixedThetaCountData
public import PseudoPrime.AnalyticNumberTheory.AGP.PrimorialP2SeedBridge

/-! # Progression count data from primorial P2 seeds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a fixed exponent and exceptional-set bound, together with the small-modulus
theta supply at every sufficiently large scale.

Claim: these data construct `AGPProgressionCountDataExists` without assuming the
initial uniform Proposition 1.5 count.

Proof: choose the coefficient from the exceptional-set budget, use the primorial P2
bridge to build full-divisor auxiliary data, then apply the theta and coarse-sieve
progression-count construction.

Role: joins the proposed narrow theta interface to the final finite progression data.
The theta supply itself remains the analytic input to be proved unconditionally.
-/
theorem agp_progression_count_data_exists_of_primorial_p2_and_theta_supply (J D Xtheta : ℕ)
    (hJ : 2 ≤ J)
    (hSupply :
      ∀ Z : ℕ,
        Xtheta ≤ Z →
          ∃ E : Finset ℕ,
            E.card ≤ D ∧
              (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
              ∀ m d a : ℕ,
                (m = 1 ∨ m = 4) →
                  0 < d →
                  Nat.Coprime d m →
                  1 < d * m →
                  (d * m) ^ J ≤ Z →
                  Nat.Coprime a (d * m) →
                  (∀ e ∈ E, ¬e ∣ d * m) →
                  (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                    thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a) :
    AGPProgressionCountDataExists := by
  let c₀ : ℝ := 1 / (128 * (2 ^ D : ℝ))
  let x₀ : ℕ := max 2 Xtheta
  have hpowPos : 0 < (2 ^ D : ℝ) := by positivity
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact one_div_pos.mpr (mul_pos (by norm_num only : (0 : ℝ) < 128) hpowPos)
  have hfactor : c₀ * (2 : ℝ) ^ D ≤ 1 / 128 := by
    dsimp only [c₀]
    field_simp [ne_of_gt hpowPos]
    norm_num only
  have hbetaQuarter :
    (1 / 4 : ℝ) < agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024) :=
    agp_fifth_power_average_coefficient_640_1024_gt_quarter
  have hbeta : 0 < agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024) :=
    lt_trans (by norm_num only : (0 : ℝ) < 1 / 4) hbetaQuarter
  have hcoeffmargin :
    16 * (2 ^ D : ℝ) * c₀ <
      agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024) := by
    calc
      16 * (2 ^ D : ℝ) * c₀ = 1 / 8 := by
        dsimp only [c₀]
        field_simp [ne_of_gt hpowPos]
        norm_num only
      _ < 1 / 4 := by norm_num only
      _ < agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024) := hbetaQuarter
  have hXtheta : Xtheta ≤ x₀ := le_max_right _ _
  have hSupply' :
    ∀ Z : ℕ,
      x₀ ≤ Z →
        ∃ E : Finset ℕ,
          E.card ≤ D ∧
            (∀ e ∈ E, 1 < e ∧ ¬e ∣ 4) ∧
            ∀ m d a : ℕ,
              (m = 1 ∨ m = 4) →
                0 < d →
                Nat.Coprime d m →
                1 < d * m →
                (d * m) ^ J ≤ Z →
                Nat.Coprime a (d * m) →
                (∀ e ∈ E, ¬e ∣ d * m) →
                (((d * Z ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * m) : ℝ))) ≤
                  thetaInProgressionReal ((d * Z ^ 3 : ℕ) : ℝ) (d * m) a := by
    intro Z hZ
    exact hSupply Z (le_trans hXtheta hZ)
  refine ⟨c₀, hc₀, x₀, le_max_left _ _, ?_⟩
  intro W C hWpos
  obtain ⟨Y, aux, hY, hAuxScale, hqleY, hx₀Y, hdivisorScale⟩ :=
    exists_full_divisor_auxiliary_data_of_p2_primorial_tail hc₀ hJ W C D x₀ hfactor hSupply'
  obtain ⟨E, hEcard, hEindividual, hTheta⟩ := hSupply' Y hx₀Y
  have hEconditions : (∀ e ∈ E, 1 < e) ∧ ∀ e ∈ E, ¬e ∣ 4 := by
    constructor
    · intro e he
      exact (hEindividual e he).1
    · intro e he
      exact (hEindividual e he).2
  let y := reliableProp15DivisorCutoff (Y ^ 5)
  let T :=
    Nat.floor (reliableProp15Coefficient c₀ 4 (Y ^ 5) * ((restrictedDivisors aux.L y).card : ℝ)) + 1
  have hLpos : 0 < aux.L := lt_trans (by norm_num only : 0 < 2) aux.hL
  have hLne : aux.L ≠ 0 := Nat.ne_of_gt hLpos
  have hL'div : exceptionalFreePartForModulus aux.L E 4 ∣ aux.L :=
    (exceptionalFreePartForModulus_properties aux.L E 4 hLne aux.hProp15Input.1).2.2.1
  have hL'pos : 0 < exceptionalFreePartForModulus aux.L E 4 := Nat.pos_of_dvd_of_pos hL'div hLpos
  have hL'ne : exceptionalFreePartForModulus aux.L E 4 ≠ 0 := Nat.ne_of_gt hL'pos
  have hDmem :
    ∀ d,
      d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q →
        d ∣ exceptionalFreePartForModulus aux.L E 4 ∧ d ≤ y ∧ aux.q < d := by
    intro d hdD
    exact (mem_largeRestrictedDivisors hL'ne).mp hdD
  have hpos :
    ∀ d, d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q → 0 < d := by
    intro d hdD
    exact Nat.pos_of_dvd_of_pos (hDmem d hdD).1 hL'pos
  have hd :
    ∀ d,
      d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q →
        d ≤ Y ^ 2 := by
    intro d hdD
    exact le_trans ((hDmem d hdD).2.1) (reliableProp15DivisorCutoff_fifth_power_le_square Y)
  have hdm :
    ∀ d,
      d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q →
        Nat.Coprime d 4 := by
    intro d hdD
    exact Nat.Coprime.coprime_dvd_left (dvd_trans (hDmem d hdD).1 hL'div) aux.hProp15Input.2.1
  have htheta :
    ∀ d,
      ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q,
        ((d * Y ^ 3 : ℕ) : ℝ) / (2 * (Nat.totient (d * 4) : ℝ)) ≤
          thetaInProgressionReal ((d * Y ^ 3 : ℕ) : ℝ) (d * 4)
            (progressionCoprimeResidue d 4 3 (hdm d hdD)) := by
    intro d hdD
    have havoid : ∀ e ∈ E, ¬e ∣ d * 4 :=
      exceptionalFreePartForModulus_divisors_avoid aux.L E 4 hLne aux.hProp15Input.1 hEconditions.1
        hEconditions.2 aux.hProp15Input.2.1 d (hDmem d hdD).1
    have hdscale : (d * 4) ^ J ≤ Y := by
      simpa only [Nat.mul_comm d 4] using hdivisorScale d (dvd_trans (hDmem d hdD).1 hL'div)
    have h1d : 1 ≤ d := Nat.succ_le_iff.mpr (hpos d hdD)
    have h2le : 2 ≤ d * 4 := by
      calc
        2 = 1 * 2 := by norm_num only
        _ ≤ d * 4 := Nat.mul_le_mul h1d (by norm_num only)
    have hdgt : 1 < d * 4 := lt_of_lt_of_le (by norm_num only) h2le
    have hres :=
      progressionCoprimeResidue_spec d 4 3 (hdm d hdD) (by norm_num only : Nat.Coprime 3 4)
    exact
      hTheta 4 d (progressionCoprimeResidue d 4 3 (hdm d hdD)) (Or.inr rfl) (hpos d hdD) (hdm d hdD)
        hdgt hdscale hres.2.2 havoid
  have hrecip : (∑ r ∈ aux.L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ) := aux.hReciprocal1024
  have hBT :
    ∀ d,
      ∀ hdD : d ∈ largeRestrictedDivisors (exceptionalFreePartForModulus aux.L E 4) y aux.q,
        ∀ r : { r // r ∈ aux.L.primeFactors },
          (primeCountInProgression (d * Y ^ 3) (d * r.val * 4)
                (progressionCoprimeResidue (d * r.val) 4 3
                  (Nat.Coprime.mul_left (hdm d hdD)
                    (Nat.Coprime.of_dvd_left (Nat.mem_primeFactors.mp r.property).2.1
                      aux.hProp15Input.2.1))) :
              ℝ) ≤
            (640 / 3) * (r.val : ℝ)⁻¹ *
              (((d * Y ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ) / Real.log ((Y ^ 5 : ℕ) : ℝ)) := by
    intro d hdD r
    have hrprop := Nat.mem_primeFactors.mp r.property
    have hrd4 : Nat.Coprime (d * r.val) 4 :=
      Nat.Coprime.mul_left (hdm d hdD) (Nat.Coprime.of_dvd_left hrprop.2.1 aux.hProp15Input.2.1)
    have hclass :=
      progressionCoprimeResidue_spec (d * r.val) 4 3 hrd4 (by norm_num only : Nat.Coprime 3 4)
    have hY32 : 32 ≤ Y := le_trans (by norm_num only : 32 ≤ 2 ^ 56) hY
    exact
      agp_coarse_sieve_bound hY32 (hpos d hdD) hrprop.1
        (le_trans (aux.hfactor r.val hrprop.2.1 hrprop.1) hqleY)
        (Nat.Coprime.of_dvd_left hrprop.2.1 aux.hProp15Input.2.1) hclass.2.2
  have hcoeff : 0 < agpFifthPowerAverageCoefficientOfProgressionBound (640 / 3) (1 / 1024) := hbeta
  let data :=
    agpProgressionCountData_of_fifth_power_theta_and_brun_titchmarsh W C c₀ x₀ Y x₀ y D T E
      (640 / 3) (1 / 1024) (by norm_num only) aux hY (by rfl) hcoeff hEconditions hEcard hAuxScale
      rfl rfl hpos hd hdm htheta hrecip hBT hcoeffmargin
  refine ⟨Y, data, hY, ?_, ?_⟩
  · rfl
  · change aux.q ≤ Y
    exact hqleY

end PseudoPrime.AnalyticNumberTheory.AGP
