/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveWitness

/-! # Scale monotonicity for the adaptive triangular root

The scaled quadratic has increasing coefficients. These identities reduce its monotonicity
to the monotonicity of the square root and of the eighth root.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The triangular eighth root is nondecreasing on the real line. Each nested square
root and multiplication by the positive coefficient is nondecreasing. This compares
the denominator costs at two logarithmic scales. -/
theorem triangularEighthRoot_mono {L M : ℝ} (hLM : L ≤ M) :
    triangularEighthRoot L ≤ triangularEighthRoot M := by
  dsimp only [triangularEighthRoot]
  apply Real.sqrt_le_sqrt
  apply Real.sqrt_le_sqrt
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hLM (by norm_num only)

/-- At logarithmic scale `L ≥ 3 * 10 ^ 10`, the quotient of `L` by the eighth
root equals its seventh power divided by `5313 / 10000`. Cancel the positive root
from its exact eighth-power equation. This identifies the monotone scaled cost. -/
theorem triangular_scale_div_root {L : ℝ} (hL : 30000000000 ≤ L) :
    L / triangularEighthRoot L = (triangularEighthRoot L) ^ 7 / (5313 / 10000 : ℝ) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hm : 0 < triangularEighthRoot L := by
    have hh := triangularEighthRoot_ge_18 hL
    linarith only [hh]
  have h8 := (triangularEighthRoot_pow hL0).2
  apply (div_eq_iff hm.ne').mpr
  have he : (triangularEighthRoot L) ^ 7 * triangularEighthRoot L = (5313 / 10000 : ℝ) * L := by
    rw [← h8]
    ring
  rw [div_mul_eq_mul_div, he, mul_div_cancel_left₀ L (by norm_num only : (5313 / 10000 : ℝ) ≠ 0)]

/-- At logarithmic scale `L ≥ 3 * 10 ^ 10`, multiplying the adaptive constant term
by `L ^ 2` gives the fixed conductor cost times `L` divided by the eighth root.
Cancel the nonzero scale. This is the constant term of the scaled quadratic. -/
theorem triangular_scaled_cost {L : ℝ} (hL : 30000000000 ≤ L) :
    triangularAdaptiveD L * L ^ 2 =
      (4000000000000 * (1001 / 1000) : ℝ) * (L / triangularEighthRoot L) := by
  have hL0 : L ≠ 0 := (show 0 < L by linarith only [hL]).ne'
  dsimp only [triangularAdaptiveD]
  rw [div_mul_eq_div_div]
  have he :
    ((4000000000000 * (1001 / 1000) : ℝ) / triangularEighthRoot L / L) * L ^ 2 =
      ((4000000000000 * (1001 / 1000) : ℝ) / triangularEighthRoot L / L * L) * L := by
    ring
  rw [he, div_mul_cancel₀ _ hL0]
  ring

/-- At logarithmic scale `L ≥ 3 * 10 ^ 10`, the scaled linear coefficient is
`36 * L + E * sqrt L + 165102`. Cancel the nonzero scale and use `sqrt L ^ 2 = L`.
This expression is nondecreasing and controls the scaled quadratic root. -/
theorem triangular_scaled_linear {L : ℝ} (hL : 30000000000 ≤ L) :
    triangularAdaptiveA L * L = 36 * L + (1456 + 13 / 10000000) * Real.sqrt L + 165102 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hv : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have he : L / Real.sqrt L = Real.sqrt L := by
    apply (div_eq_iff hv.ne').mpr
    exact (Real.sq_sqrt hL0.le).symm.trans (by ring)
  dsimp only [triangularAdaptiveA]
  have hc : (165102 : ℝ) / L * L = 165102 := div_mul_cancel₀ _ hL0.ne'
  have hs :
    ((1456 + 13 / 10000000 : ℝ) / Real.sqrt L) * L = (1456 + 13 / 10000000) * Real.sqrt L := by
    rw [div_mul_eq_mul_div, mul_div_assoc, he]
  nlinarith only [hc, hs]

/-- For `3 * 10 ^ 10 ≤ L ≤ M`, the positive quadratic root multiplied by its scale
is nondecreasing. The scaled linear and constant coefficients are nondecreasing, so the
quadratic comparison applies to the two positive roots. This transfers the adaptive
budget to a common cumulative endpoint. -/
theorem triangular_scaled_root_mono {L M : ℝ} (hL : 30000000000 ≤ L) (hLM : L ≤ M) :
    triangularPositiveRoot (68 - 3 / 10000) (triangularAdaptiveA L) (triangularAdaptiveD L) * L ≤
      triangularPositiveRoot (68 - 3 / 10000) (triangularAdaptiveA M) (triangularAdaptiveD M) *
        M := by
  let K : ℝ := 68 - 3 / 10000
  let r := triangularPositiveRoot K (triangularAdaptiveA L) (triangularAdaptiveD L)
  let s := triangularPositiveRoot K (triangularAdaptiveA M) (triangularAdaptiveD M)
  have hM : (30000000000 : ℝ) ≤ M := hL.trans hLM
  have hL0 : 0 < L := by linarith only [hL]
  have hM0 : 0 < M := by linarith only [hM]
  have hK : 0 < K := by norm_num only [K]
  have hBL := triangularAdaptive_budget hL
  have hBM := triangularAdaptive_budget hM
  have hr := triangularPositiveRoot_spec hK hBL.1 hBL.2.1
  have hs := triangularPositiveRoot_spec hK hBM.1 hBM.2.1
  have hlin : triangularAdaptiveA L * L ≤ triangularAdaptiveA M * M := by
    rw [triangular_scaled_linear hL, triangular_scaled_linear hM]
    have hsqrt := Real.sqrt_le_sqrt hLM
    linarith only [hLM, hsqrt]
  have hroot := triangularEighthRoot_mono hLM
  have hcost : triangularAdaptiveD L * L ^ 2 ≤ triangularAdaptiveD M * M ^ 2 := by
    rw [triangular_scaled_cost hL, triangular_scaled_cost hM, triangular_scale_div_root hL,
      triangular_scale_div_root hM]
    have hpow := pow_le_pow_left₀ (triangularEighthRoot_pow hL0.le).1 hroot 7
    have hdiv := div_le_div_of_nonneg_right hpow (by norm_num only : (0 : ℝ) ≤ 5313 / 10000)
    exact mul_le_mul_of_nonneg_left hdiv (by norm_num only)
  have heL :
    K * (r * L) ^ 2 = (triangularAdaptiveA L * L) * (r * L) + triangularAdaptiveD L * L ^ 2 := by
    have hh := congrArg (fun z : ℝ ↦ z * L ^ 2) hr.2
    nlinarith only [hh]
  have heM :
    K * (s * M) ^ 2 = (triangularAdaptiveA M * M) * (s * M) + triangularAdaptiveD M * M ^ 2 := by
    have hh := congrArg (fun z : ℝ ↦ z * M ^ 2) hs.2
    nlinarith only [hh]
  have hscaled : 0 < r * L := mul_pos hr.1 hL0
  have hscaledM : 0 < s * M := mul_pos hs.1 hM0
  apply triangular_root_le_of_budget hK (mul_nonneg hBL.2.1 (sq_nonneg L)) hscaled hscaledM heL
  have hh := mul_le_mul_of_nonneg_right hlin hscaledM.le
  nlinarith only [hh, hcost, heM]

/-- The radius history at the three-factor floor switch. Before the switch it is zero;
afterward it records the preceding floor evaluated at the switch. This compensates for
the downward change of the floor when transferring pointwise bounds to later endpoints. -/
noncomputable def triangularFloorHistory (L : ℝ) : ℝ :=
  if (1820000000000 : ℝ) ≤ L then Real.sqrt (28237 / 100000) * 1820000000000 else 0

/-- For `3 * 10 ^ 10 ≤ L ≤ M`, the adaptive radius times `L` is bounded by the
maximum of the radius at `M) times `M` and the floor-switch history. The scaled
positive root is nondecreasing; the floor branch is monotone except at its single
downward switch. This is the common-endpoint comparison for cumulative bounds. -/
theorem triangular_scaled_radius_le {L M : ℝ} (hL : 30000000000 ≤ L) (hLM : L ≤ M) :
    triangularAdaptiveRadius L * L ≤
      max (triangularAdaptiveRadius M * M) (triangularFloorHistory M) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hM0 : 0 ≤ M := hL0.trans hLM
  have hroot := triangular_scaled_root_mono hL hLM
  have hrootM :
    triangularPositiveRoot (68 - 3 / 10000) (triangularAdaptiveA M) (triangularAdaptiveD M) * M ≤
      triangularAdaptiveRadius M * M :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hM0
  have hfloor :
    Real.sqrt (triangularAdaptiveFloor L) * L ≤
      max (triangularAdaptiveRadius M * M) (triangularFloorHistory M) := by
    by_cases hM : (1820000000000 : ℝ) ≤ M
    · by_cases hT : (1820000000000 : ℝ) ≤ L
      · have he : triangularAdaptiveFloor L = triangularAdaptiveFloor M := by
          rw [triangularAdaptiveFloor, ite_eq_left hT, triangularAdaptiveFloor, ite_eq_left hM]
        have hs : Real.sqrt (triangularAdaptiveFloor L) ≤ triangularAdaptiveRadius M := by
          rw [he]
          exact le_max_left _ _
        have hs' :=
          mul_le_mul hs hLM hL0
            (show 0 ≤ triangularAdaptiveRadius M
              by
              have hh := (triangularAdaptiveRadius_bounds (hL.trans hLM)).1
              linarith only [hh])
        exact hs'.trans (le_max_left _ _)
      · rw [triangularAdaptiveFloor, ite_eq_right hT, triangularFloorHistory, ite_eq_left hM]
        exact
          (mul_le_mul_of_nonneg_left (le_of_not_ge hT) (Real.sqrt_nonneg _)).trans
            (le_max_right _ _)
    · have hT : ¬(1820000000000 : ℝ) ≤ L := fun ht ↦ hM (ht.trans hLM)
      have he : triangularAdaptiveFloor L = triangularAdaptiveFloor M := by
        rw [triangularAdaptiveFloor, ite_eq_right hT, triangularAdaptiveFloor, ite_eq_right hM]
      have hs : Real.sqrt (triangularAdaptiveFloor L) ≤ triangularAdaptiveRadius M := by
        rw [he]
        exact le_max_left _ _
      have hs' :=
        mul_le_mul hs hLM hL0
          (show 0 ≤ triangularAdaptiveRadius M
            by
            have hh := (triangularAdaptiveRadius_bounds (hL.trans hLM)).1
            linarith only [hh])
      exact hs'.trans (le_max_left _ _)
  dsimp only [triangularAdaptiveRadius]
  rw [max_mul_of_nonneg _ _ hL0]
  exact max_le hfloor ((hroot.trans hrootM).trans (le_max_left _ _))

end PseudoPrime.PrimeTestBounds.MillerRabin
