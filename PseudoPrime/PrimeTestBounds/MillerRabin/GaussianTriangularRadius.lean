/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveCoefficients
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveCoefficients

/-! # Compatibility of the adaptive Gaussian and triangular radii -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At scale at least two trillion, the triangular budget root is at most
`5313 / 10000`. Entrance bounds for its three correction terms certify the
quadratic inequality; this prepares the Gaussian cutoff for the large-index branch. -/
theorem gaussianTriangular_root_le {L : ℝ} (hL : 2000000000000 ≤ L) :
    triangularPositiveRoot (68 - 3 / 10000) (triangularAdaptiveA L) (triangularAdaptiveD L) ≤
      (5313 / 10000 : ℝ) := by
  have hm : (31 : ℝ) ≤ triangularEighthRoot L := by
    have ht := triangularEighthRoot_pow (show 0 ≤ L by linarith only [hL])
    have h0 : 0 ≤ triangularEighthRoot L := Real.sqrt_nonneg _
    by_contra hn
    have hh : triangularEighthRoot L < 31 := lt_of_not_ge hn
    have hp := pow_le_pow_left₀ h0 hh.le 8
    rw [ht.2] at hp
    nlinarith only [hp, hL]
  have hv : (1414213 : ℝ) ≤ Real.sqrt L := Real.le_sqrt_of_sq_le (by nlinarith only [hL])
  have hden : (31 : ℝ) * 2000000000000 ≤ triangularEighthRoot L * L :=
    mul_le_mul hm hL (by norm_num only) (by linarith only [hm])
  have ha : (1456 + 13 / 10000000 : ℝ) / Real.sqrt L ≤ (1456 + 13 / 10000000) / 1414213 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hv
  have hb : (165102 : ℝ) / L ≤ 165102 / 2000000000000 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  have hc : triangularAdaptiveD L ≤ (4000000000000 * (1001 / 1000) : ℝ) / (31 * 2000000000000) :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hden
  have h30 : (30000000000 : ℝ) ≤ L := by linarith only [hL]
  have hbudget := triangularAdaptive_budget h30
  have hr :=
    triangularPositiveRoot_spec (K := 68 - 3 / 10000) (by norm_num only) hbudget.1 hbudget.2.1
  apply triangular_root_le_of_budget (by norm_num only) hbudget.2.1 hr.1 (by norm_num only) hr.2
  dsimp only [triangularAdaptiveA]
  nlinarith only [ha, hb, hc]

/-- The adaptive Gaussian radius is strictly above `5313 / 10000` at scale
at least two trillion. The constant part of its slope already supplies this floor,
which is used by the local and sixteenth-root conditions. -/
theorem gaussianTriangular_radius_gt (L : ℝ) (hL : 2000000000000 ≤ L) :
    (5313 / 10000 : ℝ) < Real.sqrt ((21 / 10) * adaptiveGaussianA L ^ 2) := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1 : 0 ≤ (61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (39 : ℝ) / L := div_nonneg (by norm_num only) hL0
  have ha : (3666849 / 10000000 : ℝ) ≤ adaptiveGaussianA L := by
    dsimp only [adaptiveGaussianA]
    apply (le_div_iff₀ (by norm_num only)).2
    linarith only [h1, h2]
  apply (Real.lt_sqrt (by norm_num only)).2
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3666849 / 10000000) ha 2
  nlinarith only [hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
