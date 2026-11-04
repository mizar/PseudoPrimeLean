/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveProfile
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfileBounds

/-! # Prime witnesses from the scale-dependent triangular profile -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with `log n ≥ 3 * 10 ^ 10` has a rejecting prime
bounded by the adaptive triangular coefficient times `log n ^ 2`. Construct the
certified profile at the actual logarithmic scale and apply the existing profile witness
theorem. This supplies an actual prime for the adaptive candidate. -/
theorem triangularAdaptive_prime_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (30000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (triangularAdaptiveRadius (Real.log n)) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    exists_prime_triangularProfile (triangularAdaptiveProfile (Real.log n) hL) hn ho hc hGRH
      (le_refl _)

/-- For `L ≥ 5 * 10 ^ 10`, the adaptive triangular radius is at most `5 / 8).
The eighth root is at least 20, and a rational upper budget bounds the positive
quadratic root. The three-factor floor is also below `(5 / 8) ^ 2`.
This gives a simple strict comparison with the preceding high-window envelope. -/
theorem triangularAdaptiveRadius_le_5_8 {L : ℝ} (hL : 50000000000 ≤ L) :
    triangularAdaptiveRadius L ≤ 5 / 8 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hL30 : (30000000000 : ℝ) ≤ L := by linarith only [hL]
  have hm := triangularEighthRoot_pow hL0.le
  have hm20 : (20 : ℝ) ≤ triangularEighthRoot L := by
    apply
      (pow_le_pow_iff_left₀ (by norm_num only : (0 : ℝ) ≤ 20) hm.1
          (by norm_num only : (8 : ℕ) ≠ 0)).mp
    rw [hm.2]
    norm_num only
    linarith only [hL]
  have hv : (223000 : ℝ) ≤ Real.sqrt L := Real.le_sqrt_of_sq_le (by nlinarith only [hL])
  have ha : (1456 + 13 / 10000000 : ℝ) / Real.sqrt L ≤ (1456 + 13 / 10000000) / 223000 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hv
  have hb : (165102 : ℝ) / L ≤ 165102 / 50000000000 :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  have hden : (20 : ℝ) * 50000000000 ≤ triangularEighthRoot L * L :=
    mul_le_mul hm20 hL (by norm_num only) (by linarith only [hm20])
  have hd : triangularAdaptiveD L ≤ (4000000000000 * (1001 / 1000) : ℝ) / (20 * 50000000000) :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hden
  have hbgt := triangularAdaptive_budget hL30
  have hr := triangularPositiveRoot_spec (K := 68 - 3 / 10000) (by norm_num only) hbgt.1 hbgt.2.1
  have hroot :
    triangularPositiveRoot (68 - 3 / 10000) (triangularAdaptiveA L) (triangularAdaptiveD L) ≤
      5 / 8 := by
    apply triangular_root_le_of_budget (by norm_num only) hbgt.2.1 hr.1 (by norm_num only) hr.2
    dsimp only [triangularAdaptiveA]
    norm_num only at ha hb hd ⊢
    linarith only [ha, hb, hd]
  have hg : Real.sqrt (triangularAdaptiveFloor L) ≤ 5 / 8 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num only
    · by_cases h : (1820000000000 : ℝ) ≤ L
      · rw [triangularAdaptiveFloor, ite_eq_left h]
        norm_num only
      · rw [triangularAdaptiveFloor, ite_eq_right h]
        norm_num only
  exact max_le hg hroot

end PseudoPrime.PrimeTestBounds.MillerRabin
