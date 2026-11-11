/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedPiecewiseWitness
import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedRootComparison

/-! # Three-elevenths witness bound on a high logarithmic range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At logarithmic scale at least four million, the square root of the chosen
linear comparison radius is bounded by `(2 / 5535) * L`. -/
private theorem three_eleven_sqrt_cap_4m {L : ℝ} (hL : 4000000 ≤ L) :
    Real.sqrt ((52223296 / 100000000 : ℝ) * L) ≤ L / (5535 / 2) := by
  apply (Real.sqrt_le_left (show (0 : ℝ) ≤ L / (5535 / 2) by linarith only [hL])).mpr
  nlinarith only [hL, sq_nonneg (L - 4000000)]

/-- At the high-scale comparison radius, the quadratic defining the paper
root is nonpositive for every allowance at most zero. -/
private theorem three_eleven_root_budget_4m {L K z : ℝ} (hL : 4000000 ≤ L) (hK3 : K ≤ 0)
    (hzsq : z ^ 2 = (52223296 / 100000000 : ℝ) * L) (hzcap : z ≤ L / (5535 / 2)) :
    (3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K + (53 / 500 : ℝ) * z ≤ (24439 / 50000 : ℝ) * z ^ 2 := by
  norm_num only at ⊢
  nlinarith only [hzsq, hzcap, hL, hK3]

/-- For scale at least four million and allowance equal to zero,
the squared paper root is bounded by the chosen linear comparison radius. -/
private theorem three_eleven_root_sq_le_4m {L K : ℝ} (hL : 4000000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 0) :
    refinedPaperRoot L K ^ 2 ≤ (52223296 / 100000000 : ℝ) * L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  let z : ℝ := Real.sqrt ((52223296 / 100000000 : ℝ) * L)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z ^ 2 = (52223296 / 100000000 : ℝ) * L :=
    Real.sq_sqrt (mul_nonneg (by norm_num only) hL0)
  have hz20 : (20 : ℝ) ≤ z := by nlinarith only [hzsq, hz0, hL]
  have hbudget := three_eleven_root_budget_4m hL hK3 hzsq (three_eleven_sqrt_cap_4m hL)
  have hs := refined_root_le_of_budget hL0 hK hz20 hbudget
  have hp := refined_paper_root_positive L K
  have hsq := pow_le_pow_left₀ hp.le hs 2
  simpa only [hzsq] using hsq

/-- The paper's fourth-power cutoff is at most three elevenths of the squared
scale on the high range, uniformly in allowances equal to zero. -/
private theorem three_eleven_paper_bound_4m {L K : ℝ} (hL : 4000000 ≤ L) (hK : 0 ≤ K)
    (hK3 : K ≤ 0) : refinedPaperBound L K ≤ (3 / 11 : ℝ) * L ^ 2 := by
  have hroot := three_eleven_root_sq_le_4m hL hK hK3
  have hsq := pow_le_pow_left₀ (sq_nonneg (refinedPaperRoot L K)) hroot 2
  dsimp only [refinedPaperBound]
  nlinarith only [hsq, sq_nonneg L]

/-- Under GRH, every odd composite on this high logarithmic range has a
rejecting prime at most three elevenths of its squared logarithm. -/
theorem three_eleven_from_4m {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (4000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := refined_piecewise_witness hn ho hc hGRH (by linarith only [hL])
  have hcompare :
    refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ≤ (3 / 11 : ℝ) * Real.log n ^ 2 := by
    rw [refined_piecewise_high (by linarith only [hL] : (1000 : ℝ) ≤ Real.log n)]
    have hallow : refinedPaperAllowance (Real.log n) = 0 := by
      dsimp only [refinedPaperAllowance]
      rw [ite_eq_right (by linarith only [hL]), ite_eq_right (by linarith only [hL])]
    rw [hallow]
    exact three_eleven_paper_bound_4m hL le_rfl le_rfl
  exact ⟨p, hp, hb.trans hcompare, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
