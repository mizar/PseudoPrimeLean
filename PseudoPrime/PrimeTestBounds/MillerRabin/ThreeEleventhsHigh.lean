/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedRootComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedTriangularWidth24

/-! # Three-elevenths witness bound on a high logarithmic range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At logarithmic scale at least one trillion, the square root of the chosen
linear comparison radius is bounded by one millionth of the scale. -/
theorem three_eleven_sqrt_cap {L : ℝ} (hL : 1000000000000 ≤ L) :
    Real.sqrt ((52223 / 100000 : ℝ) * L) ≤ L / 1000000 := by
  apply (Real.sqrt_le_left (show (0 : ℝ) ≤ L / 1000000 by linarith only [hL])).mpr
  nlinarith only [hL, sq_nonneg (L - 1000000000000)]

/-- At the high-scale comparison radius, the quadratic defining the paper
root is nonpositive for every allowance at most three. -/
theorem three_eleven_root_budget {L K z : ℝ} (hL : 1000000000000 ≤ L) (hK3 : K ≤ 3)
    (hzsq : z ^ 2 = (52223 / 100000 : ℝ) * L) (hzcap : z ≤ L / 1000000) :
    (3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K + (53 / 500 : ℝ) * z ≤ (24439 / 50000 : ℝ) * z ^ 2 := by
  norm_num only at ⊢
  nlinarith only [hzsq, hzcap, hL, hK3]

/-- For scale at least one trillion and allowance between zero and three,
the squared paper root is bounded by the chosen linear comparison radius. -/
theorem three_eleven_root_sq_le {L K : ℝ} (hL : 1000000000000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3) :
    refinedPaperRoot L K ^ 2 ≤ (52223 / 100000 : ℝ) * L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  let z : ℝ := Real.sqrt ((52223 / 100000 : ℝ) * L)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z ^ 2 = (52223 / 100000 : ℝ) * L := Real.sq_sqrt (mul_nonneg (by norm_num only) hL0)
  have hz20 : (20 : ℝ) ≤ z := by nlinarith only [hzsq, hz0, hL]
  have hbudget := three_eleven_root_budget hL hK3 hzsq (three_eleven_sqrt_cap hL)
  have hs := refined_root_le_of_budget hL0 hK hz20 hbudget
  have hp := refined_paper_root_positive L K
  have hsq := pow_le_pow_left₀ hp.le hs 2
  simpa only [hzsq] using hsq

/-- The paper's fourth-power cutoff is at most three elevenths of the squared
scale on the high range, uniformly in allowances between zero and three. -/
theorem three_eleven_paper_bound {L K : ℝ} (hL : 1000000000000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3) :
    refinedPaperBound L K ≤ (3 / 11 : ℝ) * L ^ 2 := by
  have hroot := three_eleven_root_sq_le hL hK hK3
  have hsq := pow_le_pow_left₀ (sq_nonneg (refinedPaperRoot L K)) hroot 2
  dsimp only [refinedPaperBound]
  nlinarith only [hsq, sq_nonneg L]

/-- Under GRH, every odd composite on this high logarithmic range has a
rejecting prime at most three elevenths of its squared logarithm. -/
theorem three_eleven_high {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1000000000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hscale : (1000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hw :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 16
    · exact refined_index16_witness hn ho hc hi hGRH hscale
    · have hlarge : 10 ^ 16 ≤ (PrimeTest.fermatSubgroup n).index := Nat.le_of_lt (lt_of_not_ge hi)
      by_cases hy :
        Real.log (refinedPaperBound (Real.log n) (refinedPaperAllowance (Real.log n))) ≤ 48
      · exact refined_24_inner_witness hn ho hlarge hGRH hscale hy
      · exact refined_24_outer_witness hn ho hlarge hGRH hscale (le_of_not_ge hy)
  obtain ⟨p, hp, hb, hf⟩ := hw
  have hcompare :
    refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ≤ (3 / 11 : ℝ) * Real.log n ^ 2 := by
    rw [refined_piecewise_high (by linarith only [hL] : (1000 : ℝ) ≤ Real.log n)]
    exact three_eleven_paper_bound hL (refined_allowance_range _).1 (refined_allowance_range _).2
  exact ⟨p, hp, hb.trans hcompare, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
