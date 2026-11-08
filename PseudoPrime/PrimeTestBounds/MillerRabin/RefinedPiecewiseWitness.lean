/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Analytic1000
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedTriangularWidth24

/-! # Piecewise witnesses from the global 0.28 bound and high-range estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with `8 ≤ log n < 1000` has a prime witness
bounded by the piecewise coefficient. The stronger 0.28 witness is compared
with the low-range coefficient. -/
theorem refined_piecewise_low_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ refinedPaperCoefficient (Real.log n) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  rw [refinedPaperCoefficient, ite_eq_left hU]
  obtain ⟨p, hp, hb, hf⟩ := exists_reject_028_analytic1000 hn ho hc hGRH hL hU.le
  exact
    ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg (Real.log n))), hf⟩

/-- Under GRH, an odd composite with `log n ≥ 8` has a witness within the
piecewise bound if either its logarithm is below `1000` or its Fermat subgroup
has index at most `10^9`. The low-range witness and the certified high-range
finite-index classification cover these alternatives. -/
theorem refined_piecewise_covered_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hcover : Real.log n < 1000 ∨ (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hsmall : Real.log n < 1000
  · exact refined_piecewise_low_witness hn ho hc hGRH hL hsmall
  · have hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9 := hcover.resolve_left hsmall
    exact refined_low_index_witness hn ho hc hi hGRH (le_of_not_gt hsmall)

/-- Under GRH, the piecewise bound holds when `log n ≥ 8` and either the low
branch applies or the Fermat subgroup index is at most `10^16`. Combine the
existing low-range theorem with the finite-index reduction above. -/
theorem refined_piecewise_index16 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hcover : Real.log n < 1000 ∨ (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 16) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hsmall : Real.log n < 1000
  · exact refined_piecewise_low_witness hn ho hc hGRH hL hsmall
  · exact refined_index16_witness hn ho hc (hcover.resolve_left hsmall) hGRH (le_of_not_gt hsmall)

/-- Under GRH, the paper's piecewise cutoff has a rejecting prime whenever
the low logarithmic branch, the small Fermat-index branch, or the width-24
inner-support branch applies. Split by logarithmic size and subgroup index. -/
theorem refined_piecewise_inner_or_index {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hcover :
      Real.log n < 1000 ∨
        (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 16 ∨
        Real.log (refinedPaperBound (Real.log n) (refinedPaperAllowance (Real.log n))) ≤ 48) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hsmall : Real.log n < 1000
  · exact refined_piecewise_low_witness hn ho hc hGRH hL hsmall
  · by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 16
    · exact refined_index16_witness hn ho hc hi hGRH (le_of_not_gt hsmall)
    · have hy := (hcover.resolve_left hsmall).resolve_left hi
      have hlarge : 10 ^ 16 ≤ (PrimeTest.fermatSubgroup n).index := Nat.le_of_lt (lt_of_not_ge hi)
      exact refined_24_inner_witness hn ho hlarge hGRH (le_of_not_gt hsmall) hy

/-- Under GRH, every odd composite with `log n ≥ 8` has a rejecting prime
bounded by the piecewise paper coefficient. Combine the low and small-index
branches with the inner and outer width-24 high-index witnesses. -/
theorem refined_piecewise_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ refinedPaperCoefficient (Real.log n) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hsmall : Real.log n < 1000
  · exact refined_piecewise_low_witness hn ho hc hGRH hL hsmall
  · by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 16
    · exact refined_index16_witness hn ho hc hi hGRH (le_of_not_gt hsmall)
    · have hlarge : 10 ^ 16 ≤ (PrimeTest.fermatSubgroup n).index := Nat.le_of_lt (lt_of_not_ge hi)
      by_cases hy :
        Real.log (refinedPaperBound (Real.log n) (refinedPaperAllowance (Real.log n))) ≤ 48
      · exact refined_24_inner_witness hn ho hlarge hGRH (le_of_not_gt hsmall) hy
      · exact refined_24_outer_witness hn ho hlarge hGRH (le_of_not_gt hsmall) (le_of_not_ge hy)

end PseudoPrime.PrimeTestBounds.MillerRabin
