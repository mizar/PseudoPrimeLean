/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltSubgroup
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianVariableWitness

/-! # Gaussian witnesses for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple has a Gaussian rejecting-prime witness
at the specified radius when the 7/20-width prefix, cutoff, scalar budget and
residual conditions hold. Its conductor sum is supplied by the arithmetic
subgroup construction rather than assumed separately. -/
theorem uniformKorselt_gaussian_witness {n : ℕ} [NeZero n] (ho : Odd n) (hn : 20000 ≤ n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {P R r : ℝ} {N : ℕ} (hr : 130 ≤ r)
    (hprefix : P ≤ ∑ j ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight j)
    (hcut : (N : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2)
    (hbudget :
      (20115621 / 25000000 : ℝ) * Real.log n + R + (1598411439 / 700000000 : ℝ) * Real.sqrt r ≤
        (10971611 / 5000000 : ℝ) * r)
    (hres :
      4 *
            (21 * (2129 / 2000 : ℝ) / (10 * (7 / 20 : ℝ) * Real.sqrt r) +
              1839 * (2129 / 2000 : ℝ) / (1000 * r)) +
          13 +
          3 * LLS.PaperStatements.gaussianPrefixError P n (r ^ 2) <
        R) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (21 / 10 : ℝ) * r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨H, hi, hpass, hC⟩ := uniformKorselt_subgroup_data ho hu
  exact gaussian_seven_twentieths_witness ho hn H hi hpass hGRH hC.le hr hprefix hcut hbudget hres

end PseudoPrime.PrimeTestBounds.MillerRabin
