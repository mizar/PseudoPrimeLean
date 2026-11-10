/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorDivided
public import PseudoPrime.LLS.PaperStatements.TriangularNarrowCost

/-! # Explicit interior large-index comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, absence of rejecting primes up to `r²` gives an explicit
upper bound for the joint width-eight principal sum when the Fermat index is
at least 33000 and the scale lies within the kernel support. Combine the
interior subgroup comparison with the three principal-sum costs. -/
theorem quarter_interior_explicit_cost {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {r T : ℝ}
    (hr : 1 ≤ r) (hbound : Real.log (r ^ 2) ≤ 16) (hT : 0 ≤ T) (hscale : Real.log n ≤ T)
    (hindex : 33000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 8)
    (∑ m ∈ Finset.Icc 1 ⌊r ^ 2⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) m).re) +
        2 * (∑ m ∈ Finset.Icc 1 ⌊r ^ 2⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 m).re) ≤
      (32 - Real.log (r ^ 2)) * T + (137 / 330 : ℝ) * (r + r⁻¹) +
        (4 / 15 : ℝ) * (Real.sqrt r + (Real.sqrt r)⁻¹) +
        15 / 11 := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hX : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 1)]
  have hi : (33000 : ℝ) ≤ (PrimeTest.fermatSubgroup n).index := by exact_mod_cast hindex
  have hmain :=
    quarter_interior_divided hn ho (a := 8) (X := r ^ 2) (by norm_num only) hX
      (by linarith only [hbound]) hT hscale
      (by linarith only [hbound] : -6 * 8 + (3 / 2 : ℝ) * Real.log (r ^ 2) + 18 ≤ 0) hGRH hnone
  have hc := LLS.PaperStatements.triangular8_principal_cost hGRH.riemann hr0 hi
  dsimp only at hmain ⊢
  norm_num only at hmain
  linarith only [hmain, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
