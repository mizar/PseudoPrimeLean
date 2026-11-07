/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianMomentCells

/-! # Finite Gaussian moment grids at cutoff 21/10 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Rational cell caps bound both finite Gaussian moments at cutoff 21/10.
The explicit cell square minimum supplies the shared geometric condition.
These bounds accept independently certified inner and outer exponential endpoints. -/
theorem gaussian_moment_grid_bounds {p e uF uC : ℕ → ℝ} {n : ℕ} (hp : ∀ i < n, p i ≤ p (i + 1))
    (he : ∀ i < n, e i ≤ Real.exp (-p (i + 1)))
    (hF :
      ∀ i < n,
        Real.exp
            (-gaussianCellSquareLower (p i) (p (i + 1)) - (1 / 2 : ℝ) * p i - (21 / 10 : ℝ) * e i) ≤
          uF i)
    (hC :
      ∀ i < n,
        Real.exp
            (-gaussianCellSquareLower (p i) (p (i + 1)) - (3 / 2 : ℝ) * p i - (21 / 10 : ℝ) * e i) ≤
          uC i) :
    (∫ v in p 0..p n, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤
        ∑ i ∈ Finset.range n, (p (i + 1) - p i) * ((113 / 200 : ℝ) * uF i) ∧
      (∫ v in p 0..p n, gaussianEndpointDensity (21 / 10) v) ≤
        ∑ i ∈ Finset.range n, (p (i + 1) - p i) * ((113 / 200 : ℝ) * uC i) := by
  have hs :
    ∀ i < n, ∀ v ∈ Set.Icc (p i) (p (i + 1)), gaussianCellSquareLower (p i) (p (i + 1)) ≤ v ^ 2 :=
    fun i _ v hv ↦ gaussian_cell_square_lower hv.1 hv.2
  constructor
  · have h :=
      gaussian_density_integral_grid_upper (k := 1 / 2) (l := 21 / 10) (s := fun i ↦
        gaussianCellSquareLower (p i) (p (i + 1))) (by norm_num only) (by norm_num only) hp hs he hF
    simpa only [Analysis.gaussianGammaProfileIntegrand, neg_mul] using h
  · have h :=
      gaussian_density_integral_grid_upper (k := 3 / 2) (l := 21 / 10) (s := fun i ↦
        gaussianCellSquareLower (p i) (p (i + 1))) (by norm_num only) (by norm_num only) hp hs he hC
    simpa only [gaussianEndpointDensity, neg_mul] using h

end PseudoPrime.LLS.PaperStatements
