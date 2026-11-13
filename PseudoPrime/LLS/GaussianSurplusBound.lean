/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSignedEulerSeries
public import PseudoPrime.Analysis.GammaSignedEulerSeries
import PseudoPrime.LLS.GaussianSurplusPrefix

/-! # Table-free lower bound for the finite Gaussian surplus -/

public section

namespace PseudoPrime.LLS

/-- For `b ≥ 100`, the actual Gaussian Euler prefix exceeds seventeen
 twentieths of the corresponding Gamma prefix by at least `73/100`.
The finite certificate is consumed privately and its row data do not appear
in the statement. -/
theorem gaussian_surplus_prefix_bound {b : ℝ} (hb : 100 ≤ b) :
    (73 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊,
        (Analysis.gaussianResolventMangoldtWeight n -
          (17 / 20 : ℝ) * Analysis.gammaResolventMangoldtWeight n) := by
  have h := gaussianSurplus_prefix hb
  simpa only [gaussianSurplus_mangoldt_eq] using h

end PseudoPrime.LLS
