/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRemainderEntry
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRemainderBernstein
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData

/-! # Checked large-cutoff charge at the K186 entry -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The unit-grid calculation bounds the K186 absolute integral up to seventeen. -/
private theorem k186_entry_integral_check :
    highRemainderChargeTicks .k186 17 72 1 (1 / 4) (fun j ↦ (j : ℚ)) ≤ 6000000000000 := by
  decide +kernel

/-- The large-cutoff H27 term for log intervals contained in `[11,12]` is at most `1/10000`. -/
public theorem h27_k186_entry_bound {l u : ℝ} (hl : 11 ≤ l) (hlu : l ≤ u) (hu : u ≤ 12) :
    let D := (highRemainderRatPoly .k186).map (Rat.castHom ℝ)
    Real.exp (-(5 * (HighGaussianKernel.k186.pole : ℝ))) *
        ((5 / 4 * Real.exp (((HighGaussianKernel.k186.pole : ℝ) - 1 / 2 - 2) * 5)) *
          (Real.exp (-(5 / 2 : ℝ) * l) *
            (∫ t in (0 : ℝ)..(5 + u), Real.exp (-(1 / 4 : ℝ) * t) * |D.eval t|))) ≤
      1 / 10000 :=
  h27_k186_finite_entry hl hlu hu k186_entry_integral_check

end PseudoPrime.PrimeTestBounds.MillerRabin
