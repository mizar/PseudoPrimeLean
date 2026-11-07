/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianMomentGrid256

/-! # Fixed-point certificates for the Gaussian moment grid -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Positive fixed-point lower endpoints for the negated rational exponents
bound both Gaussian integrals on [-4,4]. Rational identities and Taylor-size
conditions connect each executable outer endpoint to the corresponding cell. -/
theorem gaussian_grid_256_fixed_bounds {aF aC : ℕ → ℤ} {bF bC : ℕ → ℕ} {n : ℕ}
    (hbF : ∀ i < 256, 0 < bF i) (hbC : ∀ i < 256, 0 < bC i)
    (hsizeF : ∀ i < 256, (|((-(aF i) : ℤ) : ℝ)| / bF i) / (n + 1 : ℕ) ≤ 1 / 2)
    (hsizeC : ∀ i < 256, (|((-(aC i) : ℤ) : ℝ)| / bC i) / (n + 1 : ℕ) ≤ 1 / 2)
    (hposF : ∀ i < 256, 0 < Analysis.expFixedPointSignedLower (-(aF i)) (bF i) (10 ^ 24) n)
    (hposC : ∀ i < 256, 0 < Analysis.expFixedPointSignedLower (-(aC i)) (bC i) (10 ^ 24) n)
    (heqF :
      ∀ i < 256,
        -gaussianCellSquareLower (gaussianMomentGridPoint i) (gaussianMomentGridPoint (i + 1)) -
            (1 / 2 : ℝ) * gaussianMomentGridPoint i -
            (21 / 10 : ℝ) * ((gaussianMomentGridInner i : ℝ) / (10 ^ 24 : ℝ)) =
          (aF i : ℝ) / bF i)
    (heqC :
      ∀ i < 256,
        -gaussianCellSquareLower (gaussianMomentGridPoint i) (gaussianMomentGridPoint (i + 1)) -
            (3 / 2 : ℝ) * gaussianMomentGridPoint i -
            (21 / 10 : ℝ) * ((gaussianMomentGridInner i : ℝ) / (10 ^ 24 : ℝ)) =
          (aC i : ℝ) / bC i) :
    (∫ v in (-4 : ℝ)..4, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤
        ∑ i ∈ Finset.range 256,
          (1 / 32 : ℝ) *
            ((113 / 200 : ℝ) *
              ((10 ^ 24 : ℝ) /
                (Analysis.expFixedPointSignedLower (-(aF i)) (bF i) (10 ^ 24) n : ℝ))) ∧
      (∫ v in (-4 : ℝ)..4, gaussianEndpointDensity (21 / 10) v) ≤
        ∑ i ∈ Finset.range 256,
          (1 / 32 : ℝ) *
            ((113 / 200 : ℝ) *
              ((10 ^ 24 : ℝ) /
                (Analysis.expFixedPointSignedLower (-(aC i)) (bC i) (10 ^ 24) n : ℝ))) := by
  apply gaussian_grid_256_bounds
  · intro i hi
    rw [heqF i hi]
    have h :=
      Analysis.exp_upper_of_signed_fixed_lower (aF i) (bF i) (10 ^ 24) n (hbF i hi)
        (by norm_num only) (hsizeF i hi) (hposF i hi)
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at h
    norm_num only
    exact h
  · intro i hi
    rw [heqC i hi]
    have h :=
      Analysis.exp_upper_of_signed_fixed_lower (aC i) (bC i) (10 ^ 24) n (hbC i hi)
        (by norm_num only) (hsizeC i hi) (hposC i hi)
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at h
    norm_num only
    exact h

end PseudoPrime.LLS.PaperStatements
