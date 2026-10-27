/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSignedEulerSeries

/-! # Nonnegative paired Gaussian prime-power mass -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The principal-plus-character Euler mass with the common nonnegative
Gaussian weight H(m). Combine the signed resolvent coefficients before using
positivity: individual coefficients may be negative. The mass retains the
whole nonnegative prime-power sum in the zero-side comparison. -/
noncomputable def gaussianPairedEulerTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  (1 + (χ m).re) * gaussianResolventMangoldtWeight m

/-- For every character, the common paired Euler series converges absolutely.
Combine the convergent common weight and its norm-bounded character twist. -/
theorem summable_gaussianPairedEulerTerm {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Summable (gaussianPairedEulerTerm χ) := by
  have hc (m : ℕ) : |(χ m).re| ≤ 1 := (Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m)
  exact
    (summable_gaussianResolventMangoldtWeight.sub
          (summable_gaussian_signed_euler (fun m ↦ (χ m).re) hc)).congr
      (fun m ↦ by
        dsimp only [gaussianPairedEulerTerm]; ring)

/-- Every common paired Euler term is nonnegative. Use the character norm
bound and the already certified nonnegative combined Gaussian weight. Individual
signed resolvent coefficients are not treated as positive coefficients. -/
theorem gaussianPairedEulerTerm_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) :
    0 ≤ gaussianPairedEulerTerm χ m := by
  have hχ := (abs_le.mp ((Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m))).1
  exact mul_nonneg (by linarith only [hχ]) (gaussianResolventMangoldtWeight_nonneg m)

/-- The negative character Euler sum plus the common paired mass equals
the untwisted total weight exactly. Absolute convergence preserves this
cancellation and avoids estimating the two logarithmic derivatives separately. -/
theorem gaussian_signed_euler_add_paired_eq_total {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑' m : ℕ, -(χ m).re * gaussianResolventMangoldtWeight m) +
        (∑' m : ℕ, gaussianPairedEulerTerm χ m) =
      ∑' m : ℕ, gaussianResolventMangoldtWeight m := by
  have hc (m : ℕ) : |(χ m).re| ≤ 1 := (Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m)
  rw [←
    (summable_gaussian_signed_euler (fun m ↦ (χ m).re) hc).tsum_add
      (summable_gaussianPairedEulerTerm χ)]
  exact
    tsum_congr
      (fun m ↦ by
        dsimp only [gaussianPairedEulerTerm]; ring)

/-- The unretained common paired Euler mass after removing a finite set B.
It is the full sum minus the exact retained finite sum, hence nonnegative.
The definition keeps the useful complementary prime-power contribution explicit. -/
noncomputable def gaussianPairedEulerTail {q : ℕ} (χ : DirichletCharacter ℂ q) (B : Finset ℕ) : ℝ :=
  (∑' m : ℕ, gaussianPairedEulerTerm χ m) - ∑ m ∈ B, gaussianPairedEulerTerm χ m

/-- The unretained paired mass is nonnegative for every finite B.
Absolute convergence and termwise positivity give finite-sum domination. -/
theorem gaussianPairedEulerTail_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (B : Finset ℕ) :
    0 ≤ gaussianPairedEulerTail χ B := by
  exact
    sub_nonneg.mpr
      ((summable_gaussianPairedEulerTerm χ).sum_le_tsum B
        (fun m _ ↦ gaussianPairedEulerTerm_nonneg χ m))

/-- The retained paired mass equals twice the common weight prefix minus
the exact character deficit on that prefix. This is an equality at all
character values, including zero and minus one. -/
theorem gaussianPairedEuler_prefix_eq_gain_sub_deficit {q : ℕ} (χ : DirichletCharacter ℂ q)
    (B : Finset ℕ) :
    (∑ m ∈ B, gaussianPairedEulerTerm χ m) =
      2 * (∑ m ∈ B, gaussianResolventMangoldtWeight m) -
        ∑ m ∈ B, (1 - (χ m).re) * gaussianResolventMangoldtWeight m := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact
    Finset.sum_congr rfl
      (fun m _ ↦ by
        dsimp only [gaussianPairedEulerTerm]; ring)

end PseudoPrime.Analysis
