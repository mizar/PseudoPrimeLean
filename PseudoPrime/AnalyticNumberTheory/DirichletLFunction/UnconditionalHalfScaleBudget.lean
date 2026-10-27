/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalRegularizedTruncation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogRemainderBound

/-! # An unconditional truncated half-scale arithmetic budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Every completed zero in the natural-height rectangle has absolute ordinate
at most that height. Extract the imaginary coordinate interval. This applies to
finite lower-strip packets before the unconditional local counting estimate. -/
theorem completedZerosInRectangle_height_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) (σ : ℝ) (H : ℕ) {ρ : ℂ}
    (hρ :
      ρ ∈
        completedZerosInRectangle χ hne ((σ : ℂ) - (H : ℝ) * Complex.I)
          ((1 : ℂ) + (H : ℝ) * Complex.I)) :
    |ρ.im| ≤ H := by
  have hb := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
    Complex.mem_reProdIm] at hb
  have him := hb.2
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_one, zero_sub, Complex.add_im, Complex.one_im, zero_add, add_zero,
    Complex.ofReal_re] at him
  rw [Set.uIcc_of_le (by linarith only [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)] : -(H : ℝ) ≤ H)] at him
  exact abs_le.mpr him

/-- For a modulus, scale, natural cutoff, and local-count constant, collect the
proved original high-zero tail and the genus correction into one explicit real
bound. Its modulus dependence is logarithmic. The half-scale family budget uses
this expression while choosing its height independently of the arithmetic scale. -/
noncomputable def regularizedHighZeroTailMajorant (q : ℕ) (x : ℝ) (H : ℕ) (K : ℝ) : ℝ :=
  24 * x * K * Real.log q / ((H - 1 : ℕ) : ℝ) +
    192 * x * K * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3) +
    Real.log 2 *
      (32 *
        (12 + LogFreeDensity.completedGenusMassShiftConstant * (Real.log 4 + 1) + Real.log q +
          LogFreeDensity.completedGenusMassCenterConstant * (Real.log 4 + 1)))

/-- There are positive absolute remainder, local-count, and tail constants giving
the displayed half-scale arithmetic bound for every primitive nonprincipal
character with nonprincipal inverse, modulus at least two, scale at least four,
real threshold at most one, and integer cutoff at least two. Split the regularized
zero sum at height `H+1`, apply the below-threshold count and high-tail bounds,
and retain only the near-one finite norm sum as the density-controlled term.
All analytic estimates in this interface are unconditional. -/
theorem exists_norm_characterLogWeightedSum_half_le_truncated_zero_budget :
    ∃ C K T : ℝ,
      0 < C ∧
        0 < K ∧
        0 < T ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ.IsPrimitive →
                ∀ hne : χ ≠ 1,
                  χ⁻¹ ≠ 1 →
                    ∀ (x σ : ℝ),
                      4 ≤ x →
                        σ ≤ 1 →
                        ∀ (H : ℕ),
                          2 ≤ H →
                            ‖Arithmetic.characterLogWeightedSum x χ -
                                  Arithmetic.characterLogWeightedSum (x / 2) χ‖ ≤
                              (∑
                                  ρ ∈
                                    completedZerosInRectangle χ hne
                                      ((σ : ℂ) - ((H + 1 : ℕ) : ℝ) * Complex.I)
                                      ((1 : ℂ) + ((H + 1 : ℕ) : ℝ) * Complex.I),
                                  ‖regularizedLogHalfZeroTerm χ x ρ‖) +
                                ((2 * ((H + 1 : ℕ) : ℝ) + 1) * K *
                                    (Real.log q + Real.log (4 + ((H + 1 : ℕ) : ℝ)) + 1)) *
                                  regularizedLowHeightMajorant x σ +
                                regularizedHighZeroTailMajorant q x H T +
                                C * (Real.log x + 1) := by
  obtain ⟨C, hC, harith⟩ := exists_norm_characterLogWeightedSum_half_le_regularized_zero_sum
  obtain ⟨K, hK, hlow⟩ := exists_sum_norm_regularizedLogHalfZeroTerm_below_threshold_bound
  obtain ⟨T, hT, htail⟩ := exists_tsum_norm_regularizedLogHalfZeroTerm_tail_bound_unconditionally
  refine ⟨C, K, T, hC, hK, hT, ?_⟩
  intro q inst hq χ hp hne hinv x σ hx hσ H hH
  have hx2 : 2 ≤ x := by linarith only [hx]
  have hb := harith q hq χ hp hne hinv x hx
  have hs := tsum_norm_regularizedLogHalfZeroTerm_le_truncated_parts hq hp hne hinv hx2 σ (H + 1)
  have hl :=
    hlow q hq χ hp hne hinv x σ hx2 hσ (H + 1)
      ((completedZerosInRectangle χ hne ((0 : ℂ) - ((H + 1 : ℕ) : ℝ) * Complex.I)
            ((1 : ℂ) + ((H + 1 : ℕ) : ℝ) * Complex.I)).filter
        (fun ρ ↦ ρ.re ≤ σ))
      (fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2)
      (fun ρ hρ ↦ completedZerosInRectangle_height_le hne 0 (H + 1) (Finset.mem_filter.mp hρ).1)
  have ht := htail q hq χ hp hne hinv x hx2 H hH
  change _ ≤ regularizedHighZeroTailMajorant q x H T at ht
  linarith only [hb, hs, hl, ht]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
