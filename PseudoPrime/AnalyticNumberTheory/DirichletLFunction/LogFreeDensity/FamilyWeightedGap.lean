/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyWeightedZeros
public import PseudoPrime.Analysis.FiniteExponentialDensityWeights

/-! # Power-weighted primitive-family density with an explicit zero gap -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- Positive absolute constants bound the actual finite family sum of
`x^Re ρ/(1+Im ρ²)` by `C x exp(-η log x/2)` for packets below `1-η` in the
near-one strip. The conductor scale satisfies `log x ≥ 2A log(Q+1)` and the lower
strip threshold has density exponent at most one half. Apply the unconditional
inverse-quadratic family density to every real-part threshold and use the finite
exponential weighting lemma. The zero-gap condition remains explicit; neither
RH nor an unproved density hypothesis is used. All analytic multiplicities are
represented by their original occurrence indices. -/
theorem exists_family_rpow_inverse_quadratic_sum_of_gap :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ (Q H : ℕ) (x σ₀ η : ℝ),
          1 < x →
            (1 / 2 : ℝ) ≤ σ₀ →
            σ₀ ≤ 1 →
            A * (1 - σ₀) ≤ 1 / 2 →
            0 ≤ η →
            2 * A * Real.log ((Q + 1 : ℕ) : ℝ) ≤ Real.log x →
            ∀ S : Finset (FamilyZeroOccurrence Q),
              S ⊆ primitiveCharacterFamilyZeroOccurrenceLedger Q (1 / 2) H →
                (∀ o ∈ S, σ₀ ≤ (familyZeroOccurrenceValue o).re) →
                (∀ o ∈ S, (familyZeroOccurrenceValue o).re ≤ 1 - η) →
                ∑ o ∈ S,
                    x ^ (familyZeroOccurrenceValue o).re /
                      (1 + (familyZeroOccurrenceValue o).im ^ 2) ≤
                  C * x * Real.exp (-η * Real.log x / 2) := by
  obtain ⟨A, C, hA, hC, hweighted⟩ := exists_family_inverse_quadratic_weighted_density
  refine
    ⟨A, C * Analysis.exponentialHalfTailConstant, hA,
      mul_pos hC Analysis.exponentialHalfTailConstant_pos, ?_⟩
  intro Q H x σ₀ η hx hσ₀lo hσ₀hi hδ hη hscale S hS hβlo hβhi
  let Z := A * Real.log ((Q + 1 : ℕ) : ℝ)
  have hQone : (1 : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le Q)
  have hZ : 0 ≤ Z := mul_nonneg hA.le (Real.log_nonneg hQone)
  have hZx : 2 * Z ≤ Real.log x := by
    dsimp only [Z]
    nlinarith only [hscale]
  have hdensity (σ : ℝ) (hσlo : σ₀ ≤ σ) (hσhi : σ ≤ 1) :
    ∑ o ∈ S.filter (fun o ↦ σ ≤ (familyZeroOccurrenceValue o).re),
        1 / (1 + (familyZeroOccurrenceValue o).im ^ 2) ≤
      C * Real.exp (Z * (1 - σ)) := by
    have hδσ : A * (1 - σ) ≤ 1 / 2 :=
      (mul_le_mul_of_nonneg_left (by linarith only [hσlo]) hA.le).trans hδ
    have hb := hweighted Q H σ (hσ₀lo.trans hσlo) hσhi hδσ S hS
    have he : Real.rpow ((Q + 1 : ℕ) : ℝ) (A * (1 - σ)) = Real.exp (Z * (1 - σ)) := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (zero_lt_one.trans_le hQone)]
      congr 1
      dsimp only [Z]
      ring
    simpa only [he] using hb
  have hb :=
    Analysis.sum_rpow_of_realpart_weighted_density S (fun o ↦ (familyZeroOccurrenceValue o).re)
      (fun o ↦ 1 / (1 + (familyZeroOccurrenceValue o).im ^ 2)) hx hZ hZx hC.le hσ₀hi hη
      (fun o _ ↦ one_div_nonneg.mpr (add_nonneg zero_le_one (sq_nonneg _))) hβlo hβhi hdensity
  convert hb using 1
  exact Finset.sum_congr rfl (fun o _ ↦ by ring)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
