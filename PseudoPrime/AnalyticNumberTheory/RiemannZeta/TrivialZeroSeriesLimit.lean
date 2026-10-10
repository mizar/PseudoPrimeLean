/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedGeometry
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalTrivialZeroSeries

/-! Exact trivial-zero sums along the expanding zeta rectangles. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The expanding rectangle contains exactly the first `m` trivial zeros.
Its left edge lies at `-(2m+1)` and its positive height contains the real axis. -/
theorem trivialZero_mem_unifiedRectangle_iff {τ : ℝ} (hτ : 1 < τ) (m k : ℕ) :
    -2 * ((k : ℂ) + 1) ∈
        riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m) ↔
      k < m := by
  have hH : 0 < unifiedContourHeightSeq m :=
    (farLeftHeightSeq_pos m).trans_le (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  rw [mem_riemannZetaZerosInAnyRectangle_iff, riemannZeta_neg_two_mul_nat_add_one]
  simp only [and_true, Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Set.mem_uIcc,
    unifiedRectangleLower, unifiedTauRectangleUpper, neg_mul, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im, Complex.natCast_re,
    Complex.natCast_im, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im,
    mul_zero, zero_mul, add_zero, sub_zero, neg_zero]
  constructor
  · intro h
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hkm : (k : ℝ) < m := by rcases h.1 with h | h <;> linarith only [h.1, h.2, hτ, hm, hk]
    exact Nat.cast_lt.mp hkm
  · intro h
    have hkm : (k : ℝ) + 1 ≤ m := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_le.mpr (Nat.succ_le_of_lt h) : ((k + 1 : ℕ) : ℝ) ≤ m)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    exact
      ⟨Or.inl ⟨by linarith only [hkm], by linarith only [hk, hτ]⟩,
        Or.inl ⟨by linarith only [hH], hH.le⟩⟩

/-- The negative-real-part zero ledger is the image of the first `m` natural indices.
Zero classification and the exact rectangle membership identify its support. -/
theorem trivialZeros_unifiedRectangle_eq_image {τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m)).filter
        (fun ρ ↦ ρ.re < 0) =
      (Finset.range m).image (fun k : ℕ ↦ -2 * ((k : ℂ) + 1)) := by
  classical
  ext ρ
  constructor
  · intro h
    have hmem := Finset.mem_filter.mp h
    obtain ⟨k, hk⟩ :=
      exists_nat_eq_neg_two_mul_add_one_of_riemannZeta_zero_re_neg hmem.2
        (mem_riemannZetaZerosInAnyRectangle_iff.mp hmem.1).2
    exact
      Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr ((trivialZero_mem_unifiedRectangle_iff hτ m k).mp (hk ▸ hmem.1)),
          hk.symm⟩
  · intro h
    obtain ⟨k, hk, hρ⟩ := Finset.mem_image.mp h
    subst ρ
    refine
      Finset.mem_filter.mpr
        ⟨(trivialZero_mem_unifiedRectangle_iff hτ m k).mpr (Finset.mem_range.mp hk), ?_⟩
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, Complex.one_re,
      Complex.one_im, add_zero, mul_zero, sub_zero]
    linarith only [Nat.cast_nonneg (α := ℝ) k]

/-- Distinct natural indices give distinct negative even zero locations. -/
theorem trivialZeroLocation_injective : Function.Injective (fun k : ℕ ↦ -2 * ((k : ℂ) + 1)) := by
  intro a b h
  exact
    Nat.cast_injective (R := ℂ)
      (add_right_cancel (mul_left_cancel₀ (by norm_num only : (-2 : ℂ) ≠ 0) h))

/-- The logarithmic contribution of all trivial zeros in the rectangle is
exactly the negative natural partial sum, rather than only bounded by its series. -/
theorem sum_logTrivialZeros_unifiedRectangle_eq {x τ : ℝ} (hx : 0 < x) (hτ : 1 < τ) (m : ℕ) :
    (∑
          ρ ∈
            (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                  (unifiedTauRectangleUpper τ m)).filter
              (fun ρ ↦ ρ.re < 0),
          riemannZetaLogZeroContribution x ρ).re =
      -(∑ k ∈ Finset.range m, x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2)) := by
  classical
  rw [trivialZeros_unifiedRectangle_eq_image hτ,
    Finset.sum_image (fun a _ b _ h ↦ trivialZeroLocation_injective h), Complex.re_sum]
  simp only [riemannZetaLogZeroContribution_neg_two_mul_nat_add_one hx, Complex.neg_re,
    Complex.ofReal_re, Finset.sum_neg_distrib]

/-- For x > 0 and right abscissa tau > 1, the real reciprocal trivial-zero ledger is
the negative sum of the first m natural reciprocal correction terms. Identify the
negative-even zero locations in the rectangle and evaluate their multiplicity-one residues.
This finite identity needs no convergence of the full series; x > 1 is used for its limit. -/
theorem sum_reciprocalTrivialZeros_unifiedRectangle_eq {x τ : ℝ} (hx : 0 < x) (hτ : 1 < τ) (m : ℕ) :
    (∑
          ρ ∈
            (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                  (unifiedTauRectangleUpper τ m)).filter
              (fun ρ ↦ ρ.re < 0),
          riemannZetaReciprocalZeroContribution x ρ).re =
      -(∑ k ∈ Finset.range m,
          x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1))) := by
  classical
  rw [trivialZeros_unifiedRectangle_eq_image hτ,
    Finset.sum_image (fun a _ b _ h ↦ trivialZeroLocation_injective h), Complex.re_sum]
  simp only [riemannZetaReciprocalZeroContribution_neg_two_mul_nat_add_one hx, Complex.neg_re,
    Complex.ofReal_re, Finset.sum_neg_distrib]

/-- For `x > 1`, logarithmic trivial-zero residue sums converge to the negative full series. -/
theorem tendsto_sum_logTrivialZeros_unifiedRectangle {x τ : ℝ} (hx : 1 < x) (hτ : 1 < τ) :
    Filter.Tendsto
      (fun m ↦
        (∑
            ρ ∈
              (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                    (unifiedTauRectangleUpper τ m)).filter
                (fun ρ ↦ ρ.re < 0),
            riemannZetaLogZeroContribution x ρ).re)
      Filter.atTop (nhds (-riemannZetaLogTrivialZeroSeries x)) := by
  exact
    (summable_logTrivialZeroTerm hx).hasSum.tendsto_sum_nat.neg.congr'
      (Filter.Eventually.of_forall fun m ↦
        (sum_logTrivialZeros_unifiedRectangle_eq (lt_trans zero_lt_one hx) hτ m).symm)

/-- For `x > 1`, reciprocal trivial-zero residue sums converge to the negative full series. -/
theorem tendsto_sum_reciprocalTrivialZeros_unifiedRectangle {x τ : ℝ} (hx : 1 < x) (hτ : 1 < τ) :
    Filter.Tendsto
      (fun m ↦
        (∑
            ρ ∈
              (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                    (unifiedTauRectangleUpper τ m)).filter
                (fun ρ ↦ ρ.re < 0),
            riemannZetaReciprocalZeroContribution x ρ).re)
      Filter.atTop (nhds (-riemannReciprocalTrivialZeroSeries x)) := by
  exact
    (summable_reciprocalTrivialZeroTerm_of_one_lt hx).hasSum.tendsto_sum_nat.neg.congr'
      (Filter.Eventually.of_forall fun m ↦
        (sum_reciprocalTrivialZeros_unifiedRectangle_eq (lt_trans zero_lt_one hx) hτ m).symm)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
