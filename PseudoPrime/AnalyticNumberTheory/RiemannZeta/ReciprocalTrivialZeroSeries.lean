/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroMultiplicity
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification

/-! General reciprocal trivial-zero series, convergence, and bounds. -/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The totalized reciprocal trivial-zero series as a function of real `x`.
For `x > 1` it is a convergent series of positive terms. -/
noncomputable def riemannReciprocalTrivialZeroSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1))

/-- The reciprocal trivial-zero series is bounded by an explicit geometric tail. -/
theorem riemannReciprocalTrivialZeroSeries_le_geometric {x : ℝ} (hx : 2 ≤ x) :
    riemannReciprocalTrivialZeroSeries x ≤ x⁻¹ ^ 3 / 6 * (1 - x⁻¹ ^ 2)⁻¹ := by
  have hxpos : 0 < x := by linarith
  have hinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hxpos.le
  have hinvle : x⁻¹ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ hxpos (by norm_num only)).2 hx
  have hratio : x⁻¹ ^ 2 < 1 := by nlinarith [sq_nonneg (x⁻¹ - (2 : ℝ)⁻¹)]
  have hgeom : Summable fun k : ℕ ↦ (x⁻¹ ^ 2) ^ k :=
    summable_geometric_of_lt_one (pow_nonneg hinv 2) hratio
  have hmajor : Summable fun k : ℕ ↦ x⁻¹ ^ 3 / 6 * (x⁻¹ ^ 2) ^ k := hgeom.mul_left (x⁻¹ ^ 3 / 6)
  have hterm :
    ∀ k : ℕ,
      x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)) ≤
        x⁻¹ ^ 3 / 6 * (x⁻¹ ^ 2) ^ k :=
    reciprocalTrivialZeroTerm_le_geometric hx
  have hseries :
    Summable fun k : ℕ ↦ x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)) :=
    hmajor.of_nonneg_of_le (fun k ↦ reciprocalTrivialZeroTerm_nonneg hxpos.le k) hterm
  rw [riemannReciprocalTrivialZeroSeries]
  calc
    _ ≤ ∑' k : ℕ, x⁻¹ ^ 3 / 6 * (x⁻¹ ^ 2) ^ k := hseries.tsum_le_tsum hterm hmajor
    _ = x⁻¹ ^ 3 / 6 * (1 - x⁻¹ ^ 2)⁻¹ := by
      rw [hgeom.tsum_mul_left, tsum_geometric_of_lt_one (pow_nonneg hinv 2) hratio]

/-- The reciprocal trivial-zero summand sequence is summable for every `x > 1`. -/
theorem summable_reciprocalTrivialZeroTerm_of_one_lt {x : ℝ} (hx : 1 < x) :
    Summable fun k : ℕ => x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)) := by
  have hxpos : 0 < x := by linarith
  have hinv : 0 ≤ x⁻¹ := inv_nonneg.mpr hxpos.le
  have hratio : x⁻¹ ^ 2 < 1 := by
    have h1 : x⁻¹ < 1 := inv_lt_one_iff₀.mpr (Or.inr hx)
    nlinarith [hinv, h1]
  have hgeom : Summable fun k : ℕ => (x⁻¹ ^ 2) ^ k :=
    summable_geometric_of_lt_one (pow_nonneg hinv 2) hratio
  have hmajor : Summable fun k : ℕ => x⁻¹ ^ 3 / 6 * (x⁻¹ ^ 2) ^ k := hgeom.mul_left (x⁻¹ ^ 3 / 6)
  exact
    hmajor.of_nonneg_of_le (fun k => reciprocalTrivialZeroTerm_nonneg hxpos.le k)
      (reciprocalTrivialZeroTerm_le_geometric_of_pos hxpos)

/-- The reciprocal trivial-zero contribution series has its expected sum for every `x > 1`. -/
theorem hasSum_riemannZetaReciprocalZeroContribution_trivialZeros_of_one_lt {x : ℝ} (hx : 1 < x) :
    HasSum (fun k : ℕ => riemannZetaReciprocalZeroContribution x (-2 * ((k : ℂ) + 1)))
      (-(riemannReciprocalTrivialZeroSeries x : ℂ)) := by
  have hxpos : 0 < x := by linarith
  have hsum :
    HasSum (fun k : ℕ => x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)))
      (riemannReciprocalTrivialZeroSeries x) :=
    (summable_reciprocalTrivialZeroTerm_of_one_lt hx).hasSum
  have hcast := (Complex.hasSum_ofReal.mpr hsum).neg
  simp_rw [riemannZetaReciprocalZeroContribution_neg_two_mul_nat_add_one hxpos]
  exact hcast

/-- Finite partial sums of reciprocal trivial-zero terms are bounded by the full positive series. -/
theorem sum_reciprocalTrivialZeroTerm_le {x : ℝ} (hx : 1 < x) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) :
    (∑ ρ ∈ S,
        x⁻¹ ^ (2 * (trivialZeroIndex ρ + 1) + 1) /
          ((2 * (trivialZeroIndex ρ + 1) : ℝ) * (2 * (trivialZeroIndex ρ + 1) + 1))) ≤
      riemannReciprocalTrivialZeroSeries x := by
  have hinj : Set.InjOn trivialZeroIndex S := by
    intro ρ₁ h1 ρ₂ h2 heq
    have hs1 := trivialZeroIndex_spec (hS ρ₁ h1)
    have hs2 := trivialZeroIndex_spec (hS ρ₂ h2)
    rw [hs1, hs2, heq]
  have himg :
    (∑ ρ ∈ S,
        x⁻¹ ^ (2 * (trivialZeroIndex ρ + 1) + 1) /
          ((2 * (trivialZeroIndex ρ + 1) : ℝ) * (2 * (trivialZeroIndex ρ + 1) + 1))) =
      ∑ k ∈ S.image trivialZeroIndex,
        x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1)) :=
    (Finset.sum_image (f := fun k : ℕ =>
        x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1))) hinj).symm
  rw [himg]
  have hxpos : 0 < x := by linarith
  have hsummable := summable_reciprocalTrivialZeroTerm_of_one_lt hx
  have hle :=
    hsummable.sum_le_tsum (S.image trivialZeroIndex)
      (fun k _ => reciprocalTrivialZeroTerm_nonneg hxpos.le k)
  rwa [show
      (∑' k : ℕ, x⁻¹ ^ (2 * (k + 1) + 1) / ((2 * (k + 1) : ℝ) * (2 * (k + 1) + 1))) =
        riemannReciprocalTrivialZeroSeries x
      from rfl] at hle

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
