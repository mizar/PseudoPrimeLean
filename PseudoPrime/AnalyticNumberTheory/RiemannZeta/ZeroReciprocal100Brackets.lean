/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalAbove100
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Numerics
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroEnumerationCount

/-! # Reciprocal bound from the height-100 ordinate brackets -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, 29 distinct positive critical-line zeros within the lower
brackets and a count of at most 58 imply the exact count 58 and a reciprocal
head bound of `11846/10000`. The count also forces completeness and simplicity. -/
theorem head100_of_count (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hbrackets : LowZero100LowerBounds g) :
    zeroCount 100 = 58 ∧ zeroReciprocalSum 100 ≤ 11846 / 10000 := by
  let z : Fin 29 → ℂ := fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hinj : Function.Injective z := critical_points_injective g hmono.injective
  have him : ∀ i, (z i).im = g i := by
    intro i
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) := by
    intro i
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
      refine ⟨hzero i, ?_, ?_⟩
      · simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num only
      · rw [him, abs_of_pos (hpos i)]
        exact hheight i
    · rw [him]
      exact hpos i
  have hc : zeroCount 100 ≤ 2 * (29 : ℕ) := by
    norm_num only [Nat.cast_ofNat]
    exact hcount
  have hp := positive_ledger_of_count (by norm_num only : (0 : ℝ) ≤ 100) hRH z hinj hz hc
  have hledger := hp.1.symm
  have hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1 := fun i ↦ hp.2 (z i) (hz i)
  have h100 : zeroCount 100 = 58 := by
    have h :=
      zeroCount_of_simple_enumeration hRH (by norm_num only : (0 : ℝ) ≤ 100) z hinj hledger hm
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have heq :=
    zeroReciprocal_of_simple_enumeration hRH (by norm_num only : (0 : ℝ) ≤ 100) z g hinj hledger hm
      him
  refine ⟨h100, ?_⟩
  rw [heq]
  exact (lowZero100_reciprocal_sharp g hbrackets).le

/-- Under RH, a complete ordered enumeration of the 29 simple positive
critical-line zeros through 100 satisfying the lower-bracket predicate gives
the explicit reciprocal zero-sum bound. The finite rational sum is checked
independently of zero existence and is consumed through its theorem. -/
theorem reciprocal_sum_of_lower100 (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hsimple : ∀ i, analyticOrderAt riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 1)
    (hcomplete :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          0 < ρ.im → ρ.im ≤ 100 → ∃ i, ρ = ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I)
    (hbrackets : LowZero100LowerBounds g) {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalSum T ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 41 / 1000 := by
  let z : Fin 29 → ℂ := fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hinj : Function.Injective z := critical_points_injective g hmono.injective
  have hledger :=
    positive_ledger_of_ordinates (by norm_num only : (0 : ℝ) ≤ 100) g hpos hheight hzero hcomplete
  have hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1 := fun i ↦
    zeroMultiplicity_eq_one (hsimple i)
  have him : ∀ i, (z i).im = g i := by
    intro i
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have h100 : zeroCount 100 = 58 := by
    have h :=
      zeroCount_of_simple_enumeration hRH (by norm_num only : (0 : ℝ) ≤ 100) z hinj hledger hm
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have heq :=
    zeroReciprocal_of_simple_enumeration hRH (by norm_num only : (0 : ℝ) ≤ 100) z g hinj hledger hm
      him
  have hh : zeroReciprocalSum 100 ≤ 237 / 200 := by
    rw [heq]
    exact (lowZero100_reciprocal_lt g hbrackets).le
  exact reciprocal_sum_of_head100 hRH h100 hh hT

/-- Under RH, 29 distinct positive zeros in the lower brackets and a
two-sided zero count at most 58 give the reciprocal zero-sum bound. The count
also proves that the enumeration is complete and every entry is simple. -/
theorem reciprocal_sum_of_count100 (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hbrackets : LowZero100LowerBounds g) {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalSum T ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 41 / 1000 := by
  let z : Fin 29 → ℂ := fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  have hinj : Function.Injective z := critical_points_injective g hmono.injective
  have him : ∀ i, (z i).im = g i := by
    intro i
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hz : ∀ i, z i ∈ (zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im) := by
    intro i
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).2
      refine ⟨hzero i, ?_, ?_⟩
      · simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num only
      · rw [him, abs_of_pos (hpos i)]
        exact hheight i
    · rw [him]
      exact hpos i
  have hc : zeroCount 100 ≤ 2 * (29 : ℕ) := by
    norm_num only [Nat.cast_ofNat]
    exact hcount
  have hp := positive_ledger_of_count (by norm_num only : (0 : ℝ) ≤ 100) hRH z hinj hz hc
  have hledger := hp.1.symm
  have hm : ∀ i, riemannZetaZeroMultiplicity (z i) = 1 := fun i ↦ hp.2 (z i) (hz i)
  have h100 : zeroCount 100 = 58 := by
    have h :=
      zeroCount_of_simple_enumeration hRH (by norm_num only : (0 : ℝ) ≤ 100) z hinj hledger hm
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have heq :=
    zeroReciprocal_of_simple_enumeration hRH (by norm_num only : (0 : ℝ) ≤ 100) z g hinj hledger hm
      him
  have hh : zeroReciprocalSum 100 ≤ 237 / 200 := by
    rw [heq]
    exact (lowZero100_reciprocal_lt g hbrackets).le
  exact reciprocal_sum_of_head100 hRH h100 hh hT

/-- For 29 nonnegative ordinates satisfying the height-100 upper brackets,
the paired sum of distances from their critical-line points to one is below
`3640`. The triangle bound and rational upper-bracket certificate supply the
constant used in the midpoint-rule remainder. -/
theorem lowZero100_distance_sum_lt (g : Fin 29 → ℝ) (hpos : ∀ i, 0 ≤ g i)
    (hu : LowZero100UpperBounds g) :
    (∑ i, (2 : ℝ) * ‖(((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) - 1‖) < 3640 := by
  have hsum :
    (∑ i, (2 : ℝ) * ‖(((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) - 1‖) ≤
      ∑ i : Fin 29, ((2 : ℝ) * g i + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    have h := critical_point_sub_one_norm_le (hpos i)
    nlinarith only [h]
  exact hsum.trans_lt (lowZero100_linear_lt g hu)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
