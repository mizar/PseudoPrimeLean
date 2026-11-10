/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ShiftedZeroReciprocal

/-! # Nontrivial zeta zeros up to a height

Finite closed-height zero ledgers, multiplicity counts and reciprocal sums.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The finite set of nontrivial zeta zeros with absolute imaginary part at
most `T`. A bounded rectangle supplies finiteness; the closed height endpoint
ensures that zeros exactly at `T` are included. -/
noncomputable def zerosUpTo (T : ℝ) : Finset ℂ :=
  (riemannZetaZerosInAnyRectangle ⟨-1, -T⟩ ⟨2, T⟩).filter (fun ρ ↦ 0 ≤ ρ.re)

/-- For `T ≥ 0`, characterize the closed-height ledger by the zeta-zero
condition, nonnegative real part and absolute height at most `T`. Zeta zeros
have real part at most one, so the chosen rectangle covers the critical strip. -/
theorem mem_zerosUpTo {T : ℝ} (hT : 0 ≤ T) {ρ : ℂ} :
    ρ ∈ zerosUpTo T ↔ riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T := by
  rw [zerosUpTo, Finset.mem_filter, mem_riemannZetaZerosInAnyRectangle_iff]
  simp only [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Set.mem_uIcc]
  constructor
  · rintro ⟨⟨⟨hr, hi⟩, hz⟩, hre⟩
    have him : -T ≤ ρ.im ∧ ρ.im ≤ T := by
      rcases hi with h | h
      · exact h
      · constructor <;> linarith only [h.1, h.2, hT]
    exact ⟨hz, hre, abs_le.mpr him⟩
  · rintro ⟨hz, hre, hi⟩
    have hr := riemannZeta_zero_re_le_one hz
    refine ⟨⟨⟨?_, ?_⟩, hz⟩, hre⟩
    · left
      constructor <;> linarith only [hre, hr]
    · left
      exact abs_le.mp hi

/-- Count all nontrivial zeros of absolute height at most `T`, weighted by
multiplicity. Both signs of the imaginary part are included. -/
noncomputable def zeroCount (T : ℝ) : ℝ :=
  ∑ ρ ∈ zerosUpTo T, (riemannZetaZeroMultiplicity ρ : ℝ)

/-- Expand the multiplicity-weighted closed-height count as its finite sum.
This identity supports downstream summation formulas. -/
theorem zeroCount_eq_sum (T : ℝ) :
    zeroCount T = ∑ ρ ∈ zerosUpTo T, (riemannZetaZeroMultiplicity ρ : ℝ) := by rfl

/-- Sum multiplicity divided by absolute height over all nontrivial zeros of
height at most `T`. Both signs are included and division is totalized. -/
noncomputable def zeroReciprocalSum (T : ℝ) : ℝ :=
  ∑ ρ ∈ zerosUpTo T, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|

/-- Expand the closed-height reciprocal sum into its finite zero ledger.
This identity relates the sum to the height-counting function. -/
theorem zeroReciprocalSum_eq (T : ℝ) :
    zeroReciprocalSum T = ∑ ρ ∈ zerosUpTo T, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| := by rfl

/-- The closed-height zero ledgers are nested as a nonnegative height grows.
Use their membership characterization and monotonicity of the cutoff. -/
theorem zerosUpTo_mono {T U : ℝ} (hT : 0 ≤ T) (hTU : T ≤ U) : zerosUpTo T ⊆ zerosUpTo U := by
  intro ρ hρ
  have h := (mem_zerosUpTo hT).1 hρ
  exact (mem_zerosUpTo (hT.trans hTU)).2 ⟨h.1, h.2.1, h.2.2.trans hTU⟩

/-- Under RH, the nontrivial zero ledger is empty at nonnegative heights at
most `2π`. Apply the low-height exclusion to any hypothetical member. -/
theorem zerosUpTo_empty (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (hTpi : T ≤ 2 * Real.pi) :
    zerosUpTo T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  have hh := (mem_zerosUpTo hT).1 hρ
  have he := zero_height_gt_two_pi hRH hh.1 hh.2.1
  linarith only [he, hh.2.2, hTpi]

/-- Under RH and for positive `T`, bound the inverse-height sum minus the
multiplicity count divided by `T`. Apply the finite shifted zero-mass estimate
to the closed-height ledger. -/
theorem zeroReciprocal_shift (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 < T) :
    zeroReciprocalSum T - zeroCount T / T ≤ T / 80 + 1 / (160 * Real.pi) := by
  unfold zeroReciprocalSum zeroCount
  apply reciprocal_sum_sub_count hRH (zerosUpTo T) hT
  · intro ρ hρ
    exact ((mem_zerosUpTo hT.le).1 hρ).1
  · intro ρ hρ
    exact ((mem_zerosUpTo hT.le).1 hρ).2.1

/-- Under RH, the shifted inverse-height sum at `2πe` is at most `109/480`.
Apply the finite zero-set entrance estimate to the closed-height ledger. -/
theorem zeroReciprocal_at_two_pi_e (hRH : RiemannHypothesis) :
    zeroReciprocalSum (2 * Real.pi * Real.exp 1) -
        zeroCount (2 * Real.pi * Real.exp 1) / (2 * Real.pi * Real.exp 1) ≤
      (109 / 480 : ℝ) := by
  have hT : 0 ≤ 2 * Real.pi * Real.exp 1 :=
    (mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)).le
  unfold zeroReciprocalSum zeroCount
  apply reciprocal_sum_at_two_pi_e hRH (zerosUpTo (2 * Real.pi * Real.exp 1))
  · intro ρ hρ
    exact ((mem_zerosUpTo hT).1 hρ).1
  · intro ρ hρ
    exact ((mem_zerosUpTo hT).1 hρ).2.1

/-- The multiplicity-weighted zero count is nondecreasing for nonnegative
cutoffs. It is a sum of nonnegative weights over nested finite ledgers. -/
theorem zeroCount_mono {T U : ℝ} (hT : 0 ≤ T) (hTU : T ≤ U) : zeroCount T ≤ zeroCount U := by
  unfold zeroCount
  exact
    Finset.sum_le_sum_of_subset_of_nonneg (zerosUpTo_mono hT hTU) (fun _ _ _ ↦ Nat.cast_nonneg _)

/-- Under RH, the zero count and reciprocal sum both vanish at heights in
`[0, 2π]`. The closed-height ledger is empty throughout this interval. -/
theorem zeroCount_low (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T) (hTpi : T ≤ 2 * Real.pi) :
    zeroCount T = 0 ∧ zeroReciprocalSum T = 0 := by
  rw [zeroCount, zeroReciprocalSum, zerosUpTo_empty hRH hT hTpi]
  simp only [Finset.sum_empty, and_self]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
