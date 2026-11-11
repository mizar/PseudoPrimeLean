/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Jensen weights for reflected Backlund zeros -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A zero at distance `a` from the center, with `0 < a ≤ 1`, contributes
at least `log 2` to the radius-2 Jensen sum. Monotonicity of the logarithm
compares `2/a` with `2`. -/
theorem backlund_single_weight {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.log 2 ≤ Real.log (2 / a) := by
  apply Real.log_le_log (by norm_num only)
  apply (le_div_iff₀ ha).2
  linarith only [ha1]

/-- Two positive distances with product at most one contribute at least
`2 log 2` to the radius-2 Jensen sum. Combine the two logarithms and use the
product constraint. -/
theorem backlund_pair_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a * b ≤ 1) :
    2 * Real.log 2 ≤ Real.log (2 / a) + Real.log (2 / b) := by
  have hm := Real.log_le_log (mul_pos ha hb) hab
  rw [Real.log_one, Real.log_mul ha.ne' hb.ne'] at hm
  rw [Real.log_div (by norm_num only : (2 : ℝ) ≠ 0) ha.ne',
    Real.log_div (by norm_num only : (2 : ℝ) ≠ 0) hb.ne']
  linarith only [hm]

/-- For reflected points indexed by `0 ≤ v ≤ u < 1`, the distances
`1-u` and `1+v` have product at most one. Their combined radius-2 Jensen
weight is therefore at least `2 log 2`. -/
theorem backlund_reflected_pair_weight {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u < 1) :
    2 * Real.log 2 ≤ Real.log (2 / (1 - u)) + Real.log (2 / (1 + v)) := by
  apply backlund_pair_weight (by linarith only [hu]) (by linarith only [hv])
  have hp := mul_nonneg (sub_nonneg.mpr hvu) (sub_nonneg.mpr hu.le)
  have hu0 : 0 ≤ u := le_trans hv hvu
  nlinarith only [hp, hu0, sq_nonneg u]

/-- A finite family of reflected pairs with `0 ≤ v ≤ u < 1` contributes
at least `2 log 2` per pair. Sum the pointwise reflected-pair inequality
over the common finite index set. -/
theorem backlund_pair_weights_sum (s : Finset ℝ) (u v : ℝ → ℝ)
    (h : ∀ i ∈ s, 0 ≤ v i ∧ v i ≤ u i ∧ u i < 1) :
    (s.card : ℝ) * (2 * Real.log 2) ≤
      (∑ i ∈ s, Real.log (2 / (1 - u i))) + ∑ i ∈ s, Real.log (2 / (1 + v i)) := by
  calc
    (s.card : ℝ) * (2 * Real.log 2) = ∑ _i ∈ s, (2 * Real.log 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, (Real.log (2 / (1 - u i)) + Real.log (2 / (1 + v i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact backlund_reflected_pair_weight (h i hi).1 (h i hi).2.1 (h i hi).2.2
    _ = (∑ i ∈ s, Real.log (2 / (1 - u i))) + ∑ i ∈ s, Real.log (2 / (1 + v i)) := by
      rw [Finset.sum_add_distrib]

/-- If the right-side zero family is indexed by `s` and a subset `t` has
reflected partners, their total Jensen weight is at least `log 2` per right
zero plus another `log 2` per paired zero. Split `s` into paired and
unpaired indices and sum the corresponding weight estimates. -/
theorem backlund_partial_pair_weights (s t : Finset ℝ) (hts : t ⊆ s) (u v : ℝ → ℝ)
    (hu : ∀ i ∈ s, 0 < u i ∧ u i < 1) (hv : ∀ i ∈ t, 0 ≤ v i ∧ v i ≤ u i) :
    ((s.card : ℝ) + (t.card : ℝ)) * Real.log 2 ≤
      (∑ i ∈ s, Real.log (2 / (1 - u i))) + ∑ i ∈ t, Real.log (2 / (1 + v i)) := by
  classical
  have hs : ∀ i ∈ s \ t, Real.log 2 ≤ Real.log (2 / (1 - u i)) := by
    intro i hi
    have hui := hu i (Finset.mem_sdiff.mp hi).1
    apply backlund_single_weight
    · linarith only [hui.2]
    · linarith only [hui.1]
  have hleft : ((s \ t).card : ℝ) * Real.log 2 ≤ ∑ i ∈ s \ t, Real.log (2 / (1 - u i)) := by
    calc
      ((s \ t).card : ℝ) * Real.log 2 = ∑ _i ∈ s \ t, Real.log 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hs
  have hpair :=
    backlund_pair_weights_sum t u v (fun i hi => ⟨(hv i hi).1, (hv i hi).2, (hu i (hts hi)).2⟩)
  have hsum := Finset.sum_sdiff (f := fun i => Real.log (2 / (1 - u i))) hts
  have hcard : (s \ t).card + t.card = s.card := by
    rw [Finset.card_sdiff_add_card, Finset.union_eq_left.mpr hts]
  have hcard' : ((s \ t).card : ℝ) + (t.card : ℝ) = (s.card : ℝ) := by exact_mod_cast hcard
  have he := congrArg (fun q : ℝ => q * Real.log 2) hcard'
  nlinarith only [hleft, hpair, hsum, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
