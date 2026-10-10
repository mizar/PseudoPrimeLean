/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CosetWeightedComparison
public import PseudoPrime.LLS.SubgroupKernelComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositePrimePowers
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Character averages for logarithmic sums in a coset

Coset orthogonality includes the inverse value at its representative. Applying
it termwise gives the character average in Section 4 of the paper.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a unit residue, membership in the coset is membership of its quotient unit.
Injectivity of unit coercion identifies the witness. This supplies the unit case
of coset character orthogonality. -/
theorem residueInCoset_iff_unit_mem {q : ℕ} (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) {n : ℕ}
    (hn : IsUnit (n : ZMod q)) : residueInCoset q H a n ↔ a⁻¹ * hn.unit ∈ H := by
  constructor
  · rintro ⟨u, hu, he⟩
    exact (Units.val_injective (he.trans hn.unit_spec.symm)) ▸ hu
  · intro hu
    exact ⟨hn.unit, hu, hn.unit_spec⟩

open Classical in
/-- For a nonzero modulus, the inverse-representative weighted annihilator sum is
the subgroup index on the coset and zero elsewhere. Unit orthogonality proves the
first case; every character vanishes on nonunits. This is the unnormalized coset
orthogonality formula, without GRH. -/
theorem sum_subgroupAnnihilator_coset_indicator {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a : (ZMod q)ˣ) (n : ℕ) :
    (∑ χ : NumberTheory.subgroupAnnihilator H,
        χ.val ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * χ.val (n : ZMod q)) =
      if residueInCoset q H a n then (H.index : ℂ) else 0 := by
  classical
  by_cases hn : IsUnit (n : ZMod q)
  · have he :
      (∑ χ : NumberTheory.subgroupAnnihilator H,
          χ.val ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * χ.val (n : ZMod q)) =
        ∑ χ : NumberTheory.subgroupAnnihilator H, χ.val ((a⁻¹ * hn.unit : (ZMod q)ˣ) : ZMod q) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [Units.val_mul, map_mul, hn.unit_spec]
    rw [he]
    by_cases hm : a⁻¹ * hn.unit ∈ H
    · rw [ite_eq_left ((residueInCoset_iff_unit_mem H a hn).mpr hm)]
      exact NumberTheory.sum_subgroupAnnihilator_eq_index H hm
    · rw [ite_eq_right (fun hc ↦ hm ((residueInCoset_iff_unit_mem H a hn).mp hc))]
      exact NumberTheory.sum_subgroupAnnihilator_eq_zero H hm
  · have hc : ¬residueInCoset q H a n := by
      rintro ⟨u, _, he⟩
      exact hn (he ▸ u.isUnit)
    rw [ite_eq_right hc]
    exact Finset.sum_eq_zero (fun χ _ ↦ by rw [χ.val.map_nonunit hn, mul_zero])

/-- For a nonzero modulus and any real cutoff, the logarithmic character average
weighted by inverse values at the representative equals the subgroup index times
the coset Mangoldt sum. Exchange the two finite sums and apply coset orthogonality
termwise. This is the exact arithmetic identity in equation (4.2). -/
theorem characterLogWeightedSum_coset_average {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a : (ZMod q)ˣ) (x : ℝ) :
    (∑ χ : NumberTheory.subgroupAnnihilator H,
        χ.val ((a⁻¹ : (ZMod q)ˣ) : ZMod q) *
          AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val) =
      (H.index : ℂ) * (cosetLogWeightedSum q H a x : ℂ) := by
  classical
  unfold AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold cosetLogWeightedSum
  rw [Complex.ofReal_sum]
  simp only [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm
  simp only [← mul_assoc]
  simp_rw [mul_right_comm _ (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x n : ℂ) _]
  rw [← Finset.sum_mul, sum_subgroupAnnihilator_coset_indicator H a n]
  by_cases hn : residueInCoset q H a n
  · rw [ite_eq_left hn, ite_eq_left hn]
  · rw [ite_eq_right hn, ite_eq_right hn, zero_mul, mul_zero]

/-- Multiplying any complex value by a character value at a unit preserves its norm.
The real part is therefore at least minus the original norm. This bounds each
nonprincipal contribution to the coset character average. -/
theorem neg_norm_le_re_unit_character_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a : (ZMod q)ˣ) (z : ℂ) : -‖z‖ ≤ (χ (a : ZMod q) * z).re := by
  have h := (abs_le.mp (Complex.abs_re_le_norm (χ (a : ZMod q) * z))).1
  rw [norm_mul, χ.unit_norm_eq_one a, one_mul] at h
  exact h

open Classical in
/-- For a nonzero modulus, the principal logarithmic sum minus the sum of the
nonprincipal norms is a lower bound for the index times the coset Mangoldt sum.
Split off the principal character in the exact average and bound the remaining
real parts by negative norms. This is the lower comparison used in Section 4. -/
theorem principal_logWeightedSum_le_coset_add_nonprincipal_norms {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) (x : ℝ) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x (1 : DirichletCharacter ℂ q)).re ≤
      (H.index : ℝ) * cosetLogWeightedSum q H a x +
        ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
          ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖ := by
  classical
  let F := fun χ : NumberTheory.subgroupAnnihilator H ↦
    (χ.val ((a⁻¹ : (ZMod q)ˣ) : ZMod q) *
        AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val).re
  have hid := congrArg Complex.re (characterLogWeightedSum_coset_average H a x)
  simp only [Complex.re_sum, Complex.mul_re (H.index : ℂ) (cosetLogWeightedSum q H a x : ℂ),
    Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] at hid
  have hs := Finset.sum_erase_add Finset.univ F (Finset.mem_univ 1)
  have hp :
    F 1 =
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x
          (1 : DirichletCharacter ℂ q)).re := by
    simp only [F, OneMemClass.coe_one, MulChar.one_apply_coe, one_mul]
  have hb :
    -(∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
          ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖) ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H), F χ := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun χ _ ↦ neg_norm_le_re_unit_character_mul χ.val a⁻¹ _)
  rw [hp] at hs
  change ∑ χ : NumberTheory.subgroupAnnihilator H, F χ = _ at hid
  linarith only [hs, hid, hb]

open Classical in
/-- If the principal logarithmic sum exceeds the index times the composite
prime-power sum plus all nonprincipal norms, then the least coset prime lies below
the positive cutoff. The index is nonnegative. Use the character-average lower bound
to obtain a strict weighted gap, then apply the bounded-prime construction.
This connects both analytic estimates in Section 4 to the least-prime conclusion. -/
theorem exists_least_prime_in_coset_le_of_principal_gap {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (a : (ZMod q)ˣ) {x : ℝ} (hx : 0 < x)
    (hgap :
      (H.index : ℝ) * AnalyticNumberTheory.Arithmetic.compositePrimePowerLogWeightedSum x +
          ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
            ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.val‖ <
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x
            (1 : DirichletCharacter ℂ q)).re) :
    ∃ p : ℕ, IsLeast (primesInCoset q H a) p ∧ (p : ℝ) ≤ x := by
  have h := principal_logWeightedSum_le_coset_add_nonprincipal_norms H a x
  have hg :
    AnalyticNumberTheory.Arithmetic.compositePrimePowerLogWeightedSum x <
      cosetLogWeightedSum q H a x := by
    nlinarith only [h, hgap, (Nat.cast_nonneg H.index : (0 : ℝ) ≤ H.index)]
  exact exists_least_prime_in_coset_le_of_weighted_gap H a hx hg

/-- At a positive cutoff, the sum of real reciprocal character sums over the
annihilator is nonnegative. Exchange the finite sums and apply subgroup
orthogonality; the remaining weights and the subgroup index are nonnegative.
This removes reciprocal contributions in the coset norm average. -/
theorem subgroup_reciprocal_average_nonneg {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) {x : ℝ}
    (hx : 0 < x) :
    0 ≤
      ∑ χ : NumberTheory.subgroupAnnihilator H,
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ.val).re := by
  classical
  rw [← Complex.re_sum]
  unfold AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum
  rw [Finset.sum_comm, Complex.re_sum]
  apply Finset.sum_nonneg
  intro n hn
  unfold AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedTerm
  rw [← Finset.mul_sum, sum_subgroupAnnihilator_eq_indicator]
  have hw :=
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm_nonneg hx
      (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2
  by_cases hm : residueInSubgroup q H n
  · rw [Set.indicator_of_mem (s := {m : ℕ | residueInSubgroup q H m}) hm]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
      Complex.natCast_im, mul_zero, sub_zero]
    exact mul_nonneg hw (Nat.cast_nonneg H.index)
  · rw [Set.indicator_of_notMem (s := {m : ℕ | residueInSubgroup q H m}) hm, mul_zero,
      Complex.zero_re]

end PseudoPrime.LLS.PaperStatements
