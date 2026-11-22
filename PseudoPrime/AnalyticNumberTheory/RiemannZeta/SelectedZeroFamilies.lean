/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroPairs

/-! # Finite families of selected conjugate zero pairs -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Distinct positive ordinates above one hundred give pairwise disjoint
conjugate pairs. Equality of imaginary parts handles like signs and positivity
excludes opposite signs; this prevents duplicate selected copies. -/
theorem conjugate_family_disjoint {n : ℕ} (z : Fin n → ℂ)
    (hinj : Function.Injective (fun i ↦ (z i).im)) (hp : ∀ i, 100 < (z i).im) :
    (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i ↦ ({z i, (starRingEnd ℂ) (z i)} : Finset ℂ)) := by
  classical
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro w hwi hwj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwi hwj
  rcases hwi with hi | hi <;> rcases hwj with hj | hj
  · exact hij (hinj (congrArg Complex.im (hi.symm.trans hj)))
  · have h := congrArg Complex.im (hi.symm.trans hj)
    rw [Complex.conj_im] at h
    linarith only [h, hp i, hp j]
  · have h := congrArg Complex.im (hi.symm.trans hj)
    rw [Complex.conj_im] at h
    linarith only [h, hp i, hp j]
  · have h := congrArg Complex.im (hi.symm.trans hj)
    simp only [Complex.conj_im, neg_inj] at h
    exact hij (hinj h)

/-- The finite selected family consists of each input point and its conjugate.
The input is a finite function, with no list lookup or table dependence.
Disjointness and zero membership are established separately by the following API. -/
@[expose]
noncomputable def conjugateFamily {n : ℕ} (z : Fin n → ℂ) : Finset ℂ := by
  classical exact Finset.univ.biUnion (fun i ↦ {z i, (starRingEnd ℂ) (z i)})

/-- Any additive sum over a conjugate family equals the sum of its pair
contributions when the positive ordinates are distinct and above one hundred.
Disjoint finite union, rather than indexed list access, gives the identity. -/
theorem conjugate_family_sum {n : ℕ} (z : Fin n → ℂ) (hinj : Function.Injective (fun i ↦ (z i).im))
    (hp : ∀ i, 100 < (z i).im) {M : Type*} [AddCommMonoid M] (f : ℂ → M) :
    ∑ w ∈ conjugateFamily z, f w = ∑ i, (f (z i) + f ((starRingEnd ℂ) (z i))) := by
  classical
  dsimp only [conjugateFamily]
  rw [Finset.sum_biUnion (conjugate_family_disjoint z hinj hp)]
  exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_pair (conjugate_pair_ne (hp i)))

/-- If each point is a zeta zero with nonnegative real part and ordinate
in (100,T], the entire conjugate family lies in the height-T zero ledger.
No RH, completeness, or simplicity assumption is needed. -/
theorem conjugate_family_subset {n : ℕ} (z : Fin n → ℂ) {T : ℝ} (hz : ∀ i, riemannZeta (z i) = 0)
    (hr : ∀ i, 0 ≤ (z i).re) (hp : ∀ i, 100 < (z i).im) (hT : ∀ i, (z i).im ≤ T) :
    conjugateFamily z ⊆ zerosUpTo T := by
  classical
    exact Finset.biUnion_subset.mpr (fun i _ ↦ conjugate_pair_subset (hz i) (hr i) (hp i) (hT i))

/-- Every point of a conjugate family has absolute ordinate above one
hundred when the positive inputs do. This supplies the strict selected band. -/
theorem conjugate_family_above {n : ℕ} (z : Fin n → ℂ) (hp : ∀ i, 100 < (z i).im) :
    ∀ w ∈ conjugateFamily z, 100 < |w.im| := by
  classical
  intro w hw
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
  exact conjugate_pair_above (hp i) w hi

/-- A family from n distinct positive ordinates above one hundred contains
exactly 2n points. Disjoint pair cardinalities establish nonduplication. -/
theorem conjugate_family_card {n : ℕ} (z : Fin n → ℂ) (hinj : Function.Injective (fun i ↦ (z i).im))
    (hp : ∀ i, 100 < (z i).im) : (conjugateFamily z).card = 2 * n := by
  classical
  dsimp only [conjugateFamily]
  rw [Finset.card_biUnion (conjugate_family_disjoint z hinj hp)]
  have h : (∑ i : Fin n, ({z i, (starRingEnd ℂ) (z i)} : Finset ℂ).card) = ∑ _ : Fin n, (2 : ℕ) :=
    Finset.sum_congr rfl (fun i _ ↦ Finset.card_pair (conjugate_pair_ne (hp i)))
  rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

/-- The unweighted absolute-ordinate moment of a conjugate family is the
sum of twice each positive ordinate plus one. This is the exact curvature
cost used by the selected-zero scalar budget. -/
theorem conjugate_family_moment {n : ℕ} (z : Fin n → ℂ)
    (hinj : Function.Injective (fun i ↦ (z i).im)) (hp : ∀ i, 100 < (z i).im) :
    (∑ w ∈ conjugateFamily z, (|w.im| + 1 / 2)) = ∑ i, 2 * ((z i).im + 1 / 2) := by
  rw [conjugate_family_sum z hinj hp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.conj_im, abs_neg, abs_of_pos (lt_trans (by norm_num only) (hp i))]
  ring

/-- The reciprocal absolute-ordinate sum of a conjugate family is the sum
of twice the reciprocal positive ordinate. This is the exact residual saving. -/
theorem conjugate_family_reciprocal {n : ℕ} (z : Fin n → ℂ)
    (hinj : Function.Injective (fun i ↦ (z i).im)) (hp : ∀ i, 100 < (z i).im) :
    (∑ w ∈ conjugateFamily z, 1 / |w.im|) = ∑ i, 2 / (z i).im := by
  rw [conjugate_family_sum z hinj hp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.conj_im, abs_neg, abs_of_pos (lt_trans (by norm_num only) (hp i))]
  ring

/-- The signed real phase of a conjugate family is the sum of twice the
positive-height real phase quotients. The identity preserves signs and requires
no multiplicity or completeness assertion for the extra zeros. -/
theorem conjugate_family_phase {n : ℕ} (z : Fin n → ℂ)
    (hinj : Function.Injective (fun i ↦ (z i).im)) (hp : ∀ i, 100 < (z i).im) (v : ℝ) :
    (∑ w ∈ conjugateFamily z, Complex.exp (((w.im * v : ℝ) : ℂ) * Complex.I) / w).re =
      ∑ i, 2 * (Complex.exp ((((z i).im * v : ℝ) : ℂ) * Complex.I) / z i).re := by
  rw [conjugate_family_sum z hinj hp]
  simp only [Complex.re_sum, Complex.add_re, re_phase_div_conj]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
