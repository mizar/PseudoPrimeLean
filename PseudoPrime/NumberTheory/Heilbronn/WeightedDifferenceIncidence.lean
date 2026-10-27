/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.WeightedFiniteCharacterMoments
public import PseudoPrime.NumberTheory.Heilbronn.DifferenceIncidenceBounds

/-! # Fourier bounds for weighted difference incidences -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Weighted count of ordered pairs whose difference lies in a finite set.

Definition: Sum `w x * w y` over all pairs with `x - y ∈ Q`.
Input: A natural-number weight on `ZMod N` and a finite set of differences.
Output: The corresponding nonnegative real weighted incidence.
Role: Supplies the arithmetic side of the weighted Fourier identity. -/
def weightedResidueDifferenceIncidence {N : ℕ} [NeZero N] (w : ZMod N → ℕ) (Q : Finset (ZMod N)) :
    ℝ :=
  ∑ x : ZMod N, ∑ y : ZMod N, ((w x : ℝ) * w y) * if x - y ∈ Q then 1 else 0

/-- Express a weighted difference incidence as a cast of a natural pair count.

Input: A natural-number residue weight `w` and a finite difference set `Q`.
Claim: The real incidence equals the natural sum over pairs whose difference
lies in `Q`.
Proof: Expand the indicator as a filtered finite sum and cast each weight.
Role: Connects weighted incidence bounds to natural-valued correlation sums.
-/
theorem weightedResidueDifferenceIncidence_eq_filtered_sum {N : ℕ} [NeZero N] (w : ZMod N → ℕ)
    (Q : Finset (ZMod N)) :
    weightedResidueDifferenceIncidence w Q =
      (∑ x : ZMod N, ∑ y ∈ Finset.univ.filter (fun y ↦ x - y ∈ Q), w x * w y : ℕ) := by
  unfold weightedResidueDifferenceIncidence
  simp only [Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : x - y ∈ Q <;> simp only [h, ite_true, ite_false, mul_one, mul_zero]

/-- Total mass of a natural-number weight on a finite cyclic group.

Definition: Sum the values of `w` over every residue class.
Input: A weight `w : ZMod N → ℕ`.
Output: Its total natural-number mass.
Role: Gives the main term in the weighted incidence estimate. -/
def weightedResidueMass {N : ℕ} [NeZero N] (w : ZMod N → ℕ) : ℕ :=
  ∑ x : ZMod N, w x

/-- Exact complex Fourier identity for weighted difference incidences.

Input: A natural-number weight `w` and a finite difference set `Q`.
Claim: The Fourier sum of `Q` against the weighted squared transform equals
`N` times the complex weighted incidence sum.
Proof: Expand the weighted norm square, interchange finite sums, and apply
the unweighted Fourier inversion formula to each difference.
Role: Provides the exact identity before separating the zero frequency. -/
theorem weightedResidueDifferenceIncidence_fourier_complex {N : ℕ} [NeZero N] (w : ZMod N → ℕ)
    (Q : Finset (ZMod N)) :
    (∑ l : ZMod N,
        residueCharacterSum Q (-l) * (Complex.normSq (weightedResidueCharacterSum w l) : ℂ)) =
      (N : ℂ) *
        ∑ x : ZMod N, ∑ y : ZMod N, (w x : ℂ) * (w y : ℂ) * if x - y ∈ Q then (1 : ℂ) else 0 := by
  simp only [weighted_residue_normSq_pairs, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]
  calc
    _ =
        ∑ y1 : ZMod N,
          ((w y : ℂ) * (w y1 : ℂ)) *
            ∑ x : ZMod N, residueCharacterSum Q (-x) * ZMod.stdAddChar (x * (y - y1)) :=
      by
      apply Finset.sum_congr rfl
      intro y1 hy1
      calc
        _ =
            ∑ x : ZMod N,
              ((w y : ℂ) * (w y1 : ℂ)) *
                (residueCharacterSum Q (-x) * ZMod.stdAddChar (x * (y - y1))) :=
          by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = _ := by rw [← Finset.mul_sum]
    _ = _ := by
      simp only [sum_residueCharacterSum_mul_char, mul_ite, mul_one, mul_zero]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : y - x ∈ Q
      · simp only [h, ite_true]
        ring
      · simp only [h, ite_false]

/-- The real part of the exact Fourier identity is the real weighted incidence.

Input: A natural-number weight `w` and a finite difference set `Q`.
Claim: The real Fourier sum equals `N` times the weighted incidence.
Proof: Take real parts of the complex identity and evaluate the real part
of the complex indicator of membership in `Q`.
Role: Prepares a real-valued estimate with an explicit zero-frequency term. -/
theorem weightedResidueDifferenceIncidence_fourier_re {N : ℕ} [NeZero N] (w : ZMod N → ℕ)
    (Q : Finset (ZMod N)) :
    (∑ l : ZMod N,
        (residueCharacterSum Q (-l)).re * Complex.normSq (weightedResidueCharacterSum w l)) =
      (N : ℝ) * weightedResidueDifferenceIncidence w Q := by
  have h := congrArg Complex.re (weightedResidueDifferenceIncidence_fourier_complex w Q)
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero, Complex.natCast_re, Complex.natCast_im] at h
  have hIndicator :
    ∀ d : ZMod N, (if d ∈ Q then (1 : ℂ) else 0).re = (if d ∈ Q then (1 : ℝ) else 0) := by
    intro d
    by_cases hd : d ∈ Q
    · simp only [hd, ite_true, Complex.one_re]
    · simp only [hd, ite_false, Complex.zero_re]
  simp only [hIndicator] at h
  exact h

/-- The weighted Fourier transform at zero is the total natural mass.

Input: A natural-number weight `w`.
Claim: Its zero-frequency transform is the cast of `weightedResidueMass w`.
Proof: The additive character is one at zero, and natural casts commute
with finite sums.
Role: Identifies the exact main term in the incidence decomposition. -/
theorem weightedResidueCharacterSum_zero {N : ℕ} [NeZero N] (w : ZMod N → ℕ) :
    weightedResidueCharacterSum w 0 = weightedResidueMass w := by
  simp only [weightedResidueCharacterSum, zero_mul, AddChar.map_zero_eq_one, mul_one,
    weightedResidueMass]
  exact (Nat.cast_sum Finset.univ w).symm

/-- Separate the zero frequency from the real weighted incidence identity.

Input: A natural-number weight `w` and a finite difference set `Q`.
Claim: The main term is `card(Q) * mass(w)^2`; all other frequencies remain
in the displayed finite sum.
Proof: Remove the zero frequency and evaluate both zero-frequency factors.
Role: Supports termwise bounds for nonzero Fourier coefficients. -/
theorem weightedResidueDifferenceIncidence_fourier_split {N : ℕ} [NeZero N] (w : ZMod N → ℕ)
    (Q : Finset (ZMod N)) :
    (N : ℝ) * weightedResidueDifferenceIncidence w Q =
      (Q.card : ℝ) * (weightedResidueMass w : ℝ) ^ 2 +
        ∑ l ∈ Finset.univ.erase (0 : ZMod N),
          (residueCharacterSum Q (-l)).re * Complex.normSq (weightedResidueCharacterSum w l) := by
  have h :=
    Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
      (fun l ↦ (residueCharacterSum Q (-l)).re * Complex.normSq (weightedResidueCharacterSum w l))
      (Finset.mem_univ (0 : ZMod N))
  rw [weightedResidueDifferenceIncidence_fourier_re, neg_zero, residueCharacterSum_zero,
    weightedResidueCharacterSum_zero, Complex.natCast_re, Complex.normSq_natCast] at h
  simpa only [pow_two] using h.symm.trans (add_comm _ _)

/-- A uniform nonzero Fourier envelope controls the scaled weighted incidence.

Input: A weight `w`, a difference set `Q`, and a nonnegative bound `M` for
all nonzero Fourier coefficients of `Q`.
Claim: `N * incidence` is at most the exact main term plus `N * M * sum(w^2)`.
Proof: Separate frequency zero, bound the remaining terms by `M`, and apply
the weighted Parseval identity to the total squared mass.
Role: This is the weighted counterpart of the finite-set incidence bound. -/
theorem weightedResidueDifferenceIncidence_mul_le_of_fourier_bound {N : ℕ} [NeZero N]
    (w : ZMod N → ℕ) (Q : Finset (ZMod N)) {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ l : ZMod N, l ≠ 0 → ‖residueCharacterSum Q l‖ ≤ M) :
    (N : ℝ) * weightedResidueDifferenceIncidence w Q ≤
      (Q.card : ℝ) * (weightedResidueMass w : ℝ) ^ 2 +
        (N : ℝ) * M * ∑ x : ZMod N, (w x : ℝ) ^ 2 := by
  rw [weightedResidueDifferenceIncidence_fourier_split]
  apply add_le_add le_rfl
  have ht :
    (∑ l ∈ Finset.univ.erase (0 : ZMod N),
        (residueCharacterSum Q (-l)).re * Complex.normSq (weightedResidueCharacterSum w l)) ≤
      M *
        ∑ l ∈ Finset.univ.erase (0 : ZMod N), Complex.normSq (weightedResidueCharacterSum w l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    have hn : -l ≠ 0 := neg_ne_zero.mpr (Finset.mem_erase.mp hl).1
    exact
      mul_le_mul_of_nonneg_right ((Complex.re_le_norm _).trans (hQ (-l) hn))
        (Complex.normSq_nonneg _)
  have hs :
    (∑ l ∈ Finset.univ.erase (0 : ZMod N), Complex.normSq (weightedResidueCharacterSum w l)) ≤
      (N : ℝ) * ∑ x : ZMod N, (w x : ℝ) ^ 2 := by
    rw [← weighted_residue_character_sum_second_moment]
    exact
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun l _ _ ↦ Complex.normSq_nonneg _)
  exact (ht.trans (mul_le_mul_of_nonneg_left hs hM)).trans_eq (by ring)

/-- Divide the scaled weighted incidence estimate by the positive modulus.

Input: The same Fourier-envelope hypotheses as the scaled estimate.
Claim: Incidence is at most `card(Q) * mass(w)^2 / N + M * sum(w^2)`.
Proof: Divide by the positive real cast of `N`.
Role: Gives the form used when summing the dyadic correlation levels. -/
theorem weightedResidueDifferenceIncidence_le_of_fourier_bound {N : ℕ} [NeZero N] (w : ZMod N → ℕ)
    (Q : Finset (ZMod N)) {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ l : ZMod N, l ≠ 0 → ‖residueCharacterSum Q l‖ ≤ M) :
    weightedResidueDifferenceIncidence w Q ≤
      (Q.card : ℝ) * (weightedResidueMass w : ℝ) ^ 2 / N + M * ∑ x : ZMod N, (w x : ℝ) ^ 2 := by
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  apply (mul_le_mul_iff_right₀ hN).mp
  calc
    (N : ℝ) * weightedResidueDifferenceIncidence w Q ≤
        (Q.card : ℝ) * (weightedResidueMass w : ℝ) ^ 2 +
          (N : ℝ) * M * ∑ x : ZMod N, (w x : ℝ) ^ 2 :=
      weightedResidueDifferenceIncidence_mul_le_of_fourier_bound w Q hM hQ
    _ =
        (N : ℝ) *
          ((Q.card : ℝ) * (weightedResidueMass w : ℝ) ^ 2 / N + M * ∑ x : ZMod N, (w x : ℝ) ^ 2) :=
      by field_simp [hN.ne']

end PseudoPrime.NumberTheory.Heilbronn
