/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.FiniteCharacterMoments

/-! # Parseval identities for natural-number weights on finite cyclic groups -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The Fourier transform of a natural-number weight on a finite cyclic group.

Definition: Sum each weight times the corresponding additive character.
Input: A weight w : ZMod N → ℕ and a frequency l.
Output: A complex Fourier coefficient.
Role: Supplies weighted Parseval and incidence estimates. -/
noncomputable def weightedResidueCharacterSum {N : ℕ} [NeZero N] (w : ZMod N → ℕ) (l : ZMod N) :
    ℂ :=
  ∑ x : ZMod N, (w x : ℂ) * ZMod.stdAddChar (l * x)

/-- The squared norm of the weighted transform expands as an ordered
difference sum with product weights.

Input: A natural-number weight and a frequency.
Claim: The squared norm equals the corresponding finite difference sum.
Proof: Expand the product with the conjugate character and collect terms.
Role: Converts Fourier moments into arithmetic incidence sums. -/
theorem weighted_residue_normSq_pairs {N : ℕ} [NeZero N] (w : ZMod N → ℕ) (l : ZMod N) :
    (Complex.normSq (weightedResidueCharacterSum w l) : ℂ) =
      ∑ x : ZMod N, ∑ y : ZMod N, (w x : ℂ) * (w y : ℂ) * ZMod.stdAddChar (l * (x - y)) := by
  rw [weightedResidueCharacterSum, ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, map_mul, Complex.conj_natCast,
    conj_stdAddChar]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  calc
    ↑(w x) * ZMod.stdAddChar (l * x) * (↑(w y) * ZMod.stdAddChar (-(l * y))) =
        ↑(w x) * ↑(w y) * (ZMod.stdAddChar (l * x) * ZMod.stdAddChar (-(l * y))) :=
      by ring
    _ = ↑(w x) * ↑(w y) * ZMod.stdAddChar (l * (x - y)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      congr 1
      ring

/-- Taking real parts makes the pair expansion an identity for
Complex.normSq.

Input: A natural-number weight and a frequency.
Claim: The norm square is the double sum of character real parts weighted
by the products of the original natural weights.
Proof: Apply the real-part map to the complex pair identity.
Role: Prepares the second-moment calculation. -/
theorem weighted_residue_normSq_pairs_real {N : ℕ} [NeZero N] (w : ZMod N → ℕ) (l : ZMod N) :
    Complex.normSq (weightedResidueCharacterSum w l) =
      ∑ x : ZMod N, ∑ y : ZMod N, ((w x : ℝ) * w y) * (ZMod.stdAddChar (l * (x - y))).re := by
  have h := congrArg Complex.re (weighted_residue_normSq_pairs w l)
  simpa only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, Complex.natCast_re, Complex.natCast_im] using
    h

/-- Parseval's identity for a natural-number weight on ZMod N.

Input: A weight w : ZMod N → ℕ and a nonzero modulus N.
Claim: The total Fourier second moment is N times the square mass.
Proof: Expand the pair sum and apply additive-character orthogonality.
Role: Provides the sum of squares of w in the weighted incidence bound. -/
theorem weighted_residue_character_sum_second_moment {N : ℕ} [NeZero N] (w : ZMod N → ℕ) :
    (∑ l : ZMod N, Complex.normSq (weightedResidueCharacterSum w l)) =
      (N : ℝ) * ∑ x : ZMod N, (w x : ℝ) ^ 2 := by
  calc
    _ =
        ∑ l : ZMod N,
          ∑ x : ZMod N, ∑ y : ZMod N, ((w x : ℝ) * w y) * (ZMod.stdAddChar (l * (x - y))).re :=
      by
      apply Finset.sum_congr rfl
      intro l hl
      exact weighted_residue_normSq_pairs_real w l
    _ = _ := by
      rw [Finset.sum_comm]
      calc
        _ =
            ∑ x : ZMod N,
              ∑ y : ZMod N, ((w x : ℝ) * w y) * ∑ l : ZMod N, (ZMod.stdAddChar (l * (x - y))).re :=
          by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          rw [← Finset.mul_sum]
        _ = ∑ x : ZMod N, ∑ y : ZMod N, ((w x : ℝ) * w y) * (if x = y then (N : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          congr 1
          have hchar :
            (∑ l : ZMod N, (ZMod.stdAddChar (l * (x - y))).re) = if x = y then (N : ℝ) else 0 := by
            rw [← Complex.re_sum]
            have ht :
              (∑ l : ZMod N, ZMod.stdAddChar (l * (x - y))) =
                ∑ l : ZMod N, ZMod.stdAddChar ((x - y) * l) := by
              apply Finset.sum_congr rfl
              intro l _
              congr 1
              ring
            rw [ht, sum_stdAddChar_mul]
            by_cases hxy : x = y
            · subst y
              simp only [sub_self, ite_true, Complex.natCast_re]
            · have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
              simp only [sub_eq_zero, hxy, ite_false, Complex.zero_re]
          exact hchar
        _ = ∑ x : ZMod N, (N : ℝ) * (w x : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hinner :
            (∑ y : ZMod N, ((w x : ℝ) * w y) * (if x = y then (N : ℝ) else 0)) =
              (N : ℝ) * (w x : ℝ) ^ 2 := by
            rw [Finset.sum_eq_single x]
            · simp only [ite_true]
              ring
            · intro y hy hne
              rw [ite_eq_right (Ne.symm hne), mul_zero]
            · intro hx'
              exact (hx' (Finset.mem_univ x)).elim
          exact hinner
        _ = _ := by rw [← Finset.mul_sum]

end PseudoPrime.NumberTheory.Heilbronn
