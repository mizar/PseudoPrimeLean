/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedEulerSeries

/-! # Nonnegative paired mass for the signed common Gamma Euler weight -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The principal-plus-character Euler mass with the common nonnegative
Gamma weight H(m). Combine the signed resolvent coefficients before using
positivity: individual coefficients may be negative. The mass retains the
whole nonnegative prime-power sum in the zero-side comparison. -/
noncomputable def gammaPairedEulerTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  (1 + (χ m).re) * gammaResolventMangoldtWeight m

/-- For every character, the common paired Euler series converges absolutely.
Combine the convergent common weight and its norm-bounded character twist. -/
theorem summable_gammaPairedEulerTerm {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Summable (gammaPairedEulerTerm χ) := by
  have hc (m : ℕ) : |(χ m).re| ≤ 1 := (Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m)
  exact
    (summable_gammaResolventMangoldtWeight.sub
          (summable_gamma_signed_euler (fun m ↦ (χ m).re) hc)).congr
      (fun m ↦ by
        dsimp only [gammaPairedEulerTerm]; ring)

/-- Every common paired Euler term is nonnegative. Use the character norm
bound and the already certified nonnegative combined Gamma weight. Individual
signed resolvent coefficients are not treated as positive coefficients. -/
theorem gammaPairedEulerTerm_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (m : ℕ) :
    0 ≤ gammaPairedEulerTerm χ m := by
  have hχ := (abs_le.mp ((Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m))).1
  exact mul_nonneg (by linarith only [hχ]) (gammaResolventMangoldtWeight_nonneg m)

/-- The negative character Euler sum plus the common paired mass equals
the untwisted total weight exactly. Absolute convergence preserves this
cancellation and avoids estimating the two logarithmic derivatives separately. -/
theorem gamma_signed_euler_add_paired_eq_total {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑' m : ℕ, -(χ m).re * gammaResolventMangoldtWeight m) + (∑' m : ℕ, gammaPairedEulerTerm χ m) =
      ∑' m : ℕ, gammaResolventMangoldtWeight m := by
  have hc (m : ℕ) : |(χ m).re| ≤ 1 := (Complex.abs_re_le_norm (χ m)).trans (χ.norm_le_one m)
  rw [←
    (summable_gamma_signed_euler (fun m ↦ (χ m).re) hc).tsum_add (summable_gammaPairedEulerTerm χ)]
  exact
    tsum_congr
      (fun m ↦ by
        dsimp only [gammaPairedEulerTerm]; ring)

/-- The unretained common paired Euler mass after removing a finite set B.
It is the full sum minus the exact retained finite sum, hence nonnegative.
The definition keeps the useful complementary prime-power contribution explicit. -/
noncomputable def gammaPairedEulerTail {q : ℕ} (χ : DirichletCharacter ℂ q) (B : Finset ℕ) : ℝ :=
  (∑' m : ℕ, gammaPairedEulerTerm χ m) - ∑ m ∈ B, gammaPairedEulerTerm χ m

/-- The unretained paired mass is nonnegative for every finite B.
Absolute convergence and termwise positivity give finite-sum domination. -/
theorem gammaPairedEulerTail_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (B : Finset ℕ) :
    0 ≤ gammaPairedEulerTail χ B := by
  exact
    sub_nonneg.mpr
      ((summable_gammaPairedEulerTerm χ).sum_le_tsum B (fun m _ ↦ gammaPairedEulerTerm_nonneg χ m))

/-- The retained paired mass equals twice the common weight prefix minus
the exact character deficit on that prefix. This is an equality at all
character values, including zero and minus one. -/
theorem gammaPairedEuler_prefix_eq_gain_sub_deficit {q : ℕ} (χ : DirichletCharacter ℂ q)
    (B : Finset ℕ) :
    (∑ m ∈ B, gammaPairedEulerTerm χ m) =
      2 * (∑ m ∈ B, gammaResolventMangoldtWeight m) -
        ∑ m ∈ B, (1 - (χ m).re) * gammaResolventMangoldtWeight m := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact
    Finset.sum_congr rfl
      (fun m _ ↦ by
        dsimp only [gammaPairedEulerTerm]; ring)

/-- A finite set C disjoint from the retained set B contributes a certified
lower bound to the paired tail. Sum over B∪C, retaining all nonnegative terms.
This supplies explicit extra prime-power gains beyond the original prefix. -/
theorem gammaPairedEulerTail_ge_disjoint_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (B C : Finset ℕ)
    (hBC : Disjoint B C) : (∑ m ∈ C, gammaPairedEulerTerm χ m) ≤ gammaPairedEulerTail χ B := by
  classical
  have h :=
    (summable_gammaPairedEulerTerm χ).sum_le_tsum (B ∪ C)
      (fun m _ ↦ gammaPairedEulerTerm_nonneg χ m)
  rw [Finset.sum_union hBC] at h
  exact (le_sub_iff_add_le).mpr (by simpa only [add_comm] using h)

/-- At a square input, a quadratic character has value zero or one.
Consequently its paired term contains at least one full common weight,
including ramified inputs. This gives a factorization-independent tail gain. -/
theorem gammaPairedEulerTerm_square_ge_weight {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {m : ℕ} (hm : IsSquare m) :
    gammaResolventMangoldtWeight m ≤ gammaPairedEulerTerm χ m := by
  rcases hm with ⟨a, rfl⟩
  have hv : 0 ≤ (χ (a * a : ℕ)).re := by
    simp only [Nat.cast_mul, map_mul]
    rcases hquad (a : ZMod q) with h0 | h1 | hm
    · simp only [h0, zero_mul, Complex.zero_re, le_refl]
    · simp only [h1, one_mul, Complex.one_re, zero_le_one]
    · simp only [hm, neg_mul_neg, one_mul, Complex.one_re, zero_le_one]
  have h :=
    mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + (χ (a * a : ℕ)).re by linarith only [hv])
      (gammaResolventMangoldtWeight_nonneg (a * a))
  simpa only [gammaPairedEulerTerm, one_mul] using h

/-- A finite set of square inputs outside B contributes at least its full
common weight to the paired tail of a quadratic character. Combine the
square-value bound with disjoint finite-sum domination; ramified inputs
remain valid and need no separate exclusions. -/
theorem gammaPairedEulerTail_ge_square_sum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (B C : Finset ℕ) (hBC : Disjoint B C) (hC : ∀ m ∈ C, IsSquare m) :
    (∑ m ∈ C, gammaResolventMangoldtWeight m) ≤ gammaPairedEulerTail χ B := by
  exact
    (Finset.sum_le_sum (fun m hm ↦ gammaPairedEulerTerm_square_ge_weight χ hquad (hC m hm))).trans
      (gammaPairedEulerTail_ge_disjoint_sum χ B C hBC)

end PseudoPrime.Analysis
