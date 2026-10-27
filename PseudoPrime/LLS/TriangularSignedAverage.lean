/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSubgroupAverage

/-! # Signed arithmetic averages for triangular zero budgets -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- At positive scale, replacing a complex Dirichlet character by its inverse
does not change the arithmetic summand's real part. Use conjugate character
values and the real inverse Mellin transform. This preserves signed averages. -/
theorem summand_inv_re_eq (K : MellinKernel) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (n : ℕ) : (K.summand χ⁻¹ x n).re = (K.summand χ x n).re := by
  by_cases hn : n = 0
  · simp only [summand, hn, ite_true, Complex.zero_re]
  · have hu : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
    have hi : (K.transform ((n : ℝ) / x)).im = 0 := K.mellin_real _ hu
    rw [summand, summand, ite_eq_right hn, ite_eq_right hn, ← MulChar.star_apply']
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, hi, mul_zero, Complex.star_def, Complex.conj_re]

end PseudoPrime.LLS.PaperStatements.MellinKernel

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- At positive scale, the inverse character arithmetic series has the same
real part as the original series. Commute the continuous real-part map with
the summable series and apply the term identity. This removes inverse terms
from signed zero-mass budgets. -/
theorem tsum_summand_inv_re_eq (K : MellinKernel) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) : (∑' n : ℕ, K.summand χ⁻¹ x n).re = (∑' n : ℕ, K.summand χ x n).re := by
  change Complex.reCLM (∑' n : ℕ, K.summand χ⁻¹ x n) = Complex.reCLM (∑' n : ℕ, K.summand χ x n)
  rw [Complex.reCLM.map_tsum (summable_summand K χ⁻¹ hx),
    Complex.reCLM.map_tsum (summable_summand K χ hx)]
  exact tsum_congr (summand_inv_re_eq K χ hx)

/-- For a finite character subgroup at positive scale, the real full primitive
arithmetic aggregate is nonnegative. Interchange the finite and infinite sums
and use local primitive orthogonality at each index. This supplies the sign
needed to bound nonprincipal arithmetic averages. -/
theorem primitive_tsum_sum_re_nonneg (K : MellinKernel) {q : ℕ} [NeZero q]
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] {x : ℝ} (hx : 0 < x) :
    0 ≤ (∑ χ : S, (∑' n : ℕ, K.summand χ.val.primitiveCharacter x n)).re := by
  have hs (χ : S) : Summable (K.summand χ.val.primitiveCharacter x) := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact summable_summand K χ.val.primitiveCharacter hx
  have he := Summable.tsum_finsetSum (fun χ (_ : χ ∈ Finset.univ) ↦ hs χ)
  have hi := (hasSum_sum (fun χ (_ : χ ∈ Finset.univ) ↦ (hs χ).hasSum)).summable
  change 0 ≤ Complex.reCLM (∑ χ : S, ∑' n : ℕ, K.summand χ.val.primitiveCharacter x n)
  rw [← he, Complex.reCLM.map_tsum hi]
  exact tsum_nonneg (fun n ↦ primitive_summand_sum_re_nonneg K S hx)

end PseudoPrime.LLS.PaperStatements.MellinKernel

namespace PseudoPrime.LLS.PaperStatements

/-- For the alpha-18 kernel at positive scale, the nonprincipal annihilator
sum of character and inverse arithmetic real parts is at least minus twice
the level-one principal sum. Remove the unique principal term from the
nonnegative full primitive aggregate and use the inverse real-part identity.
This closes the signed arithmetic term in the conductor comparison. -/
theorem triangular18_nonprincipal_arithmetic_pair_sum_lower {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) {x : ℝ} (hx : 0 < x) :
    letI := Classical.propDecidable
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18);
    -(2 : ℝ) * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
        ((∑' n : ℕ, K.summand χ.val.primitiveCharacter x n).re +
          (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ x n).re) := by
  classical
  let _ := Classical.propDecidable
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let A := NumberTheory.subgroupAnnihilator H
  let F := fun χ : A ↦ (∑' n : ℕ, K.summand χ.val.primitiveCharacter x n).re
  have hn := MellinKernel.primitive_tsum_sum_re_nonneg K A hx
  rw [Complex.re_sum] at hn
  have he := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re := by
    exact
      congrArg Complex.re (tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x))
  have hr (χ : A) : (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ x n).re = F χ := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact MellinKernel.tsum_summand_inv_re_eq K χ.val.primitiveCharacter hx
  have hs :=
    Finset.sum_congr (s₁ := Finset.univ.erase (1 : A)) rfl
      (fun χ _ ↦ congrArg (fun y : ℝ ↦ F χ + y) (hr χ))
  change -(2 : ℝ) * _ ≤ _
  rw [hs, Finset.sum_add_distrib]
  rw [hp] at he
  change 0 ≤ ∑ χ : A, F χ at hn
  linarith only [hn, he]

end PseudoPrime.LLS.PaperStatements
