/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPolePrincipalSharp
public import PseudoPrime.LLS.PaperStatements.RationalPoleScalarBudget

/-!
# Actual witnesses from the improved fourth-pole principal gap

Only the principal error is replaced. The existing character, Euler, arithmetic and
ambient local costs are retained, including their primitive-conductor dependence.
No logarithmic entrance or finite numerical row is selected in this module.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and primitive nonprincipal quadratic data, the improved principal gap
and the unchanged exact character and local costs produce an eligible actual prime.
Contradict the no-witness comparison using the new actual principal lower bound and
the existing full character estimate. This is the kernel-level witness criterion. -/
theorem fourPole_abel_exists_prime {q a : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hq : 2 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (A B : Finset ℕ)
    (hgap :
      rationalPoleFourEulerBudget χ A B + 3 + (24 * Real.log q + 793) * x ^ (-3 / 4 : ℝ) +
          (2 * x ^ (1 / 4 : ℝ) + 14) +
          fourPoleLocalCost χ a x <
        Real.sqrt x *
          (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
            (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4))) :
    ∃ p : ℕ, p.Prime ∧ Nat.Coprime p a ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  by_contra hno
  have hsmall : ∀ p : ℕ, p.Prime → Nat.Coprime p a → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hpp hpc hpx
    by_contra hpne
    exact hno ⟨p, hpp, hpc, hpx, hpne⟩
  have hc :=
    fourPole_no_witness_comparison χ hquad ((by norm_num only : (0 : ℝ) < 2).trans_le hx) hsmall
  have hP := fourPole_principal_gap_sharp hGRH.riemann hx
  have hC :=
    rationalPole_four_smoothed_le hq hGRH hp hne hinv ((by norm_num only : (1 : ℝ) ≤ 2).trans hx) A
      B
  have hr := le_abs_self (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) χ x n).re
  linarith only [hc, hP, hC, hr, hgap]

/-- For an odd nonsquare under GRH, the improved finite gap yields an actual negative
Jacobi odd-prime witness through the chosen cutoff. The primitive conductor remains
on the character side and the original level 4*n remains in the exact local cost.
Use the canonical arithmetic bridge to transfer the actual quadratic prime criterion. -/
theorem fourPole_abel_jacobi_of_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x)
    (A B : Finset ℕ)
    (hgap :
      rationalPoleFourEulerBudget bridge.character A B + 3 +
          (24 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 793) *
            x ^ (-3 / 4 : ℝ) +
          (2 * x ^ (1 / 4 : ℝ) + 14) +
          fourPoleLocalCost bridge.character (4 * n) x <
        Real.sqrt x *
          (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
            (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p = -1 := by
  have hq3 := LLS.gamma_jacobi_modulus_ge_three bridge
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3) hq3).ne'⟩
  have hinv : bridge.character⁻¹ ≠ 1 := by
    rw [bridge.character_quadratic.inv]
    exact bridge.character_ne_one
  obtain ⟨p, hp, hpc, hpx, hne⟩ :=
    fourPole_abel_exists_prime bridge.character bridge.character_quadratic
      ((by norm_num only : (2 : ℕ) ≤ 3).trans hq3) hGRH bridge.character_primitive
      bridge.character_ne_one hinv hx A B hgap
  by_contra hnone
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → jacobiSym n p ≠ -1 := by
    intro p hpp hpo hpb hpj
    exact hnone ⟨p, hpp, hpo, hpb, hpj⟩
  exact hne (LLS.gamma_jacobi_no_negative_prefix_prime_one bridge hno p hp hpx hpc)

/-- Under GRH, the displayed scalar gap with the improved principal error produces
an actual negative Jacobi odd-prime witness. Apply the unchanged empty-prefix Euler
bound and ambient logarithmic local bound before using the exact Jacobi criterion.
This preserves the existing character and local coefficients for new entrance certificates. -/
theorem fourPole_abel_jacobi_scalar {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x)
    (hgap :
      (2501 / 10000 : ℝ) * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 1003 +
          (24 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 793) *
            x ^ (-3 / 4 : ℝ) +
          (2 * x ^ (1 / 4 : ℝ) + 14) +
          (20 / Real.sqrt x) * (Real.log x / Real.log 2) * Real.log (4 * n) <
        Real.sqrt x *
          (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
            (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p = -1 := by
  apply fourPole_abel_jacobi_of_gap bridge hGRH hx ∅ ∅
  have he := fourPole_emptyEulerBudget_le bridge.character
  have hl :=
    fourPoleLocalCost_le_log bridge.character bridge.character_quadratic
      (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hx
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hl
  linarith only [he, hl, hgap]

end PseudoPrime.LLS.PaperStatements
