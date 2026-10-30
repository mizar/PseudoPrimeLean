/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleNoWitness
public import PseudoPrime.LLS.GammaNoNegativeRampSupport
public import PseudoPrime.LLS.GammaResolventCharacterComparison

/-! # Finite fourth-pole criterion for actual Jacobi witnesses -/

public section

namespace PseudoPrime.LLS.PaperStatements

/-- For an odd nonsquare input under GRH, the explicit fourth-pole finite gap
produces an odd-prime negative Jacobi witness through the chosen cutoff.
The Euler side retains the primitive conductor, while the exact local cost retains
the ambient modulus `4*n`; existing Jacobi prime agreement discharges all exclusions. -/
theorem fourPole_exists_jacobi_of_gap {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x)
    (A B : Finset ℕ)
    (hgap :
      rationalPoleFourEulerBudget bridge.character A B + 3 +
          (24 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 793) *
            x ^ (-3 / 4 : ℝ) +
          (65 * x ^ (1 / 4 : ℝ) + 120 / Real.sqrt x) +
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
    fourPole_exists_prime_of_gap bridge.character bridge.character_quadratic
      ((by norm_num only : (2 : ℕ) ≤ 3).trans hq3) hGRH bridge.character_primitive
      bridge.character_ne_one hinv hx A B hgap
  by_contra hnone
  have hno : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → jacobiSym n p ≠ -1 := by
    intro p hpp hpo hpb hpj
    exact hnone ⟨p, hpp, hpo, hpb, hpj⟩
  exact hne (LLS.gamma_jacobi_no_negative_prefix_prime_one bridge hno p hp hpx hpc)

end PseudoPrime.LLS.PaperStatements
