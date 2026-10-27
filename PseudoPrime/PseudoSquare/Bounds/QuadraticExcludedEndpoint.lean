/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.QuadraticExcludedEndpoint
public import PseudoPrime.PseudoSquare.Bounds.ExcludedEndpointJacobi

/-! # Jacobi bounds from one structural quadratic exclusion budget -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

open AnalyticNumberTheory.Arithmetic in
/-- For odd nonsquare n under GRH and x>=64, a negative zero-cost endpoint
limit plus the structural exclusion budget gives an odd negative Jacobi prime
at most x. Transfer the primitive quadratic witness, retaining coprimality to n. -/
theorem exists_odd_prime_jacobi_neg_one_of_quadratic_excluded_budget {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 64 ≤ x)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit
            (NumberTheory.complexQuadraticCharacter n hn).conductor x x 0 0 +
          quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
            (Finset.Ioc 0 ⌊x⌋₊) (LLS.PaperStatements.excludedEndpointWeight x) <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let χ := NumberTheory.primitiveQuadraticCharacter n hn
  let _ : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨(NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero⟩
  have hp : χ.IsPrimitive :=
    (NumberTheory.complexQuadraticCharacter n hn).primitiveCharacter_isPrimitive
  have hquad : χ.IsQuadratic :=
    NumberTheory.isQuadratic_primitiveCharacter (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
  have hne : χ ≠ 1 := NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
  have hq : 2 ≤ (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    (Nat.two_le_iff _).mpr ⟨NeZero.ne _, fun he ↦ hne (DirichletCharacter.level_one' χ he)⟩
  obtain ⟨p, hprime, hodd, hpx, hpc, hv⟩ :=
    LLS.PaperStatements.exists_odd_prime_neg_one_of_quadratic_excluded_budget hq
      (NumberTheory.complexQuadraticCharacter n hn).conductor_dvd_level
      (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩) hGRH hp hne hquad hx hsep
  have hcp : Nat.Coprime p n := hpc.of_dvd_right (show n ∣ 4 * n from ⟨4, by ring⟩)
  have he :=
    NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hprime hodd
      (hprime.coprime_iff_not_dvd.mp hcp)
  simp only [Int.cast_natCast] at he
  have hj : jacobiSym n p = -1 := by exact_mod_cast (he.symm.trans hv)
  exact ⟨p, hprime, hodd, hpx, hcp, hj⟩

open AnalyticNumberTheory.Arithmetic in
/-- Under the same one-budget condition, the least odd-prime negative Jacobi
witness is at most x. Apply leastness to the constructed prime; the nonempty-set
input supplies the existing witness definition. -/
theorem primeNegOneWitness_cast_le_of_quadratic_excluded_budget {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 64 ≤ x)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit
            (NumberTheory.complexQuadraticCharacter n hn).conductor x x 0 0 +
          quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
            (Finset.Ioc 0 ⌊x⌋₊) (LLS.PaperStatements.excludedEndpointWeight x) <
        0)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, _, hv⟩ :=
    exists_odd_prime_jacobi_neg_one_of_quadratic_excluded_budget hn hns hGRH hx hsep
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

open AnalyticNumberTheory.Arithmetic in
/-- Under GRH and x>=64, one uniform structural-budget upper bound Z for all
admissible n<=B and a negative zero-cost endpoint expression at 4*B imply
QNegOne(B)<=x. Use level monotonicity and pointwise leastness; uniform local
budget certification remains an explicit hypothesis. -/
theorem QNegOne_cast_le_of_quadratic_excluded_budget {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Z : ℝ} (hx : 64 ≤ x)
    (hlocal :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
              (Finset.Ioc 0 ⌊x⌋₊) (LLS.PaperStatements.excludedEndpointWeight x) ≤
            Z)
    (hsep : LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x x 0 0 + Z < 0) :
    (QNegOne B : ℝ) ≤ x := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  apply QNegOne_cast_le_of_forall (zero_le_one.trans hx1)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) ha.odd.pos.ne'⟩
  have hq := (NumberTheory.complexQuadraticCharacter n ha.odd).conductor_dvd_level
  have hqle :=
    (Nat.le_of_dvd (Nat.mul_pos (by norm_num only : 0 < 4) ha.odd.pos) hq).trans
      (Nat.mul_le_mul_left 4 ha.le)
  have hm :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := 0) (D := 0)
      (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n ha.odd).conductor_ne_zero) hqle
      hx1 hx
  have hl := hlocal n hn ha.odd
  have hs := lt_of_le_of_lt (add_le_add hm hl) hsep
  exact
    primeNegOneWitness_cast_le_of_quadratic_excluded_budget ha.odd ha.not_isSquare hGRH hx hs
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

open AnalyticNumberTheory.Arithmetic in
/-- The same uniform one-budget condition bounds QNeOne(B) by x, since the
non-one finite maximum is at most the negative finite maximum. This preserves
the arithmetic certification boundary of the negative-witness theorem. -/
theorem QNeOne_cast_le_of_quadratic_excluded_budget {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Z : ℝ} (hx : 64 ≤ x)
    (hlocal :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
              (Finset.Ioc 0 ⌊x⌋₊) (LLS.PaperStatements.excludedEndpointWeight x) ≤
            Z)
    (hsep : LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x x 0 0 + Z < 0) :
    (QNeOne B : ℝ) ≤ x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_cast_le_of_quadratic_excluded_budget hGRH hx hlocal hsep)

end PseudoPrime.PseudoSquare
