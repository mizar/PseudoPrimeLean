/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FiniteExcludedTaperSavings
public import PseudoPrime.PseudoSquare.Bounds.ExcludedEndpointJacobi

/-! # Negative Jacobi witnesses retaining the finite excluded-support taper -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

open AnalyticNumberTheory.Arithmetic in
/-- For odd nonsquare n under GRH and x>=64, an upper bound C on its canonical
untapered exclusion budget and a negative improved separation at 4n give an
odd n-coprime Jacobi-minus-one prime. Insert the finite taper saving before
transferring the primitive character witness. Zero Jacobi values are excluded. -/
theorem exists_prime_neg_one_of_finite_excluded_taper {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 64 ≤ x)
    (hC :
      quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
          (Finset.Ioc 0 ⌊x⌋₊) (LLS.PaperStatements.untaperedExcludedEndpointWeight x) ≤
        C)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x x 0 0 + C -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
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
  have hqle :=
    Nat.le_of_dvd (NeZero.pos (4 * n))
      (NumberTheory.complexQuadraticCharacter n hn).conductor_dvd_level
  have hx1 : 1 < x := by linarith only [hx]
  have hm :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (x := x) (Y := x) (c := 0) (D := 0)
      (Nat.pos_of_ne_zero (NeZero.ne _)) hqle hx1.le hx
  have hs :
    LLS.PaperStatements.oddEndpointTwoCostLimit
            (NumberTheory.complexQuadraticCharacter n hn).conductor x x 0 0 +
          C -
        (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
      0 := by
    linarith only [hm, hsep]
  obtain ⟨p, hprime, hodd, hpx, hpc, hv⟩ :=
    LLS.PaperStatements.exists_prime_neg_one_of_finite_excluded_taper hq
      (NumberTheory.complexQuadraticCharacter n hn).conductor_dvd_level
      (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩) hGRH hp hne hquad hx hC hs
  have hcp : Nat.Coprime p n := hpc.of_dvd_right (show n ∣ 4 * n from ⟨4, by ring⟩)
  have he :=
    NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hprime hodd
      (hprime.coprime_iff_not_dvd.mp hcp)
  simp only [Int.cast_natCast] at he
  have hj : jacobiSym n p = -1 := by exact_mod_cast (he.symm.trans hv)
  exact ⟨p, hprime, hodd, hpx, hcp, hj⟩

open AnalyticNumberTheory.Arithmetic in
/-- Under the canonical untapered budget and improved separation hypotheses,
the least negative odd-prime Jacobi witness is at most x. Apply leastness to
the constructed negative prime. The nonempty set supplies the existing definition. -/
theorem primeNegOneWitness_le_of_finite_excluded_taper {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 64 ≤ x)
    (hC :
      quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
          (Finset.Ioc 0 ⌊x⌋₊) (LLS.PaperStatements.untaperedExcludedEndpointWeight x) ≤
        C)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x x 0 0 + C -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, _, hv⟩ :=
    exists_prime_neg_one_of_finite_excluded_taper hn hns hGRH hx hC hsep
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

open AnalyticNumberTheory.Arithmetic in
/-- Under GRH, a common untapered exclusion budget for every admissible n<=B
and the improved separation at 4B give QNegOne(B)<=x. Use conductor and level
monotonicity and the least-witness bound; no finite input certificate is assumed. -/
theorem QNegOne_le_of_finite_excluded_taper {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C : ℝ} (hx : 64 ≤ x)
    (hlocal :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          quadraticExcludedBudget (NumberTheory.complexQuadraticCharacter n hn).conductor (4 * n)
              (Finset.Ioc 0 ⌊x⌋₊) (LLS.PaperStatements.untaperedExcludedEndpointWeight x) ≤
            C)
    (hsep :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x x 0 0 + C -
          (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
        0) :
    (QNegOne B : ℝ) ≤ x := by
  have hx1 : 1 < x := by linarith only [hx]
  apply QNegOne_cast_le_of_forall (zero_lt_one.trans hx1).le
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hq0 : 0 < 4 * n := Nat.mul_pos (by norm_num only) ha.odd.pos
  have hm :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (x := x) (Y := x) (c := 0) (D := 0) hq0
      (Nat.mul_le_mul_left 4 ha.le) hx1.le hx
  have hs :
    LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x x 0 0 + C -
        (LLS.PaperStatements.excludedReciprocalCoefficient x / x) * Real.log 2 <
      0 := by
    linarith only [hm, hsep]
  exact
    primeNegOneWitness_le_of_finite_excluded_taper ha.odd ha.not_isSquare hGRH hx
      (hlocal n hn ha.odd) hs
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

end PseudoPrime.PseudoSquare
