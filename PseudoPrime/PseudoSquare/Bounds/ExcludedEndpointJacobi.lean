/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExcludedEndpointWitness
public import PseudoPrime.PseudoSquare.Bounds.ReciprocalGapEndpointJacobi
public import PseudoPrime.PseudoSquare.QNeOneHalfShiftBounds

/-! # Negative Jacobi witnesses from exact excluded-support endpoint costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

open AnalyticNumberTheory.Arithmetic in
/-- For odd nonsquare n under GRH, exact excluded reciprocal and logarithmic
cost bounds and a negative endpoint limit at the canonical conductor give an
odd prime at most x coprime to n with Jacobi value minus one. Transfer the
primitive character witness; no selected support or positive gap is required. -/
theorem exists_odd_prime_jacobi_neg_one_of_excluded_endpoint {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c D : ℝ}
    (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hC :
      excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
          (Finset.Ioc 0 ⌊Y⌋₊) (reciprocalWeightedMangoldtTerm Y) ≤
        c)
    (hD :
      excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
          (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) ≤
        D)
    (hlim :
      LLS.PaperStatements.oddEndpointTwoCostLimit
          (NumberTheory.complexQuadraticCharacter n hn).conductor x Y c D <
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
    LLS.PaperStatements.exists_odd_prime_neg_one_of_excluded_two_cost_limit_neg hq
      (NumberTheory.complexQuadraticCharacter n hn).conductor_dvd_level
      (show 2 ∣ 4 * n from ⟨2 * n, by ring⟩) hGRH hp hne hquad hx hY hYx hC hD hlim
  have hcp : Nat.Coprime p n := hpc.of_dvd_right (show n ∣ 4 * n from ⟨4, by ring⟩)
  have he :=
    NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hprime hodd
      (hprime.coprime_iff_not_dvd.mp hcp)
  simp only [Int.cast_natCast] at he
  have hj : jacobiSym n p = -1 := by exact_mod_cast (he.symm.trans hv)
  exact ⟨p, hprime, hodd, hpx, hcp, hj⟩

open AnalyticNumberTheory.Arithmetic in
/-- Under the same excluded-cost endpoint conditions, the least odd-prime
negative Jacobi witness is at most x. Apply leastness to the constructed prime;
the nonempty-set input supplies the existing witness definition. -/
theorem primeNegOneWitness_cast_le_of_excluded_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c D : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hC :
      excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
          (Finset.Ioc 0 ⌊Y⌋₊) (reciprocalWeightedMangoldtTerm Y) ≤
        c)
    (hD :
      excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
          (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) ≤
        D)
    (hlim :
      LLS.PaperStatements.oddEndpointTwoCostLimit
          (NumberTheory.complexQuadraticCharacter n hn).conductor x Y c D <
        0)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, _, hv⟩ :=
    exists_odd_prime_jacobi_neg_one_of_excluded_endpoint hn hns hGRH hx hY hYx hC hD hlim
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

open AnalyticNumberTheory.Arithmetic in
/-- Under GRH and 64<=Y<=x, uniform local defect bounds on all admissible
n<=B and a negative endpoint limit at 4*B bound QNegOne(B) by x. Use conductor
level monotonicity and the pointwise least-witness theorem. The uniform local
cost bounds remain explicit mathematical hypotheses, not enumerated certificates. -/
theorem QNegOne_cast_le_of_excluded_endpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c D : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlocal :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
                (Finset.Ioc 0 ⌊Y⌋₊) (reciprocalWeightedMangoldtTerm Y) ≤
              c ∧
            excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
                (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) ≤
              D)
    (hlim : LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x Y c D < 0) :
    (QNegOne B : ℝ) ≤ x := by
  apply QNegOne_cast_le_of_forall (zero_lt_one.trans hx).le
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) ha.odd.pos.ne'⟩
  have hl := hlocal n hn ha.odd
  have hq := (NumberTheory.complexQuadraticCharacter n ha.odd).conductor_dvd_level
  have hqle :=
    (Nat.le_of_dvd (Nat.mul_pos (by norm_num only : 0 < 4) ha.odd.pos) hq).trans
      (Nat.mul_le_mul_left 4 ha.le)
  have hm :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c := c) (D := D)
      (Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n ha.odd).conductor_ne_zero) hqle
      hx.le hY
  exact
    primeNegOneWitness_cast_le_of_excluded_endpoint ha.odd ha.not_isSquare hGRH hx hY hYx hl.1 hl.2
      (hm.trans_lt hlim)
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

open AnalyticNumberTheory.Arithmetic in
/-- Under the same uniform local bounds and endpoint negativity at 4*B,
QNeOne(B)<=x follows from QNeOne(B)<=QNegOne(B). This transfers the negative
witness result while preserving its explicit local-cost hypotheses. -/
theorem QNeOne_cast_le_of_excluded_endpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c D : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlocal :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
                (Finset.Ioc 0 ⌊Y⌋₊) (reciprocalWeightedMangoldtTerm Y) ≤
              c ∧
            excludedCharacterDefect (NumberTheory.primitiveQuadraticCharacter n hn) (4 * n)
                (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) ≤
              D)
    (hlim : LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x Y c D < 0) :
    (QNeOne B : ℝ) ≤ x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_cast_le_of_excluded_endpoint hGRH hx hY hYx hlocal hlim)

end PseudoPrime.PseudoSquare
