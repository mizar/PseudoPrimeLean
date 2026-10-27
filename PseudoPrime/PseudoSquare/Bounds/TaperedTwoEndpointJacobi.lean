/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TaperedTwoEndpointWitness
public import PseudoPrime.LLS.OddEndpointCostMonotonicity
public import PseudoPrime.NumberTheory.JacobiWitness.PrimitiveTransfer
public import PseudoPrime.PseudoSquare.QNeOneHalfShiftBounds

/-! # Jacobi non-one witnesses with retained finite reciprocal taper costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For odd nonsquare n under GRH and 64<=Y<=x, negativity of the canonical
primitive endpoint with tapered reciprocal cost gives an odd non-one Jacobi
prime through x. Transfer the constructed primitive-character witness; zero
Jacobi values remain allowed. This retains the value at two and its finite cost. -/
theorem exists_prime_ne_one_of_tapered_two_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim :
      let χ := NumberTheory.complexQuadraticCharacter n hn
      LLS.PaperStatements.oddEndpointTwoCostLimit χ.conductor x Y
          (LLS.PaperStatements.taperedTwoReciprocalCost Y (χ.primitiveCharacter 2))
          (LLS.PaperStatements.quadraticTwoLogCost x (χ.primitiveCharacter 2)) <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p ≠ 1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let χ := NumberTheory.complexQuadraticCharacter n hn
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hne : χ.primitiveCharacter ≠ 1 :=
    NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.level_one' χ.primitiveCharacter he)⟩
  have hquad : χ.primitiveCharacter.IsQuadratic :=
    NumberTheory.isQuadratic_primitiveCharacter χ
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn)
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    LLS.PaperStatements.exists_odd_prime_inducing_ne_one_of_tapered_limit χ hq hne hquad hGRH hx hY
      hYx (le_refl _) hlim
  exact
    ⟨p, hp, ho, hpx, NumberTheory.jacobi_ne_one_of_primitiveQuadraticCharacter_ne_one hn hp ho hv⟩

/-- Under the same analytic and arithmetic assumptions, the least odd-prime
non-one witness is at most x. Apply leastness to the actual tapered-endpoint
witness. The nonempty-set parameter supplies the established witness definition. -/
theorem primeNeOneWitness_le_of_tapered_two_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim :
      let χ := NumberTheory.complexQuadraticCharacter n hn
      LLS.PaperStatements.oddEndpointTwoCostLimit χ.conductor x Y
          (LLS.PaperStatements.taperedTwoReciprocalCost Y (χ.primitiveCharacter 2))
          (LLS.PaperStatements.quadraticTwoLogCost x (χ.primitiveCharacter 2)) <
        0)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_prime_ne_one_of_tapered_two_endpoint hn hns hGRH hx hY hYx hlim
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- Under GRH and 64<=Y<=x, a common tapered endpoint condition for every
admissible n<=B bounds the entire finite maximum QNeOne(B) by x. Apply the
pointwise least-witness bound without enumerating the admissible inputs. -/
theorem QNeOne_le_of_tapered_two_endpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim :
      ∀ n ∈ NumberTheory.admissibleFinset B,
        ∀ hn : Odd n,
          let χ := NumberTheory.complexQuadraticCharacter n hn
          LLS.PaperStatements.oddEndpointTwoCostLimit χ.conductor x Y
              (LLS.PaperStatements.taperedTwoReciprocalCost Y (χ.primitiveCharacter 2))
              (LLS.PaperStatements.quadraticTwoLogCost x (χ.primitiveCharacter 2)) <
            0) :
    (QNeOne B : ℝ) ≤ x := by
  apply QNeOne_cast_le_of_forall (zero_lt_one.trans hx).le
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNeOneWitness_le_of_tapered_two_endpoint ha.odd ha.not_isSquare hGRH hx hY hYx
      (hlim n hn ha.odd)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

/-- For odd nonsquare n under GRH and 64<=Y<=x, the explicit reciprocal
envelope (4/3)log 2-log 2/Y and the refined logarithmic envelope at level 4n
give an odd non-one prime if the endpoint limit is negative. Bound the finite
cost uniformly, then use conductor monotonicity and the exact tapered consumer. -/
theorem exists_prime_ne_one_of_uniform_tapered_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x Y
          ((4 / 3 : ℝ) * Real.log 2 - Real.log 2 / Y)
          ((Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p ≠ 1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let χ := NumberTheory.complexQuadraticCharacter n hn
  have hqle := Nat.le_of_dvd (NeZero.pos (4 * n)) χ.conductor_dvd_level
  have hy2 : 2 ≤ Y := by linarith only [hY]
  have hx4 : 4 ≤ x := le_trans (by linarith only [hY] : 4 ≤ Y) hYx
  have hmC :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_costs χ.conductor (Y := Y) hx.le
      (LLS.PaperStatements.taperedTwoReciprocalCost_le_uniform hy2 (χ.primitiveCharacter 2))
      (LLS.PaperStatements.quadraticTwoLogCost_le_envelope hx4 (χ.primitiveCharacter 2))
  have hmL :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c :=
      (4 / 3 : ℝ) * Real.log 2 - Real.log 2 / Y) (D :=
      (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2))
      (Nat.pos_of_ne_zero χ.conductor_ne_zero) hqle hx.le hY
  exact
    exists_prime_ne_one_of_tapered_two_endpoint hn hns hGRH hx hY hYx
      ((hmC.trans hmL).trans_lt hlim)

/-- Under the uniform tapered endpoint condition, the least odd-prime non-one
Jacobi witness is at most x. Apply leastness to the actual constructed prime.
This exposes the explicit finite-cutoff improvement to pointwise bounds. -/
theorem primeNeOneWitness_le_of_uniform_tapered_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * n) x Y
          ((4 / 3 : ℝ) * Real.log 2 - Real.log 2 / Y)
          ((Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) <
        0)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ x := by
  obtain ⟨p, hp, ho, hpx, hv⟩ :=
    exists_prime_ne_one_of_uniform_tapered_endpoint hn hns hGRH hx hY hYx hlim
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpx

/-- Under GRH and 64<=Y<=x, the uniform tapered endpoint condition at 4B
bounds QNeOne(B) by x, including small inputs n<=B. Use level monotonicity
and the pointwise least-witness consumer without a finite enumeration. -/
theorem QNeOne_le_of_uniform_tapered_endpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hlim :
      LLS.PaperStatements.oddEndpointTwoCostLimit (4 * B) x Y
          ((4 / 3 : ℝ) * Real.log 2 - Real.log 2 / Y)
          ((Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) <
        0) :
    (QNeOne B : ℝ) ≤ x := by
  apply QNeOne_cast_le_of_forall (zero_lt_one.trans hx).le
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hq0 : 0 < 4 * n := Nat.mul_pos (by norm_num only) ha.odd.pos
  have hm :=
    LLS.PaperStatements.oddEndpointTwoCostLimit_mono_level (c :=
      (4 / 3 : ℝ) * Real.log 2 - Real.log 2 / Y) (D :=
      (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) hq0
      (Nat.mul_le_mul_left 4 ha.le) hx.le hY
  exact
    primeNeOneWitness_le_of_uniform_tapered_endpoint ha.odd ha.not_isSquare hGRH hx hY hYx
      (hm.trans_lt hlim)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

end PseudoPrime.PseudoSquare
