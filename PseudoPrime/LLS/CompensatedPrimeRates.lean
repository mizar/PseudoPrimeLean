/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EvenRetainedPrimeRates

/-! # Conductor compensation for unequal local exclusion rates -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- For any bridge and real rate a, choosing b=a+the conductor coefficient makes
the complete coupled comparison equal its level-4n rate-a expression. The exact
square-factor gain is zero. This identity concerns comparisons, not cost budgets. -/
theorem conductorSquare_compensated_identity {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) (x a : ℝ) (T : Finset ℕ)
    (e : ℕ → ℝ) :
    oddEndpointTwoCostLimit (4 * bridge.squarefreePart) x x 0 0 +
          conductorSquareUntaperedBudget bridge x a (a + equalEndpointLevelCoefficient x) T e -
        (excludedReciprocalCoefficient x / x) * Real.log 2 =
      oddEndpointTwoCostLimit (4 * n) x x 0 0 +
          quadraticExcludedPrimeCost (NumberTheory.complexQuadraticCharacter n hn).conductor x
            (untaperedExcludedEndpointWeight x) 2 +
          a * Real.log n +
          ∑ p ∈ T, e p -
        (excludedReciprocalCoefficient x / x) * Real.log 2 := by
  have hg := conductorSquare_comparison_gain bridge x a (a + equalEndpointLevelCoefficient x) T e
  have hz : equalEndpointLevelCoefficient x + a - (a + equalEndpointLevelCoefficient x) = 0 := by
    ring
  rw [hz, mul_zero, zero_mul] at hg
  exact (sub_eq_zero.mp hg).symm

/-- Finite prime deficit with ramified rate alpha and unramified rate alpha+kappa.
Keep even-power cancellation and take the nonnegative maximum of both deficits.
The conductor saving pays for the larger unramified rate in the complete comparison. -/
noncomputable def compensatedPrimeExcess (x : ℝ) (P p : ℕ) : ℝ :=
  max 0
    (max (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
      (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
        2 * (explicitUntaperedPrimeRate x P + equalEndpointLevelCoefficient x) * Real.log p))

/-- For arbitrary arguments the compensated deficit is nonnegative by its outer maximum.
This permits enlarging its finite support in the conductor-square budget. -/
theorem compensatedPrimeExcess_nonneg (x : ℝ) (P p : ℕ) : 0 ≤ compensatedPrimeExcess x P p :=
  le_max_left _ _

/-- For a prime and x>1 the compensated deficit is at most the even-retained deficit.
The conductor coefficient and log p are nonnegative, so the second deficit decreases.
This proves domination of the former finite-exception comparison. -/
theorem compensatedPrimeExcess_le {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 1 < x) (P : ℕ) :
    compensatedPrimeExcess x P p ≤ evenRetainedPrimeExcess x P p := by
  have hm :=
    mul_nonneg (equalEndpointLevelCoefficient_pos hx).le
      (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_le))
  dsimp only [compensatedPrimeExcess, evenRetainedPrimeExcess]
  apply max_le_max_left
  apply max_le_max_left
  nlinarith only [hm]

/-- The comparison allowance after conductor compensation: twice the envelope at two,
alpha log n and compensated finite deficits. This is not asserted to bound the
structural cost alone. It bounds the complete comparison after changing level to 4n. -/
noncomputable def compensatedInputCost (x : ℝ) (P n : ℕ) : ℝ :=
  2 * untaperedPrimeEnvelope x 2 + explicitUntaperedPrimeRate x P * Real.log n +
    ∑ p ∈ explicitUntaperedPrimeExceptions P, compensatedPrimeExcess x P p

/-- At x>1 the compensated allowance is no larger than the former retained budget.
Sum the local deficit comparisons over odd primes below P. This compares scalar
witness criteria without discarding the conductor compensation. -/
theorem compensatedInputCost_le {x : ℝ} (hx : 1 < x) (P n : ℕ) :
    compensatedInputCost x P n ≤ evenRetainedInputBudget x P n := by
  have hs :=
    Finset.sum_le_sum (s := explicitUntaperedPrimeExceptions P)
      (fun p hp ↦ compensatedPrimeExcess_le (Finset.mem_filter.mp hp).2.1 hx P)
  dsimp only [compensatedInputCost, evenRetainedInputBudget]
  linarith only [hs]

/-- For positive n<=B and admissible x,P, the compensated allowance is monotone in n.
Only its nonnegative alpha log n term changes. Used for finite-maximum witnesses. -/
theorem compensatedInputCost_mono {n B P : ℕ} (hn : 0 < n) (hnB : n ≤ B) {x : ℝ} (hx : 1 < x)
    (hP : 2 ≤ P) : compensatedInputCost x P n ≤ compensatedInputCost x P B := by
  have hm :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (Nat.cast_pos.mpr hn) (Nat.cast_le.mpr hnB))
      (explicitUntaperedPrimeRate_nonneg hx hP)
  dsimp only [compensatedInputCost]
  linarith only [hm]

open AnalyticNumberTheory.Arithmetic in
/-- At a conductor-dividing odd prime, alpha and the compensated deficit bound the
local cost. The finite branch uses its ramified deficit; the tail is unchanged.
This discharges the ramified hypothesis of the coupled witness theorem. -/
theorem untaperedPrimeCost_le_compensated_ramified {x : ℝ} (hx : 1 < x) {P p : ℕ} (hP : 2 ≤ P)
    (hp : p.Prime) (ho : Odd p) (q : ℕ) (hd : p ∣ q) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤
      explicitUntaperedPrimeRate x P * Real.log p +
        if p ∈ explicitUntaperedPrimeExceptions P then compensatedPrimeExcess x P p else 0 := by
  by_cases hm : p ∈ explicitUntaperedPrimeExceptions P
  · rw [ite_eq_left hm]
    have hc := untaperedPrimeCost_le_envelope_of_dvd hp q hd hx
    have h1 :=
      le_max_left (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
        (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
          2 * (explicitUntaperedPrimeRate x P + equalEndpointLevelCoefficient x) * Real.log p)
    have h2 :=
      le_max_right 0
        (max (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
          (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
            2 * (explicitUntaperedPrimeRate x P + equalEndpointLevelCoefficient x) * Real.log p))
    dsimp only [compensatedPrimeExcess]
    linarith only [hc, h1, h2]
  · have hc := untaperedPrimeCost_le_explicit_ramified hx hP hp ho q hd
    simpa only [ite_eq_right hm] using hc

open AnalyticNumberTheory.Arithmetic in
/-- At a conductor-coprime odd prime, rate 2(alpha+kappa) and the compensated deficit
bound its cost. Keep even-power cancellation inside the exception support and
use kappa>=0 for the tail. This discharges the unramified local hypothesis. -/
theorem untaperedPrimeCost_le_compensated_unramified {x : ℝ} (hx : 1 < x) {P p : ℕ} (hP : 2 ≤ P)
    (hp : p.Prime) (ho : Odd p) (q : ℕ) (hd : ¬p ∣ q) :
    quadraticExcludedPrimeCost q x (untaperedExcludedEndpointWeight x) p ≤
      2 * (explicitUntaperedPrimeRate x P + equalEndpointLevelCoefficient x) * Real.log p +
        if p ∈ explicitUntaperedPrimeExceptions P then compensatedPrimeExcess x P p else 0 := by
  by_cases hm : p ∈ explicitUntaperedPrimeExceptions P
  · rw [ite_eq_left hm]
    have hc := untaperedPrimeCost_add_even_le hp q (hp.coprime_iff_not_dvd.mpr hd) hx
    have h1 :=
      le_max_right (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
        (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
          2 * (explicitUntaperedPrimeRate x P + equalEndpointLevelCoefficient x) * Real.log p)
    have h2 :=
      le_max_right 0
        (max (untaperedPrimeEnvelope x p - explicitUntaperedPrimeRate x P * Real.log p)
          (2 * untaperedPrimeEnvelope x p - 2 * untaperedEvenPrimeCost x p -
            2 * (explicitUntaperedPrimeRate x P + equalEndpointLevelCoefficient x) * Real.log p))
    dsimp only [compensatedPrimeExcess]
    linarith only [hc, h1, h2]
  · have hc := untaperedPrimeCost_le_explicit_twice hx hP hp ho q
    rw [ite_eq_right hm, add_zero] at hc ⊢
    have hk :=
      mul_nonneg (equalEndpointLevelCoefficient_pos hx).le
        (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_le))
    nlinarith only [hc, hk]

/-- At x>1 the complete coupled comparison with compensated rates is bounded by the
explicit level-4n allowance. Apply the exact conductor cancellation and bound
only the remaining two-adic cost. The structural cost alone need not obey this bound. -/
theorem compensatedComparison_le_input {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns) {x : ℝ} (hx : 1 < x) (P : ℕ) :
    oddEndpointTwoCostLimit (4 * bridge.squarefreePart) x x 0 0 +
          conductorSquareUntaperedBudget bridge x (explicitUntaperedPrimeRate x P)
            (explicitUntaperedPrimeRate x P + equalEndpointLevelCoefficient x)
            (explicitUntaperedPrimeExceptions P) (compensatedPrimeExcess x P) -
        (excludedReciprocalCoefficient x / x) * Real.log 2 ≤
      oddEndpointTwoCostLimit (4 * n) x x 0 0 + compensatedInputCost x P n -
        (excludedReciprocalCoefficient x / x) * Real.log 2 := by
  rw [conductorSquare_compensated_identity]
  have h :=
    untaperedPrimeCost_le_twice_envelope Nat.prime_two
      (NumberTheory.complexQuadraticCharacter n hn).conductor hx
  dsimp only [compensatedInputCost]
  linarith only [h]

end PseudoPrime.LLS.PaperStatements
