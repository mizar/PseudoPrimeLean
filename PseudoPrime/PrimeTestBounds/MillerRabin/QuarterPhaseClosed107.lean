/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhase107
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftReflected
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhase107
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Closed phase remainder for section 107 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The closed RH cap for the scaled reflected tail at its actual cutoff X.
The three terms are the main moments, the endpoint error, and the slope moments. -/
@[expose]
noncomputable def phaseReflectedCap107 (X : ℝ) : ℝ :=
  let z := Real.log X - 1 / 5
  Real.exp (-(51 / 50) * Real.log X) *
    ((∑ k ∈ Finset.range 6,
        (Nat.choose 5 k : ℝ) * z ^ (5 - k) * eulerMomentValue570 (13 / 25) k X) +
      Real.sqrt X * (Real.log X ^ 2 / 24) * twoShiftReflectedDensity z X +
      ∑ k ∈ Finset.range 6, twoShiftSlopeCoeff z k * eulerMomentValue570 (51 / 50) (k + 2) X)

/-- Under RH the reflected tail is bounded by the closed cap whenever the
logarithmic shift and the cutoff satisfy the hypotheses of the Abel estimate. -/
theorem phase_reflected_cap107 (hRH : RiemannHypothesis) {X : ℝ} (hX : 101 ≤ X)
    (hl : 5 ≤ Real.log X) : twoShiftReflectedTail X ≤ phaseReflectedCap107 X := by
  unfold twoShiftReflectedTail phaseReflectedCap107
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply twoShiftReflected_tail_subtype hRH hX
  · linarith only [hl]
  · linarith only [hl]

/-- The section 107 phase remainder with a closed expression for the
cost of the reflected tail, suitable for real-variable estimates. -/
@[expose]
noncomputable def phaseClosed107 (r : ℝ) : ℝ :=
  let u : ℝ := 11 / 25
  let v : ℝ := 91 / 200
  let x := r ^ 2
  let l := 2 * Real.log r
  phasePole107 - 0.000002191 -
        4 *
          (weightedEulerMain x + Real.sqrt x * (Real.log x ^ 2 / 24) * weightedEulerDensity x +
            weightedEulerError x) +
      ((51 / 50 : ℝ) ^ 5 / 30) * Real.exp (-(13 / 25) * l) *
        (u * l ^ 5 - v * Real.exp ((51 / 50) * (1 / 5)) * (l - 1 / 5) ^ 5) +
      (3 * (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6) * (v * Real.exp (1 / 10) - u) / r -
    4 * (v - u * Real.exp (-(51 / 50) * (1 / 5))) *
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5))) *
      phaseReflectedCap107 x

/-- The closed comparison remainder is a lower bound for the remainder
with the actual reflected Euler tail. -/
theorem phase_closed_le107 (hRH : RiemannHypothesis) {r : ℝ} (hX : 101 ≤ r ^ 2)
    (hl : 5 ≤ Real.log (r ^ 2)) : phaseClosed107 r ≤ phaseRemainder107 r := by
  have he := Real.exp_le_one_iff.mpr (by norm_num only : -(51 / 50 : ℝ) * (1 / 5) ≤ 0)
  have hn : 0 ≤ (91 / 200 : ℝ) - (11 / 25) * Real.exp (-(51 / 50) * (1 / 5)) := by
    linarith only [he]
  have h :=
    mul_le_mul_of_nonneg_left (phase_reflected_cap107 hRH hX hl)
      (show
        0 ≤
          4 * ((91 / 200 : ℝ) - (11 / 25) * Real.exp (-(51 / 50) * (1 / 5))) *
            ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)))
        by positivity)
  dsimp only [phaseClosed107, phaseRemainder107]
  linarith only [h]

/-- Under GRH, prime-prefix passage gives a phase lower bound with the
closed section 107 remainder at every radius at least 300. -/
theorem closed_passing_phase_107 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 300 ≤ R)
    (hL : Real.log n = 2 * R) (hprod : n = p * q * r)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    0.0011365 * R + phaseClosed107 R ≤
      twoShiftZeroPhase a (R ^ 2) + twoShiftZeroPhase b (R ^ 2) + twoShiftZeroPhase c (R ^ 2) := by
  intro a b c
  have hx : 101 ≤ R ^ 2 :=
    (by norm_num only : (101 : ℝ) ≤ 300 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hR 2)
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 20) (lo := 5) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlo
  have hlog : 5 ≤ Real.log (R ^ 2) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hlo.trans (Real.log_le_log (by norm_num only) hR)]
  exact
    (add_le_add (le_refl (0.0011365 * R)) (phase_closed_le107 hG.riemann hx hlog)).trans
      (weighted_passing_phase_107 hsq hn ho hp hq hr hpq hpr hqr hpk hqk hrk hvq hvr hG hR hL hprod
        hpass)

end PseudoPrime.PrimeTestBounds.MillerRabin
