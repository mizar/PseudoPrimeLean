/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.WitnessTransfer
public import PseudoPrime.PseudoSquare.Bounds.GammaJointEntranceBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaMixedLog290Bounds
public import PseudoPrime.PseudoSquare.Bounds.GammaWitnessBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaPrincipalEulerNonOneBounds
public import PseudoPrime.PseudoSquare.Bounds.SharpOddEndpointDoubleLogBounds

/-! # Improved analytic upper bounds for classical and Wheel30 Selfridge stops -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Under GRH for odd nonsquare n with log n>=255, both classical and Wheel30
pure negative discriminant magnitudes are at most (9999/10000)log(n)^2.
Apply the negative-prime entrance bound and absorb the exceptional candidate 27.
The same logarithmic entrance condition is retained. -/
theorem selfridgeNegOneMagnitudes_le_joint_entrance {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 255 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (9999 / 10000 : ℝ) * (Real.log n) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (9999 / 10000 : ℝ) * (Real.log n) ^ 2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb :=
    PseudoSquare.primeNegOneWitness_cast_le_joint_entrance_endpoint hn hns hGRH hL (le_refl _) hw
  exact
    selfridgeNegOneMagnitudes_le_of_prime_witness_bound hn hns hw
      (by nlinarith only [hL, sq_nonneg (Real.log n - 255)]) hb

/-- Under GRH for odd nonsquare n with log n>=290, the classical and Wheel30
pure negative discriminant magnitudes are at most (99/100)log(n)^2.
Transfer the mixed negative-prime bound while retaining its entrance condition. -/
theorem selfridgeNegOneMagnitudes_le_mixed_log_290 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 290 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (99 / 100 : ℝ) * (Real.log n) ^ 2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb :=
    PseudoSquare.primeNegOneWitness_cast_le_mixed_log_290_endpoint hn hns hGRH hL (le_refl _) hw
  exact
    selfridgeNegOneMagnitudes_le_of_prime_witness_bound hn hns hw
      (by nlinarith only [hL, sq_nonneg (Real.log n - 290)]) hb

/-- Under GRH for odd nonsquare n with log n>=46000, both classical and
Wheel30 pure negative discriminant magnitudes are at most (4/5)log(n)^2.
The logarithmic threshold also implies the required ambient level 4n>=20000.
Minimize the proved Gamma witness and absorb 27 through the generic transfer. -/
theorem selfridgeNegOneMagnitudes_le_four_fifths {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 46000 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hqR : (20000 : ℝ) ≤ 4 * n := by nlinarith only [hL, Real.log_le_self (Nat.cast_nonneg n)]
  have hq : 20000 ≤ 4 * n := by exact_mod_cast hqR
  obtain ⟨p, hm, hb⟩ :=
    PseudoSquare.exists_primeNegOneWitness_le_gamma_of_large_log hn hns hq hL hGRH
  have hb' := (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hm)).trans hb
  exact
    selfridgeNegOneMagnitudes_le_of_prime_witness_bound hn hns hw
      (by nlinarith only [hL, sq_nonneg (Real.log n - 46000)]) hb'

/-- Under GRH for odd nonsquare n with log n>=22221, the classical and
Wheel30 factor-detecting magnitudes are at most (4/5)log(n)^2. Transfer the
non-one witness estimate with its earlier entrance and absorb 15.
This does not assert the same entrance for pure negative stopping. -/
theorem selfridgeNeOneMagnitudes_le_four_fifths {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 22221 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (4 / 5 : ℝ) * (Real.log n) ^ 2 := by
  let hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  have hb :=
    PseudoSquare.primeNeOneWitness_cast_le_gamma_endpoint_principal_euler_even hGRH hn hns hL
      (le_refl _) hw
  exact
    selfridgeNeOneMagnitudes_le_of_prime_witness_bound hn hns hw
      (by nlinarith only [hL, sq_nonneg (Real.log n - 22221)]) hb

/-- Under GRH for odd nonsquare n with log n>=96, both factor-detecting
discriminant magnitudes are bounded by (log n-2log log n+149/20)^2.
The certified positive root is at least 94, so it absorbs the exceptional
candidate 15. Transfer the non-one prime bound for both candidate scans. -/
theorem selfridgeNeOneMagnitudes_le_sharp_double_log {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 96 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (Real.log n - 2 * Real.log (Real.log n) + 149 / 20) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (Real.log n - 2 * Real.log (Real.log n) + 149 / 20) ^ 2 := by
  let hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  have hb := PseudoSquare.primeNeOneWitness_cast_le_sharpDoubleLog hn hns hGRH hL hw
  have hr := (LLS.PaperStatements.sharpOddEndpointDoubleLogRoot_data hL).1
  dsimp only [LLS.PaperStatements.sharpOddEndpointDoubleLogRoot] at hr
  exact
    selfridgeNeOneMagnitudes_le_of_prime_witness_bound hn hns hw
      (by nlinarith only [hr, sq_nonneg (Real.log n - 2 * Real.log (Real.log n) + 149 / 20 - 94)])
      hb

end PseudoPrime.PrimeTestBounds.Selfridge
