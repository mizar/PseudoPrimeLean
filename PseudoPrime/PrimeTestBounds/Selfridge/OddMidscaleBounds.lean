/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.WitnessTransfer
public import PseudoPrime.PrimeTestBounds.Selfridge.TrialCount
public import PseudoPrime.PseudoSquare.Bounds.OddMidscaleEndpointBounds

/-! # Affine intermediate bounds for Selfridge stops and trial counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Any real bound X>=15 for QNeOne(B) bounds both factor-detecting stopping
maxima on all positive odd nonsquares through B. Cast the unconditional
max(15,QNeOne) comparison and use equality of the classical and Wheel30 maxima.
This interface accepts later analytic estimates without an entrance threshold. -/
theorem selfridgeNeOneMaxima_le_of_QNeOne_bound {B : ℕ} {X : ℝ} (h15 : 15 ≤ X)
    (hb : (PseudoSquare.QNeOne B : ℝ) ≤ X) :
    (classicalNeOneMaximum B : ℝ) ≤ X ∧ (wheel30NeOneMaximum B : ℝ) ≤ X := by
  have hc : (classicalNeOneMaximum B : ℝ) ≤ max 15 (PseudoSquare.QNeOne B : ℝ) := by
    exact_mod_cast classicalNeOneMaximum_le_max_fifteen_QNeOne B
  have hb' := hc.trans (max_le h15 hb)
  rw [wheel30NeOneMaximum_eq_classicalNeOneMaximum]
  exact ⟨hb', hb'⟩

/-- For every natural i>=5, the real classical trial count is at most
(i-3)/2. Cast natural division and subtract five exactly. No oddness or
candidate assumption is needed. This sharpens the earlier i/2+1 bound. -/
theorem classicalTrialCountThrough_real_le_sub_three {i : ℕ} (hi : 5 ≤ i) :
    (PrimeTest.classicalTrialCountThrough i : ℝ) ≤ ((i : ℝ) - 3) / 2 := by
  have hd : (((i - 5) / 2 : ℕ) : ℝ) ≤ ((i - 5 : ℕ) : ℝ) / 2 := Nat.cast_div_le
  rw [Nat.cast_sub hi, Nat.cast_ofNat] at hd
  dsimp only [PrimeTest.classicalTrialCountThrough]
  rw [Nat.cast_add, Nat.cast_one]
  linarith only [hd]

/-- A real value bound X>=5 yields the sharp trial bound (X-3)/2 for every
natural stopping value i<=X. Use the sharper count estimate when i>=5;
below five the totalized trial count is one. This also covers empty maxima. -/
theorem classicalTrialCountThrough_real_le_of_value_bound {i : ℕ} {X : ℝ} (hX : 5 ≤ X)
    (hi : (i : ℝ) ≤ X) : (PrimeTest.classicalTrialCountThrough i : ℝ) ≤ (X - 3) / 2 := by
  by_cases h5 : 5 ≤ i
  · have hc := classicalTrialCountThrough_real_le_sub_three h5
    linarith only [hc, hi]
  · have hn : i ≤ 5 := (Nat.lt_of_not_ge h5).le
    rw [PrimeTest.classicalTrialCountThrough, Nat.sub_eq_zero_of_le hn]
    norm_num only
    linarith only [hX]

/-- Under GRH on the affine odd-prime interval, both factor-detecting
stopping maxima through B are at most the squared affine radius.
Apply QNeOne's common ambient bound and absorb the constant fifteen. -/
theorem selfridgeNeOneMaxima_le_oddMidscale {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 3259 / 25 ≤ Real.log B)
    (hhi : Real.log B ≤ 16277 / 100) :
    (classicalNeOneMaximum B : ℝ) ≤
        (LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log B)) ^ 2 ∧
      (wheel30NeOneMaximum B : ℝ) ≤
        (LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log B)) ^ 2 := by
  have hr := (LLS.PaperStatements.oddMidscaleEndpointRadius_data hlo hhi).1
  have hb := PseudoSquare.QNeOne_le_oddMidscale hGRH hlo hhi
  exact selfridgeNeOneMaxima_le_of_QNeOne_bound (by nlinarith only [hr]) hb

/-- Under GRH for an odd nonsquare input in the affine interval, the
classical and Wheel30 factor-detecting discriminant magnitudes obey the new
odd-prime radius bound. Transfer leastness and absorb the exceptional fifteen.
This does not bound pure negative stopping, which excludes factor detection. -/
theorem selfridgeNeOneMagnitudes_le_oddMidscale {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 3259 / 25 ≤ Real.log n)
    (hhi : Real.log n ≤ 16277 / 100) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log n)) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log n)) ^ 2 := by
  let hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  have hb := PseudoSquare.primeNeOneWitness_cast_le_oddMidscale hn hns hGRH hlo hhi hw
  have hr := (LLS.PaperStatements.oddMidscaleEndpointRadius_data hlo hhi).1
  exact selfridgeNeOneMagnitudes_le_of_prime_witness_bound hn hns hw (by nlinarith only [hr]) hb

/-- Under GRH in the affine interval, the classical factor-detecting trial
maximum through B is at most (r(log B)^2-3)/2. Feed the common stopping-value
bound to the sharp generic trial conversion. This counts Jacobi trials only. -/
theorem classicalNeOneTrialMaximum_le_oddMidscale {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 3259 / 25 ≤ Real.log B)
    (hhi : Real.log B ≤ 16277 / 100) :
    (classicalNeOneTrialMaximum B : ℝ) ≤
      ((LLS.PaperStatements.oddMidscaleEndpointRadius (Real.log B)) ^ 2 - 3) / 2 := by
  have hr := (LLS.PaperStatements.oddMidscaleEndpointRadius_data hlo hhi).1
  have hb := (selfridgeNeOneMaxima_le_oddMidscale hGRH hlo hhi).1
  exact classicalTrialCountThrough_real_le_of_value_bound (by nlinarith only [hr]) hb

end PseudoPrime.PrimeTestBounds.Selfridge
