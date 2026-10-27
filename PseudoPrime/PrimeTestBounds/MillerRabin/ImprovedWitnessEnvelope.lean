/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SmallPointwiseBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPointwise
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFixed67
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSharpEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMRClippedWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularThresholdBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedEnvelopeGlobalOrder
/-! # Guarded improvements of the all-input least MR witness envelope -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- The guarded minimum of the compatible interval envelope and the new pointwise,
endpoint, Gamma, clipped Gaussian and triangular candidates. Each candidate uses only its
proved domain; otherwise it returns the compatible envelope. All inputs are natural numbers. -/
noncomputable def improvedWitnessEnvelope (n : ℕ) : ℝ :=
  let L := Real.log n
  let B := selectedWitnessEnvelope n
  min B (min (if n < 3000 then smallIntervalBound n else B)
    (min (if L ≤ 2877 / 250 then 61 else B)
      (min (if L ≤ 47 / 4 then 67 else B)
        (min (if 45 / 4 ≤ L then LLS.PaperStatements.endpointFourStepCutoff L else B)
          (min (if 100 ≤ L then gammaSharpBound L else B)
            (min (if 63 ≤ L then Analysis.gaussianFloorSelected L else B)
              (if 2000000000000 ≤ L then (282924 / 1000000 : ℝ) * L ^ 2 else B)))))))

/-- For every natural n, the improved envelope is at most the compatible envelope.
The latter is an explicit minimum entry, so no analytic assumptions are needed. -/
theorem improvedWitnessEnvelope_le_old (n : ℕ) :
    improvedWitnessEnvelope n ≤ selectedWitnessEnvelope n := min_le_left _ _

/-- Under GRH, every odd composite n>1 has a least prime rejecting strong MR within
the improved envelope. Fix the compatible least witness and transfer every valid candidate
bound by its minimality. No index, factor count, Korselt or squarefreeness assumption is public. -/
theorem exists_least_improvedWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ improvedWitnessEnvelope n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_selectedWitness hn ho hc hGRH
  have transfer {C : ℝ}
      (h : ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ C ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)) : (p : ℝ) ≤ C := by
    obtain ⟨q, hq, hqb, hqr⟩ := h
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  have hsmall : (p : ℝ) ≤
      (if n < 3000 then smallIntervalBound n else selectedWitnessEnvelope n) := by
    by_cases h : n < 3000
    · rw [ite_eq_left h]
      exact transfer (exists_prime_smallInterval hn ho hc h)
    · rw [ite_eq_right h]
      exact hb
  have h61 : (p : ℝ) ≤
      (if Real.log n ≤ 2877 / 250 then 61 else selectedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 2877 / 250
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpointPointwise61 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h67 : (p : ℝ) ≤
      (if Real.log n ≤ 47 / 4 then 67 else selectedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 47 / 4
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint67 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have hfour : (p : ℝ) ≤
      (if 45 / 4 ≤ Real.log n then LLS.PaperStatements.endpointFourStepCutoff (Real.log n) else
        selectedWitnessEnvelope n) := by
    by_cases h : 45 / 4 ≤ Real.log n
    · rw [ite_eq_left h]
      exact transfer (exists_prime_fourStep hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have hgamma : (p : ℝ) ≤
      (if 100 ≤ Real.log n then gammaSharpBound (Real.log n) else selectedWitnessEnvelope n) := by
    by_cases h : 100 ≤ Real.log n
    · rw [ite_eq_left h]
      exact transfer (exists_prime_gammaSharp hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have hgauss : (p : ℝ) ≤
      (if 63 ≤ Real.log n then Analysis.gaussianFloorSelected (Real.log n) else
        selectedWitnessEnvelope n) := by
    by_cases h : 63 ≤ Real.log n
    · rw [ite_eq_left h]
      rw [← Analysis.gaussianFloor_min_eq_selected h]
      exact transfer (exists_prime_gaussianClippedEnvelope ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have htri : (p : ℝ) ≤
      (if 2000000000000 ≤ Real.log n then (282924 / 1000000 : ℝ) * Real.log n ^ 2 else
        selectedWitnessEnvelope n) := by
    by_cases h : 2000000000000 ≤ Real.log n
    · rw [ite_eq_left h]
      exact transfer (exists_prime_triangularThreshold hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  refine ⟨p, hp, hr, ?_, hm⟩
  exact le_min hb (le_min hsmall (le_min h61 (le_min h67
    (le_min hfour (le_min hgamma (le_min hgauss htri))))))

/-- Under GRH, every odd composite n>1 has a prime rejecting strong MR within
the improved envelope. Project the actual witness from the all-input least-prime theorem. -/
theorem exists_prime_improvedWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ improvedWitnessEnvelope n ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_improvedWitness hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩



/-- On its proved guard, this candidate bounds the improved envelope from above.
Project the corresponding minimum entry. This supports interval comparisons and strict gains. -/
theorem improved_le_small {n : ℕ} (h : n < 3000) :
    improvedWitnessEnvelope n ≤ smallIntervalBound n := by
  have hm : improvedWitnessEnvelope n ≤
      (if n < 3000 then smallIntervalBound n else selectedWitnessEnvelope n) := by
    dsimp only [improvedWitnessEnvelope]
    exact (min_le_right _ _).trans (min_le_left _ _)
  simpa only [ite_eq_left h] using hm

/-- On its proved guard, this candidate bounds the improved envelope from above.
Project the corresponding minimum entry. This supports interval comparisons and strict gains. -/
theorem improved_le_fixed61 {n : ℕ} (h : Real.log n ≤ 2877 / 250) :
    improvedWitnessEnvelope n ≤ 61 := by
  have hm : improvedWitnessEnvelope n ≤
      (if Real.log n ≤ 2877 / 250 then 61 else selectedWitnessEnvelope n) := by
    dsimp only [improvedWitnessEnvelope]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  simpa only [ite_eq_left h] using hm

/-- On its proved guard, this candidate bounds the improved envelope from above.
Project the corresponding minimum entry. This supports interval comparisons and strict gains. -/
theorem improved_le_fixed67 {n : ℕ} (h : Real.log n ≤ 47 / 4) :
    improvedWitnessEnvelope n ≤ 67 := by
  have hm : improvedWitnessEnvelope n ≤
      (if Real.log n ≤ 47 / 4 then 67 else selectedWitnessEnvelope n) := by
    dsimp only [improvedWitnessEnvelope]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  simpa only [ite_eq_left h] using hm

/-- On its proved guard, this candidate bounds the improved envelope from above.
Project the corresponding minimum entry. This supports interval comparisons and strict gains. -/
theorem improved_le_fourStep {n : ℕ} (h : 45 / 4 ≤ Real.log n) :
    improvedWitnessEnvelope n ≤ LLS.PaperStatements.endpointFourStepCutoff (Real.log n) := by
  have hm : improvedWitnessEnvelope n ≤
      (if 45 / 4 ≤ Real.log n then LLS.PaperStatements.endpointFourStepCutoff (Real.log n) else
        selectedWitnessEnvelope n) := by
    dsimp only [improvedWitnessEnvelope]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  simpa only [ite_eq_left h] using hm

/-- On its proved guard, this candidate bounds the improved envelope from above.
Project the corresponding minimum entry. This supports interval comparisons and strict gains. -/
theorem improved_le_sharp {n : ℕ} (h : 100 ≤ Real.log n) :
    improvedWitnessEnvelope n ≤ gammaSharpBound (Real.log n) := by
  have hm : improvedWitnessEnvelope n ≤
      (if 100 ≤ Real.log n then gammaSharpBound (Real.log n) else selectedWitnessEnvelope n) := by
    dsimp only [improvedWitnessEnvelope]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  simpa only [ite_eq_left h] using hm

/-- On its proved guard, this candidate bounds the improved envelope from above.
Project the corresponding minimum entry. This supports interval comparisons and strict gains. -/
theorem improved_le_gaussian {n : ℕ} (h : 63 ≤ Real.log n) :
    improvedWitnessEnvelope n ≤ Analysis.gaussianFloorSelected (Real.log n) := by
  have hm : improvedWitnessEnvelope n ≤
      (if 63 ≤ Real.log n then Analysis.gaussianFloorSelected (Real.log n) else
        selectedWitnessEnvelope n) := by
    dsimp only [improvedWitnessEnvelope]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left
      _ _))))))
  simpa only [ite_eq_left h] using hm

/-- On its proved guard, this candidate bounds the improved envelope from above.
Project the corresponding minimum entry. This supports interval comparisons and strict gains. -/
theorem improved_le_triangular {n : ℕ} (h : 2000000000000 ≤ Real.log n) :
    improvedWitnessEnvelope n ≤ (282924 / 1000000 : ℝ) * Real.log n ^ 2 := by
  have hm : improvedWitnessEnvelope n ≤
      (if 2000000000000 ≤ Real.log n then (282924 / 1000000 : ℝ) * Real.log n ^ 2 else
        selectedWitnessEnvelope n) := by
    dsimp only [improvedWitnessEnvelope]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (le_refl _)))))))
  simpa only [ite_eq_left h] using hm

end PseudoPrime.PrimeTestBounds.MillerRabin
