/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableCumulative
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourSeries

/-! # History-safe combination of reduced-contour quadratic bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Add an entrance-guarded quadratic candidate to a common-scale history bound.
The maximum retains the bound at the entrance for all preceding inputs. -/
noncomputable def reducedHistoryStep (B : ℝ → ℝ) (T C L : ℝ) : ℝ :=
  min (B L) (max (B T) (C * L ^ 2))

/-- The history step stays nonnegative when the prior bound and coefficient are nonnegative. -/
theorem reducedStep_nonneg {B : ℝ → ℝ} (hB : ∀ L, 0 ≤ B L) {T C : ℝ} (hC : 0 ≤ C) :
    ∀ L, 0 ≤ reducedHistoryStep B T C L := by
  intro L
  exact le_min (hB L) ((mul_nonneg hC (sq_nonneg L)).trans (le_max_right _ _))

/-- Once the quadratic reaches the preceding entrance history, it bounds the combined
history at every later nonnegative scale. The result applies to every fixed coefficient. -/
theorem reducedStep_absorbed {B : ℝ → ℝ} {T C U L : ℝ} (hC : 0 ≤ C) (hU : 0 ≤ U) (hL : U ≤ L)
    (habs : B T ≤ C * U ^ 2) : reducedHistoryStep B T C L ≤ C * L ^ 2 := by
  have hs := pow_le_pow_left₀ hU hL 2
  have hh := habs.trans (mul_le_mul_of_nonneg_left hs hC)
  exact (min_le_right _ _).trans (max_le hh le_rfl)

/-- Under GRH, an actual witness above the entrance extends any common-scale least-witness
bound. The earlier bound covers inputs below the entrance. -/
theorem reducedStep_bound {B : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprev :
      ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L → (compositeLeastPrime n : ℝ) ≤ B L)
    (hwit :
      ∀ {n : ℕ},
        1 < n →
          Odd n →
          ¬n.Prime →
          T ≤ Real.log n →
          ∃ p : ℕ,
            p.Prime ∧
              (p : ℝ) ≤ C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n))
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ reducedHistoryStep B T C L := by
  refine le_min (hprev hn ho hc L hlog) ?_
  by_cases hhigh : T ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := hwit hn ho hc hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have hs := pow_le_pow_left₀ (hT.trans hhigh) hlog 2
    exact
      ((Nat.cast_le.mpr hm).trans hb).trans
        ((mul_le_mul_of_nonneg_left hs hC).trans (le_max_right _ _))
  · exact (hprev hn ho hc T (le_of_not_ge hhigh)).trans (le_max_left _ _)

end PseudoPrime.PrimeTestBounds.MillerRabin
