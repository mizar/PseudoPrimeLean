/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointExactEvenPolynomial
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaClippedComparison

/-! # The endpoint and clipped Gamma minimum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Pointwise minimum of the `7/4` endpoint radius and clipped-log Gamma bound
on the short overlap where both are available and may exchange order. -/
noncomputable def endpointGammaEnvelope (L : ℝ) : ℝ :=
  min (LLS.PaperStatements.midscaleEndpointRadius (L - 7 / 4) ^ 2) (gammaClippedUpper L)

/-- On `120 ≤ log n ≤ 122`, the least rejecting prime is bounded by the
pointwise minimum of the improved endpoint and clipped-log Gamma candidates. -/
theorem exists_least_prime_witness_le_endpointGammaEnvelope {n : ℕ} (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 120 ≤ Real.log n) (hLhi : Real.log n ≤ 122) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ endpointGammaEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, Real.log_zero] at hLlo
    norm_num only at hLlo
  let : NeZero n := ⟨hn0⟩
  have hn : 1 < n := by
    have hreal : (1 : ℝ) < n := by
      by_contra h
      have hle : (n : ℝ) ≤ 1 := le_of_not_gt h
      have hlog := Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos n)) hle
      rw [Real.log_one] at hlog
      linarith only [hLlo, hlog]
    exact Nat.one_lt_cast.mp hreal
  by_cases hE :
    (LLS.PaperStatements.midscaleEndpointRadius (Real.log n - 7 / 4)) ^ 2 ≤
      gammaClippedUpper (Real.log n)
  · obtain ⟨p, hp, hbound, hreject, hmin⟩ :=
      exists_least_prime_reject_le_7over4_shifted_midscale_radius_sq hn hnOdd hcomp hGRH
        (by linarith only [hLlo] : 144 / 5 ≤ Real.log n)
        (by linarith only [hLhi] : Real.log n ≤ 13517 / 100)
    have hbound' : (p : ℝ) ≤ endpointGammaEnvelope (Real.log n) := by
      rw [endpointGammaEnvelope, min_eq_left hE]
      exact hbound
    exact ⟨p, hp, hreject, hbound', hmin⟩
  · have hGE :
      gammaClippedUpper (Real.log n) ≤
        (LLS.PaperStatements.midscaleEndpointRadius (Real.log n - 7 / 4)) ^ 2 :=
      le_of_not_ge hE
    obtain ⟨p, hp, hbound, hreject, hmin⟩ :=
      exists_least_prime_witness_le_gammaClippedUpper hn hnOdd hcomp hGRH hLlo
    have hbound' : (p : ℝ) ≤ endpointGammaEnvelope (Real.log n) := by
      rw [endpointGammaEnvelope, min_eq_right hGE]
      exact hbound
    exact ⟨p, hp, hreject, hbound', hmin⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
