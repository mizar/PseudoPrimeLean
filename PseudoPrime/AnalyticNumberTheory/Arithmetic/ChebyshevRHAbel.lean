/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevRHError

/-! # Centered Euler tails under the Riemann hypothesis -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Under RH and `a ≥ 625`, the total Mangoldt sum differs from the finite prefix plus
its main integral and exact psi boundary correction by at most the integral of
`t^(3/4) |f'(t)|`. The differentiability, summability and integrability requirements
are explicit, and the weight may be signed. -/
theorem mangoldt_centered_abel_rh_error (hRH : RiemannHypothesis) {a : ℝ} (ha : 625 ≤ a) {f : ℝ → ℝ}
    (hd : ∀ b : ℝ, a ≤ b → ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hi : ∀ b : ℝ, a ≤ b → MeasureTheory.IntegrableOn (deriv f) (Set.Icc a b))
    (hmain : MeasureTheory.IntegrableOn f (Set.Ioi a))
    (hboundary : Filter.Tendsto (fun b : ℝ ↦ (Chebyshev.psi b - b) * f b) Filter.atTop (nhds 0))
    (hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n))
    (hB :
      MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.sqrt t * Real.sqrt (Real.sqrt t) * |deriv f t|)
        (Set.Ioi a)) :
    |(∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
          ((∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) +
              (∫ t in Set.Ioi a, f t) -
            (Chebyshev.psi a - a) * f a)| ≤
      ∫ t in Set.Ioi a, Real.sqrt t * Real.sqrt (Real.sqrt t) * |deriv f t| := by
  apply
    mangoldt_centered_abel_error (B := fun t ↦ Real.sqrt t * Real.sqrt (Real.sqrt t))
      (by linarith only [ha]) hd hi hmain hboundary hs hB
  intro t ht
  exact psi_error_le_three_quarter_sqrt hRH (ha.trans (Set.mem_Ioi.mp ht).le)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
