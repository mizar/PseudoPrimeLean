/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.Analysis.FloorIntervalBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalDerivative

/-! # Cross-endpoint certificates for Lee–Nosal error bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For a monotone floor-invariant function, certified values at `a` and `b - 1`,
certified envelope lower bounds at `a` and `b`, and the two cross inequalities imply
the Lee–Nosal error inequality throughout `[a, b)` when `a ≥ exp 1`. -/
theorem lee_nosal_cross_cell {f : ℝ → ℝ} (hf : Monotone f) (hfloor : ∀ t : ℝ, f t = f ⌊t⌋₊)
    {a b : ℕ} {L U ca cb x : ℝ} (ha : Real.exp 1 ≤ a) (hax : (a : ℝ) ≤ x) (hxb : x < b)
    (hl : L ≤ f a) (hu : f (b - 1 : ℕ) ≤ U)
    (hca : ca ≤ Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi)))
    (hcb : cb ≤ Real.sqrt b * (Real.log b * (Real.log b - Real.log (Real.log b)) / (8 * Real.pi)))
    (hcrossl : (b : ℝ) ≤ L + cb) (hcrossu : U ≤ (a : ℝ) + ca) :
    |f x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply Analysis.halfopen_error_of_endpoints hf hfloor hax hxb _ _ hl hu hca hcb hcrossl hcrossu
  · apply lee_nosal_sub_mono.mono
    intro t ht
    exact ha.trans ht.1
  · apply lee_nosal_add_mono.mono
    intro t ht
    exact ha.trans ht.1

/-- Certified psi endpoint bounds and Lee–Nosal envelope lower bounds satisfying
the two cross inequalities prove the psi error inequality on `[a, b)`. -/
theorem psi_lee_nosal_cross_cell {a b : ℕ} {L U ca cb x : ℝ} (ha : Real.exp 1 ≤ a)
    (hax : (a : ℝ) ≤ x) (hxb : x < b) (hl : L ≤ Chebyshev.psi a)
    (hu : Chebyshev.psi (b - 1 : ℕ) ≤ U)
    (hca : ca ≤ Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi)))
    (hcb : cb ≤ Real.sqrt b * (Real.log b * (Real.log b - Real.log (Real.log b)) / (8 * Real.pi)))
    (hcrossl : (b : ℝ) ≤ L + cb) (hcrossu : U ≤ (a : ℝ) + ca) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_cross_cell Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor ha hax hxb hl hu hca hcb
      hcrossl hcrossu

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
