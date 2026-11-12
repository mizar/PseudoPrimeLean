/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.Analysis.FloorIntervalBounds

/-! # Half-open finite interval certificates for Lee–Nosal bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For a floor-invariant monotone function, endpoint and envelope bounds imply the
Lee–Nosal error inequality on the half-open real interval `[a, b)`. Only the prefix
through `b - 1` is needed for the upper endpoint. -/
theorem lee_nosal_halfopen_cell {f : ℝ → ℝ} (hf : Monotone f) (hfloor : ∀ t : ℝ, f t = f ⌊t⌋₊)
    {a b : ℕ} {c x : ℝ} (ha : Real.exp 1 ≤ a) (hax : (a : ℝ) ≤ x) (hxb : x < b)
    (hl : (b : ℝ) - c ≤ f a) (hu : f (b - 1 : ℕ) ≤ (a : ℝ) + c)
    (hc : c ≤ Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi))) :
    |f x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have hbounds := Analysis.floor_monotone_bounds hf hfloor hax hxb
  have he : |f x - x| ≤ c := by
    apply abs_le.mpr
    constructor <;> linarith only [hax, hxb, hl, hu, hbounds.1, hbounds.2]
  exact he.trans (hc.trans (lee_nosal_envelope_mono ha hax))

/-- Endpoint bounds for `psi a` and `psi (b - 1)`, together with an envelope lower
bound at `a ≥ exp 1`, certify the Lee–Nosal psi inequality on `[a, b)`. -/
theorem psi_lee_nosal_halfopen {a b : ℕ} {c x : ℝ} (ha : Real.exp 1 ≤ a) (hax : (a : ℝ) ≤ x)
    (hxb : x < b) (hl : (b : ℝ) - c ≤ Chebyshev.psi a)
    (hu : Chebyshev.psi (b - 1 : ℕ) ≤ (a : ℝ) + c)
    (hc : c ≤ Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi))) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_halfopen_cell Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor ha hax hxb hl hu hc

/-- Endpoint bounds for `theta a` and `theta (b - 1)`, together with an envelope lower
bound at `a ≥ exp 1`, certify the Lee–Nosal theta inequality on `[a, b)`. -/
theorem theta_lee_nosal_halfopen {a b : ℕ} {c x : ℝ} (ha : Real.exp 1 ≤ a) (hax : (a : ℝ) ≤ x)
    (hxb : x < b) (hl : (b : ℝ) - c ≤ Chebyshev.theta a)
    (hu : Chebyshev.theta (b - 1 : ℕ) ≤ (a : ℝ) + c)
    (hc : c ≤ Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi))) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_halfopen_cell Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor ha hax hxb hl hu
      hc

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
