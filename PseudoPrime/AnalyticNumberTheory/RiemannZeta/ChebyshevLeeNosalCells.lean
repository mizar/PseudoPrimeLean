/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone

/-! # Finite interval certificates for Lee–Nosal error bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For a monotone function `f`, endpoint bounds `b - c ≤ f a` and `f b ≤ a + c`,
and a lower bound `c` for the Lee–Nosal envelope at `a ≥ exp 1`, imply the
Lee–Nosal error bound on the closed interval `[a, b]`. -/
theorem lee_nosal_cell {f : ℝ → ℝ} (hf : Monotone f) {a b c x : ℝ} (ha : Real.exp 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hl : b - c ≤ f a) (hu : f b ≤ a + c)
    (hc : c ≤ Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi))) :
    |f x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have he : |f x - x| ≤ c := by
    apply abs_le.mpr
    have h1 := hf hax
    have h2 := hf hxb
    constructor <;> linarith only [hax, hxb, hl, hu, h1, h2]
  exact he.trans (hc.trans (lee_nosal_envelope_mono ha hax))

/-- A checked pair of psi endpoint bounds and an envelope lower bound at `a ≥ exp 1`
imply the Lee–Nosal psi error inequality on `[a, b]`. -/
theorem psi_lee_nosal_cell {a b c x : ℝ} (ha : Real.exp 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hl : b - c ≤ Chebyshev.psi a) (hu : Chebyshev.psi b ≤ a + c)
    (hc : c ≤ Real.sqrt a * (Real.log a * (Real.log a - Real.log (Real.log a)) / (8 * Real.pi))) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact lee_nosal_cell Chebyshev.psi_mono ha hax hxb hl hu hc

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
