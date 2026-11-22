/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComputedScalarPhase
public import PseudoPrime.Analysis.IntegerPhaseSteps

/-! # Scalar quotients from checked integer phase walks -/

public section

namespace PseudoPrime.Analysis

/-- A certified phase center, its norm-error radius, and certified input boxes
enclose the scalar quotient. Positivity and order of the ordinate box discharge
all computed-domain guards; no successful-check premise is exposed. -/
theorem scalar_point_contains {G r a b : ℤ} {A V W : IntegerInterval} {g v t : ℝ} (hG : 0 < G)
    (hA : G ≤ A.lower) (hord : A.lower ≤ A.upper) (hg : A.Contains G g) (hv : V.Contains G v)
    (hw : W.Contains G t)
    (hp : ‖Complex.exp ((t : ℂ) * Complex.I) - integerComplexPoint G a b‖ ≤ (r : ℝ) / G) :
    (computedScalarPhase G A V W ⟨a - r, a + r⟩ ⟨b - r, b + r⟩).quotient.Contains G
      ((Real.cos (g * v) + 2 * g * Real.sin (g * v)) / ((1 / 4 : ℝ) + g ^ 2)) := by
  have hphase := integer_point_error_contains hp
  exact (computedScalarPhase_sound hg hv hw hphase (scalarPhaseDomainCheck_true hG hA hord)).2.2

/-- Initial and rotation certificates plus checked integer transitions enclose
the scalar quotient at any step through the finite horizon. A certified argument
box supplies the actual continuous input independently of the nominal center.
This interface is shared by the terms of a finite selected-zero budget. -/
theorem scalar_walk_contains {t h : ℝ} {G c d r e η : ℤ} {A V W : IntegerInterval} (N : ℕ)
    (w : ℕ → ℤ × ℤ) (hG : 0 < G) (hA : G ≤ A.lower) (hord : A.lower ≤ A.upper)
    (h0 : ‖Complex.exp ((t : ℂ) * Complex.I) - integerComplexPoint G (w 0).1 (w 0).2‖ ≤ (r : ℝ) / G)
    (hp : ‖Complex.exp ((h : ℂ) * Complex.I) - integerComplexPoint G c d‖ ≤ (e : ℝ) / G)
    (hc :
      ∀ k, k < N → integerRotationCheck G (w k).1 (w k).2 c d (w (k + 1)).1 (w (k + 1)).2 η = true)
    {n : ℕ} (hn : n ≤ N) {g v : ℝ} (hg : A.Contains G g) (hv : V.Contains G v)
    (hw : W.Contains G (t + (n : ℝ) * h)) :
    (computedScalarPhase G A V W
          ⟨(w n).1 - (r + (n : ℤ) * (2 * e + η)), (w n).1 + (r + (n : ℤ) * (2 * e + η))⟩
          ⟨(w n).2 - (r + (n : ℤ) * (2 * e + η)),
            (w n).2 + (r + (n : ℤ) * (2 * e + η))⟩).quotient.Contains
      G ((Real.cos (g * v) + 2 * g * Real.sin (g * v)) / ((1 / 4 : ℝ) + g ^ 2)) := by
  exact scalar_point_contains hG hA hord hg hv hw (integer_phase_steps_le N w h0 hp hc hn)

end PseudoPrime.Analysis
