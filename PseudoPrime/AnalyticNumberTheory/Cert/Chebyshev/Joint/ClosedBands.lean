/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Band3500
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PointSound

/-! # Closed theta coefficient bands -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def stop3100 : Edge :=
  ⟨3100, 3097355316838818, 3097393709094831, 68735438166433, 68735438166554⟩

/-- The stronger theta coefficient remains valid at the right endpoint 3100. -/
theorem thetaClosed3100 {x : ℝ} (hl : 2657 ≤ x) (hr : x ≤ 3100) :
    |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x := by
  rcases hr.lt_or_eq with hx | rfl
  · exact (prefix3100.2 x hl hx).2
  · have hs : Valid stop3100 := prefix3100.1
    have hn : ¬IsPrimePow (3099 + 1 : ℕ) := by decide +kernel
    have hp := prefix_other (n := 3099) hs.2 hn (fun h ↦ hn h.isPrimePow)
    exact
      (point_of_prefix (u := 4) (v := 5) (U := 9) (V := 5) hp (by decide) (by decide)
          (by norm_num only) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

private def stop3500 : Edge :=
  ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩

/-- The stronger theta coefficient remains valid at the right endpoint 3500. -/
theorem thetaClosed3500 {x : ℝ} (hl : 3100 ≤ x) (hr : x ≤ 3500) :
    |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x := by
  rcases hr.lt_or_eq with hx | rfl
  · exact (prefix3500.2 x hl hx).2
  · have hs : Valid stop3500 := prefix3500.1
    have hn : ¬IsPrimePow (3499 + 1 : ℕ) := by decide +kernel
    have hp := prefix_other (n := 3499) hs.2 hn (fun h ↦ hn h.isPrimePow)
    exact
      (point_of_prefix (u := 4) (v := 5) (U := 19) (V := 10) hp (by decide) (by decide)
          (by norm_num only) (by decide +kernel) (by decide +kernel) (by decide +kernel)).2

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
