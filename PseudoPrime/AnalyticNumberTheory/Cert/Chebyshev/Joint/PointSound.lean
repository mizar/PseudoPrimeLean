/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.CellSound

/-! # Real estimates at shared coefficient endpoints -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- At a natural endpoint the two psi tick checks and the direct theta lower check
give both absolute-error estimates for the specified coefficients. -/
theorem point_of_prefix {n l h d e u v U V : ℕ} (st : Prefix n l h d e) (hv : 0 < v) (hV : 0 < V)
    (hc : (u : ℝ) / v ≤ (U : ℝ) / V) (hl : within (scale * n - l) n u v = true)
    (hh : within (h - scale * n) n u v = true) (ht : within (scale * n - (l - d)) n U V = true) :
    |Chebyshev.psi n - n| ≤ ((u : ℝ) / v) * Real.sqrt n ∧
      |Chebyshev.theta n - n| ≤ ((U : ℝ) / V) * Real.sqrt n := by
  have hpl : (l : ℝ) / scale ≤ Chebyshev.psi n :=
    (div_le_iff₀ scale_pos).2 (by simpa only [mul_comm (scale : ℝ)] using st.psiLo)
  have hph : Chebyshev.psi n ≤ (h : ℝ) / scale :=
    (le_div_iff₀ scale_pos).2 (by simpa only [mul_comm (scale : ℝ)] using st.psiHi)
  have hp :=
    abs_le.mpr
      (show
        -((u : ℝ) / v * Real.sqrt n) ≤ Chebyshev.psi n - n ∧
          Chebyshev.psi n - n ≤ (u : ℝ) / v * Real.sqrt n
        from
        ⟨by linarith only [hpl, lower_crossing hv hl], by
          linarith only [hph, upper_crossing hv hh]⟩)
  exact
    ⟨hp,
      theta_abs_of_lower hc hp
        (by linarith only [theta_lower_from_prefix st (le_refl (n : ℝ)), lower_crossing hV ht])⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
