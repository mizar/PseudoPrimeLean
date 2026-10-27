/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PrecisePiLogBound
public import PseudoPrime.LLS.SharperTheorem11S2

/-! # Conductor estimates retaining the rational precision of log pi -/

@[expose] public section

namespace PseudoPrime.LLS

/-- At nonzero level q, log(conductor/pi) ≤ log q-2096/1831.
Apply the parameterized conductor lemma to the certified precise lower
bound for log pi. This supplies the sharper conductor input without
claiming a new witness cutoff before its scalar separation is proved. -/
theorem log_conductor_div_pi_le_precisePi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Real.log ((χ.conductor : ℝ) / Real.pi) ≤ Real.log q - 2096 / 1831 := by
  exact log_conductor_div_pi_le_of_lower χ Analysis.log_pi_ge_2096_div_1831

end PseudoPrime.LLS
