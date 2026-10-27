/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaMixedIntervalSeparation

/-! # Two compact separation checks covering the remaining logarithmic bridge -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Claim: all logarithm, error-envelope and endpoint-gap checks hold on [310,350].
Proof: exact kernel arithmetic. Role: supply the generic uniform separation soundness theorem. -/
theorem separation_bridge_310_350_check :
    gammaProfileSeparationCheck 310 350 11 12 (31 / 10) (2 / 5) 7 16 17 = true := by decide +kernel

/-- Claim: all logarithm, error-envelope and endpoint-gap checks hold on [350,550].
Proof: exact kernel arithmetic. Role: supply the generic uniform separation soundness theorem. -/
theorem separation_bridge_350_550_check :
    gammaProfileSeparationCheck 350 550 12 13 (37 / 10) (9 / 20) 8 17 19 = true := by decide +kernel

end PseudoPrime.LLS
