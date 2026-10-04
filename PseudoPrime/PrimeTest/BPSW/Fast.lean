/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.BPSW.Prime
import PseudoPrime.PrimeTest.StrongLucas.Fast

/-! # Explicit fast parameterized ordinary BPSW

The definition-side composition remains unchanged. This entry explicitly selects
the reference Strong Lucas PQ procedure and its total shared-state fallback.
-/

namespace PseudoPrime.PrimeTest

/-- Run prechecked base-two MR and explicit fast Strong Lucas with signed parameters.
Parameter selection is separate; the total fallback preserves unsupported Jacobi branches.
This entry avoids recomputing Lucas values independently at each strong-test index. -/
def bailliePSWWithParamsFast (n : ℕ) (D P Q : ℤ) : Bool :=
  strongMillerRabinBase2WithPrecheck n && strongLucasWithParamsFast n D P Q

/-- Explicit fast parameterized BPSW preserves its definition-side composition on all inputs.
The Strong Lucas Boolean equality transports the unchanged MR conjunction. -/
theorem bailliePSWWithParamsFast_eq (n : ℕ) (D P Q : ℤ) :
    bailliePSWWithParamsFast n D P Q = bailliePSWWithParams n D P Q :=
  congrArg (fun strong ↦ strongMillerRabinBase2WithPrecheck n && strong)
    (strongLucasWithParamsFast_eq n D P Q)

/-- Every prime passes fast parameterized BPSW with valid Jacobi-minus-one parameters.
The all-input composition equality transfers the original prime completeness theorem. -/
theorem bailliePSWWithParamsFast_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ)
    (hdisc : D = P * P - 4 * Q) (hjacobi : jacobiSym D n = -1) :
    bailliePSWWithParamsFast n D P Q = true :=
  (bailliePSWWithParamsFast_eq n D P Q).trans (bailliePSWWithParams_of_prime hn D P Q hdisc hjacobi)

end PseudoPrime.PrimeTest
