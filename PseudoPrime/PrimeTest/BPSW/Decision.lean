/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Decision
import PseudoPrime.PrimeTest.BPSW.Top

/-! # Certified one-sided BPSW decisions -/

namespace PseudoPrime.PrimeTest

/-- Apply the full prechecked test specification; rejection proves non-primality.
Acceptance remains unknown, including at two; use SmallInput for an exact small decision. -/
def BPSW.decide (n : ℕ) : Decision n :=
  decideByTest bailliePSW bailliePSW_spec_unconditional n

/-- Apply the full prechecked test specification; rejection proves non-primality.
Acceptance remains unknown, including at two; use SmallInput for an exact small decision. -/
def BPSW.decideStrengthened (n : ℕ) : Decision n :=
  decideByTest strengthenedBPSW strengthenedBPSW_spec_unconditional n

end PseudoPrime.PrimeTest
