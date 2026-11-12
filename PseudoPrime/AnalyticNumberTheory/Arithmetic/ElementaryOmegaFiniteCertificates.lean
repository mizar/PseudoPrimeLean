/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaStatement
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ElementaryOmegaFiniteData

/-! # Unconditional elementary omega bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Every odd `n ≥ 750` satisfies the elementary bound on `ω(4n)`.
The anchor certificates settle factor counts below `163`; the independent
calculus tail theorem supplies all larger counts, so no certificate hypothesis remains. -/
theorem elementaryOmegaStatement : ElementaryOmegaStatement :=
  elementaryOmegaStatement_of_finite
    (elementaryOmegaFinite_of_certificates elementaryOmegaFiniteCertificates)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
