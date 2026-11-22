/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin3500To1000000
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.FiniteBounds

/-! # High segment through one million -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The complete finite high segment with its exact exit state. -/
theorem high_million : HighSegment := by exact joined3500To1000000

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
