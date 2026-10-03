/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Data.Nat.Prime.Basic

/-!
# Caller-supplied prime leaf certification
-/

namespace PseudoPrime.NumberTheory.Factorization

/-- Executable sufficient condition for certifying a prime leaf.
Acceptance implies primality; rejection may mean unknown. The caller supplies both the decision
procedure and its soundness proof, so factorization selects no primality algorithm. -/
structure PrimeLeafPolicy where
  /-- Condition under which a leaf may be retained as prime. -/
  accepts : ℕ → Prop
  /-- Executable decision procedure for the sufficient condition. -/
  decideAccepts : DecidablePred accepts
  /-- Every accepted leaf is prime; completeness is not required. -/
  sound : ∀ n, accepts n → Nat.Prime n

instance (policy : PrimeLeafPolicy) : DecidablePred policy.accepts :=
  policy.decideAccepts

end PseudoPrime.NumberTheory.Factorization
