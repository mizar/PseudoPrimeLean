/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64EndpointCertificateSoundness
public import PseudoPrime.LLS.Phase64EndpointPrincipal00
public import PseudoPrime.LLS.Phase64EndpointPrincipal01
public import PseudoPrime.LLS.Phase64EndpointPrincipal02
public import PseudoPrime.LLS.Phase64EndpointPrincipal03
public import PseudoPrime.LLS.Phase64EndpointRamp

/-! # Fully checked finite analytic endpoint caps for the first phase64 cell -/

@[expose] public section

namespace PseudoPrime.LLS.Phase64EndpointCertificates

/-- All sixteen ramp blocks have their kernel-checked natural lower sums.
Enumerate only the finite block index and reuse each independent proof. -/
theorem ramp_blocks : ∀ i : Fin 16, RampBlockValid i.val := by
  intro i
  fin_cases i
  · exact ramp_block00
  · exact ramp_block01
  · exact ramp_block02
  · exact ramp_block03
  · exact ramp_block04
  · exact ramp_block05
  · exact ramp_block06
  · exact ramp_block07
  · exact ramp_block08
  · exact ramp_block09
  · exact ramp_block10
  · exact ramp_block11
  · exact ramp_block12
  · exact ramp_block13
  · exact ramp_block14
  · exact ramp_block15

/-- All thirty-two principal blocks have checked logarithm gates and natural
upper sums. Reuse the independent kernel proofs without re-evaluating their data. -/
theorem principal_blocks : ∀ i : Fin 32, PrincipalBlockValid i.val := by
  intro i
  fin_cases i
  · exact principal_block00
  · exact principal_block01
  · exact principal_block02
  · exact principal_block03
  · exact principal_block04
  · exact principal_block05
  · exact principal_block06
  · exact principal_block07
  · exact principal_block08
  · exact principal_block09
  · exact principal_block10
  · exact principal_block11
  · exact principal_block12
  · exact principal_block13
  · exact principal_block14
  · exact principal_block15
  · exact principal_block16
  · exact principal_block17
  · exact principal_block18
  · exact principal_block19
  · exact principal_block20
  · exact principal_block21
  · exact principal_block22
  · exact principal_block23
  · exact principal_block24
  · exact principal_block25
  · exact principal_block26
  · exact principal_block27
  · exact principal_block28
  · exact principal_block29
  · exact principal_block30
  · exact principal_block31

end PseudoPrime.LLS.Phase64EndpointCertificates
