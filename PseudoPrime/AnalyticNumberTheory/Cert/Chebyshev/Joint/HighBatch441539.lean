/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 441539 to 446539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e441539 : Edge :=
  ⟨441539, 441586288667678169, 441589611114374059, 758160967129436, 758170675943213⟩

private def e446539 : Edge :=
  ⟨446539, 446709666635591964, 446713004250775895, 758160967129436, 758170675943213⟩

private def extra441539 : ℕ → ℕ
  | 441539 => 491
  | 442031 => 467
  | 442499 => 461
  | 442961 => 329
  | 443291 => 299
  | 443591 => 289
  | 443881 => 269
  | 444151 => 291
  | 444443 => 227
  | 444671 => 215
  | 444887 => 203
  | 445091 => 229
  | 445321 => 297
  | 445619 => 311
  | 445931 => 341
  | 446273 => 265
  | _ => 0

private theorem part441539 : Segment Valid highEstimate e441539 e446539 := by
  apply gcd_batch (by decide) (by decide) extra441539 16
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [441539,446539). -/
theorem batch441539 :
    Segment Valid highEstimate
      ⟨441539, 441586288667678169, 441589611114374059, 758160967129436, 758170675943213⟩
      ⟨446539, 446709666635591964, 446713004250775895, 758160967129436, 758170675943213⟩ := by
  exact part441539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
