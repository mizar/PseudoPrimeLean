/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 436539 to 441539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e436539 : Edge :=
  ⟨436539, 436733609062523898, 436736905534581059, 751667213436352, 751676893203048⟩

private def e441539 : Edge :=
  ⟨441539, 441586288667678169, 441589611114374059, 758160967129436, 758170675943213⟩

private def extra436539 : ℕ → ℕ
  | 436539 => 349
  | 436889 => 353
  | 437243 => 397
  | 437641 => 449
  | 438091 => 477
  | 438569 => 493
  | 439063 => 537
  | 439601 => 499
  | 440101 => 465
  | 440567 => 473
  | 441041 => 481
  | 441523 => 15
  | _ => 0

private theorem part436539 : Segment Valid highEstimate e436539 e441539 := by
  apply gcd_batch (by decide) (by decide) extra436539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [436539,441539). -/
theorem batch436539 :
    Segment Valid highEstimate
      ⟨436539, 436733609062523898, 436736905534581059, 751667213436352, 751676893203048⟩
      ⟨441539, 441586288667678169, 441589611114374059, 758160967129436, 758170675943213⟩ := by
  exact part436539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
