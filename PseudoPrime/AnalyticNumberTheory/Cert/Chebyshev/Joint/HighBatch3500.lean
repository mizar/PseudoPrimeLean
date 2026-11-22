/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 3500 to 6539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e3500 : Edge :=
  ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩

private def e6539 : Edge :=
  ⟨6539, 6525660194961613, 6525735033785668, 99186924014031, 99187319472619⟩

private def extra3500 : ℕ → ℕ
  | 3500 => 23
  | 3524 => 16
  | 3541 => 40
  | 3582 => 40
  | 3623 => 47
  | 3671 => 37
  | 3709 => 29
  | 3739 => 39
  | 3779 => 43
  | 3823 => 39
  | 3863 => 47
  | 3911 => 31
  | 3943 => 57
  | 4001 => 40
  | 4042 => 48
  | 4091 => 41
  | 4133 => 43
  | 4177 => 51
  | 4229 => 31
  | 4261 => 27
  | 4289 => 49
  | 4339 => 57
  | 4397 => 51
  | 4449 => 41
  | 4491 => 42
  | 4534 => 50
  | 4585 => 42
  | 4628 => 33
  | 4662 => 50
  | 4713 => 42
  | 4756 => 42
  | 4799 => 51
  | 4851 => 33
  | 4885 => 25
  | 4911 => 25
  | 4937 => 33
  | 4971 => 43
  | 5015 => 59
  | 5075 => 42
  | 5118 => 60
  | 5179 => 51
  | 5231 => 42
  | 5274 => 34
  | 5309 => 42
  | 5352 => 34
  | 5387 => 16
  | 5404 => 17
  | 5422 => 34
  | 5457 => 42
  | 5500 => 34
  | 5535 => 55
  | 5591 => 57
  | 5649 => 34
  | 5684 => 51
  | 5736 => 43
  | 5780 => 43
  | 5824 => 42
  | 5867 => 35
  | 5903 => 49
  | 5953 => 72
  | 6026 => 34
  | 6061 => 43
  | 6105 => 52
  | 6158 => 52
  | 6211 => 52
  | 6264 => 52
  | 6317 => 41
  | 6359 => 29
  | 6389 => 37
  | 6427 => 53
  | 6481 => 57
  | _ => 0

private theorem part3500 : Segment Valid highEstimate e3500 e6539 := by
  apply gcd_batch (by decide) (by decide) extra3500 71
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [3500,6539). -/
theorem batch3500 :
    Segment Valid highEstimate
      ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩
      ⟨6539, 6525660194961613, 6525735033785668, 99186924014031, 99187319472619⟩ := by
  exact part3500

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
