/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 41539 to 46539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e41539 : Edge :=
  ⟨41539, 41499131825914016, 41499532330518635, 243180280503640, 243182711459752⟩

private def e46539 : Edge :=
  ⟨46539, 46486299092317656, 46486745158536790, 248532137647683, 248534672616378⟩

private def extra41539 : ℕ → ℕ
  | 41539 => 122
  | 41662 => 159
  | 41822 => 138
  | 41961 => 127
  | 42089 => 131
  | 42221 => 127
  | 42349 => 101
  | 42451 => 57
  | 42509 => 79
  | 42589 => 93
  | 42683 => 59
  | 42743 => 53
  | 42797 => 55
  | 42853 => 69
  | 42923 => 55
  | 42979 => 57
  | 43037 => 55
  | 43093 => 83
  | 43177 => 105
  | 43283 => 119
  | 43403 => 169
  | 43573 => 143
  | 43717 => 171
  | 43889 => 139
  | 44029 => 129
  | 44159 => 113
  | 44273 => 143
  | 44417 => 131
  | 44549 => 137
  | 44687 => 131
  | 44819 => 133
  | 44953 => 165
  | 45119 => 167
  | 45287 => 151
  | 45439 => 173
  | 45613 => 169
  | 45783 => 160
  | 45944 => 129
  | 46074 => 128
  | 46203 => 139
  | 46343 => 129
  | 46473 => 65
  | _ => 0

private theorem part41539 : Segment Valid highEstimate e41539 e46539 := by
  apply gcd_batch (by decide) (by decide) extra41539 42
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [41539,46539). -/
theorem batch41539 :
    Segment Valid highEstimate
      ⟨41539, 41499131825914016, 41499532330518635, 243180280503640, 243182711459752⟩
      ⟨46539, 46486299092317656, 46486745158536790, 248532137647683, 248534672616378⟩ := by
  exact part41539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
