/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 16539 to 21539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e16539 : Edge :=
  ⟨16539, 16544435023027948, 16544593292855358, 153426883084412, 153427728502157⟩

private def e21539 : Edge :=
  ⟨21539, 21517387920455064, 21517611333191912, 171201049835284, 171202440239984⟩

private def extra16539 : ℕ → ℕ
  | 16539 => 101
  | 16641 => 97
  | 16739 => 97
  | 16837 => 87
  | 16925 => 77
  | 17003 => 88
  | 17092 => 87
  | 17180 => 78
  | 17259 => 87
  | 17347 => 78
  | 17426 => 82
  | 17509 => 89
  | 17599 => 107
  | 17707 => 101
  | 17809 => 98
  | 17908 => 78
  | 17987 => 101
  | 18089 => 91
  | 18181 => 71
  | 18253 => 59
  | 18313 => 65
  | 18379 => 63
  | 18443 => 59
  | 18503 => 49
  | 18553 => 83
  | 18637 => 105
  | 18743 => 113
  | 18857 => 78
  | 18936 => 69
  | 19006 => 48
  | 19055 => 49
  | 19105 => 48
  | 19154 => 29
  | 19184 => 39
  | 19224 => 39
  | 19264 => 38
  | 19303 => 39
  | 19343 => 29
  | 19373 => 9
  | 19383 => 19
  | 19403 => 29
  | 19433 => 58
  | 19492 => 89
  | 19582 => 88
  | 19671 => 49
  | 19721 => 59
  | 19781 => 68
  | 19850 => 59
  | 19910 => 49
  | 19960 => 49
  | 20010 => 69
  | 20080 => 79
  | 20160 => 98
  | 20259 => 89
  | 20349 => 89
  | 20439 => 99
  | 20539 => 89
  | 20629 => 79
  | 20709 => 59
  | 20769 => 79
  | 20849 => 59
  | 20909 => 69
  | 20979 => 59
  | 21039 => 89
  | 21129 => 70
  | 21200 => 99
  | 21300 => 69
  | 21370 => 59
  | 21430 => 80
  | 21511 => 27
  | _ => 0

private theorem part16539 : Segment Valid highEstimate e16539 e21539 := by
  apply gcd_batch (by decide) (by decide) extra16539 70
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [16539,21539). -/
theorem batch16539 :
    Segment Valid highEstimate
      ⟨16539, 16544435023027948, 16544593292855358, 153426883084412, 153427728502157⟩
      ⟨21539, 21517387920455064, 21517611333191912, 171201049835284, 171202440239984⟩ := by
  exact part16539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
