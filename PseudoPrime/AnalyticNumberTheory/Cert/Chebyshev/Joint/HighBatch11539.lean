/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 11539 to 16539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e11539 : Edge :=
  ⟨11539, 11521820701190191, 11521949081268747, 131327986379440, 131328717576433⟩

private def e16539 : Edge :=
  ⟨16539, 16544435023027948, 16544593292855358, 153426883084412, 153427728502157⟩

private def extra11539 : ℕ → ℕ
  | 11539 => 59
  | 11599 => 56
  | 11656 => 27
  | 11684 => 27
  | 11712 => 28
  | 11741 => 27
  | 11769 => 8
  | 11778 => 9
  | 11788 => 18
  | 11807 => 27
  | 11835 => 47
  | 11883 => 27
  | 11911 => 37
  | 11949 => 46
  | 11996 => 56
  | 12053 => 56
  | 12110 => 56
  | 12167 => 65
  | 12233 => 37
  | 12271 => 56
  | 12328 => 47
  | 12376 => 37
  | 12414 => 56
  | 12471 => 46
  | 12518 => 75
  | 12594 => 64
  | 12659 => 79
  | 12739 => 81
  | 12821 => 87
  | 12909 => 69
  | 12979 => 63
  | 13043 => 65
  | 13109 => 61
  | 13171 => 69
  | 13241 => 71
  | 13313 => 85
  | 13399 => 77
  | 13477 => 99
  | 13577 => 77
  | 13655 => 66
  | 13722 => 76
  | 13799 => 79
  | 13879 => 83
  | 13963 => 87
  | 14051 => 93
  | 14145 => 67
  | 14213 => 66
  | 14280 => 38
  | 14319 => 28
  | 14348 => 47
  | 14396 => 28
  | 14425 => 47
  | 14473 => 47
  | 14521 => 38
  | 14560 => 57
  | 14618 => 38
  | 14657 => 66
  | 14724 => 57
  | 14782 => 86
  | 14869 => 87
  | 14957 => 105
  | 15063 => 67
  | 15131 => 77
  | 15209 => 76
  | 15286 => 74
  | 15361 => 77
  | 15439 => 71
  | 15511 => 89
  | 15601 => 65
  | 15667 => 69
  | 15737 => 53
  | 15791 => 67
  | 15859 => 53
  | 15913 => 57
  | 15971 => 85
  | 16057 => 45
  | 16103 => 79
  | 16183 => 65
  | 16249 => 89
  | 16339 => 87
  | 16427 => 91
  | 16519 => 19
  | _ => 0

private theorem part11539 : Segment Valid highEstimate e11539 e16539 := by
  apply gcd_batch (by decide) (by decide) extra11539 82
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [11539,16539). -/
theorem batch11539 :
    Segment Valid highEstimate
      ⟨11539, 11521820701190191, 11521949081268747, 131327986379440, 131328717576433⟩
      ⟨16539, 16544435023027948, 16544593292855358, 153426883084412, 153427728502157⟩ := by
  exact part11539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
