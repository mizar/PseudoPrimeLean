/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 6539 to 11539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e6539 : Edge :=
  ⟨6539, 6525660194961613, 6525735033785668, 99186924014031, 99187319472619⟩

private def e11539 : Edge :=
  ⟨11539, 11521820701190191, 11521949081268747, 131327986379440, 131328717576433⟩

private def extra6539 : ℕ → ℕ
  | 6539 => 43
  | 6583 => 71
  | 6655 => 43
  | 6699 => 53
  | 6753 => 52
  | 6806 => 56
  | 6863 => 47
  | 6911 => 55
  | 6967 => 33
  | 7001 => 37
  | 7039 => 39
  | 7079 => 49
  | 7129 => 63
  | 7193 => 53
  | 7247 => 73
  | 7321 => 58
  | 7380 => 44
  | 7425 => 26
  | 7452 => 17
  | 7470 => 17
  | 7488 => 26
  | 7515 => 26
  | 7542 => 44
  | 7587 => 61
  | 7649 => 53
  | 7703 => 53
  | 7757 => 71
  | 7829 => 64
  | 7894 => 56
  | 7951 => 79
  | 8031 => 44
  | 8076 => 35
  | 8112 => 54
  | 8167 => 44
  | 8212 => 36
  | 8249 => 54
  | 8304 => 62
  | 8367 => 45
  | 8413 => 36
  | 8450 => 53
  | 8504 => 27
  | 8532 => 26
  | 8559 => 27
  | 8587 => 26
  | 8614 => 27
  | 8642 => 35
  | 8678 => 36
  | 8715 => 54
  | 8770 => 63
  | 8834 => 63
  | 8898 => 72
  | 8971 => 71
  | 9043 => 75
  | 9119 => 54
  | 9174 => 64
  | 9239 => 72
  | 9312 => 64
  | 9377 => 59
  | 9437 => 41
  | 9479 => 53
  | 9533 => 79
  | 9613 => 63
  | 9677 => 61
  | 9739 => 51
  | 9791 => 47
  | 9839 => 43
  | 9883 => 45
  | 9929 => 43
  | 9973 => 87
  | 10061 => 71
  | 10133 => 47
  | 10181 => 65
  | 10247 => 53
  | 10301 => 35
  | 10337 => 53
  | 10391 => 65
  | 10457 => 55
  | 10513 => 83
  | 10597 => 65
  | 10663 => 65
  | 10729 => 69
  | 10799 => 67
  | 10867 => 81
  | 10949 => 84
  | 11034 => 65
  | 11100 => 74
  | 11175 => 84
  | 11260 => 65
  | 11326 => 74
  | 11401 => 65
  | 11467 => 55
  | 11523 => 15
  | _ => 0

private theorem part6539 : Segment Valid highEstimate e6539 e11539 := by
  apply gcd_batch (by decide) (by decide) extra6539 92
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [6539,11539). -/
theorem batch6539 :
    Segment Valid highEstimate
      ⟨6539, 6525660194961613, 6525735033785668, 99186924014031, 99187319472619⟩
      ⟨11539, 11521820701190191, 11521949081268747, 131327986379440, 131328717576433⟩ := by
  exact part6539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
