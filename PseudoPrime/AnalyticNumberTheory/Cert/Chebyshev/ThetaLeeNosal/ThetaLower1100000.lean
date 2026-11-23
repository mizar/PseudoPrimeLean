/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Direct theta estimate up to 1100000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private def base : ℕ :=
  let n : ℕ := 0x134c43df05c1b2271
  let n := (n <<< 240) + 0xbb1d3eacca431a87bdfd6193b3da20584feed2db5d79762955a76c03d726
  let n := (n <<< 240) + 0xdefb75b0ed5b77545c660545973c5eeac854abcc980fd38cfa87d63d24bc
  let n := (n <<< 240) + 0xa0ca6dc5d144ec32741caee69d8c17bda126c3606f4f54110f5aa8afb07f
  let n := (n <<< 240) + 0x0800715ba8103dcbd38a1efdbc3b8eded49fba5e348c5d3699ab5627c656
  let n := (n <<< 240) + 0xfc3e6ff6fce67b917dae2817d23c4e8c2ad94a68821db300d37a2b4742c2
  let n := (n <<< 240) + 0x220df58c067ac037d73f4e78db5e64a2ebe82de8cd63ccc1694ce7b7c422
  let n := (n <<< 240) + 0x9d406f1bb4005cca805859f0a6fadba86f6cbcdb91b7c6b4421cf2da4d9d
  let n := (n <<< 240) + 0xa334d1edc07a110535632b8b939741024f19e691b1c7f767ed656a1e4397
  let n := (n <<< 240) + 0xe8ace81d8dbcc455b7924251d2ea670b64e6624203372af08abde2a694dd
  let n := (n <<< 240) + 0x1f941882f4a724253b92024f3978f17990d6e9f22c6e98d3b822e5ef0b5b
  let n := (n <<< 240) + 0x260254b9538bd1ddc15eb80183d041c1df7744a006ae549814c71910c23a
  let n := (n <<< 240) + 0xc3472b608810c7b6f1f3d9ca2d55ae26b06e46c2249d8b4e4fe67dbe6800
  n

private theorem covers (m : ℕ) (hm : 2 ≤ m) (hb : m ≤ 2048) : m ∣ base := by
  have h : divisorBase 11 1 = base := by decide +kernel
  rw [← h]
  exact dvd_divisorBase 11 1 m ((by decide : 1 ≤ 2).trans hm) (Nat.lt_succ_of_le hb)

private theorem tile (a b t d k r j : ℕ) (e f q u : ℚ) (ha : 1000000 ≤ a)
    (hb : b < (2048 + 1) * (2048 + 1)) (he : a + 2 ^ (t + d) = b)
    (hc : tiledPrimeCount base 200560490130 t d a = k) (hs : r ^ 2 ≤ a)
    (hl : PseudoPrime.Analysis.rationalLogIntervalCheck a j 20 q u = true) (hf : f ≤ e + k * q)
    (hw : (b : ℚ) ≤ e + 5 * r) : ThetaLowerSegment a b e f := by
  apply theta_segment_of_count covers a b t d k 200560490130 r e f q ha hb he hc hs _ hf hw
  simpa only [Rat.cast_natCast] using (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1

private theorem cell1050624 :
    ThetaLowerSegment 1050624 1052672 (5243944 / 5) (656706177 / 625) := by
  exact
    tile 1050624 1052672 7 4 140 1024 20 _ _ (173311 / 12500) (1386491 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052672 :
    ThetaLowerSegment 1052672 1054720 (656706177 / 625) (52637722019 / 50000) := by
  exact
    tile 1052672 1054720 7 4 146 1025 20 _ _ (1386683 / 100000) (693343 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054720 :
    ThetaLowerSegment 1054720 1056768 (52637722019 / 50000) (52737577163 / 50000) := by
  exact
    tile 1054720 1056768 7 4 144 1026 20 _ _ (1386877 / 100000) (8668 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1056768 :
    ThetaLowerSegment 1056768 1058816 (52737577163 / 50000) (21136365581 / 20000) := by
  exact
    tile 1056768 1058816 7 4 149 1027 20 _ _ (1387071 / 100000) (693537 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058816 :
    ThetaLowerSegment 1058816 1060864 (21136365581 / 20000) (10587743227 / 10000) := by
  exact
    tile 1058816 1060864 7 4 141 1028 20 _ _ (277453 / 20000) (346817 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060864 :
    ThetaLowerSegment 1060864 1062912 (10587743227 / 10000) (53030288363 / 50000) := by
  exact
    tile 1060864 1062912 7 4 132 1029 20 _ _ (693729 / 50000) (1387461 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062912 :
    ThetaLowerSegment 1062912 1064960 (53030288363 / 50000) (6642489099 / 6250) := by
  exact
    tile 1062912 1064960 7 4 158 1030 20 _ _ (1387651 / 100000) (693827 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064960 :
    ThetaLowerSegment 1064960 1067008 (6642489099 / 6250) (10647689929 / 10000) := by
  exact
    tile 1064960 1067008 7 4 142 1031 20 _ _ (1387843 / 100000) (693923 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1067008 :
    ThetaLowerSegment 1067008 1069056 (10647689929 / 10000) (10668788061 / 10000) := by
  exact
    tile 1067008 1069056 7 4 152 1032 20 _ _ (277607 / 20000) (694019 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1069056 :
    ThetaLowerSegment 1069056 1071104 (10668788061 / 10000) (106894726433 / 100000) := by
  exact
    tile 1069056 1071104 7 4 149 1033 20 _ _ (1388227 / 100000) (138823 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1071104 :
    ThetaLowerSegment 1071104 1073152 (106894726433 / 100000) (26774011797 / 25000) := by
  exact
    tile 1071104 1073152 7 4 145 1034 20 _ _ (1388419 / 100000) (694211 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1073152 :
    ThetaLowerSegment 1073152 1075200 (26774011797 / 25000) (26826778977 / 25000) := by
  exact
    tile 1073152 1075200 7 4 152 1035 20 _ _ (138861 / 10000) (1388613 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1075200 :
    ThetaLowerSegment 1075200 1077248 (26826778977 / 25000) (26878511777 / 25000) := by
  exact
    tile 1075200 1077248 7 4 149 1036 20 _ _ (1736 / 125) (1388803 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1077248 :
    ThetaLowerSegment 1077248 1079296 (26878511777 / 25000) (13463563231 / 12500) := by
  exact
    tile 1077248 1079296 7 4 140 1037 20 _ _ (1388991 / 100000) (694497 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1079296 :
    ThetaLowerSegment 1079296 1081344 (13463563231 / 12500) (3373097179 / 3125) := by
  exact
    tile 1079296 1081344 7 4 166 1038 20 _ _ (69459 / 5000) (1389183 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1081344 :
    ThetaLowerSegment 1081344 1083392 (3373097179 / 3125) (3379349344 / 3125) := by
  exact
    tile 1081344 1083392 7 4 144 1039 20 _ _ (138937 / 10000) (1389373 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1083392 :
    ThetaLowerSegment 1083392 1085440 (3379349344 / 3125) (54168248193 / 50000) := by
  exact
    tile 1083392 1085440 7 4 142 1040 20 _ _ (1389559 / 100000) (694781 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1085440 :
    ThetaLowerSegment 1085440 1087488 (54168248193 / 50000) (54266920301 / 50000) := by
  exact
    tile 1085440 1087488 7 4 142 1041 20 _ _ (347437 / 25000) (1389751 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1087488 :
    ThetaLowerSegment 1087488 1089536 (54266920301 / 50000) (27184192851 / 25000) := by
  exact
    tile 1087488 1089536 7 4 146 1042 20 _ _ (1389937 / 100000) (69497 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1089536 :
    ThetaLowerSegment 1089536 1091584 (27184192851 / 25000) (108943900029 / 100000) := by
  exact
    tile 1089536 1091584 7 4 149 1043 20 _ _ (11121 / 800) (86883 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1091584 :
    ThetaLowerSegment 1091584 1093632 (108943900029 / 100000) (54575528333 / 50000) := by
  exact
    tile 1091584 1093632 7 4 149 1044 20 _ _ (1390313 / 100000) (347579 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1093632 :
    ThetaLowerSegment 1093632 1095680 (54575528333 / 50000) (54686768333 / 50000) := by
  exact
    tile 1093632 1095680 7 4 160 1045 20 _ _ (2781 / 200) (1390503 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1095680 :
    ThetaLowerSegment 1095680 1097728 (54686768333 / 50000) (13697072121 / 12500) := by
  exact
    tile 1095680 1097728 7 4 146 1046 20 _ _ (1390687 / 100000) (139069 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1097728 :
    ThetaLowerSegment 1097728 1099776 (13697072121 / 12500) (27443520269 / 25000) := by
  exact
    tile 1097728 1099776 7 4 142 1047 20 _ _ (695437 / 50000) (1390877 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099776 :
    ThetaLowerSegment 1099776 1099904 (27443520269 / 25000) (27446997919 / 25000) := by
  exact
    tile 1099776 1099904 7 0 10 1048 20 _ _ (69553 / 5000) (1391063 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1099904 :
    ThetaLowerSegment 1099904 1099968 (27446997919 / 25000) (27448388991 / 25000) := by
  exact
    tile 1099904 1099968 6 0 4 1048 20 _ _ (43471 / 3125) (55643 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1099968 :
    ThetaLowerSegment 1099968 1100000 (27448388991 / 25000) (54897473521 / 50000) := by
  exact
    tile 1099968 1100000 5 0 1 1048 20 _ _ (695539 / 50000) (1391081 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1050624_1100000 :
    ThetaLowerSegment 1050624 1100000 (5243944 / 5) (54897473521 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell1050624 cell1052672)
            (ThetaLowerSegment.join cell1054720 cell1056768))
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell1058816 cell1060864)
            (ThetaLowerSegment.join cell1062912 cell1064960)))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell1067008 cell1069056)
            (ThetaLowerSegment.join cell1071104 cell1073152))
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell1075200 cell1077248)
            (ThetaLowerSegment.join cell1079296 cell1081344))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell1083392 cell1085440)
            (ThetaLowerSegment.join cell1087488 cell1089536))
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell1091584 cell1093632)
            (ThetaLowerSegment.join cell1095680 cell1097728)))
        (ThetaLowerSegment.join (ThetaLowerSegment.join cell1099776 cell1099904) cell1099968)))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
