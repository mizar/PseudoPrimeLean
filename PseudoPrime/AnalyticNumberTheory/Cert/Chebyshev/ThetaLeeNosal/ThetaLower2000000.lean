/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Direct theta estimate up to 2000000 -/

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

private theorem cell1100000 :
    ThetaLowerSegment 1100000 1102048 (54897473521 / 50000) (11000082703 / 10000) := by
  exact
    tile 1100000 1102048 7 4 148 1048 20 _ _ (1391081 / 100000) (347771 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1102048 :
    ThetaLowerSegment 1102048 1104096 (11000082703 / 10000) (22040512149 / 20000) := by
  exact
    tile 1102048 1104096 7 4 145 1049 20 _ _ (1391267 / 100000) (139127 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1104096 :
    ThetaLowerSegment 1104096 1106144 (22040512149 / 20000) (110421018709 / 100000) := by
  exact
    tile 1104096 1106144 7 4 157 1050 20 _ _ (347863 / 25000) (278291 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1106144 :
    ThetaLowerSegment 1106144 1108192 (110421018709 / 100000) (110629764409 / 100000) := by
  exact
    tile 1106144 1108192 7 4 150 1051 20 _ _ (695819 / 50000) (1391641 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1108192 :
    ThetaLowerSegment 1108192 1110240 (110629764409 / 100000) (55419964841 / 50000) := by
  exact
    tile 1108192 1110240 7 4 151 1052 20 _ _ (1391823 / 100000) (695913 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1110240 :
    ThetaLowerSegment 1110240 1112288 (55419964841 / 50000) (27764966697 / 25000) := by
  exact
    tile 1110240 1112288 7 4 158 1053 20 _ _ (1392007 / 100000) (139201 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1112288 :
    ThetaLowerSegment 1112288 1114336 (27764966697 / 25000) (22252903773 / 20000) := by
  exact
    tile 1112288 1114336 7 4 147 1054 20 _ _ (1392191 / 100000) (696097 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1114336 :
    ThetaLowerSegment 1114336 1116384 (22252903773 / 20000) (22294118073 / 20000) := by
  exact
    tile 1114336 1116384 7 4 148 1055 20 _ _ (11139 / 800) (696189 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1116384 :
    ThetaLowerSegment 1116384 1118432 (22294118073 / 20000) (111676689097 / 100000) := by
  exact
    tile 1116384 1118432 7 4 148 1056 20 _ _ (1392559 / 100000) (696281 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1118432 :
    ThetaLowerSegment 1118432 1120480 (111676689097 / 100000) (111859138299 / 100000) := by
  exact
    tile 1118432 1120480 7 4 131 1057 20 _ _ (696371 / 50000) (278549 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1120480 :
    ThetaLowerSegment 1120480 1122528 (111859138299 / 100000) (112070862899 / 100000) := by
  exact
    tile 1120480 1122528 7 4 152 1058 20 _ _ (55717 / 4000) (43529 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1122528 :
    ThetaLowerSegment 1122528 1124576 (112070862899 / 100000) (112265898019 / 100000) := by
  exact
    tile 1122528 1124576 7 4 140 1059 20 _ _ (348277 / 25000) (1393111 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1124576 :
    ThetaLowerSegment 1124576 1126624 (112265898019 / 100000) (112465138489 / 100000) := by
  exact
    tile 1124576 1126624 7 4 143 1060 20 _ _ (139329 / 10000) (1393293 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1126624 :
    ThetaLowerSegment 1126624 1128672 (112465138489 / 100000) (22535667941 / 20000) := by
  exact
    tile 1126624 1128672 7 4 153 1061 20 _ _ (43546 / 3125) (55739 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1128672 :
    ThetaLowerSegment 1128672 1130720 (22535667941 / 20000) (22577477561 / 20000) := by
  exact
    tile 1128672 1130720 7 4 150 1062 20 _ _ (696827 / 50000) (1393657 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1130720 :
    ThetaLowerSegment 1130720 1132768 (22577477561 / 20000) (22619292611 / 20000) := by
  exact
    tile 1130720 1132768 7 4 150 1063 20 _ _ (278767 / 20000) (696919 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1132768 :
    ThetaLowerSegment 1132768 1134816 (22619292611 / 20000) (113306959471 / 100000) := by
  exact
    tile 1132768 1134816 7 4 151 1064 20 _ _ (43563 / 3125) (1394019 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134816 :
    ThetaLowerSegment 1134816 1136864 (113306959471 / 100000) (56758741609 / 50000) := by
  exact
    tile 1134816 1136864 7 4 151 1065 20 _ _ (1394197 / 100000) (6971 / 500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1136864 :
    ThetaLowerSegment 1136864 1138912 (56758741609 / 50000) (113708512867 / 100000) := by
  exact
    tile 1136864 1138912 7 4 137 1066 20 _ _ (1394377 / 100000) (69719 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138912 :
    ThetaLowerSegment 1138912 1140960 (113708512867 / 100000) (28476286351 / 25000) := by
  exact
    tile 1138912 1140960 7 4 141 1067 20 _ _ (1394557 / 100000) (8716 / 625) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1140960 :
    ThetaLowerSegment 1140960 1143008 (28476286351 / 25000) (114110171743 / 100000) := by
  exact
    tile 1140960 1143008 7 4 147 1068 20 _ _ (1394737 / 100000) (69737 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143008 :
    ThetaLowerSegment 1143008 1145056 (114110171743 / 100000) (114309644731 / 100000) := by
  exact
    tile 1143008 1145056 7 4 143 1069 20 _ _ (348729 / 25000) (1394919 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145056 :
    ThetaLowerSegment 1145056 1147104 (114309644731 / 100000) (114510538411 / 100000) := by
  exact
    tile 1145056 1147104 7 4 144 1070 20 _ _ (279019 / 20000) (697549 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147104 :
    ThetaLowerSegment 1147104 1149152 (114510538411 / 100000) (114704481497 / 100000) := by
  exact
    tile 1147104 1149152 7 4 139 1071 20 _ _ (697637 / 50000) (1395277 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149152 :
    ThetaLowerSegment 1149152 1151200 (114704481497 / 100000) (114922172009 / 100000) := by
  exact
    tile 1149152 1151200 7 4 156 1071 20 _ _ (348863 / 25000) (279091 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151200 :
    ThetaLowerSegment 1151200 1153248 (114922172009 / 100000) (115130120879 / 100000) := by
  exact
    tile 1151200 1153248 7 4 149 1072 20 _ _ (139563 / 10000) (1395633 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153248 :
    ThetaLowerSegment 1153248 1155296 (115130120879 / 100000) (115324138191 / 100000) := by
  exact
    tile 1153248 1155296 7 4 139 1073 20 _ _ (43619 / 3125) (1395811 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155296 :
    ThetaLowerSegment 1155296 1157344 (115324138191 / 100000) (57773049903 / 50000) := by
  exact
    tile 1155296 1157344 7 4 159 1074 20 _ _ (279197 / 20000) (348997 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157344 :
    ThetaLowerSegment 1157344 1159392 (57773049903 / 50000) (14469265993 / 12500) := by
  exact
    tile 1157344 1159392 7 4 149 1075 20 _ _ (698081 / 50000) (279233 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159392 :
    ThetaLowerSegment 1159392 1161440 (14469265993 / 12500) (115956597099 / 100000) := by
  exact
    tile 1159392 1161440 7 4 145 1076 20 _ _ (1396339 / 100000) (698171 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161440 :
    ThetaLowerSegment 1161440 1163488 (115956597099 / 100000) (116189815271 / 100000) := by
  exact
    tile 1161440 1163488 7 4 167 1077 20 _ _ (349129 / 25000) (1396519 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1163488 :
    ThetaLowerSegment 1163488 1165536 (116189815271 / 100000) (116397922379 / 100000) := by
  exact
    tile 1163488 1165536 7 4 149 1078 20 _ _ (349173 / 25000) (279339 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1165536 :
    ThetaLowerSegment 1165536 1167584 (116397922379 / 100000) (116594880767 / 100000) := by
  exact
    tile 1165536 1167584 7 4 141 1079 20 _ _ (349217 / 25000) (1396871 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1167584 :
    ThetaLowerSegment 1167584 1169632 (116594880767 / 100000) (116804437217 / 100000) := by
  exact
    tile 1167584 1169632 7 4 150 1080 20 _ _ (1397043 / 100000) (698523 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1169632 :
    ThetaLowerSegment 1169632 1171680 (116804437217 / 100000) (117007033827 / 100000) := by
  exact
    tile 1169632 1171680 7 4 145 1081 20 _ _ (698609 / 50000) (1397221 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1171680 :
    ThetaLowerSegment 1171680 1173728 (117007033827 / 100000) (29299619167 / 25000) := by
  exact
    tile 1171680 1173728 7 4 137 1082 20 _ _ (1397393 / 100000) (349349 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1173728 :
    ThetaLowerSegment 1173728 1175776 (29299619167 / 25000) (1174067143 / 1000) := by
  exact
    tile 1173728 1175776 7 4 149 1083 20 _ _ (43674 / 3125) (1397571 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1175776 :
    ThetaLowerSegment 1175776 1177824 (1174067143 / 1000) (58808886671 / 50000) := by
  exact
    tile 1175776 1177824 7 4 151 1084 20 _ _ (698871 / 50000) (279549 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1177824 :
    ThetaLowerSegment 1177824 1179872 (58808886671 / 50000) (58917225161 / 50000) := by
  exact
    tile 1177824 1179872 7 4 155 1085 20 _ _ (349479 / 25000) (1397919 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1179872 :
    ThetaLowerSegment 1179872 1181920 (58917225161 / 50000) (29513487613 / 25000) := by
  exact
    tile 1179872 1181920 7 4 157 1086 20 _ _ (139809 / 10000) (1398093 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1181920 :
    ThetaLowerSegment 1181920 1183968 (29513487613 / 25000) (29565223381 / 25000) := by
  exact
    tile 1181920 1183968 7 4 148 1087 20 _ _ (174783 / 12500) (1398267 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1183968 :
    ThetaLowerSegment 1183968 1186016 (29565223381 / 25000) (59238126411 / 50000) := by
  exact
    tile 1183968 1186016 7 4 154 1088 20 _ _ (1398437 / 100000) (34961 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1186016 :
    ThetaLowerSegment 1186016 1190112 (59238126411 / 50000) (29722210693 / 25000) := by
  exact
    tile 1186016 1190112 7 5 295 1089 20 _ _ (139861 / 10000) (1398613 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1190112 :
    ThetaLowerSegment 1190112 1194208 (29722210693 / 25000) (7456258453 / 6250) := by
  exact
    tile 1190112 1194208 7 5 294 1090 20 _ _ (699477 / 50000) (1398957 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1194208 :
    ThetaLowerSegment 1194208 1198304 (7456258453 / 6250) (59853665483 / 50000) := by
  exact
    tile 1194208 1198304 7 5 291 1092 20 _ _ (699649 / 50000) (1399301 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1198304 :
    ThetaLowerSegment 1198304 1202400 (59853665483 / 50000) (60052414363 / 50000) := by
  exact
    tile 1198304 1202400 7 5 284 1094 20 _ _ (34991 / 2500) (1399643 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1202400 :
    ThetaLowerSegment 1202400 1206496 (60052414363 / 50000) (60247011861 / 50000) := by
  exact
    tile 1202400 1206496 7 5 278 1096 20 _ _ (699991 / 50000) (279997 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1206496 :
    ThetaLowerSegment 1206496 1208544 (60247011861 / 50000) (12068166687 / 10000) := by
  exact
    tile 1206496 1208544 7 4 134 1098 20 _ _ (700161 / 50000) (56013 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1208544 :
    ThetaLowerSegment 1208544 1210592 (12068166687 / 10000) (120881937083 / 100000) := by
  exact
    tile 1208544 1210592 7 4 143 1099 20 _ _ (1400491 / 100000) (700247 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1210592 :
    ThetaLowerSegment 1210592 1212640 (120881937083 / 100000) (60546718447 / 50000) := by
  exact
    tile 1210592 1212640 7 4 151 1100 20 _ _ (1400661 / 100000) (175083 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1212640 :
    ThetaLowerSegment 1212640 1214688 (60546718447 / 50000) (15165221523 / 12500) := by
  exact
    tile 1212640 1214688 7 4 163 1101 20 _ _ (140083 / 10000) (1400833 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1214688 :
    ThetaLowerSegment 1214688 1216736 (15165221523 / 12500) (12151370891 / 10000) := by
  exact
    tile 1214688 1216736 7 4 137 1102 20 _ _ (700499 / 50000) (1401001 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1216736 :
    ThetaLowerSegment 1216736 1218784 (12151370891 / 10000) (24346177959 / 20000) := by
  exact
    tile 1216736 1218784 7 4 155 1103 20 _ _ (1401167 / 100000) (140117 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1218784 :
    ThetaLowerSegment 1218784 1220832 (24346177959 / 20000) (1219312807 / 1000) := by
  exact
    tile 1218784 1220832 7 4 143 1103 20 _ _ (280267 / 20000) (700669 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1220832 :
    ThetaLowerSegment 1220832 1222880 (1219312807 / 1000) (122128892623 / 100000) := by
  exact
    tile 1220832 1222880 7 4 141 1104 20 _ _ (1401503 / 100000) (700753 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1222880 :
    ThetaLowerSegment 1222880 1224928 (122128892623 / 100000) (122325126423 / 100000) := by
  exact
    tile 1222880 1224928 7 4 140 1105 20 _ _ (140167 / 10000) (1401673 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1224928 :
    ThetaLowerSegment 1224928 1226976 (122325126423 / 100000) (122542411313 / 100000) := by
  exact
    tile 1224928 1226976 7 4 155 1106 20 _ _ (700919 / 50000) (1401841 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1226976 :
    ThetaLowerSegment 1226976 1229024 (122542411313 / 100000) (61370047009 / 50000) := by
  exact
    tile 1226976 1229024 7 4 141 1107 20 _ _ (280401 / 20000) (175251 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1229024 :
    ThetaLowerSegment 1229024 1231072 (61370047009 / 50000) (61467497963 / 50000) := by
  exact
    tile 1229024 1231072 7 4 139 1108 20 _ _ (350543 / 25000) (56087 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1231072 :
    ThetaLowerSegment 1231072 1233120 (61467497963 / 50000) (30785284903 / 25000) := by
  exact
    tile 1231072 1233120 7 4 147 1109 20 _ _ (701169 / 50000) (1402341 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1233120 :
    ThetaLowerSegment 1233120 1235168 (30785284903 / 25000) (30831918161 / 25000) := by
  exact
    tile 1233120 1235168 7 4 133 1110 20 _ _ (175313 / 12500) (1402507 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1235168 :
    ThetaLowerSegment 1235168 1237216 (30831918161 / 25000) (61761321887 / 50000) := by
  exact
    tile 1235168 1237216 7 4 139 1111 20 _ _ (140267 / 10000) (1402673 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1237216 :
    ThetaLowerSegment 1237216 1239264 (61761321887 / 50000) (61864430333 / 50000) := by
  exact
    tile 1237216 1239264 7 4 147 1112 20 _ _ (350709 / 25000) (1402839 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1239264 :
    ThetaLowerSegment 1239264 1241312 (61864430333 / 50000) (123932295811 / 100000) := by
  exact
    tile 1239264 1241312 7 4 145 1113 20 _ _ (1403001 / 100000) (350751 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1241312 :
    ThetaLowerSegment 1241312 1243360 (123932295811 / 100000) (24825467177 / 20000) := by
  exact
    tile 1241312 1243360 7 4 139 1114 20 _ _ (701583 / 50000) (1403169 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1243360 :
    ThetaLowerSegment 1243360 1245408 (24825467177 / 20000) (62169619433 / 50000) := by
  exact
    tile 1243360 1245408 7 4 151 1115 20 _ _ (1403331 / 100000) (701667 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1245408 :
    ThetaLowerSegment 1245408 1247456 (62169619433 / 50000) (498221509 / 400) := by
  exact
    tile 1245408 1247456 7 4 154 1115 20 _ _ (175437 / 12500) (1403499 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1247456 :
    ThetaLowerSegment 1247456 1249504 (498221509 / 400) (12477575187 / 10000) := by
  exact
    tile 1247456 1249504 7 4 157 1116 20 _ _ (70183 / 5000) (1403663 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1249504 :
    ThetaLowerSegment 1249504 1251552 (12477575187 / 10000) (62483335967 / 50000) := by
  exact
    tile 1249504 1251552 7 4 136 1117 20 _ _ (87739 / 6250) (1403827 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1251552 :
    ThetaLowerSegment 1251552 1253600 (62483335967 / 50000) (12515901829 / 10000) := by
  exact
    tile 1251552 1253600 7 4 137 1118 20 _ _ (350997 / 25000) (1403991 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1253600 :
    ThetaLowerSegment 1253600 1255648 (12515901829 / 10000) (31345218537 / 25000) := by
  exact
    tile 1253600 1255648 7 4 158 1119 20 _ _ (1404151 / 100000) (702077 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1255648 :
    ThetaLowerSegment 1255648 1257696 (31345218537 / 25000) (125587308453 / 100000) := by
  exact
    tile 1255648 1257696 7 4 147 1120 20 _ _ (280863 / 20000) (702159 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257696 :
    ThetaLowerSegment 1257696 1259744 (125587308453 / 100000) (125805002543 / 100000) := by
  exact
    tile 1257696 1259744 7 4 155 1121 20 _ _ (702239 / 50000) (1404481 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259744 :
    ThetaLowerSegment 1259744 1261792 (125805002543 / 100000) (126000247503 / 100000) := by
  exact
    tile 1259744 1261792 7 4 139 1122 20 _ _ (8779 / 625) (1404643 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1261792 :
    ThetaLowerSegment 1261792 1263840 (126000247503 / 100000) (2524191263 / 2000) := by
  exact
    tile 1261792 1263840 7 4 149 1123 20 _ _ (1404803 / 100000) (702403 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263840 :
    ThetaLowerSegment 1263840 1265888 (2524191263 / 2000) (3160367201 / 2500) := by
  exact
    tile 1263840 1265888 7 4 146 1124 20 _ _ (280993 / 20000) (175621 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265888 :
    ThetaLowerSegment 1265888 1267936 (3160367201 / 2500) (63315538799 / 50000) := by
  exact
    tile 1265888 1267936 7 4 154 1125 20 _ _ (1405127 / 100000) (140513 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267936 :
    ThetaLowerSegment 1267936 1269984 (63315538799 / 50000) (126834844503 / 100000) := by
  exact
    tile 1267936 1269984 7 4 145 1126 20 _ _ (1405289 / 100000) (351323 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269984 :
    ThetaLowerSegment 1269984 1272032 (126834844503 / 100000) (127049878353 / 100000) := by
  exact
    tile 1269984 1272032 7 4 153 1126 20 _ _ (28109 / 2000) (1405453 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272032 :
    ThetaLowerSegment 1272032 1276128 (127049878353 / 100000) (63723833133 / 50000) := by
  exact
    tile 1272032 1276128 7 5 283 1127 20 _ _ (1405611 / 100000) (702807 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276128 :
    ThetaLowerSegment 1276128 1278176 (63723833133 / 50000) (127640279087 / 100000) := by
  exact
    tile 1276128 1278176 7 4 137 1129 20 _ _ (1405933 / 100000) (87871 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278176 :
    ThetaLowerSegment 1278176 1280224 (127640279087 / 100000) (12785259913 / 10000) := by
  exact
    tile 1278176 1280224 7 4 151 1130 20 _ _ (1406093 / 100000) (87881 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280224 :
    ThetaLowerSegment 1280224 1282272 (12785259913 / 10000) (64027549781 / 50000) := by
  exact
    tile 1280224 1282272 7 4 144 1131 20 _ _ (1406253 / 100000) (87891 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282272 :
    ThetaLowerSegment 1282272 1284320 (64027549781 / 50000) (128256216621 / 100000) := by
  exact
    tile 1282272 1284320 7 4 143 1132 20 _ _ (1406413 / 100000) (87901 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284320 :
    ThetaLowerSegment 1284320 1286368 (128256216621 / 100000) (128467202421 / 100000) := by
  exact
    tile 1284320 1286368 7 4 150 1133 20 _ _ (351643 / 25000) (56263 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1286368 :
    ThetaLowerSegment 1286368 1288416 (128467202421 / 100000) (128685245881 / 100000) := by
  exact
    tile 1286368 1288416 7 4 155 1134 20 _ _ (351683 / 25000) (281347 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288416 :
    ThetaLowerSegment 1288416 1292512 (128685245881 / 100000) (129081989143 / 100000) := by
  exact
    tile 1288416 1292512 7 5 282 1135 20 _ _ (1406891 / 100000) (703447 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1292512 :
    ThetaLowerSegment 1292512 1294560 (129081989143 / 100000) (129280405471 / 100000) := by
  exact
    tile 1292512 1294560 7 4 141 1136 20 _ _ (175901 / 12500) (1407211 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1294560 :
    ThetaLowerSegment 1294560 1296608 (129280405471 / 100000) (6474364421 / 5000) := by
  exact
    tile 1294560 1296608 7 4 147 1137 20 _ _ (1407367 / 100000) (140737 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1296608 :
    ThetaLowerSegment 1296608 1298656 (6474364421 / 5000) (25937149889 / 20000) := by
  exact
    tile 1296608 1298656 7 4 141 1138 20 _ _ (56301 / 4000) (175941 / 12500) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1298656 :
    ThetaLowerSegment 1298656 1300704 (25937149889 / 20000) (3247246587 / 2500) := by
  exact
    tile 1298656 1300704 7 4 145 1139 20 _ _ (1407683 / 100000) (703843 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1300704 :
    ThetaLowerSegment 1300704 1302752 (3247246587 / 2500) (3252385203 / 2500) := by
  exact
    tile 1300704 1302752 7 4 146 1140 20 _ _ (8799 / 625) (1407843 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1302752 :
    ThetaLowerSegment 1302752 1304800 (3252385203 / 2500) (32575947919 / 25000) := by
  exact
    tile 1302752 1304800 7 4 148 1141 20 _ _ (1407997 / 100000) (352 / 25) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1304800 :
    ThetaLowerSegment 1304800 1306848 (32575947919 / 25000) (130505157841 / 100000) := by
  exact
    tile 1304800 1306848 7 4 143 1142 20 _ _ (281631 / 20000) (704079 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1306848 :
    ThetaLowerSegment 1306848 1308896 (130505157841 / 100000) (32675932423 / 25000) := by
  exact
    tile 1306848 1308896 7 4 141 1143 20 _ _ (1408311 / 100000) (704157 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1308896 :
    ThetaLowerSegment 1308896 1310944 (32675932423 / 25000) (32728749973 / 25000) := by
  exact
    tile 1308896 1310944 7 4 150 1144 20 _ _ (352117 / 25000) (1408471 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1310944 :
    ThetaLowerSegment 1310944 1312992 (32728749973 / 25000) (32781221217 / 25000) := by
  exact
    tile 1310944 1312992 7 4 149 1144 20 _ _ (88039 / 6250) (1408627 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1312992 :
    ThetaLowerSegment 1312992 1315040 (32781221217 / 25000) (32827710957 / 25000) := by
  exact
    tile 1312992 1315040 7 4 132 1145 20 _ _ (70439 / 5000) (1408783 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1315040 :
    ThetaLowerSegment 1315040 1317088 (32827710957 / 25000) (32879137121 / 25000) := by
  exact
    tile 1315040 1317088 7 4 146 1146 20 _ _ (176117 / 12500) (1408939 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1317088 :
    ThetaLowerSegment 1317088 1319136 (32879137121 / 25000) (4116541293 / 3125) := by
  exact
    tile 1317088 1319136 7 4 151 1147 20 _ _ (352273 / 25000) (281819 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1319136 :
    ThetaLowerSegment 1319136 1321184 (4116541293 / 3125) (6595767099 / 5000) := by
  exact
    tile 1319136 1321184 7 4 132 1148 20 _ _ (1409247 / 100000) (5637 / 400) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1321184 :
    ThetaLowerSegment 1321184 1323232 (6595767099 / 5000) (66078174861 / 50000) := by
  exact
    tile 1321184 1323232 7 4 171 1149 20 _ _ (704701 / 50000) (281881 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1323232 :
    ThetaLowerSegment 1323232 1325280 (66078174861 / 50000) (132355097259 / 100000) := by
  exact
    tile 1323232 1325280 7 4 141 1150 20 _ _ (1409557 / 100000) (35239 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1325280 :
    ThetaLowerSegment 1325280 1327328 (132355097259 / 100000) (132559505499 / 100000) := by
  exact
    tile 1325280 1327328 7 4 145 1151 20 _ _ (88107 / 6250) (281943 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1327328 :
    ThetaLowerSegment 1327328 1329376 (132559505499 / 100000) (132752657141 / 100000) := by
  exact
    tile 1327328 1329376 7 4 137 1152 20 _ _ (704933 / 50000) (1409869 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1329376 :
    ThetaLowerSegment 1329376 1331424 (132752657141 / 100000) (132947240039 / 100000) := by
  exact
    tile 1329376 1331424 7 4 138 1152 20 _ _ (1410021 / 100000) (176253 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1331424 :
    ThetaLowerSegment 1331424 1333472 (132947240039 / 100000) (133153125443 / 100000) := by
  exact
    tile 1331424 1333472 7 4 146 1153 20 _ _ (705087 / 50000) (1410177 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1333472 :
    ThetaLowerSegment 1333472 1335520 (133153125443 / 100000) (26669832207 / 20000) := by
  exact
    tile 1333472 1335520 7 4 139 1154 20 _ _ (176291 / 12500) (1410331 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1335520 :
    ThetaLowerSegment 1335520 1337568 (26669832207 / 20000) (133559322853 / 100000) := by
  exact
    tile 1335520 1337568 7 4 149 1155 20 _ _ (705241 / 50000) (282097 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1337568 :
    ThetaLowerSegment 1337568 1339616 (133559322853 / 100000) (133765275563 / 100000) := by
  exact
    tile 1337568 1339616 7 4 146 1156 20 _ _ (282127 / 20000) (705319 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1339616 :
    ThetaLowerSegment 1339616 1341664 (133765275563 / 100000) (133978304551 / 100000) := by
  exact
    tile 1339616 1341664 7 4 151 1157 20 _ _ (352697 / 25000) (1410791 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1341664 :
    ThetaLowerSegment 1341664 1343712 (133978304551 / 100000) (134192767583 / 100000) := by
  exact
    tile 1341664 1343712 7 4 152 1158 20 _ _ (1410941 / 100000) (44092 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1343712 :
    ThetaLowerSegment 1343712 1345760 (134192767583 / 100000) (134390320603 / 100000) := by
  exact
    tile 1343712 1345760 7 4 140 1159 20 _ _ (1411093 / 100000) (176387 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1345760 :
    ThetaLowerSegment 1345760 1347808 (134390320603 / 100000) (134587894903 / 100000) := by
  exact
    tile 1345760 1347808 7 4 140 1160 20 _ _ (282249 / 20000) (88203 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1347808 :
    ThetaLowerSegment 1347808 1349856 (134587894903 / 100000) (26953993049 / 20000) := by
  exact
    tile 1347808 1349856 7 4 129 1160 20 _ _ (705699 / 50000) (1411401 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1349856 :
    ThetaLowerSegment 1349856 1351904 (26953993049 / 20000) (134984520693 / 100000) := by
  exact
    tile 1349856 1351904 7 4 152 1161 20 _ _ (1411549 / 100000) (44111 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1351904 :
    ThetaLowerSegment 1351904 1353952 (134984520693 / 100000) (67591785267 / 50000) := by
  exact
    tile 1351904 1353952 7 4 141 1162 20 _ _ (1411701 / 100000) (176463 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1353952 :
    ThetaLowerSegment 1353952 1356000 (67591785267 / 50000) (67700497871 / 50000) := by
  exact
    tile 1353952 1356000 7 4 154 1163 20 _ _ (352963 / 25000) (282371 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1356000 :
    ThetaLowerSegment 1356000 1358048 (67700497871 / 50000) (2711860563 / 2000) := by
  exact
    tile 1356000 1358048 7 4 136 1164 20 _ _ (1412003 / 100000) (706003 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1358048 :
    ThetaLowerSegment 1358048 1360096 (2711860563 / 2000) (33950153697 / 25000) := by
  exact
    tile 1358048 1360096 7 4 147 1165 20 _ _ (706077 / 50000) (1412157 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1360096 :
    ThetaLowerSegment 1360096 1362144 (33950153697 / 25000) (68003405659 / 50000) := by
  exact
    tile 1360096 1362144 7 4 146 1166 20 _ _ (282461 / 20000) (353077 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1362144 :
    ThetaLowerSegment 1362144 1364192 (68003405659 / 50000) (68108633631 / 50000) := by
  exact
    tile 1362144 1364192 7 4 149 1167 20 _ _ (176557 / 12500) (1412459 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1364192 :
    ThetaLowerSegment 1364192 1366240 (68108633631 / 50000) (8525498067 / 6250) := by
  exact
    tile 1364192 1366240 7 4 135 1167 20 _ _ (706303 / 50000) (1412609 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1366240 :
    ThetaLowerSegment 1366240 1368288 (8525498067 / 6250) (17078191687 / 12500) := by
  exact
    tile 1366240 1368288 7 4 154 1168 20 _ _ (353189 / 25000) (1412759 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1368288 :
    ThetaLowerSegment 1368288 1370336 (17078191687 / 12500) (68415202433 / 50000) := by
  exact
    tile 1368288 1370336 7 4 145 1169 20 _ _ (706453 / 50000) (1412909 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1370336 :
    ThetaLowerSegment 1370336 1372384 (68415202433 / 50000) (68514116283 / 50000) := by
  exact
    tile 1370336 1372384 7 4 140 1170 20 _ _ (282611 / 20000) (706529 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1372384 :
    ThetaLowerSegment 1372384 1374432 (68514116283 / 50000) (68613040563 / 50000) := by
  exact
    tile 1372384 1374432 7 4 140 1171 20 _ _ (353301 / 25000) (1413207 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1374432 :
    ThetaLowerSegment 1374432 1376480 (68613040563 / 50000) (6871974879 / 5000) := by
  exact
    tile 1374432 1376480 7 4 151 1172 20 _ _ (706677 / 50000) (1413357 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1376480 :
    ThetaLowerSegment 1376480 1378528 (6871974879 / 5000) (137655763539 / 100000) := by
  exact
    tile 1376480 1378528 7 4 153 1173 20 _ _ (1413503 / 100000) (706753 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1378528 :
    ThetaLowerSegment 1378528 1380576 (137655763539 / 100000) (137870638491 / 100000) := by
  exact
    tile 1378528 1380576 7 4 152 1174 20 _ _ (1413651 / 100000) (706827 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1380576 :
    ThetaLowerSegment 1380576 1382624 (137870638491 / 100000) (138078467091 / 100000) := by
  exact
    tile 1380576 1382624 7 4 147 1174 20 _ _ (7069 / 500) (1413803 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1382624 :
    ThetaLowerSegment 1382624 1384672 (138078467091 / 100000) (138255210591 / 100000) := by
  exact
    tile 1382624 1384672 7 4 125 1175 20 _ _ (353487 / 25000) (1413951 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1384672 :
    ThetaLowerSegment 1384672 1386720 (138255210591 / 100000) (138477223663 / 100000) := by
  exact
    tile 1384672 1386720 7 4 157 1176 20 _ _ (88381 / 6250) (1414099 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1386720 :
    ThetaLowerSegment 1386720 1388768 (138477223663 / 100000) (138678046311 / 100000) := by
  exact
    tile 1386720 1388768 7 4 142 1177 20 _ _ (353561 / 25000) (1414247 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1388768 :
    ThetaLowerSegment 1388768 1390816 (138678046311 / 100000) (138884547397 / 100000) := by
  exact
    tile 1388768 1390816 7 4 146 1178 20 _ _ (1414391 / 100000) (707197 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1390816 :
    ThetaLowerSegment 1390816 1392864 (138884547397 / 100000) (139074095623 / 100000) := by
  exact
    tile 1390816 1392864 7 4 134 1179 20 _ _ (1414539 / 100000) (707271 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1392864 :
    ThetaLowerSegment 1392864 1394912 (139074095623 / 100000) (139286298523 / 100000) := by
  exact
    tile 1392864 1394912 7 4 150 1180 20 _ _ (707343 / 50000) (1414689 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1394912 :
    ThetaLowerSegment 1394912 1396960 (139286298523 / 100000) (69752798819 / 50000) := by
  exact
    tile 1394912 1396960 7 4 155 1181 20 _ _ (1414833 / 100000) (353709 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1396960 :
    ThetaLowerSegment 1396960 1399008 (69752798819 / 50000) (139730579299 / 100000) := by
  exact
    tile 1396960 1399008 7 4 159 1181 20 _ _ (1414979 / 100000) (707491 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1399008 :
    ThetaLowerSegment 1399008 1403104 (139730579299 / 100000) (140129644831 / 100000) := by
  exact
    tile 1399008 1403104 7 5 282 1182 20 _ _ (707563 / 50000) (1415129 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1403104 :
    ThetaLowerSegment 1403104 1407200 (140129644831 / 100000) (140527377289 / 100000) := by
  exact
    tile 1403104 1407200 7 5 281 1184 20 _ _ (707709 / 50000) (1415421 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1407200 :
    ThetaLowerSegment 1407200 1409248 (140527377289 / 100000) (140735486659 / 100000) := by
  exact
    tile 1407200 1409248 7 4 147 1186 20 _ _ (141571 / 10000) (1415713 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1409248 :
    ThetaLowerSegment 1409248 1411296 (140735486659 / 100000) (140942201489 / 100000) := by
  exact
    tile 1409248 1411296 7 4 146 1187 20 _ _ (283171 / 20000) (707929 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1411296 :
    ThetaLowerSegment 1411296 1413344 (140942201489 / 100000) (141160265489 / 100000) := by
  exact
    tile 1411296 1413344 7 4 154 1187 20 _ _ (354 / 25) (1416003 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1413344 :
    ThetaLowerSegment 1413344 1417440 (141160265489 / 100000) (141528463189 / 100000) := by
  exact
    tile 1413344 1417440 7 5 260 1188 20 _ _ (283229 / 20000) (354037 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1417440 :
    ThetaLowerSegment 1417440 1419488 (141528463189 / 100000) (141721098349 / 100000) := by
  exact
    tile 1417440 1419488 7 4 136 1190 20 _ _ (283287 / 20000) (708219 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1419488 :
    ThetaLowerSegment 1419488 1421536 (141721098349 / 100000) (4435203197 / 3125) := by
  exact
    tile 1419488 1421536 7 4 145 1191 20 _ _ (1416579 / 100000) (708291 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1421536 :
    ThetaLowerSegment 1421536 1423584 (4435203197 / 3125) (71066671931 / 50000) := by
  exact
    tile 1421536 1423584 7 4 146 1192 20 _ _ (1416723 / 100000) (708363 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1423584 :
    ThetaLowerSegment 1423584 1425632 (71066671931 / 50000) (35585051611 / 25000) := by
  exact
    tile 1423584 1425632 7 4 146 1193 20 _ _ (1416867 / 100000) (141687 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1425632 :
    ThetaLowerSegment 1425632 1427680 (35585051611 / 25000) (142559843149 / 100000) := by
  exact
    tile 1425632 1427680 7 4 155 1193 20 _ _ (1417011 / 100000) (708507 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1427680 :
    ThetaLowerSegment 1427680 1429728 (142559843149 / 100000) (71378413847 / 50000) := by
  exact
    tile 1427680 1429728 7 4 139 1194 20 _ _ (283431 / 20000) (708579 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1429728 :
    ThetaLowerSegment 1429728 1431776 (71378413847 / 50000) (14297225699 / 10000) := by
  exact
    tile 1429728 1431776 7 4 152 1195 20 _ _ (708649 / 50000) (1417301 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1431776 :
    ThetaLowerSegment 1431776 1433824 (14297225699 / 10000) (143186290581 / 100000) := by
  exact
    tile 1431776 1433824 7 4 151 1196 20 _ _ (1417441 / 100000) (354361 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1433824 :
    ThetaLowerSegment 1433824 1435872 (143186290581 / 100000) (143401763349 / 100000) := by
  exact
    tile 1433824 1435872 7 4 152 1197 20 _ _ (88599 / 6250) (1417587 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1435872 :
    ThetaLowerSegment 1435872 1439968 (143401763349 / 100000) (143812904179 / 100000) := by
  exact
    tile 1435872 1439968 7 5 290 1198 20 _ _ (1417727 / 100000) (141773 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1439968 :
    ThetaLowerSegment 1439968 1444064 (143812904179 / 100000) (144211365551 / 100000) := by
  exact
    tile 1439968 1444064 7 5 281 1199 20 _ _ (354503 / 25000) (283603 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1444064 :
    ThetaLowerSegment 1444064 1446112 (144211365551 / 100000) (144425528247 / 100000) := by
  exact
    tile 1444064 1446112 7 4 151 1201 20 _ _ (177287 / 12500) (1418299 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1446112 :
    ThetaLowerSegment 1446112 1450208 (144425528247 / 100000) (144831201229 / 100000) := by
  exact
    tile 1446112 1450208 7 5 286 1202 20 _ _ (1418437 / 100000) (35461 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1450208 :
    ThetaLowerSegment 1450208 1454304 (144831201229 / 100000) (145238373869 / 100000) := by
  exact
    tile 1450208 1454304 7 5 287 1204 20 _ _ (8867 / 625) (1418723 / 100000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1454304 :
    ThetaLowerSegment 1454304 1458400 (145238373869 / 100000) (145658398461 / 100000) := by
  exact
    tile 1454304 1458400 7 5 296 1205 20 _ _ (709501 / 50000) (283801 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1458400 :
    ThetaLowerSegment 1458400 1462496 (145658398461 / 100000) (146075667957 / 100000) := by
  exact
    tile 1458400 1462496 7 5 294 1207 20 _ _ (354821 / 25000) (1419287 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462496 :
    ThetaLowerSegment 1462496 1466592 (146075667957 / 100000) (146491600209 / 100000) := by
  exact
    tile 1462496 1466592 7 5 293 1209 20 _ _ (354891 / 25000) (1419567 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1466592 :
    ThetaLowerSegment 1466592 1470688 (146491600209 / 100000) (146879217621 / 100000) := by
  exact
    tile 1466592 1470688 7 5 273 1211 20 _ _ (354961 / 25000) (1419847 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470688 :
    ThetaLowerSegment 1470688 1474784 (146879217621 / 100000) (147291053291 / 100000) := by
  exact
    tile 1470688 1474784 7 5 290 1212 20 _ _ (1420123 / 100000) (710063 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474784 :
    ThetaLowerSegment 1474784 1478880 (147291053291 / 100000) (73849354189 / 50000) := by
  exact
    tile 1474784 1478880 7 5 287 1214 20 _ _ (1420401 / 100000) (355101 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1478880 :
    ThetaLowerSegment 1478880 1482976 (73849354189 / 50000) (9257540609 / 6250) := by
  exact
    tile 1478880 1482976 7 5 297 1216 20 _ _ (710339 / 50000) (1420681 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1482976 :
    ThetaLowerSegment 1482976 1487072 (9257540609 / 6250) (148525621919 / 100000) := by
  exact
    tile 1482976 1487072 7 5 285 1217 21 _ _ (284191 / 20000) (710479 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1487072 :
    ThetaLowerSegment 1487072 1491168 (148525621919 / 100000) (148946305999 / 100000) := by
  exact
    tile 1487072 1491168 7 5 296 1219 21 _ _ (142123 / 10000) (1421233 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1491168 :
    ThetaLowerSegment 1491168 1495264 (148946305999 / 100000) (5974682871 / 4000) := by
  exact
    tile 1491168 1495264 7 5 296 1221 21 _ _ (710753 / 50000) (1421509 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1495264 :
    ThetaLowerSegment 1495264 1499360 (5974682871 / 4000) (29953602747 / 20000) := by
  exact
    tile 1495264 1499360 7 5 282 1222 21 _ _ (71089 / 5000) (1421783 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1499360 :
    ThetaLowerSegment 1499360 1503456 (29953602747 / 20000) (37544746763 / 25000) := by
  exact
    tile 1499360 1503456 7 5 289 1224 21 _ _ (1422053 / 100000) (177757 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1503456 :
    ThetaLowerSegment 1503456 1507552 (37544746763 / 25000) (37652843539 / 25000) := by
  exact
    tile 1503456 1507552 7 5 304 1226 21 _ _ (711163 / 50000) (1422329 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1507552 :
    ThetaLowerSegment 1507552 1511648 (37652843539 / 25000) (9439351123 / 6250) := by
  exact
    tile 1507552 1511648 7 5 294 1227 21 _ _ (711299 / 50000) (1422601 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1511648 :
    ThetaLowerSegment 1511648 1515744 (9439351123 / 6250) (37857716827 / 25000) := by
  exact
    tile 1511648 1515744 7 5 282 1229 21 _ _ (142287 / 10000) (1422873 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1515744 :
    ThetaLowerSegment 1515744 1519840 (37857716827 / 25000) (37960894477 / 25000) := by
  exact
    tile 1515744 1519840 7 5 290 1231 21 _ _ (71157 / 5000) (1423143 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1519840 :
    ThetaLowerSegment 1519840 1523936 (37960894477 / 25000) (19029199031 / 12500) := by
  exact
    tile 1519840 1523936 7 5 274 1232 21 _ _ (142341 / 10000) (1423413 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1523936 :
    ThetaLowerSegment 1523936 1528032 (19029199031 / 12500) (76323229579 / 50000) := by
  exact
    tile 1523936 1528032 7 5 290 1234 21 _ _ (1423679 / 100000) (711841 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1528032 :
    ThetaLowerSegment 1528032 1532128 (76323229579 / 50000) (76517598481 / 50000) := by
  exact
    tile 1528032 1532128 7 5 273 1236 21 _ _ (355987 / 25000) (1423951 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1532128 :
    ThetaLowerSegment 1532128 1536224 (76517598481 / 50000) (153443946667 / 100000) := by
  exact
    tile 1532128 1536224 7 5 287 1237 21 _ _ (284843 / 20000) (712109 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1536224 :
    ThetaLowerSegment 1536224 1540320 (153443946667 / 100000) (153852773001 / 100000) := by
  exact
    tile 1536224 1540320 7 5 287 1239 21 _ _ (712241 / 50000) (284897 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1540320 :
    ThetaLowerSegment 1540320 1544416 (153852773001 / 100000) (154240304729 / 100000) := by
  exact
    tile 1540320 1544416 7 5 272 1241 21 _ _ (1424749 / 100000) (89047 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1544416 :
    ThetaLowerSegment 1544416 1548512 (154240304729 / 100000) (154660683859 / 100000) := by
  exact
    tile 1544416 1548512 7 5 295 1242 21 _ _ (712507 / 50000) (1425017 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1548512 :
    ThetaLowerSegment 1548512 1552608 (154660683859 / 100000) (38767434733 / 25000) := by
  exact
    tile 1548512 1552608 7 5 287 1244 21 _ _ (1425279 / 100000) (712641 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552608 :
    ThetaLowerSegment 1552608 1556704 (38767434733 / 25000) (155487423031 / 100000) := by
  exact
    tile 1552608 1556704 7 5 293 1246 21 _ _ (1425543 / 100000) (712773 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1556704 :
    ThetaLowerSegment 1556704 1560800 (155487423031 / 100000) (77952592241 / 50000) := by
  exact
    tile 1556704 1560800 7 5 293 1247 21 _ _ (1425807 / 100000) (142581 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560800 :
    ThetaLowerSegment 1560800 1564896 (77952592241 / 50000) (156294501319 / 100000) := by
  exact
    tile 1560800 1564896 7 5 273 1249 21 _ _ (1426069 / 100000) (178259 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1564896 :
    ThetaLowerSegment 1564896 1568992 (156294501319 / 100000) (4896817281 / 3125) := by
  exact
    tile 1564896 1568992 7 5 283 1250 21 _ _ (1426331 / 100000) (713167 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568992 :
    ThetaLowerSegment 1568992 1573088 (4896817281 / 3125) (157121851113 / 100000) := by
  exact
    tile 1568992 1573088 7 5 297 1252 21 _ _ (1426593 / 100000) (356649 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1573088 :
    ThetaLowerSegment 1573088 1577184 (157121851113 / 100000) (31505130159 / 20000) := by
  exact
    tile 1573088 1577184 7 5 283 1254 21 _ _ (713427 / 50000) (1426857 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577184 :
    ThetaLowerSegment 1577184 1581280 (31505130159 / 20000) (157929524057 / 100000) := by
  exact
    tile 1577184 1581280 7 5 283 1255 21 _ _ (713557 / 50000) (1427117 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1581280 :
    ThetaLowerSegment 1581280 1585376 (157929524057 / 100000) (31664695801 / 20000) := by
  exact
    tile 1581280 1585376 7 5 276 1257 21 _ _ (1427373 / 100000) (89211 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1585376 :
    ThetaLowerSegment 1585376 1589472 (31664695801 / 20000) (1269842833 / 800) := by
  exact
    tile 1585376 1589472 7 5 285 1259 21 _ _ (89227 / 6250) (285527 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1589472 :
    ThetaLowerSegment 1589472 1593568 (1269842833 / 800) (31824319197 / 20000) := by
  exact
    tile 1589472 1593568 7 5 274 1260 21 _ _ (142789 / 10000) (1427893 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1593568 :
    ThetaLowerSegment 1593568 1595616 (31824319197 / 20000) (4979199684 / 3125) := by
  exact
    tile 1593568 1595616 7 4 149 1262 21 _ _ (1428147 / 100000) (28563 / 2000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1595616 :
    ThetaLowerSegment 1595616 1597664 (4979199684 / 3125) (19941436497 / 12500) := by
  exact
    tile 1595616 1597664 7 4 138 1263 21 _ _ (357069 / 25000) (1428279 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1597664 :
    ThetaLowerSegment 1597664 1599712 (19941436497 / 12500) (7986644847 / 5000) := by
  exact
    tile 1597664 1599712 7 4 141 1263 21 _ _ (357101 / 25000) (1428407 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1599712 :
    ThetaLowerSegment 1599712 1601760 (7986644847 / 5000) (7997358837 / 5000) := by
  exact
    tile 1599712 1601760 7 4 150 1264 21 _ _ (357133 / 25000) (285707 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1601760 :
    ThetaLowerSegment 1601760 1603808 (7997358837 / 5000) (4004286909 / 2500) := by
  exact
    tile 1601760 1603808 7 4 157 1265 21 _ _ (71433 / 5000) (1428663 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1603808 :
    ThetaLowerSegment 1603808 1607904 (4004286909 / 2500) (40146813417 / 25000) := by
  exact
    tile 1603808 1607904 7 5 291 1266 21 _ _ (357197 / 25000) (1428791 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1607904 :
    ThetaLowerSegment 1607904 1612000 (40146813417 / 25000) (160988814751 / 100000) := by
  exact
    tile 1607904 1612000 7 5 281 1268 21 _ _ (1429043 / 100000) (714523 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1612000 :
    ThetaLowerSegment 1612000 1616096 (160988814751 / 100000) (161383300723 / 100000) := by
  exact
    tile 1612000 1616096 7 5 276 1269 21 _ _ (1429297 / 100000) (14293 / 1000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616096 :
    ThetaLowerSegment 1616096 1618144 (161383300723 / 100000) (161583437863 / 100000) := by
  exact
    tile 1616096 1618144 7 4 140 1271 21 _ _ (1429551 / 100000) (714777 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1618144 :
    ThetaLowerSegment 1618144 1620192 (161583437863 / 100000) (161787881817 / 100000) := by
  exact
    tile 1618144 1620192 7 4 143 1272 21 _ _ (714839 / 50000) (1429681 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1620192 :
    ThetaLowerSegment 1620192 1622240 (161787881817 / 100000) (161996633201 / 100000) := by
  exact
    tile 1620192 1622240 7 4 146 1272 21 _ _ (357451 / 25000) (1429807 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622240 :
    ThetaLowerSegment 1622240 1624288 (161996633201 / 100000) (162199683261 / 100000) := by
  exact
    tile 1622240 1624288 7 4 142 1273 21 _ _ (142993 / 10000) (1429933 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624288 :
    ThetaLowerSegment 1624288 1626336 (162199683261 / 100000) (40603905467 / 25000) := by
  exact
    tile 1624288 1626336 7 4 151 1274 21 _ _ (1430057 / 100000) (71503 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1626336 :
    ThetaLowerSegment 1626336 1630432 (40603905467 / 25000) (16283609567 / 10000) := by
  exact
    tile 1626336 1630432 7 5 294 1275 21 _ _ (1430183 / 100000) (715093 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630432 :
    ThetaLowerSegment 1630432 1634528 (16283609567 / 10000) (81629752067 / 50000) := by
  exact
    tile 1630432 1634528 7 5 296 1276 21 _ _ (715217 / 50000) (1430437 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1634528 :
    ThetaLowerSegment 1634528 1638624 (81629752067 / 50000) (81824325227 / 50000) := by
  exact
    tile 1634528 1638624 7 5 272 1278 21 _ _ (286137 / 20000) (44709 / 3125) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1638624 :
    ThetaLowerSegment 1638624 1642720 (81824325227 / 50000) (164039295709 / 100000) := by
  exact
    tile 1638624 1642720 7 5 273 1280 21 _ _ (286187 / 20000) (715469 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1642720 :
    ThetaLowerSegment 1642720 1644768 (164039295709 / 100000) (164251111089 / 100000) := by
  exact
    tile 1642720 1644768 7 4 148 1281 21 _ _ (286237 / 20000) (357797 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1644768 :
    ThetaLowerSegment 1644768 1648864 (164251111089 / 100000) (1646504463 / 1000) := by
  exact
    tile 1644768 1648864 7 5 279 1282 21 _ _ (1431309 / 100000) (89457 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1648864 :
    ThetaLowerSegment 1648864 1650912 (1646504463 / 1000) (82433305779 / 50000) := by
  exact
    tile 1648864 1650912 7 4 151 1284 21 _ _ (715779 / 50000) (1431561 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1650912 :
    ThetaLowerSegment 1650912 1655008 (82433305779 / 50000) (82639467987 / 50000) := by
  exact
    tile 1650912 1655008 7 5 288 1284 21 _ _ (715841 / 50000) (286337 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1655008 :
    ThetaLowerSegment 1655008 1659104 (82639467987 / 50000) (41422474971 / 25000) := by
  exact
    tile 1655008 1659104 7 5 287 1286 21 _ _ (143193 / 10000) (1431933 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1659104 :
    ThetaLowerSegment 1659104 1663200 (41422474971 / 25000) (83046886899 / 50000) := by
  exact
    tile 1659104 1663200 7 5 282 1288 21 _ _ (1432177 / 100000) (71609 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1663200 :
    ThetaLowerSegment 1663200 1667296 (83046886899 / 50000) (83248858683 / 50000) := by
  exact
    tile 1663200 1667296 7 5 282 1289 21 _ _ (179053 / 12500) (1432427 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1667296 :
    ThetaLowerSegment 1667296 1671392 (83248858683 / 50000) (20866477047 / 12500) := by
  exact
    tile 1667296 1671392 7 5 303 1291 21 _ _ (143267 / 10000) (1432673 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1671392 :
    ThetaLowerSegment 1671392 1675488 (20866477047 / 12500) (167340197151 / 100000) := by
  exact
    tile 1671392 1675488 7 5 285 1292 21 _ _ (286583 / 20000) (716459 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1675488 :
    ThetaLowerSegment 1675488 1679584 (167340197151 / 100000) (167761546191 / 100000) := by
  exact
    tile 1675488 1679584 7 5 294 1294 21 _ _ (35829 / 2500) (1433163 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1679584 :
    ThetaLowerSegment 1679584 1683680 (167761546191 / 100000) (168160032503 / 100000) := by
  exact
    tile 1679584 1683680 7 5 278 1295 21 _ _ (358351 / 25000) (1433407 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1683680 :
    ThetaLowerSegment 1683680 1687776 (168160032503 / 100000) (168562887591 / 100000) := by
  exact
    tile 1683680 1687776 7 5 281 1297 21 _ _ (89603 / 6250) (1433651 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1687776 :
    ThetaLowerSegment 1687776 1691872 (168562887591 / 100000) (168967244853 / 100000) := by
  exact
    tile 1687776 1691872 7 5 282 1299 21 _ _ (1433891 / 100000) (716947 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1691872 :
    ThetaLowerSegment 1691872 1695968 (168967244853 / 100000) (42343276123 / 25000) := by
  exact
    tile 1691872 1695968 7 5 283 1300 21 _ _ (1434133 / 100000) (179267 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1695968 :
    ThetaLowerSegment 1695968 1700064 (42343276123 / 25000) (84900274121 / 50000) := by
  exact
    tile 1695968 1700064 7 5 298 1302 21 _ _ (459 / 32) (717189 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1700064 :
    ThetaLowerSegment 1700064 1704160 (84900274121 / 50000) (85102554977 / 50000) := by
  exact
    tile 1700064 1704160 7 5 282 1303 21 _ _ (179327 / 12500) (1434619 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1704160 :
    ThetaLowerSegment 1704160 1708256 (85102554977 / 50000) (10663467441 / 6250) := by
  exact
    tile 1704160 1708256 7 5 286 1305 21 _ _ (1434857 / 100000) (71743 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1708256 :
    ThetaLowerSegment 1708256 1712352 (10663467441 / 6250) (85512958399 / 50000) := by
  exact
    tile 1708256 1712352 7 5 286 1307 21 _ _ (1435097 / 100000) (14351 / 1000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1712352 :
    ThetaLowerSegment 1712352 1716448 (85512958399 / 50000) (85716058443 / 50000) := by
  exact
    tile 1712352 1716448 7 5 283 1308 21 _ _ (179417 / 12500) (1435339 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1716448 :
    ThetaLowerSegment 1716448 1720544 (85716058443 / 50000) (85917038943 / 50000) := by
  exact
    tile 1716448 1720544 7 5 280 1310 21 _ _ (57423 / 4000) (717789 / 50000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1720544 :
    ThetaLowerSegment 1720544 1724640 (85917038943 / 50000) (86112309647 / 50000) := by
  exact
    tile 1720544 1724640 7 5 272 1311 21 _ _ (717907 / 50000) (1435817 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1724640 :
    ThetaLowerSegment 1724640 1728736 (86112309647 / 50000) (172636765931 / 100000) := by
  exact
    tile 1724640 1728736 7 5 287 1313 21 _ _ (1436051 / 100000) (718027 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1728736 :
    ThetaLowerSegment 1728736 1732832 (172636765931 / 100000) (86518745281 / 50000) := by
  exact
    tile 1728736 1732832 7 5 279 1314 21 _ _ (1436289 / 100000) (359073 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1732832 :
    ThetaLowerSegment 1732832 1736928 (86518745281 / 50000) (173441154087 / 100000) := by
  exact
    tile 1732832 1736928 7 5 281 1316 21 _ _ (57461 / 4000) (89783 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1736928 :
    ThetaLowerSegment 1736928 1738976 (173441154087 / 100000) (17364661091 / 10000) := by
  exact
    tile 1736928 1738976 7 4 143 1317 21 _ _ (1436761 / 100000) (359191 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1738976 :
    ThetaLowerSegment 1738976 1741024 (17364661091 / 10000) (4346553569 / 2500) := by
  exact
    tile 1738976 1741024 7 4 150 1318 21 _ _ (1436879 / 100000) (718441 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1741024 :
    ThetaLowerSegment 1741024 1745120 (4346553569 / 2500) (174251568947 / 100000) := by
  exact
    tile 1741024 1745120 7 5 271 1319 21 _ _ (1436997 / 100000) (1437 / 100) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1745120 :
    ThetaLowerSegment 1745120 1747168 (174251568947 / 100000) (174474339907 / 100000) := by
  exact
    tile 1745120 1747168 7 4 155 1321 21 _ _ (89827 / 6250) (287447 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1747168 :
    ThetaLowerSegment 1747168 1751264 (174474339907 / 100000) (174902669909 / 100000) := by
  exact
    tile 1747168 1751264 7 5 298 1321 21 _ _ (1437349 / 100000) (179669 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1751264 :
    ThetaLowerSegment 1751264 1755360 (174902669909 / 100000) (175316693813 / 100000) := by
  exact
    tile 1751264 1755360 7 5 288 1323 21 _ _ (1437583 / 100000) (718793 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1755360 :
    ThetaLowerSegment 1755360 1759456 (175316693813 / 100000) (87854608927 / 50000) := by
  exact
    tile 1755360 1759456 7 5 273 1324 21 _ _ (1437817 / 100000) (71891 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1759456 :
    ThetaLowerSegment 1759456 1763552 (87854608927 / 50000) (22010568613 / 12500) := by
  exact
    tile 1759456 1763552 7 5 261 1326 21 _ _ (28761 / 2000) (1438053 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1763552 :
    ThetaLowerSegment 1763552 1765600 (22010568613 / 12500) (44071477131 / 25000) := by
  exact
    tile 1763552 1765600 7 4 140 1327 21 _ _ (1438283 / 100000) (719143 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1765600 :
    ThetaLowerSegment 1765600 1767648 (44071477131 / 25000) (176497353177 / 100000) := by
  exact
    tile 1765600 1767648 7 4 147 1328 21 _ _ (1438399 / 100000) (719201 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1767648 :
    ThetaLowerSegment 1767648 1769696 (176497353177 / 100000) (88351530411 / 50000) := by
  exact
    tile 1767648 1769696 7 4 143 1329 21 _ _ (287703 / 20000) (719259 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1769696 :
    ThetaLowerSegment 1769696 1771744 (88351530411 / 50000) (44226476913 / 25000) := by
  exact
    tile 1769696 1771744 7 4 141 1330 21 _ _ (143863 / 10000) (1438633 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1771744 :
    ThetaLowerSegment 1771744 1773792 (44226476913 / 25000) (11069388099 / 6250) := by
  exact
    tile 1771744 1773792 7 4 142 1331 21 _ _ (719373 / 50000) (1438749 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1773792 :
    ThetaLowerSegment 1773792 1775840 (11069388099 / 6250) (88660861149 / 50000) := by
  exact
    tile 1773792 1775840 7 4 147 1331 21 _ _ (719431 / 50000) (287773 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1775840 :
    ThetaLowerSegment 1775840 1777888 (88660861149 / 50000) (17751742317 / 10000) := by
  exact
    tile 1775840 1777888 7 4 136 1332 21 _ _ (1438977 / 100000) (71949 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1777888 :
    ThetaLowerSegment 1777888 1779936 (17751742317 / 10000) (88868082577 / 50000) := by
  exact
    tile 1777888 1779936 7 4 152 1333 21 _ _ (359773 / 25000) (287819 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1779936 :
    ThetaLowerSegment 1779936 1781984 (88868082577 / 50000) (177950606997 / 100000) := by
  exact
    tile 1779936 1781984 7 4 149 1334 21 _ _ (1439207 / 100000) (143921 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1781984 :
    ThetaLowerSegment 1781984 1786080 (177950606997 / 100000) (178349299191 / 100000) := by
  exact
    tile 1781984 1786080 7 5 277 1334 21 _ _ (719661 / 50000) (57573 / 4000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1786080 :
    ThetaLowerSegment 1786080 1788128 (178349299191 / 100000) (178558034231 / 100000) := by
  exact
    tile 1786080 1788128 7 4 145 1336 21 _ _ (44986 / 3125) (287911 / 20000) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1788128 :
    ThetaLowerSegment 1788128 1792224 (178558034231 / 100000) (286347039 / 160) := by
  exact
    tile 1788128 1792224 7 5 284 1337 21 _ _ (719833 / 50000) (1439669 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1792224 :
    ThetaLowerSegment 1792224 1796320 (286347039 / 160) (35877469743 / 20000) := by
  exact
    tile 1792224 1796320 7 5 292 1338 21 _ _ (287979 / 20000) (719949 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1796320 :
    ThetaLowerSegment 1796320 1800416 (35877469743 / 20000) (179802104427 / 100000) := by
  exact
    tile 1796320 1800416 7 5 288 1340 21 _ _ (360031 / 25000) (1440127 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1800416 :
    ThetaLowerSegment 1800416 1804512 (179802104427 / 100000) (180196760601 / 100000) := by
  exact
    tile 1800416 1804512 7 5 274 1341 21 _ _ (1440351 / 100000) (720177 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1804512 :
    ThetaLowerSegment 1804512 1808608 (180196760601 / 100000) (180620290827 / 100000) := by
  exact
    tile 1804512 1808608 7 5 294 1343 21 _ _ (1440579 / 100000) (720291 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1808608 :
    ThetaLowerSegment 1808608 1812704 (180620290827 / 100000) (181038124277 / 100000) := by
  exact
    tile 1808608 1812704 7 5 290 1344 21 _ _ (288161 / 20000) (180101 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1812704 :
    ThetaLowerSegment 1812704 1816800 (181038124277 / 100000) (181443054269 / 100000) := by
  exact
    tile 1812704 1816800 7 5 281 1346 21 _ _ (180129 / 12500) (288207 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1816800 :
    ThetaLowerSegment 1816800 1820896 (181443054269 / 100000) (181840841201 / 100000) := by
  exact
    tile 1816800 1820896 7 5 276 1347 21 _ _ (1441257 / 100000) (72063 / 5000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1820896 :
    ThetaLowerSegment 1820896 1824992 (181840841201 / 100000) (182264636909 / 100000) := by
  exact
    tile 1820896 1824992 7 5 294 1349 21 _ _ (720741 / 50000) (288297 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1824992 :
    ThetaLowerSegment 1824992 1829088 (182264636909 / 100000) (182682731939 / 100000) := by
  exact
    tile 1824992 1829088 7 5 290 1350 21 _ _ (1441707 / 100000) (144171 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1829088 :
    ThetaLowerSegment 1829088 1833184 (182682731939 / 100000) (91552608861 / 50000) := by
  exact
    tile 1829088 1833184 7 5 293 1352 21 _ _ (1441931 / 100000) (720967 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1833184 :
    ThetaLowerSegment 1833184 1837280 (91552608861 / 50000) (183490273107 / 100000) := by
  exact
    tile 1833184 1837280 7 5 267 1353 21 _ _ (288431 / 20000) (721079 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1837280 :
    ThetaLowerSegment 1837280 1841376 (183490273107 / 100000) (183878272789 / 100000) := by
  exact
    tile 1837280 1841376 7 5 269 1355 21 _ _ (721189 / 50000) (1442381 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1841376 :
    ThetaLowerSegment 1841376 1845472 (183878272789 / 100000) (46075960021 / 25000) := by
  exact
    tile 1841376 1845472 7 5 295 1356 21 _ _ (1442601 / 100000) (360651 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1845472 :
    ThetaLowerSegment 1845472 1849568 (46075960021 / 25000) (184720815931 / 100000) := by
  exact
    tile 1845472 1849568 7 5 289 1358 21 _ _ (1442823 / 100000) (721413 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1849568 :
    ThetaLowerSegment 1849568 1853664 (184720815931 / 100000) (185124868531 / 100000) := by
  exact
    tile 1849568 1853664 7 5 280 1359 21 _ _ (288609 / 20000) (180381 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1853664 :
    ThetaLowerSegment 1853664 1857760 (185124868531 / 100000) (185553518533 / 100000) := by
  exact
    tile 1853664 1857760 7 5 297 1361 21 _ _ (721633 / 50000) (1443269 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1857760 :
    ThetaLowerSegment 1857760 1861856 (185553518533 / 100000) (37193271163 / 20000) := by
  exact
    tile 1857760 1861856 7 5 286 1362 21 _ _ (1443487 / 100000) (144349 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1861856 :
    ThetaLowerSegment 1861856 1865952 (37193271163 / 20000) (186390805673 / 100000) := by
  exact
    tile 1861856 1865952 7 5 294 1364 21 _ _ (1443707 / 100000) (144371 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1865952 :
    ThetaLowerSegment 1865952 1870048 (186390805673 / 100000) (186797993087 / 100000) := by
  exact
    tile 1865952 1870048 7 5 282 1365 21 _ _ (1443927 / 100000) (144393 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1870048 :
    ThetaLowerSegment 1870048 1874144 (186797993087 / 100000) (187202353967 / 100000) := by
  exact
    tile 1870048 1874144 7 5 280 1367 21 _ _ (722073 / 50000) (1444149 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1874144 :
    ThetaLowerSegment 1874144 1878240 (187202353967 / 100000) (187621219817 / 100000) := by
  exact
    tile 1874144 1878240 7 5 290 1368 21 _ _ (288873 / 20000) (90273 / 6250) (by decide) (by decide)
      (by decide) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

private theorem cell1878240 :
    ThetaLowerSegment 1878240 1882336 (187621219817 / 100000) (188040148887 / 100000) := by
  exact
    tile 1878240 1882336 7 5 290 1370 21 _ _ (1444583 / 100000) (722293 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1882336 :
    ThetaLowerSegment 1882336 1886432 (188040148887 / 100000) (188438913963 / 100000) := by
  exact
    tile 1882336 1886432 7 5 276 1371 21 _ _ (1444801 / 100000) (361201 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1886432 :
    ThetaLowerSegment 1886432 1890528 (188438913963 / 100000) (188857969183 / 100000) := by
  exact
    tile 1886432 1890528 7 5 290 1373 21 _ _ (722509 / 50000) (1445021 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1890528 :
    ThetaLowerSegment 1890528 1894624 (188857969183 / 100000) (94634930579 / 50000) := by
  exact
    tile 1890528 1894624 7 5 285 1374 21 _ _ (289047 / 20000) (722619 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1894624 :
    ThetaLowerSegment 1894624 1898720 (94634930579 / 50000) (94839462037 / 50000) := by
  exact
    tile 1894624 1898720 7 5 283 1376 21 _ _ (361363 / 25000) (289091 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1898720 :
    ThetaLowerSegment 1898720 1902816 (94839462037 / 50000) (19006491743 / 10000) := by
  exact
    tile 1898720 1902816 7 5 267 1377 21 _ _ (361417 / 25000) (1445671 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1902816 :
    ThetaLowerSegment 1902816 1906912 (19006491743 / 10000) (19046976467 / 10000) := by
  exact
    tile 1902816 1906912 7 5 280 1379 21 _ _ (1445883 / 100000) (722943 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1906912 :
    ThetaLowerSegment 1906912 1911008 (19046976467 / 10000) (95446012643 / 50000) := by
  exact
    tile 1906912 1911008 7 5 292 1380 21 _ _ (723049 / 50000) (1446101 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1911008 :
    ThetaLowerSegment 1911008 1915104 (95446012643 / 50000) (191312902369 / 100000) := by
  exact
    tile 1911008 1915104 7 5 291 1382 21 _ _ (1446313 / 100000) (361579 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1915104 :
    ThetaLowerSegment 1915104 1919200 (191312902369 / 100000) (191726609091 / 100000) := by
  exact
    tile 1915104 1919200 7 5 286 1383 21 _ _ (1446527 / 100000) (144653 / 10000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1919200 :
    ThetaLowerSegment 1919200 1923296 (191726609091 / 100000) (192131696291 / 100000) := by
  exact
    tile 1919200 1923296 7 5 280 1385 21 _ _ (72337 / 5000) (1446743 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1923296 :
    ThetaLowerSegment 1923296 1927392 (192131696291 / 100000) (38510551981 / 20000) := by
  exact
    tile 1923296 1927392 7 5 291 1386 21 _ _ (723477 / 50000) (1446957 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1927392 :
    ThetaLowerSegment 1927392 1931488 (38510551981 / 20000) (192970990879 / 100000) := by
  exact
    tile 1927392 1931488 7 5 289 1388 21 _ _ (723583 / 50000) (1447169 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1931488 :
    ThetaLowerSegment 1931488 1935584 (192970990879 / 100000) (7734702909 / 4000) := by
  exact
    tile 1931488 1935584 7 5 274 1389 21 _ _ (1447379 / 100000) (723691 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1935584 :
    ThetaLowerSegment 1935584 1939680 (7734702909 / 4000) (38756606211 / 20000) := by
  exact
    tile 1935584 1939680 7 5 287 1391 21 _ _ (144759 / 10000) (1447593 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1939680 :
    ThetaLowerSegment 1939680 1943776 (38756606211 / 20000) (194201445833 / 100000) := by
  exact
    tile 1939680 1943776 7 5 289 1392 21 _ _ (723901 / 50000) (289561 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1943776 :
    ThetaLowerSegment 1943776 1947872 (194201445833 / 100000) (12163926101 / 6250) := by
  exact
    tile 1943776 1947872 7 5 291 1394 21 _ _ (1448013 / 100000) (90501 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1947872 :
    ThetaLowerSegment 1947872 1951968 (12163926101 / 6250) (97506918913 / 50000) := by
  exact
    tile 1947872 1951968 7 5 270 1395 21 _ _ (1448223 / 100000) (724113 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1951968 :
    ThetaLowerSegment 1951968 1956064 (97506918913 / 50000) (97718390131 / 50000) := by
  exact
    tile 1951968 1956064 7 5 292 1397 21 _ _ (1448433 / 100000) (362109 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1956064 :
    ThetaLowerSegment 1956064 1960160 (97718390131 / 50000) (195826465229 / 100000) := by
  exact
    tile 1956064 1960160 7 5 269 1398 21 _ _ (1448643 / 100000) (724323 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1960160 :
    ThetaLowerSegment 1960160 1964256 (195826465229 / 100000) (196242285753 / 100000) := by
  exact
    tile 1960160 1964256 7 5 287 1400 21 _ _ (362213 / 25000) (289771 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1964256 :
    ThetaLowerSegment 1964256 1968352 (196242285753 / 100000) (39327286069 / 20000) := by
  exact
    tile 1964256 1968352 7 5 272 1401 21 _ _ (1449061 / 100000) (181133 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968352 :
    ThetaLowerSegment 1968352 1972448 (39327286069 / 20000) (49254397023 / 25000) := by
  exact
    tile 1968352 1972448 7 5 263 1402 21 _ _ (1449269 / 100000) (181159 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1972448 :
    ThetaLowerSegment 1972448 1976544 (49254397023 / 25000) (9870012501 / 5000) := by
  exact
    tile 1972448 1976544 7 5 264 1404 21 _ _ (1449477 / 100000) (36237 / 2500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976544 :
    ThetaLowerSegment 1976544 1980640 (9870012501 / 5000) (9891467839 / 5000) := by
  exact
    tile 1976544 1980640 7 5 296 1405 21 _ _ (289937 / 20000) (181211 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1980640 :
    ThetaLowerSegment 1980640 1984736 (9891467839 / 5000) (9912491273 / 5000) := by
  exact
    tile 1980640 1984736 7 5 290 1407 21 _ _ (362473 / 25000) (289979 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984736 :
    ThetaLowerSegment 1984736 1988832 (9912491273 / 5000) (24832344137 / 12500) := by
  exact
    tile 1984736 1988832 7 5 282 1408 21 _ _ (725049 / 50000) (1450101 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988832 :
    ThetaLowerSegment 1988832 1992928 (24832344137 / 12500) (24883467353 / 12500) := by
  exact
    tile 1988832 1992928 7 5 282 1410 21 _ _ (45322 / 3125) (1450307 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992928 :
    ThetaLowerSegment 1992928 1997024 (24883467353 / 12500) (24935685713 / 12500) := by
  exact
    tile 1992928 1997024 7 5 288 1411 21 _ _ (145051 / 10000) (1450513 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1997024 :
    ThetaLowerSegment 1997024 1999072 (24935685713 / 12500) (199707445099 / 100000) := by
  exact
    tile 1997024 1999072 7 4 153 1413 21 _ _ (290143 / 20000) (725359 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999072 :
    ThetaLowerSegment 1999072 1999584 (199707445099 / 100000) (199755322093 / 100000) := by
  exact
    tile 1999072 1999584 7 2 33 1413 21 _ _ (725409 / 50000) (1450821 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999584 :
    ThetaLowerSegment 1999584 1999840 (199755322093 / 100000) (24972498303 / 12500) := by
  exact
    tile 1999584 1999840 7 1 17 1414 21 _ _ (1450843 / 100000) (725423 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999840 :
    ThetaLowerSegment 1999840 1999968 (24972498303 / 12500) (12486883901 / 6250) := by
  exact
    tile 1999840 1999968 7 0 7 1414 21 _ _ (181357 / 12500) (1450859 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1999968 :
    ThetaLowerSegment 1999968 2000000 (12486883901 / 6250) (39958899001 / 20000) := by
  exact
    tile 1999968 2000000 5 0 3 1414 21 _ _ (1450863 / 100000) (725433 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1100000_2000000 :
    ThetaLowerSegment 1100000 2000000 (54897473521 / 50000) (39958899001 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1100000 cell1102048)
                    (ThetaLowerSegment.join cell1104096 cell1106144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1108192 cell1110240)
                    (ThetaLowerSegment.join cell1112288 cell1114336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1116384 cell1118432)
                    (ThetaLowerSegment.join cell1120480 cell1122528))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1124576 cell1126624)
                    (ThetaLowerSegment.join cell1128672 cell1130720))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1132768 cell1134816)
                    (ThetaLowerSegment.join cell1136864 cell1138912))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1140960 cell1143008)
                    (ThetaLowerSegment.join cell1145056 cell1147104)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1149152 cell1151200)
                    (ThetaLowerSegment.join cell1153248 cell1155296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1157344 cell1159392)
                    (ThetaLowerSegment.join cell1161440 cell1163488)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1165536 cell1167584)
                    (ThetaLowerSegment.join cell1169632 cell1171680))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1173728 cell1175776)
                    (ThetaLowerSegment.join cell1177824 cell1179872)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1181920 cell1183968)
                    (ThetaLowerSegment.join cell1186016 cell1190112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1194208 cell1198304)
                    (ThetaLowerSegment.join cell1202400 cell1206496))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1208544 cell1210592)
                    (ThetaLowerSegment.join cell1212640 cell1214688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1216736 cell1218784)
                    (ThetaLowerSegment.join cell1220832 cell1222880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1224928 cell1226976)
                    (ThetaLowerSegment.join cell1229024 cell1231072))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1233120 cell1235168)
                    (ThetaLowerSegment.join cell1237216 cell1239264))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1241312 cell1243360)
                    (ThetaLowerSegment.join cell1245408 cell1247456))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1249504 cell1251552)
                    (ThetaLowerSegment.join cell1253600 cell1255648)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1257696 cell1259744)
                    (ThetaLowerSegment.join cell1261792 cell1263840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1265888 cell1267936)
                    (ThetaLowerSegment.join cell1269984 cell1272032))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1276128 cell1278176)
                    (ThetaLowerSegment.join cell1280224 cell1282272))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1284320 cell1286368)
                    (ThetaLowerSegment.join cell1288416 cell1292512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1294560 cell1296608)
                    (ThetaLowerSegment.join cell1298656 cell1300704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1302752 cell1304800)
                    (ThetaLowerSegment.join cell1306848 cell1308896)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1310944 cell1312992)
                    (ThetaLowerSegment.join cell1315040 cell1317088))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1319136 cell1321184)
                    (ThetaLowerSegment.join cell1323232 cell1325280)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1327328 cell1329376)
                    (ThetaLowerSegment.join cell1331424 cell1333472))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1335520 cell1337568)
                    (ThetaLowerSegment.join cell1339616 cell1341664))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1343712 cell1345760)
                    (ThetaLowerSegment.join cell1347808 cell1349856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1351904 cell1353952)
                    (ThetaLowerSegment.join cell1356000 cell1358048)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1360096 cell1362144)
                    (ThetaLowerSegment.join cell1364192 cell1366240))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1368288 cell1370336)
                    (ThetaLowerSegment.join cell1372384 cell1374432)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1376480 cell1378528)
                    (ThetaLowerSegment.join cell1380576 cell1382624))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1384672 cell1386720)
                    (ThetaLowerSegment.join cell1388768 cell1390816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1392864 cell1394912)
                    (ThetaLowerSegment.join cell1396960 cell1399008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1403104 cell1407200)
                    (ThetaLowerSegment.join cell1409248 cell1411296))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1413344 cell1417440)
                    (ThetaLowerSegment.join cell1419488 cell1421536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1423584 cell1425632)
                    (ThetaLowerSegment.join cell1427680 cell1429728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1431776 cell1433824)
                    (ThetaLowerSegment.join cell1435872 cell1439968))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1444064 cell1446112)
                    (ThetaLowerSegment.join cell1450208 cell1454304)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1458400 cell1462496)
                    (ThetaLowerSegment.join cell1466592 cell1470688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1474784 cell1478880)
                    (ThetaLowerSegment.join cell1482976 cell1487072)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1491168 cell1495264)
                    (ThetaLowerSegment.join cell1499360 cell1503456))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1507552 cell1511648)
                    (ThetaLowerSegment.join cell1515744 cell1519840))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1523936 cell1528032)
                    (ThetaLowerSegment.join cell1532128 cell1536224))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1540320 cell1544416)
                    (ThetaLowerSegment.join cell1548512 cell1552608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1556704 cell1560800)
                    (ThetaLowerSegment.join cell1564896 cell1568992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1573088 cell1577184)
                    (ThetaLowerSegment.join cell1581280 cell1585376))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1589472 cell1593568)
                    (ThetaLowerSegment.join cell1595616 cell1597664))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1599712 cell1601760)
                    (ThetaLowerSegment.join cell1603808 cell1607904)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1612000 cell1616096)
                    (ThetaLowerSegment.join cell1618144 cell1620192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1622240 cell1624288)
                    (ThetaLowerSegment.join cell1626336 cell1630432))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1634528 cell1638624)
                    (ThetaLowerSegment.join cell1642720 cell1644768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1648864 cell1650912)
                    (ThetaLowerSegment.join cell1655008 cell1659104)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1663200 cell1667296)
                    (ThetaLowerSegment.join cell1671392 cell1675488))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1679584 cell1683680)
                    (ThetaLowerSegment.join cell1687776 cell1691872)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1695968 cell1700064)
                    (ThetaLowerSegment.join cell1704160 cell1708256))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1712352 cell1716448)
                    (ThetaLowerSegment.join cell1720544 cell1724640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1728736 cell1732832)
                    (ThetaLowerSegment.join cell1736928 cell1738976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1741024 cell1745120)
                    (ThetaLowerSegment.join cell1747168 cell1751264))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1755360 cell1759456)
                    (ThetaLowerSegment.join cell1763552 cell1765600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1767648 cell1769696)
                    (ThetaLowerSegment.join cell1771744 cell1773792)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1775840 cell1777888)
                    (ThetaLowerSegment.join cell1779936 cell1781984))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1786080 cell1788128)
                    (ThetaLowerSegment.join cell1792224 cell1796320))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1800416 cell1804512)
                (ThetaLowerSegment.join cell1808608 cell1812704))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1816800 cell1820896)
                (ThetaLowerSegment.join cell1824992 cell1829088)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1833184 cell1837280)
                (ThetaLowerSegment.join cell1841376 cell1845472))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1849568 cell1853664)
                (ThetaLowerSegment.join cell1857760 cell1861856))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1865952 cell1870048)
                (ThetaLowerSegment.join cell1874144 cell1878240))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1882336 cell1886432)
                (ThetaLowerSegment.join cell1890528 cell1894624)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1898720 cell1902816)
                (ThetaLowerSegment.join cell1906912 cell1911008))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1915104 cell1919200)
                (ThetaLowerSegment.join cell1923296 cell1927392)))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1931488 cell1935584)
                (ThetaLowerSegment.join cell1939680 cell1943776))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1947872 cell1951968)
                (ThetaLowerSegment.join cell1956064 cell1960160)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1964256 cell1968352)
                (ThetaLowerSegment.join cell1972448 cell1976544))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1980640 cell1984736)
                (ThetaLowerSegment.join cell1988832 cell1992928))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join (ThetaLowerSegment.join cell1997024 cell1999072)
              (ThetaLowerSegment.join cell1999584 cell1999840))
            cell1999968))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
