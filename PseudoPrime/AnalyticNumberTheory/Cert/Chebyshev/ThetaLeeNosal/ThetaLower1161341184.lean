/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1161341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1129341184 :
    ThetaLowerSegment 1129341184 1129472256 (56465729480737 / 50000)
      (112944414060609 / 100000) := by
  exact
    packedTile65536 1129341184 1129472256 14 6215 33605 30 _ _ (2084489 / 100000) (521123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129472256 :
    ThetaLowerSegment 1129472256 1129603328 (112944414060609 / 100000)
      (112957373397109 / 100000) := by
  exact
    packedTile65536 1129472256 1129603328 14 6217 33607 30 _ _ (4169 / 200) (2084503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129603328 :
    ThetaLowerSegment 1129603328 1129734400 (112957373397109 / 100000)
      (112970514160757 / 100000) := by
  exact
    packedTile65536 1129603328 1129734400 14 6304 33609 30 _ _ (65141 / 3125) (416903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129734400 :
    ThetaLowerSegment 1129734400 1129865472 (112970514160757 / 100000)
      (112983609134243 / 100000) := by
  exact
    packedTile65536 1129734400 1129865472 14 6282 33611 30 _ _ (2084523 / 100000) (1042263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129865472 :
    ThetaLowerSegment 1129865472 1129996544 (112983609134243 / 100000)
      (112996687506833 / 100000) := by
  exact
    packedTile65536 1129865472 1129996544 14 6274 33613 30 _ _ (416907 / 20000) (1042269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1129996544 :
    ThetaLowerSegment 1129996544 1130127616 (112996687506833 / 100000) (282524347139 / 250) := by
  exact
    packedTile65536 1129996544 1130127616 14 6261 33615 30 _ _ (2084547 / 100000) (41691 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1130127616 :
    ThetaLowerSegment 1130127616 1130258688 (282524347139 / 250) (56511466011591 / 50000) := by
  exact
    packedTile65536 1130127616 1130258688 14 6329 33617 30 _ _ (1042279 / 50000) (2084561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1130258688 :
    ThetaLowerSegment 1130258688 1130389760 (56511466011591 / 50000) (56517992800261 / 50000) := by
  exact
    packedTile65536 1130258688 1130389760 14 6262 33619 30 _ _ (208457 / 10000) (2084573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1130389760 :
    ThetaLowerSegment 1130389760 1130520832 (56517992800261 / 50000) (141311236521 / 125) := by
  exact
    packedTile65536 1130389760 1130520832 14 6238 33621 30 _ _ (2084581 / 100000) (260573 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1130520832 :
    ThetaLowerSegment 1130520832 1130651904 (141311236521 / 125) (7066389409471 / 6250) := by
  exact
    packedTile65536 1130520832 1130651904 14 6352 33623 30 _ _ (2084593 / 100000) (521149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1130651904 :
    ThetaLowerSegment 1130651904 1130782976 (7066389409471 / 6250) (28268807537079 / 25000) := by
  exact
    packedTile65536 1130651904 1130782976 14 6236 33625 30 _ _ (416921 / 20000) (65144 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1130782976 :
    ThetaLowerSegment 1130782976 1130914048 (28268807537079 / 25000) (5654420141841 / 5000) := by
  exact
    packedTile65536 1130782976 1130914048 14 6319 33627 30 _ _ (260577 / 12500) (2084619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1130914048 :
    ThetaLowerSegment 1130914048 1131045120 (5654420141841 / 5000) (28275374617479 / 25000) := by
  exact
    packedTile65536 1130914048 1131045120 14 6282 33629 30 _ _ (521157 / 25000) (2084631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1131045120 :
    ThetaLowerSegment 1131045120 1131176192 (28275374617479 / 25000) (14139326877313 / 12500) := by
  exact
    packedTile65536 1131045120 1131176192 14 6292 33631 30 _ _ (2084639 / 100000) (1042321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1131176192 :
    ThetaLowerSegment 1131176192 1131307264 (14139326877313 / 12500)
      (113127754573757 / 100000) := by
  exact
    packedTile65536 1131176192 1131307264 14 6303 33632 30 _ _ (2084651 / 100000) (1042327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1131307264 :
    ThetaLowerSegment 1131307264 1131438336 (113127754573757 / 100000)
      (113140933806921 / 100000) := by
  exact
    packedTile65536 1131307264 1131438336 14 6322 33634 30 _ _ (1042331 / 50000) (416933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1131438336 :
    ThetaLowerSegment 1131438336 1131569408 (113140933806921 / 100000)
      (113153804584197 / 100000) := by
  exact
    packedTile65536 1131438336 1131569408 14 6174 33636 30 _ _ (1042337 / 50000) (2084677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1131569408 :
    ThetaLowerSegment 1131569408 1131700480 (113153804584197 / 100000)
      (113166754653629 / 100000) := by
  exact
    packedTile65536 1131569408 1131700480 14 6212 33638 30 _ _ (1042343 / 50000) (2084689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1131700480 :
    ThetaLowerSegment 1131700480 1131831552 (113166754653629 / 100000)
      (113179921599881 / 100000) := by
  exact
    packedTile65536 1131700480 1131831552 14 6316 33640 30 _ _ (2084697 / 100000) (20847 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1131831552 :
    ThetaLowerSegment 1131831552 1131962624 (113179921599881 / 100000)
      (56596532845063 / 50000) := by
  exact
    packedTile65536 1131831552 1131962624 14 6305 33642 30 _ _ (2084709 / 100000) (260589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1131962624 :
    ThetaLowerSegment 1131962624 1132093696 (56596532845063 / 50000) (56603060103383 / 50000) := by
  exact
    packedTile65536 1131962624 1132093696 14 6262 33644 30 _ _ (26059 / 1250) (2084723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1132093696 :
    ThetaLowerSegment 1132093696 1132224768 (56603060103383 / 50000) (11321942496639 / 10000) := by
  exact
    packedTile65536 1132093696 1132224768 14 6382 33646 30 _ _ (521183 / 25000) (416947 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1132224768 :
    ThetaLowerSegment 1132224768 1132355840 (11321942496639 / 10000) (56616276299679 / 50000) := by
  exact
    packedTile65536 1132224768 1132355840 14 6297 33648 30 _ _ (260593 / 12500) (2084747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1132355840 :
    ThetaLowerSegment 1132355840 1132486912 (56616276299679 / 50000) (56622847447439 / 50000) := by
  exact
    packedTile65536 1132355840 1132486912 14 6304 33650 30 _ _ (416951 / 20000) (1042379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1132486912 :
    ThetaLowerSegment 1132486912 1132617984 (56622847447439 / 50000) (56629468667431 / 50000) := by
  exact
    packedTile65536 1132486912 1132617984 14 6352 33652 30 _ _ (2084767 / 100000) (208477 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1132617984 :
    ThetaLowerSegment 1132617984 1132749056 (56629468667431 / 50000) (56636025294241 / 50000) := by
  exact
    packedTile65536 1132617984 1132749056 14 6290 33654 30 _ _ (1042389 / 50000) (2084781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1132749056 :
    ThetaLowerSegment 1132749056 1132880128 (56636025294241 / 50000) (14160638974729 / 12500) := by
  exact
    packedTile65536 1132749056 1132880128 14 6265 33656 30 _ _ (208479 / 10000) (2084793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1132880128 :
    ThetaLowerSegment 1132880128 1133011200 (14160638974729 / 12500) (28324569850237 / 25000) := by
  exact
    packedTile65536 1132880128 1133011200 14 6316 33658 30 _ _ (2084801 / 100000) (521201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1133011200 :
    ThetaLowerSegment 1133011200 1133142272 (28324569850237 / 25000)
      (113311253192247 / 100000) := by
  exact
    packedTile65536 1133011200 1133142272 14 6223 33660 30 _ _ (2084813 / 100000) (130301 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1133142272 :
    ThetaLowerSegment 1133142272 1133273344 (113311253192247 / 100000)
      (28331072400743 / 25000) := by
  exact
    packedTile65536 1133142272 1133273344 14 6253 33662 30 _ _ (83393 / 4000) (521207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1133273344 :
    ThetaLowerSegment 1133273344 1133404416 (28331072400743 / 25000) (28334343508427 / 25000) := by
  exact
    packedTile65536 1133273344 1133404416 14 6276 33664 30 _ _ (521209 / 25000) (2084839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1133404416 :
    ThetaLowerSegment 1133404416 1133535488 (28334343508427 / 25000) (1133504126731 / 1000) := by
  exact
    packedTile65536 1133404416 1133535488 14 6254 33666 30 _ _ (130303 / 6250) (2084851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1133535488 :
    ThetaLowerSegment 1133535488 1133666560 (1133504126731 / 1000) (113363445126709 / 100000) := by
  exact
    packedTile65536 1133535488 1133666560 14 6251 33668 30 _ _ (2084859 / 100000) (1042431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1133666560 :
    ThetaLowerSegment 1133666560 1133797632 (113363445126709 / 100000)
      (56688230488181 / 50000) := by
  exact
    packedTile65536 1133666560 1133797632 14 6243 33669 30 _ _ (2084871 / 100000) (1042437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1133797632 :
    ThetaLowerSegment 1133797632 1133928704 (56688230488181 / 50000) (7086837093713 / 6250) := by
  exact
    packedTile65536 1133797632 1133928704 14 6203 33671 30 _ _ (1042441 / 50000) (416977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1133928704 :
    ThetaLowerSegment 1133928704 1134059776 (7086837093713 / 6250) (56701254783781 / 50000) := by
  exact
    packedTile65536 1133928704 1134059776 14 6291 33673 30 _ _ (1042447 / 50000) (2084897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134059776 :
    ThetaLowerSegment 1134059776 1134190848 (56701254783781 / 50000) (56707793045861 / 50000) := by
  exact
    packedTile65536 1134059776 1134190848 14 6272 33675 30 _ _ (416981 / 20000) (521227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134190848 :
    ThetaLowerSegment 1134190848 1134321920 (56707793045861 / 50000) (14178571890579 / 12500) := by
  exact
    packedTile65536 1134190848 1134321920 14 6230 33677 30 _ _ (2084917 / 100000) (52123 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134321920 :
    ThetaLowerSegment 1134321920 1134452992 (14178571890579 / 12500) (22688336614651 / 20000) := by
  exact
    packedTile65536 1134321920 1134452992 14 6287 33679 30 _ _ (2084929 / 100000) (521233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134452992 :
    ThetaLowerSegment 1134452992 1134584064 (22688336614651 / 20000) (22690950712423 / 20000) := by
  exact
    packedTile65536 1134452992 1134584064 14 6269 33681 30 _ _ (104247 / 5000) (2084943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134584064 :
    ThetaLowerSegment 1134584064 1134715136 (22690950712423 / 20000)
      (113467824126203 / 100000) := by
  exact
    packedTile65536 1134584064 1134715136 14 6269 33683 30 _ _ (260619 / 12500) (416991 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134715136 :
    ThetaLowerSegment 1134715136 1134846208 (113467824126203 / 100000)
      (22696201886443 / 20000) := by
  exact
    packedTile65536 1134715136 1134846208 14 6324 33685 30 _ _ (2084963 / 100000) (1042483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134846208 :
    ThetaLowerSegment 1134846208 1134977280 (22696201886443 / 20000) (2837346269831 / 2500) := by
  exact
    packedTile65536 1134846208 1134977280 14 6159 33687 30 _ _ (83399 / 4000) (1042489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1134977280 :
    ThetaLowerSegment 1134977280 1135042816 (2837346269831 / 2500) (56750218632007 / 50000) := by
  exact
    packedTile65536 1134977280 1135042816 13 3159 33689 30 _ _ (1042493 / 50000) (2084989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135042816 :
    ThetaLowerSegment 1135042816 1135108352 (56750218632007 / 50000) (56753439944647 / 50000) := by
  exact
    packedTile65536 1135042816 1135108352 13 3090 33690 30 _ _ (65156 / 3125) (416999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135108352 :
    ThetaLowerSegment 1135108352 1135173888 (56753439944647 / 50000) (28378369726991 / 25000) := by
  exact
    packedTile65536 1135108352 1135173888 13 3165 33691 30 _ _ (1042499 / 50000) (2085001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135173888 :
    ThetaLowerSegment 1135173888 1135239424 (28378369726991 / 25000) (7094996792211 / 6250) := by
  exact
    packedTile65536 1135173888 1135239424 13 3103 33692 30 _ _ (521251 / 25000) (2085007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135239424 :
    ThetaLowerSegment 1135239424 1135304960 (7094996792211 / 6250) (113526572748969 / 100000) := by
  exact
    packedTile65536 1135239424 1135304960 13 3177 33693 30 _ _ (2085009 / 100000) (521253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135304960 :
    ThetaLowerSegment 1135304960 1135370496 (113526572748969 / 100000)
      (113533123866099 / 100000) := by
  exact
    packedTile65536 1135304960 1135370496 13 3142 33694 30 _ _ (417003 / 20000) (1042509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135370496 :
    ThetaLowerSegment 1135370496 1135436032 (113533123866099 / 100000)
      (56769871903887 / 50000) := by
  exact
    packedTile65536 1135370496 1135436032 13 3175 33695 30 _ _ (2085021 / 100000) (65157 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135436032 :
    ThetaLowerSegment 1135436032 1135501568 (56769871903887 / 50000)
      (113546363768499 / 100000) := by
  exact
    packedTile65536 1135436032 1135501568 13 3175 33696 30 _ _ (2085027 / 100000) (208503 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135501568 :
    ThetaLowerSegment 1135501568 1135567104 (113546363768499 / 100000)
      (11355284196603 / 10000) := by
  exact
    packedTile65536 1135501568 1135567104 13 3107 33697 30 _ _ (2085033 / 100000) (521259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135567104 :
    ThetaLowerSegment 1135567104 1135632640 (11355284196603 / 10000) (56779713258017 / 50000) := by
  exact
    packedTile65536 1135567104 1135632640 13 3158 33698 30 _ _ (1042519 / 50000) (2085041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135632640 :
    ThetaLowerSegment 1135632640 1135698176 (56779713258017 / 50000) (56782976351877 / 50000) := by
  exact
    packedTile65536 1135632640 1135698176 13 3130 33699 30 _ _ (521261 / 25000) (2085047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135698176 :
    ThetaLowerSegment 1135698176 1135763712 (56782976351877 / 50000) (56786226944827 / 50000) := by
  exact
    packedTile65536 1135698176 1135763712 13 3118 33700 30 _ _ (41701 / 2000) (2085053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135763712 :
    ThetaLowerSegment 1135763712 1135829248 (56786226944827 / 50000) (56789552609147 / 50000) := by
  exact
    packedTile65536 1135763712 1135829248 13 3190 33701 30 _ _ (65158 / 3125) (2085059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135829248 :
    ThetaLowerSegment 1135829248 1135894784 (56789552609147 / 50000)
      (113585683585749 / 100000) := by
  exact
    packedTile65536 1135829248 1135894784 13 3155 33702 30 _ _ (2085061 / 100000) (260633 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135894784 :
    ThetaLowerSegment 1135894784 1135960320 (113585683585749 / 100000)
      (113592201505191 / 100000) := by
  exact
    packedTile65536 1135894784 1135960320 13 3126 33703 30 _ _ (2085067 / 100000) (208507 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1135960320 :
    ThetaLowerSegment 1135960320 1136025856 (113592201505191 / 100000)
      (113598698592659 / 100000) := by
  exact
    packedTile65536 1135960320 1136025856 13 3116 33704 30 _ _ (2085073 / 100000) (521269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136025856 :
    ThetaLowerSegment 1136025856 1136091392 (113598698592659 / 100000)
      (22721050816207 / 20000) := by
  exact
    packedTile65536 1136025856 1136091392 13 3144 33704 30 _ _ (2085079 / 100000) (1042541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136091392 :
    ThetaLowerSegment 1136091392 1136156928 (22721050816207 / 20000) (22722362334043 / 20000) := by
  exact
    packedTile65536 1136091392 1136156928 13 3145 33705 30 _ _ (521271 / 25000) (2085087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136156928 :
    ThetaLowerSegment 1136156928 1136222464 (22722362334043 / 20000) (22723664264239 / 20000) := by
  exact
    packedTile65536 1136156928 1136222464 13 3122 33706 30 _ _ (208509 / 10000) (2085093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136222464 :
    ThetaLowerSegment 1136222464 1136288000 (22723664264239 / 20000)
      (113625022819739 / 100000) := by
  exact
    packedTile65536 1136222464 1136288000 13 3214 33707 30 _ _ (260637 / 12500) (2085099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136288000 :
    ThetaLowerSegment 1136288000 1136353536 (113625022819739 / 100000)
      (113631530423081 / 100000) := by
  exact
    packedTile65536 1136288000 1136353536 13 3121 33708 30 _ _ (1042551 / 50000) (417021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136353536 :
    ThetaLowerSegment 1136353536 1136419072 (113631530423081 / 100000)
      (113638067236661 / 100000) := by
  exact
    packedTile65536 1136353536 1136419072 13 3135 33709 30 _ _ (521277 / 25000) (2085111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136419072 :
    ThetaLowerSegment 1136419072 1136484608 (113638067236661 / 100000)
      (113644493554927 / 100000) := by
  exact
    packedTile65536 1136419072 1136484608 13 3082 33710 30 _ _ (2085113 / 100000) (521279 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136484608 :
    ThetaLowerSegment 1136484608 1136550144 (113644493554927 / 100000)
      (56825571499709 / 50000) := by
  exact
    packedTile65536 1136484608 1136550144 13 3189 33711 30 _ _ (2085119 / 100000) (1042561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136550144 :
    ThetaLowerSegment 1136550144 1136615680 (56825571499709 / 50000) (7103600691073 / 6250) := by
  exact
    packedTile65536 1136550144 1136615680 13 3102 33712 30 _ _ (16681 / 800) (260641 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136615680 :
    ThetaLowerSegment 1136615680 1136681216 (7103600691073 / 6250) (113664081218661 / 100000) := by
  exact
    packedTile65536 1136615680 1136681216 13 3103 33713 30 _ _ (2085131 / 100000) (1042567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136681216 :
    ThetaLowerSegment 1136681216 1136746752 (113664081218661 / 100000)
      (113670524288901 / 100000) := by
  exact
    packedTile65536 1136681216 1136746752 13 3090 33714 30 _ _ (130321 / 6250) (2085139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136746752 :
    ThetaLowerSegment 1136746752 1136812288 (113670524288901 / 100000)
      (22735415161013 / 20000) := by
  exact
    packedTile65536 1136746752 1136812288 13 3142 33715 30 _ _ (1042571 / 50000) (417029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136812288 :
    ThetaLowerSegment 1136812288 1136877824 (22735415161013 / 20000)
      (113683537678717 / 100000) := by
  exact
    packedTile65536 1136812288 1136877824 13 3099 33716 30 _ _ (521287 / 25000) (2085151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136877824 :
    ThetaLowerSegment 1136877824 1136943360 (113683537678717 / 100000)
      (113689941186651 / 100000) := by
  exact
    packedTile65536 1136877824 1136943360 13 3071 33717 30 _ _ (1042577 / 50000) (2085157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1136943360 :
    ThetaLowerSegment 1136943360 1137008896 (113689941186651 / 100000)
      (113696442712413 / 100000) := by
  exact
    packedTile65536 1136943360 1137008896 13 3118 33718 30 _ _ (2085159 / 100000) (1042581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137008896 :
    ThetaLowerSegment 1137008896 1137074432 (113696442712413 / 100000)
      (28425767862987 / 25000) := by
  exact
    packedTile65536 1137008896 1137074432 13 3179 33719 30 _ _ (417033 / 20000) (130323 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137074432 :
    ThetaLowerSegment 1137074432 1137139968 (28425767862987 / 25000) (56854782337221 / 50000) := by
  exact
    packedTile65536 1137074432 1137139968 13 3114 33720 30 _ _ (2085171 / 100000) (1042587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137139968 :
    ThetaLowerSegment 1137139968 1137205504 (56854782337221 / 50000) (56858064405819 / 50000) := by
  exact
    packedTile65536 1137139968 1137205504 13 3148 33721 30 _ _ (2085177 / 100000) (104259 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137205504 :
    ThetaLowerSegment 1137205504 1137271040 (56858064405819 / 50000) (11372268879421 / 10000) := by
  exact
    packedTile65536 1137205504 1137271040 13 3146 33722 30 _ _ (1042591 / 50000) (417037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137271040 :
    ThetaLowerSegment 1137271040 1137336576 (11372268879421 / 10000) (56864595205197 / 50000) := by
  exact
    packedTile65536 1137271040 1137336576 13 3118 33723 30 _ _ (521297 / 25000) (2085191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137336576 :
    ThetaLowerSegment 1137336576 1137402112 (56864595205197 / 50000) (3554244090667 / 3125) := by
  exact
    packedTile65536 1137336576 1137402112 13 3175 33724 30 _ _ (1042597 / 50000) (2085197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137402112 :
    ThetaLowerSegment 1137402112 1137467648 (3554244090667 / 3125) (7108901181259 / 6250) := by
  exact
    packedTile65536 1137402112 1137467648 13 3169 33725 30 _ _ (5213 / 250) (2085203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137467648 :
    ThetaLowerSegment 1137467648 1137533184 (7108901181259 / 6250) (7109301540811 / 6250) := by
  exact
    packedTile65536 1137467648 1137533184 13 3072 33726 30 _ _ (1042603 / 50000) (2085209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137533184 :
    ThetaLowerSegment 1137533184 1137598720 (7109301540811 / 6250) (11375544311269 / 10000) := by
  exact
    packedTile65536 1137533184 1137598720 13 3174 33727 30 _ _ (2085211 / 100000) (1042607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137598720 :
    ThetaLowerSegment 1137598720 1137664256 (11375544311269 / 10000) (56881028710507 / 50000) := by
  exact
    packedTile65536 1137598720 1137664256 13 3172 33728 30 _ _ (2085217 / 100000) (104261 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137664256 :
    ThetaLowerSegment 1137664256 1137729792 (56881028710507 / 50000)
      (113768690515377 / 100000) := by
  exact
    packedTile65536 1137664256 1137729792 13 3181 33729 30 _ _ (2085223 / 100000) (1042613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137729792 :
    ThetaLowerSegment 1137729792 1137795328 (113768690515377 / 100000)
      (113775254816269 / 100000) := by
  exact
    packedTile65536 1137729792 1137795328 13 3148 33730 30 _ _ (2085229 / 100000) (130327 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137795328 :
    ThetaLowerSegment 1137795328 1137860864 (113775254816269 / 100000)
      (113781825388603 / 100000) := by
  exact
    packedTile65536 1137795328 1137860864 13 3151 33731 30 _ _ (1042617 / 50000) (2085237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137860864 :
    ThetaLowerSegment 1137860864 1137926400 (113781825388603 / 100000)
      (113788454366563 / 100000) := by
  exact
    packedTile65536 1137860864 1137926400 13 3179 33732 30 _ _ (52131 / 2500) (2085243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137926400 :
    ThetaLowerSegment 1137926400 1137991936 (113788454366563 / 100000)
      (22758988730423 / 20000) := by
  exact
    packedTile65536 1137926400 1137991936 13 3112 33733 30 _ _ (1042623 / 50000) (2085249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1137991936 :
    ThetaLowerSegment 1137991936 1138057472 (22758988730423 / 20000)
      (113801455894111 / 100000) := by
  exact
    packedTile65536 1137991936 1138057472 13 3123 33734 30 _ _ (521313 / 25000) (417051 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138057472 :
    ThetaLowerSegment 1138057472 1138123008 (113801455894111 / 100000)
      (113808191274221 / 100000) := by
  exact
    packedTile65536 1138057472 1138123008 13 3230 33735 30 _ _ (2085257 / 100000) (104263 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138123008 :
    ThetaLowerSegment 1138123008 1138188544 (113808191274221 / 100000)
      (113814764023197 / 100000) := by
  exact
    packedTile65536 1138123008 1138188544 13 3152 33736 30 _ _ (2085263 / 100000) (1042633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138188544 :
    ThetaLowerSegment 1138188544 1138254080 (113814764023197 / 100000)
      (113821224186559 / 100000) := by
  exact
    packedTile65536 1138188544 1138254080 13 3098 33737 30 _ _ (2085269 / 100000) (260659 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138254080 :
    ThetaLowerSegment 1138254080 1138319616 (113821224186559 / 100000)
      (28456944551471 / 25000) := by
  exact
    packedTile65536 1138254080 1138319616 13 3143 33738 30 _ _ (83411 / 4000) (1042639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138319616 :
    ThetaLowerSegment 1138319616 1138385152 (28456944551471 / 25000) (28458600263791 / 25000) := by
  exact
    packedTile65536 1138319616 1138385152 13 3176 33738 30 _ _ (13033 / 625) (2085283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138385152 :
    ThetaLowerSegment 1138385152 1138450688 (28458600263791 / 25000) (56920479639817 / 50000) := by
  exact
    packedTile65536 1138385152 1138450688 13 3145 33739 30 _ _ (1042643 / 50000) (2085289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138450688 :
    ThetaLowerSegment 1138450688 1138516224 (56920479639817 / 50000) (56923818192309 / 50000) := by
  exact
    packedTile65536 1138450688 1138516224 13 3202 33740 30 _ _ (521323 / 25000) (417059 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138516224 :
    ThetaLowerSegment 1138516224 1138581760 (56923818192309 / 50000) (28463544491111 / 25000) := by
  exact
    packedTile65536 1138516224 1138581760 13 3137 33741 30 _ _ (1042649 / 50000) (2085301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138581760 :
    ThetaLowerSegment 1138581760 1138647296 (28463544491111 / 25000)
      (113860811313287 / 100000) := by
  exact
    packedTile65536 1138581760 1138647296 13 3181 33742 30 _ _ (2085303 / 100000) (1042653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138647296 :
    ThetaLowerSegment 1138647296 1138712832 (113860811313287 / 100000)
      (113867329989221 / 100000) := by
  exact
    packedTile65536 1138647296 1138712832 13 3126 33743 30 _ _ (2085309 / 100000) (65166 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138712832 :
    ThetaLowerSegment 1138712832 1138778368 (113867329989221 / 100000)
      (113873840342651 / 100000) := by
  exact
    packedTile65536 1138712832 1138778368 13 3122 33744 30 _ _ (417063 / 20000) (1042659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138778368 :
    ThetaLowerSegment 1138778368 1138843904 (113873840342651 / 100000)
      (113880367397381 / 100000) := by
  exact
    packedTile65536 1138778368 1138843904 13 3130 33745 30 _ _ (2085321 / 100000) (521331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138843904 :
    ThetaLowerSegment 1138843904 1138909440 (113880367397381 / 100000)
      (113886942430259 / 100000) := by
  exact
    packedTile65536 1138843904 1138909440 13 3153 33746 30 _ _ (1042663 / 50000) (2085329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138909440 :
    ThetaLowerSegment 1138909440 1138974976 (113886942430259 / 100000)
      (113893502884731 / 100000) := by
  exact
    packedTile65536 1138909440 1138974976 13 3146 33747 30 _ _ (521333 / 25000) (417067 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1138974976 :
    ThetaLowerSegment 1138974976 1139040512 (113893502884731 / 100000)
      (113900086296797 / 100000) := by
  exact
    packedTile65536 1138974976 1139040512 13 3157 33748 30 _ _ (1042669 / 50000) (2085341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139040512 :
    ThetaLowerSegment 1139040512 1139106048 (113900086296797 / 100000)
      (113906563375261 / 100000) := by
  exact
    packedTile65536 1139040512 1139106048 13 3106 33749 30 _ _ (65167 / 3125) (2085347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139106048 :
    ThetaLowerSegment 1139106048 1139171584 (113906563375261 / 100000)
      (113913194785081 / 100000) := by
  exact
    packedTile65536 1139106048 1139171584 13 3180 33750 30 _ _ (2085349 / 100000) (260669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139171584 :
    ThetaLowerSegment 1139171584 1139237120 (113913194785081 / 100000)
      (56959899552183 / 50000) := by
  exact
    packedTile65536 1139171584 1139237120 13 3167 33751 30 _ _ (417071 / 20000) (1042679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139237120 :
    ThetaLowerSegment 1139237120 1139302656 (56959899552183 / 50000) (14240803297703 / 12500) := by
  exact
    packedTile65536 1139237120 1139302656 13 3178 33752 30 _ _ (2085361 / 100000) (521341 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139302656 :
    ThetaLowerSegment 1139302656 1139368192 (14240803297703 / 12500)
      (113932901446159 / 100000) := by
  exact
    packedTile65536 1139302656 1139368192 13 3105 33753 30 _ _ (2085367 / 100000) (208537 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139368192 :
    ThetaLowerSegment 1139368192 1139433728 (113932901446159 / 100000)
      (113939391123823 / 100000) := by
  exact
    packedTile65536 1139368192 1139433728 13 3112 33754 30 _ _ (521343 / 25000) (16683 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139433728 :
    ThetaLowerSegment 1139433728 1139499264 (113939391123823 / 100000)
      (113946018455107 / 100000) := by
  exact
    packedTile65536 1139433728 1139499264 13 3178 33755 30 _ _ (1042689 / 50000) (2085381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139499264 :
    ThetaLowerSegment 1139499264 1139564800 (113946018455107 / 100000)
      (113952595756243 / 100000) := by
  exact
    packedTile65536 1139499264 1139564800 13 3154 33756 30 _ _ (260673 / 12500) (2085387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139564800 :
    ThetaLowerSegment 1139564800 1139630336 (113952595756243 / 100000)
      (113959018757443 / 100000) := by
  exact
    packedTile65536 1139564800 1139630336 13 3080 33757 30 _ _ (208539 / 10000) (2085393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139630336 :
    ThetaLowerSegment 1139630336 1139695872 (113959018757443 / 100000)
      (28491420398617 / 25000) := by
  exact
    packedTile65536 1139630336 1139695872 13 3195 33758 30 _ _ (417079 / 20000) (1042699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139695872 :
    ThetaLowerSegment 1139695872 1139761408 (28491420398617 / 25000) (22794457211887 / 20000) := by
  exact
    packedTile65536 1139695872 1139761408 13 3167 33759 30 _ _ (2085401 / 100000) (521351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139761408 :
    ThetaLowerSegment 1139761408 1139826944 (22794457211887 / 20000)
      (113978809212531 / 100000) := by
  exact
    packedTile65536 1139761408 1139826944 13 3128 33760 30 _ _ (2085407 / 100000) (208541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139826944 :
    ThetaLowerSegment 1139826944 1139892480 (113978809212531 / 100000) (5699267140573 / 5000) := by
  exact
    packedTile65536 1139826944 1139892480 13 3133 33761 30 _ _ (2085413 / 100000) (260677 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139892480 :
    ThetaLowerSegment 1139892480 1139958016 (5699267140573 / 5000) (56995923615101 / 50000) := by
  exact
    packedTile65536 1139892480 1139958016 13 3119 33762 30 _ _ (1042709 / 50000) (2085421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1139958016 :
    ThetaLowerSegment 1139958016 1140023552 (56995923615101 / 50000) (56999217542309 / 50000) := by
  exact
    packedTile65536 1139958016 1140023552 13 3159 33763 30 _ _ (130339 / 6250) (2085427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140023552 :
    ThetaLowerSegment 1140023552 1140089088 (56999217542309 / 50000) (28501226543477 / 25000) := by
  exact
    packedTile65536 1140023552 1140089088 13 3103 33764 30 _ _ (208543 / 10000) (2085433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140089088 :
    ThetaLowerSegment 1140089088 1140154624 (28501226543477 / 25000) (28502905319457 / 25000) := by
  exact
    packedTile65536 1140089088 1140154624 13 3220 33765 30 _ _ (521359 / 25000) (2085439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140154624 :
    ThetaLowerSegment 1140154624 1140220160 (28502905319457 / 25000)
      (114018209185947 / 100000) := by
  exact
    packedTile65536 1140154624 1140220160 13 3159 33766 30 _ _ (2085441 / 100000) (521361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140220160 :
    ThetaLowerSegment 1140220160 1140285696 (114018209185947 / 100000)
      (114024736635057 / 100000) := by
  exact
    packedTile65536 1140220160 1140285696 13 3130 33767 30 _ _ (2085447 / 100000) (41709 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140285696 :
    ThetaLowerSegment 1140285696 1140351232 (114024736635057 / 100000)
      (114031289128383 / 100000) := by
  exact
    packedTile65536 1140285696 1140351232 13 3142 33768 30 _ _ (2085453 / 100000) (130341 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140351232 :
    ThetaLowerSegment 1140351232 1140416768 (114031289128383 / 100000)
      (57018936461223 / 50000) := by
  exact
    packedTile65536 1140351232 1140416768 13 3157 33769 30 _ _ (2085459 / 100000) (1042731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140416768 :
    ThetaLowerSegment 1140416768 1140482304 (57018936461223 / 50000) (57022186656867 / 50000) := by
  exact
    packedTile65536 1140416768 1140482304 13 3117 33770 30 _ _ (260683 / 12500) (2085467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140482304 :
    ThetaLowerSegment 1140482304 1140547840 (57022186656867 / 50000) (57025433733657 / 50000) := by
  exact
    packedTile65536 1140482304 1140547840 13 3114 33771 30 _ _ (208547 / 10000) (2085473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140547840 :
    ThetaLowerSegment 1140547840 1140613376 (57025433733657 / 50000) (57028671435147 / 50000) := by
  exact
    packedTile65536 1140547840 1140613376 13 3105 33771 30 _ _ (521369 / 25000) (2085479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140613376 :
    ThetaLowerSegment 1140613376 1140678912 (57028671435147 / 50000) (3564498492586 / 3125) := by
  exact
    packedTile65536 1140613376 1140678912 13 3169 33772 30 _ _ (1042741 / 50000) (417097 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140678912 :
    ThetaLowerSegment 1140678912 1140744448 (3564498492586 / 3125) (2851762713347 / 2500) := by
  exact
    packedTile65536 1140678912 1140744448 13 3144 33773 30 _ _ (2085487 / 100000) (208549 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140744448 :
    ThetaLowerSegment 1140744448 1140809984 (2851762713347 / 2500) (5703848678109 / 5000) := by
  exact
    packedTile65536 1140744448 1140809984 13 3100 33774 30 _ _ (2085493 / 100000) (260687 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140809984 :
    ThetaLowerSegment 1140809984 1140875520 (5703848678109 / 5000) (5704174015953 / 5000) := by
  exact
    packedTile65536 1140809984 1140875520 13 3120 33775 30 _ _ (2085499 / 100000) (1042751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140875520 :
    ThetaLowerSegment 1140875520 1140941056 (5704174015953 / 5000) (11409012473799 / 10000) := by
  exact
    packedTile65536 1140875520 1140941056 13 3186 33776 30 _ _ (417101 / 20000) (521377 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1140941056 :
    ThetaLowerSegment 1140941056 1141006592 (11409012473799 / 10000) (11409657313491 / 10000) := by
  exact
    packedTile65536 1140941056 1141006592 13 3092 33777 30 _ _ (208551 / 10000) (2085513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141006592 :
    ThetaLowerSegment 1141006592 1141072128 (11409657313491 / 10000) (57051495133821 / 50000) := by
  exact
    packedTile65536 1141006592 1141072128 13 3077 33778 30 _ _ (521379 / 25000) (2085519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141072128 :
    ThetaLowerSegment 1141072128 1141137664 (57051495133821 / 50000) (57054723521877 / 50000) := by
  exact
    packedTile65536 1141072128 1141137664 13 3096 33779 30 _ _ (1042761 / 50000) (83421 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141137664 :
    ThetaLowerSegment 1141137664 1141203200 (57054723521877 / 50000) (2282319578349 / 2000) := by
  exact
    packedTile65536 1141137664 1141203200 13 3132 33780 30 _ _ (260691 / 12500) (2085531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141203200 :
    ThetaLowerSegment 1141203200 1141268736 (2282319578349 / 2000) (22824503412681 / 20000) := by
  exact
    packedTile65536 1141203200 1141268736 13 3135 33781 30 _ _ (2085533 / 100000) (65173 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141268736 :
    ThetaLowerSegment 1141268736 1141334272 (22824503412681 / 20000) (57064556811631 / 50000) := by
  exact
    packedTile65536 1141268736 1141334272 13 3163 33782 30 _ _ (2085539 / 100000) (1042771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141334272 :
    ThetaLowerSegment 1141334272 1141399808 (57064556811631 / 50000)
      (114135597582667 / 100000) := by
  exact
    packedTile65536 1141334272 1141399808 13 3109 33783 30 _ _ (417109 / 20000) (521387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141399808 :
    ThetaLowerSegment 1141399808 1141465344 (114135597582667 / 100000) (7133885050729 / 6250) := by
  exact
    packedTile65536 1141399808 1141465344 13 3147 33784 30 _ _ (2085551 / 100000) (1042777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141465344 :
    ThetaLowerSegment 1141465344 1141530880 (7133885050729 / 6250) (14268597545801 / 12500) := by
  exact
    packedTile65536 1141465344 1141530880 13 3174 33785 30 _ _ (521389 / 25000) (2085559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141530880 :
    ThetaLowerSegment 1141530880 1141596416 (14268597545801 / 12500) (28538806188247 / 25000) := by
  exact
    packedTile65536 1141530880 1141596416 13 3090 33786 30 _ _ (1042781 / 50000) (417113 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141596416 :
    ThetaLowerSegment 1141596416 1141661952 (28538806188247 / 25000) (28540443880519 / 25000) := by
  exact
    packedTile65536 1141596416 1141661952 13 3141 33787 30 _ _ (65174 / 3125) (2085571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141661952 :
    ThetaLowerSegment 1141661952 1141727488 (28540443880519 / 25000) (2854210504021 / 2500) := by
  exact
    packedTile65536 1141661952 1141727488 13 3186 33788 30 _ _ (1042787 / 50000) (2085577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141727488 :
    ThetaLowerSegment 1141727488 1141793024 (2854210504021 / 2500) (114174941766373 / 100000) := by
  exact
    packedTile65536 1141727488 1141793024 13 3127 33789 30 _ _ (2085579 / 100000) (1042791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141793024 :
    ThetaLowerSegment 1141793024 1141858560 (114174941766373 / 100000)
      (57090712925069 / 50000) := by
  exact
    packedTile65536 1141793024 1141858560 13 3109 33790 30 _ _ (417117 / 20000) (521397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141858560 :
    ThetaLowerSegment 1141858560 1141924096 (57090712925069 / 50000) (11418799963297 / 10000) := by
  exact
    packedTile65536 1141858560 1141924096 13 3152 33791 30 _ _ (2085591 / 100000) (1042797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141924096 :
    ThetaLowerSegment 1141924096 1141989632 (11418799963297 / 10000) (28548640230283 / 25000) := by
  exact
    packedTile65536 1141924096 1141989632 13 3146 33792 30 _ _ (2085597 / 100000) (2607 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1141989632 :
    ThetaLowerSegment 1141989632 1142055168 (28548640230283 / 25000) (57100541299293 / 50000) := by
  exact
    packedTile65536 1141989632 1142055168 13 3127 33793 30 _ _ (1042801 / 50000) (417121 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142055168 :
    ThetaLowerSegment 1142055168 1142120704 (57100541299293 / 50000) (57103835517129 / 50000) := by
  exact
    packedTile65536 1142055168 1142120704 13 3159 33794 30 _ _ (260701 / 12500) (2085611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142120704 :
    ThetaLowerSegment 1142120704 1142186240 (57103835517129 / 50000) (14276779829093 / 12500) := by
  exact
    packedTile65536 1142120704 1142186240 13 3149 33795 30 _ _ (1042807 / 50000) (2085617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142186240 :
    ThetaLowerSegment 1142186240 1142251776 (14276779829093 / 12500) (14277600520563 / 12500) := by
  exact
    packedTile65536 1142186240 1142251776 13 3148 33796 30 _ _ (104281 / 5000) (2085623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142251776 :
    ThetaLowerSegment 1142251776 1142317312 (14277600520563 / 12500) (57113632715377 / 50000) := by
  exact
    packedTile65536 1142251776 1142317312 13 3098 33797 30 _ _ (3337 / 160) (521407 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142317312 :
    ThetaLowerSegment 1142317312 1142382848 (57113632715377 / 50000) (14279224181973 / 12500) := by
  exact
    packedTile65536 1142317312 1142382848 13 3130 33798 30 _ _ (2085631 / 100000) (1042817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142382848 :
    ThetaLowerSegment 1142382848 1142448384 (14279224181973 / 12500)
      (114240373640519 / 100000) := by
  exact
    packedTile65536 1142382848 1142448384 13 3155 33799 30 _ _ (2085637 / 100000) (52141 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142448384 :
    ThetaLowerSegment 1142448384 1142513920 (114240373640519 / 100000)
      (22849383677023 / 20000) := by
  exact
    packedTile65536 1142448384 1142513920 13 3138 33800 30 _ _ (1042821 / 50000) (417129 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142513920 :
    ThetaLowerSegment 1142513920 1142579456 (22849383677023 / 20000)
      (114253411007339 / 100000) := by
  exact
    packedTile65536 1142513920 1142579456 13 3113 33801 30 _ _ (130353 / 6250) (2085651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142579456 :
    ThetaLowerSegment 1142579456 1142644992 (114253411007339 / 100000)
      (114259893219971 / 100000) := by
  exact
    packedTile65536 1142579456 1142644992 13 3108 33802 30 _ _ (1042827 / 50000) (2085657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142644992 :
    ThetaLowerSegment 1142644992 1142710528 (114259893219971 / 100000)
      (114266492248211 / 100000) := by
  exact
    packedTile65536 1142644992 1142710528 13 3164 33803 30 _ _ (104283 / 5000) (2085663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142710528 :
    ThetaLowerSegment 1142710528 1142776064 (114266492248211 / 100000)
      (114273107977591 / 100000) := by
  exact
    packedTile65536 1142710528 1142776064 13 3172 33804 30 _ _ (417133 / 20000) (521417 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142776064 :
    ThetaLowerSegment 1142776064 1142841600 (114273107977591 / 100000)
      (114279631956479 / 100000) := by
  exact
    packedTile65536 1142776064 1142841600 13 3128 33804 30 _ _ (2085671 / 100000) (1042837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142841600 :
    ThetaLowerSegment 1142841600 1142907136 (114279631956479 / 100000)
      (22857235362181 / 20000) := by
  exact
    packedTile65536 1142841600 1142907136 13 3138 33805 30 _ _ (2085677 / 100000) (26071 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142907136 :
    ThetaLowerSegment 1142907136 1142972672 (22857235362181 / 20000)
      (114292554829519 / 100000) := by
  exact
    packedTile65536 1142907136 1142972672 13 3058 33806 30 _ _ (2085683 / 100000) (1042843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1142972672 :
    ThetaLowerSegment 1142972672 1143038208 (114292554829519 / 100000)
      (114298955805991 / 100000) := by
  exact
    packedTile65536 1142972672 1143038208 13 3069 33807 30 _ _ (260711 / 12500) (2085691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143038208 :
    ThetaLowerSegment 1143038208 1143103744 (114298955805991 / 100000)
      (114305438142943 / 100000) := by
  exact
    packedTile65536 1143038208 1143103744 13 3108 33808 30 _ _ (1042847 / 50000) (2085697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143103744 :
    ThetaLowerSegment 1143103744 1143169280 (114305438142943 / 100000)
      (114312039383443 / 100000) := by
  exact
    packedTile65536 1143103744 1143169280 13 3165 33809 30 _ _ (20857 / 1000) (2085703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143169280 :
    ThetaLowerSegment 1143169280 1143234816 (114312039383443 / 100000)
      (114318536357633 / 100000) := by
  exact
    packedTile65536 1143169280 1143234816 13 3115 33810 30 _ _ (1042853 / 50000) (2085709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143234816 :
    ThetaLowerSegment 1143234816 1143300352 (114318536357633 / 100000)
      (11432505837593 / 10000) := by
  exact
    packedTile65536 1143234816 1143300352 13 3127 33811 30 _ _ (2085711 / 100000) (1042857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143300352 :
    ThetaLowerSegment 1143300352 1143365888 (11432505837593 / 10000)
      (114331547041517 / 100000) := by
  exact
    packedTile65536 1143300352 1143365888 13 3111 33812 30 _ _ (2085717 / 100000) (52143 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143365888 :
    ThetaLowerSegment 1143365888 1143431424 (114331547041517 / 100000)
      (57169055405899 / 50000) := by
  exact
    packedTile65536 1143365888 1143431424 13 3147 33813 30 _ _ (2085723 / 100000) (1042863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143431424 :
    ThetaLowerSegment 1143431424 1143496960 (57169055405899 / 50000) (57172342513227 / 50000) := by
  exact
    packedTile65536 1143431424 1143496960 13 3152 33814 30 _ _ (65179 / 3125) (2085731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143496960 :
    ThetaLowerSegment 1143496960 1143562496 (57172342513227 / 50000) (14293906103919 / 12500) := by
  exact
    packedTile65536 1143496960 1143562496 13 3147 33815 30 _ _ (1042867 / 50000) (2085737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143562496 :
    ThetaLowerSegment 1143562496 1143628032 (14293906103919 / 12500) (28589450035173 / 25000) := by
  exact
    packedTile65536 1143562496 1143628032 13 3141 33816 30 _ _ (104287 / 5000) (2085743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143628032 :
    ThetaLowerSegment 1143628032 1143693568 (28589450035173 / 25000) (57182179905931 / 50000) := by
  exact
    packedTile65536 1143628032 1143693568 13 3145 33817 30 _ _ (1042873 / 50000) (2085749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143693568 :
    ThetaLowerSegment 1143693568 1143759104 (57182179905931 / 50000) (14296366240939 / 12500) := by
  exact
    packedTile65536 1143693568 1143759104 13 3150 33818 30 _ _ (2085751 / 100000) (1042877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143759104 :
    ThetaLowerSegment 1143759104 1143824640 (14296366240939 / 12500) (22875487080719 / 20000) := by
  exact
    packedTile65536 1143759104 1143824640 13 3119 33819 30 _ _ (2085757 / 100000) (13036 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143824640 :
    ThetaLowerSegment 1143824640 1143890176 (22875487080719 / 20000) (22876801111409 / 20000) := by
  exact
    packedTile65536 1143824640 1143890176 13 3150 33820 30 _ _ (2085763 / 100000) (1042883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143890176 :
    ThetaLowerSegment 1143890176 1143955712 (22876801111409 / 20000) (57195228420281 / 50000) := by
  exact
    packedTile65536 1143890176 1143955712 13 3093 33821 30 _ _ (2085769 / 100000) (521443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1143955712 :
    ThetaLowerSegment 1143955712 1144021248 (57195228420281 / 50000) (5719851038567 / 5000) := by
  exact
    packedTile65536 1143955712 1144021248 13 3147 33822 30 _ _ (1042887 / 50000) (2085777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144021248 :
    ThetaLowerSegment 1144021248 1144086784 (5719851038567 / 5000) (715022899879 / 625) := by
  exact
    packedTile65536 1144021248 1144086784 13 3185 33823 30 _ _ (104289 / 5000) (2085783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144086784 :
    ThetaLowerSegment 1144086784 1144152320 (715022899879 / 625) (28602571066351 / 25000) := by
  exact
    packedTile65536 1144086784 1144152320 13 3174 33824 30 _ _ (1042893 / 50000) (2085789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144152320 :
    ThetaLowerSegment 1144152320 1144217856 (28602571066351 / 25000) (22883371318569 / 20000) := by
  exact
    packedTile65536 1144152320 1144217856 13 3151 33825 30 _ _ (2085791 / 100000) (1042897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144217856 :
    ThetaLowerSegment 1144217856 1144283392 (22883371318569 / 20000)
      (114423276676011 / 100000) := by
  exact
    packedTile65536 1144217856 1144283392 13 3078 33826 30 _ _ (2085797 / 100000) (10429 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144283392 :
    ThetaLowerSegment 1144283392 1144348928 (114423276676011 / 100000)
      (114429734322099 / 100000) := by
  exact
    packedTile65536 1144283392 1144348928 13 3096 33827 30 _ _ (2085803 / 100000) (1042903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144348928 :
    ThetaLowerSegment 1144348928 1144414464 (114429734322099 / 100000)
      (57218174211219 / 50000) := by
  exact
    packedTile65536 1144348928 1144414464 13 3171 33828 30 _ _ (2085809 / 100000) (521453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144414464 :
    ThetaLowerSegment 1144414464 1144480000 (57218174211219 / 50000) (57221492741293 / 50000) := by
  exact
    packedTile65536 1144414464 1144480000 13 3182 33829 30 _ _ (1042907 / 50000) (2085817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144480000 :
    ThetaLowerSegment 1144480000 1144545536 (57221492741293 / 50000) (57224776864883 / 50000) := by
  exact
    packedTile65536 1144480000 1144545536 13 3149 33830 30 _ _ (104291 / 5000) (2085823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144545536 :
    ThetaLowerSegment 1144545536 1144611072 (57224776864883 / 50000) (57228051611703 / 50000) := by
  exact
    packedTile65536 1144545536 1144611072 13 3140 33831 30 _ _ (1042913 / 50000) (2085829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144611072 :
    ThetaLowerSegment 1144611072 1144676608 (57228051611703 / 50000) (11446256304511 / 10000) := by
  exact
    packedTile65536 1144611072 1144676608 13 3097 33832 30 _ _ (260729 / 12500) (417167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144676608 :
    ThetaLowerSegment 1144676608 1144742144 (11446256304511 / 10000) (5723452499909 / 5000) := by
  exact
    packedTile65536 1144676608 1144742144 13 3110 33833 30 _ _ (2085837 / 100000) (26073 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144742144 :
    ThetaLowerSegment 1144742144 1144807680 (5723452499909 / 5000) (114475584944299 / 100000) := by
  exact
    packedTile65536 1144742144 1144807680 13 3133 33834 30 _ _ (2085843 / 100000) (1042923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144807680 :
    ThetaLowerSegment 1144807680 1144873216 (114475584944299 / 100000)
      (57241095414041 / 50000) := by
  exact
    packedTile65536 1144807680 1144873216 13 3167 33835 30 _ _ (2085849 / 100000) (521463 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144873216 :
    ThetaLowerSegment 1144873216 1144938752 (57241095414041 / 50000) (57244324316033 / 50000) := by
  exact
    packedTile65536 1144873216 1144938752 13 3096 33835 30 _ _ (1042927 / 50000) (2085857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1144938752 :
    ThetaLowerSegment 1144938752 1145004288 (57244324316033 / 50000) (57247582429353 / 50000) := by
  exact
    packedTile65536 1144938752 1145004288 13 3124 33836 30 _ _ (104293 / 5000) (2085863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145004288 :
    ThetaLowerSegment 1145004288 1145069824 (57247582429353 / 50000) (5725080404939 / 5000) := by
  exact
    packedTile65536 1145004288 1145069824 13 3089 33837 30 _ _ (1042933 / 50000) (2085869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145069824 :
    ThetaLowerSegment 1145069824 1145135360 (5725080404939 / 5000) (28627004495859 / 25000) := by
  exact
    packedTile65536 1145069824 1145135360 13 3073 33838 30 _ _ (130367 / 6250) (16687 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145135360 :
    ThetaLowerSegment 1145135360 1145200896 (28627004495859 / 25000) (14314327212283 / 12500) := by
  exact
    packedTile65536 1145135360 1145200896 13 3164 33839 30 _ _ (2085877 / 100000) (52147 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145200896 :
    ThetaLowerSegment 1145200896 1145266432 (14314327212283 / 12500) (57260519023069 / 50000) := by
  exact
    packedTile65536 1145200896 1145266432 13 3078 33840 30 _ _ (2085883 / 100000) (1042943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145266432 :
    ThetaLowerSegment 1145266432 1145331968 (57260519023069 / 50000) (28631929265679 / 25000) := by
  exact
    packedTile65536 1145266432 1145331968 13 3202 33841 30 _ _ (2085889 / 100000) (521473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145331968 :
    ThetaLowerSegment 1145331968 1145397504 (28631929265679 / 25000) (57267152159563 / 50000) := by
  exact
    packedTile65536 1145331968 1145397504 13 3158 33842 30 _ _ (417179 / 20000) (1042949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145397504 :
    ThetaLowerSegment 1145397504 1145463040 (57267152159563 / 50000) (57270369660313 / 50000) := by
  exact
    packedTile65536 1145397504 1145463040 13 3085 33843 30 _ _ (20859 / 1000) (2085903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145463040 :
    ThetaLowerSegment 1145463040 1145528576 (57270369660313 / 50000) (57273744656221 / 50000) := by
  exact
    packedTile65536 1145463040 1145528576 13 3236 33844 30 _ _ (1042953 / 50000) (2085909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145528576 :
    ThetaLowerSegment 1145528576 1145594112 (57273744656221 / 50000) (57277041440137 / 50000) := by
  exact
    packedTile65536 1145528576 1145594112 13 3161 33845 30 _ _ (260739 / 12500) (417183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145594112 :
    ThetaLowerSegment 1145594112 1145659648 (57277041440137 / 50000)
      (114560759900591 / 100000) := by
  exact
    packedTile65536 1145594112 1145659648 13 3201 33846 30 _ _ (2085917 / 100000) (13037 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145659648 :
    ThetaLowerSegment 1145659648 1145725184 (114560759900591 / 100000) (2291345901947 / 2000) := by
  exact
    packedTile65536 1145659648 1145725184 13 3133 33847 30 _ _ (2085923 / 100000) (1042963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145725184 :
    ThetaLowerSegment 1145725184 1145790720 (2291345901947 / 2000) (458295045909 / 400) := by
  exact
    packedTile65536 1145725184 1145790720 13 3100 33848 30 _ _ (2085929 / 100000) (521483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145790720 :
    ThetaLowerSegment 1145790720 1145856256 (458295045909 / 400) (22916063514191 / 20000) := by
  exact
    packedTile65536 1145790720 1145856256 13 3143 33849 30 _ _ (417187 / 20000) (1042969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145856256 :
    ThetaLowerSegment 1145856256 1145921792 (22916063514191 / 20000) (22917375570451 / 20000) := by
  exact
    packedTile65536 1145856256 1145921792 13 3145 33850 30 _ _ (104297 / 5000) (2085943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145921792 :
    ThetaLowerSegment 1145921792 1145987328 (22917375570451 / 20000)
      (114593557051347 / 100000) := by
  exact
    packedTile65536 1145921792 1145987328 13 3202 33851 30 _ _ (1042973 / 50000) (2085949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1145987328 :
    ThetaLowerSegment 1145987328 1146052864 (114593557051347 / 100000)
      (114600048533971 / 100000) := by
  exact
    packedTile65536 1145987328 1146052864 13 3112 33852 30 _ _ (65186 / 3125) (417191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146052864 :
    ThetaLowerSegment 1146052864 1146118400 (114600048533971 / 100000)
      (57303377442863 / 50000) := by
  exact
    packedTile65536 1146052864 1146118400 13 3215 33853 30 _ _ (2085957 / 100000) (52149 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146118400 :
    ThetaLowerSegment 1146118400 1146183936 (57303377442863 / 50000) (28653333503257 / 25000) := by
  exact
    packedTile65536 1146118400 1146183936 13 3154 33854 30 _ _ (2085963 / 100000) (1042983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146183936 :
    ThetaLowerSegment 1146183936 1146249472 (28653333503257 / 25000)
      (114620007027859 / 100000) := by
  exact
    packedTile65536 1146183936 1146249472 13 3199 33855 30 _ _ (2085969 / 100000) (521493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146249472 :
    ThetaLowerSegment 1146249472 1146315008 (114620007027859 / 100000)
      (114626615396659 / 100000) := by
  exact
    packedTile65536 1146249472 1146315008 13 3168 33856 30 _ _ (83439 / 4000) (1042989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146315008 :
    ThetaLowerSegment 1146315008 1146380544 (114626615396659 / 100000)
      (114633275930799 / 100000) := by
  exact
    packedTile65536 1146315008 1146380544 13 3193 33857 30 _ _ (104299 / 5000) (2085983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146380544 :
    ThetaLowerSegment 1146380544 1146446080 (114633275930799 / 100000)
      (22927963516579 / 20000) := by
  exact
    packedTile65536 1146380544 1146446080 13 3136 33858 30 _ _ (1042993 / 50000) (2085989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146446080 :
    ThetaLowerSegment 1146446080 1146511616 (22927963516579 / 20000)
      (114646350909839 / 100000) := by
  exact
    packedTile65536 1146446080 1146511616 13 3132 33859 30 _ _ (260749 / 12500) (417199 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146511616 :
    ThetaLowerSegment 1146511616 1146577152 (114646350909839 / 100000)
      (22930566837703 / 20000) := by
  exact
    packedTile65536 1146511616 1146577152 13 3108 33860 30 _ _ (2085997 / 100000) (1043 / 50)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146577152 :
    ThetaLowerSegment 1146577152 1146642688 (22930566837703 / 20000) (57329680645951 / 50000) := by
  exact
    packedTile65536 1146577152 1146642688 13 3129 33861 30 _ _ (2086003 / 100000) (1043003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146642688 :
    ThetaLowerSegment 1146642688 1146708224 (57329680645951 / 50000) (57332959852099 / 50000) := by
  exact
    packedTile65536 1146642688 1146708224 13 3144 33862 30 _ _ (2086009 / 100000) (521503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146708224 :
    ThetaLowerSegment 1146708224 1146773760 (57332959852099 / 50000) (28668103888727 / 25000) := by
  exact
    packedTile65536 1146708224 1146773760 13 3114 33863 30 _ _ (417203 / 20000) (1043009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146773760 :
    ThetaLowerSegment 1146773760 1146839296 (28668103888727 / 25000) (28669741414427 / 25000) := by
  exact
    packedTile65536 1146773760 1146839296 13 3140 33864 30 _ _ (104301 / 5000) (2086023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146839296 :
    ThetaLowerSegment 1146839296 1146904832 (28669741414427 / 25000) (57342748502557 / 50000) := by
  exact
    packedTile65536 1146839296 1146904832 13 3131 33865 30 _ _ (1043013 / 50000) (2086029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146904832 :
    ThetaLowerSegment 1146904832 1146970368 (57342748502557 / 50000) (57346017314701 / 50000) := by
  exact
    packedTile65536 1146904832 1146970368 13 3134 33865 30 _ _ (130377 / 6250) (417207 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1146970368 :
    ThetaLowerSegment 1146970368 1147035904 (57346017314701 / 50000)
      (114698474225621 / 100000) := by
  exact
    packedTile65536 1146970368 1147035904 13 3087 33866 30 _ _ (2086037 / 100000) (52151 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147035904 :
    ThetaLowerSegment 1147035904 1147101440 (114698474225621 / 100000)
      (114705057777329 / 100000) := by
  exact
    packedTile65536 1147035904 1147101440 13 3156 33867 30 _ _ (2086043 / 100000) (1043023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147101440 :
    ThetaLowerSegment 1147101440 1147166976 (114705057777329 / 100000)
      (114711587110699 / 100000) := by
  exact
    packedTile65536 1147101440 1147166976 13 3130 33868 30 _ _ (2086049 / 100000) (521513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147166976 :
    ThetaLowerSegment 1147166976 1147232512 (114711587110699 / 100000)
      (114718033020649 / 100000) := by
  exact
    packedTile65536 1147166976 1147232512 13 3090 33869 30 _ _ (417211 / 20000) (1043029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147232512 :
    ThetaLowerSegment 1147232512 1147298048 (114718033020649 / 100000)
      (114724539441789 / 100000) := by
  exact
    packedTile65536 1147232512 1147298048 13 3119 33870 30 _ _ (104303 / 5000) (2086063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147298048 :
    ThetaLowerSegment 1147298048 1147363584 (114724539441789 / 100000)
      (114731068828369 / 100000) := by
  exact
    packedTile65536 1147298048 1147363584 13 3130 33871 30 _ _ (1043033 / 50000) (2086069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147363584 :
    ThetaLowerSegment 1147363584 1147429120 (114731068828369 / 100000)
      (114737569028721 / 100000) := by
  exact
    packedTile65536 1147363584 1147429120 13 3116 33872 30 _ _ (260759 / 12500) (83443 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147429120 :
    ThetaLowerSegment 1147429120 1147494656 (114737569028721 / 100000)
      (57372044009673 / 50000) := by
  exact
    packedTile65536 1147429120 1147494656 13 3125 33873 30 _ _ (2086077 / 100000) (13038 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147494656 :
    ThetaLowerSegment 1147494656 1147560192 (57372044009673 / 50000)
      (114750736365867 / 100000) := by
  exact
    packedTile65536 1147494656 1147560192 13 3187 33874 30 _ _ (2086083 / 100000) (1043043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147560192 :
    ThetaLowerSegment 1147560192 1147625728 (114750736365867 / 100000)
      (14344673612961 / 12500) := by
  exact
    packedTile65536 1147560192 1147625728 13 3189 33875 30 _ _ (2086089 / 100000) (521523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147625728 :
    ThetaLowerSegment 1147625728 1147691264 (14344673612961 / 12500) (57381988395849 / 50000) := by
  exact
    packedTile65536 1147625728 1147691264 13 3158 33876 30 _ _ (417219 / 20000) (1043049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147691264 :
    ThetaLowerSegment 1147691264 1147756800 (57381988395849 / 50000) (57385294864349 / 50000) := by
  exact
    packedTile65536 1147691264 1147756800 13 3170 33877 30 _ _ (20861 / 1000) (2086103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147756800 :
    ThetaLowerSegment 1147756800 1147822336 (57385294864349 / 50000) (28694285546911 / 25000) := by
  exact
    packedTile65536 1147756800 1147822336 13 3141 33878 30 _ _ (1043053 / 50000) (2086109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147822336 :
    ThetaLowerSegment 1147822336 1147887872 (28694285546911 / 25000) (28695913235799 / 25000) := by
  exact
    packedTile65536 1147822336 1147887872 13 3121 33879 30 _ _ (65191 / 3125) (417223 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147887872 :
    ThetaLowerSegment 1147887872 1147953408 (28695913235799 / 25000)
      (114790222125629 / 100000) := by
  exact
    packedTile65536 1147887872 1147953408 13 3149 33880 30 _ _ (2086117 / 100000) (52153 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1147953408 :
    ThetaLowerSegment 1147953408 1148018944 (114790222125629 / 100000)
      (28699189487247 / 25000) := by
  exact
    packedTile65536 1147953408 1148018944 13 3133 33881 30 _ _ (2086123 / 100000) (1043063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148018944 :
    ThetaLowerSegment 1148018944 1148084480 (28699189487247 / 25000)
      (114803364719531 / 100000) := by
  exact
    packedTile65536 1148018944 1148084480 13 3167 33882 30 _ _ (2086129 / 100000) (521533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148084480 :
    ThetaLowerSegment 1148084480 1148150016 (114803364719531 / 100000)
      (114809936044781 / 100000) := by
  exact
    packedTile65536 1148084480 1148150016 13 3150 33883 30 _ _ (417227 / 20000) (1043069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148150016 :
    ThetaLowerSegment 1148150016 1148215552 (114809936044781 / 100000)
      (114816488610521 / 100000) := by
  exact
    packedTile65536 1148150016 1148215552 13 3141 33884 30 _ _ (104307 / 5000) (2086143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148215552 :
    ThetaLowerSegment 1148215552 1148281088 (114816488610521 / 100000)
      (114822916026347 / 100000) := by
  exact
    packedTile65536 1148215552 1148281088 13 3081 33885 30 _ _ (1043073 / 50000) (2086149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148281088 :
    ThetaLowerSegment 1148281088 1148346624 (114822916026347 / 100000)
      (114829587540443 / 100000) := by
  exact
    packedTile65536 1148281088 1148346624 13 3198 33886 30 _ _ (260769 / 12500) (417231 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148346624 :
    ThetaLowerSegment 1148346624 1148412160 (114829587540443 / 100000)
      (57418093027517 / 50000) := by
  exact
    packedTile65536 1148346624 1148412160 13 3163 33887 30 _ _ (2086157 / 100000) (26077 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148412160 :
    ThetaLowerSegment 1148412160 1148477696 (57418093027517 / 50000)
      (114842880552101 / 100000) := by
  exact
    packedTile65536 1148412160 1148477696 13 3209 33888 30 _ _ (2086163 / 100000) (1043083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148477696 :
    ThetaLowerSegment 1148477696 1148543232 (114842880552101 / 100000)
      (114849376882367 / 100000) := by
  exact
    packedTile65536 1148477696 1148543232 13 3114 33889 30 _ _ (2086169 / 100000) (521543 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148543232 :
    ThetaLowerSegment 1148543232 1148608768 (114849376882367 / 100000)
      (114856086021167 / 100000) := by
  exact
    packedTile65536 1148543232 1148608768 13 3216 33890 30 _ _ (83447 / 4000) (1043089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148608768 :
    ThetaLowerSegment 1148608768 1148674304 (114856086021167 / 100000)
      (114862619936927 / 100000) := by
  exact
    packedTile65536 1148608768 1148674304 13 3132 33891 30 _ _ (104309 / 5000) (2086183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148674304 :
    ThetaLowerSegment 1148674304 1148739840 (114862619936927 / 100000)
      (114869212284687 / 100000) := by
  exact
    packedTile65536 1148674304 1148739840 13 3160 33892 30 _ _ (1043093 / 50000) (2086189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148739840 :
    ThetaLowerSegment 1148739840 1148805376 (114869212284687 / 100000)
      (114875648187007 / 100000) := by
  exact
    packedTile65536 1148739840 1148805376 13 3085 33893 30 _ _ (130387 / 6250) (417239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148805376 :
    ThetaLowerSegment 1148805376 1148870912 (114875648187007 / 100000) (4595284115221 / 4000) := by
  exact
    packedTile65536 1148805376 1148870912 13 3094 33894 30 _ _ (2086197 / 100000) (10431 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148870912 :
    ThetaLowerSegment 1148870912 1148936448 (4595284115221 / 4000) (114888495006517 / 100000) := by
  exact
    packedTile65536 1148870912 1148936448 13 3064 33894 30 _ _ (2086203 / 100000) (1043103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1148936448 :
    ThetaLowerSegment 1148936448 1149001984 (114888495006517 / 100000)
      (11489508116833 / 10000) := by
  exact
    packedTile65536 1148936448 1149001984 13 3157 33895 30 _ _ (2086209 / 100000) (521553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149001984 :
    ThetaLowerSegment 1149001984 1149067520 (11489508116833 / 10000) (11490165274243 / 10000) := by
  exact
    packedTile65536 1149001984 1149067520 13 3150 33896 30 _ _ (1043107 / 50000) (2086217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149067520 :
    ThetaLowerSegment 1149067520 1149133056 (11490165274243 / 10000) (11490827231849 / 10000) := by
  exact
    packedTile65536 1149067520 1149133056 13 3173 33897 30 _ _ (104311 / 5000) (2086223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149133056 :
    ThetaLowerSegment 1149133056 1149198592 (11490827231849 / 10000) (3591088677241 / 3125) := by
  exact
    packedTile65536 1149133056 1149198592 13 3147 33898 30 _ _ (1043113 / 50000) (2086229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149198592 :
    ThetaLowerSegment 1149198592 1149264128 (3591088677241 / 3125) (3591295735767 / 3125) := by
  exact
    packedTile65536 1149198592 1149264128 13 3176 33899 30 _ _ (260779 / 12500) (417247 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149264128 :
    ThetaLowerSegment 1149264128 1149329664 (3591295735767 / 3125) (57463967525859 / 50000) := by
  exact
    packedTile65536 1149264128 1149329664 13 3102 33900 30 _ _ (2086237 / 100000) (13039 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149329664 :
    ThetaLowerSegment 1149329664 1149395200 (57463967525859 / 50000) (14366811253403 / 12500) := by
  exact
    packedTile65536 1149329664 1149395200 13 3142 33901 30 _ _ (2086243 / 100000) (1043123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149395200 :
    ThetaLowerSegment 1149395200 1149460736 (14366811253403 / 12500) (919527642503 / 800) := by
  exact
    packedTile65536 1149395200 1149460736 13 3099 33902 30 _ _ (2086249 / 100000) (521563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149460736 :
    ThetaLowerSegment 1149460736 1149526272 (919527642503 / 800) (114947635498183 / 100000) := by
  exact
    packedTile65536 1149460736 1149526272 13 3202 33903 30 _ _ (1043127 / 50000) (2086257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149526272 :
    ThetaLowerSegment 1149526272 1149591808 (114947635498183 / 100000)
      (114954157146943 / 100000) := by
  exact
    packedTile65536 1149526272 1149591808 13 3126 33904 30 _ _ (104313 / 5000) (2086263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149591808 :
    ThetaLowerSegment 1149591808 1149657344 (114954157146943 / 100000)
      (114960799817887 / 100000) := by
  exact
    packedTile65536 1149591808 1149657344 13 3184 33905 30 _ _ (1043133 / 50000) (2086269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149657344 :
    ThetaLowerSegment 1149657344 1149722880 (114960799817887 / 100000)
      (57483638844671 / 50000) := by
  exact
    packedTile65536 1149657344 1149722880 13 3105 33906 30 _ _ (2086271 / 100000) (1043137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149722880 :
    ThetaLowerSegment 1149722880 1149788416 (57483638844671 / 50000) (11497383694423 / 10000) := by
  exact
    packedTile65536 1149722880 1149788416 13 3144 33907 30 _ _ (2086277 / 100000) (52157 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149788416 :
    ThetaLowerSegment 1149788416 1149853952 (11497383694423 / 10000)
      (114980323198077 / 100000) := by
  exact
    packedTile65536 1149788416 1149853952 13 3109 33908 30 _ _ (2086283 / 100000) (1043143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149853952 :
    ThetaLowerSegment 1149853952 1149919488 (114980323198077 / 100000)
      (114986928389051 / 100000) := by
  exact
    packedTile65536 1149853952 1149919488 13 3166 33909 30 _ _ (2086289 / 100000) (521573 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149919488 :
    ThetaLowerSegment 1149919488 1149985024 (114986928389051 / 100000)
      (22998696287701 / 20000) := by
  exact
    packedTile65536 1149919488 1149985024 13 3141 33910 30 _ _ (1043147 / 50000) (2086297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1149985024 :
    ThetaLowerSegment 1149985024 1150050560 (22998696287701 / 20000) (22999998556161 / 20000) := by
  exact
    packedTile65536 1149985024 1150050560 13 3121 33911 30 _ _ (20863 / 1000) (2086303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150050560 :
    ThetaLowerSegment 1150050560 1150116096 (22999998556161 / 20000)
      (115006727376573 / 100000) := by
  exact
    packedTile65536 1150050560 1150116096 13 3228 33912 30 _ _ (1043153 / 50000) (2086309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150116096 :
    ThetaLowerSegment 1150116096 1150181632 (115006727376573 / 100000)
      (11501325127107 / 10000) := by
  exact
    packedTile65536 1150116096 1150181632 13 3127 33913 30 _ _ (2086311 / 100000) (1043157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150181632 :
    ThetaLowerSegment 1150181632 1150247168 (11501325127107 / 10000) (2300396046129 / 2000) := by
  exact
    packedTile65536 1150181632 1150247168 13 3140 33914 30 _ _ (2086317 / 100000) (26079 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150247168 :
    ThetaLowerSegment 1150247168 1150312704 (2300396046129 / 2000) (57513168335043 / 50000) := by
  exact
    packedTile65536 1150247168 1150312704 13 3132 33915 30 _ _ (2086323 / 100000) (1043163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150312704 :
    ThetaLowerSegment 1150312704 1150378240 (57513168335043 / 50000) (11503292529391 / 10000) := by
  exact
    packedTile65536 1150312704 1150378240 13 3158 33916 30 _ _ (260791 / 12500) (2086331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150378240 :
    ThetaLowerSegment 1150378240 1150443776 (11503292529391 / 10000) (14379939502877 / 12500) := by
  exact
    packedTile65536 1150378240 1150443776 13 3159 33917 30 _ _ (1043167 / 50000) (2086337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150443776 :
    ThetaLowerSegment 1150443776 1150509312 (14379939502877 / 12500) (14380761520837 / 12500) := by
  exact
    packedTile65536 1150443776 1150509312 13 3152 33918 30 _ _ (104317 / 5000) (2086343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150509312 :
    ThetaLowerSegment 1150509312 1150574848 (14380761520837 / 12500) (57526339380509 / 50000) := by
  exact
    packedTile65536 1150509312 1150574848 13 3157 33919 30 _ _ (1043173 / 50000) (2086349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150574848 :
    ThetaLowerSegment 1150574848 1150640384 (57526339380509 / 50000)
      (115059194435191 / 100000) := by
  exact
    packedTile65536 1150574848 1150640384 13 3123 33920 30 _ _ (2086351 / 100000) (1043177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150640384 :
    ThetaLowerSegment 1150640384 1150705920 (115059194435191 / 100000)
      (115065649623749 / 100000) := by
  exact
    packedTile65536 1150640384 1150705920 13 3094 33921 30 _ _ (2086357 / 100000) (52159 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150705920 :
    ThetaLowerSegment 1150705920 1150771456 (115065649623749 / 100000)
      (115072376058061 / 100000) := by
  exact
    packedTile65536 1150705920 1150771456 13 3224 33922 30 _ _ (2086363 / 100000) (1043183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150771456 :
    ThetaLowerSegment 1150771456 1150836992 (115072376058061 / 100000)
      (115078868835277 / 100000) := by
  exact
    packedTile65536 1150771456 1150836992 13 3112 33923 30 _ _ (65199 / 3125) (2086371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150836992 :
    ThetaLowerSegment 1150836992 1150902528 (115078868835277 / 100000)
      (115085468036239 / 100000) := by
  exact
    packedTile65536 1150836992 1150902528 13 3163 33923 30 _ _ (1043187 / 50000) (2086377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150902528 :
    ThetaLowerSegment 1150902528 1150968064 (115085468036239 / 100000)
      (115091965023559 / 100000) := by
  exact
    packedTile65536 1150902528 1150968064 13 3114 33924 30 _ _ (104319 / 5000) (2086383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1150968064 :
    ThetaLowerSegment 1150968064 1151033600 (115091965023559 / 100000)
      (57549207019797 / 50000) := by
  exact
    packedTile65536 1150968064 1151033600 13 3091 33925 30 _ _ (417277 / 20000) (521597 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151033600 :
    ThetaLowerSegment 1151033600 1151099136 (57549207019797 / 50000) (7194056941323 / 6250) := by
  exact
    packedTile65536 1151033600 1151099136 13 3114 33926 30 _ _ (2086391 / 100000) (1043197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151099136 :
    ThetaLowerSegment 1151099136 1151164672 (7194056941323 / 6250) (28777857241349 / 25000) := by
  exact
    packedTile65536 1151099136 1151164672 13 3124 33927 30 _ _ (2086397 / 100000) (2608 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151164672 :
    ThetaLowerSegment 1151164672 1151230208 (28777857241349 / 25000)
      (115118078331757 / 100000) := by
  exact
    packedTile65536 1151164672 1151230208 13 3187 33928 30 _ _ (2086403 / 100000) (1043203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151230208 :
    ThetaLowerSegment 1151230208 1151295744 (115118078331757 / 100000) (920996720089 / 800) := by
  exact
    packedTile65536 1151230208 1151295744 13 3121 33929 30 _ _ (260801 / 12500) (2086411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151295744 :
    ThetaLowerSegment 1151295744 1151361280 (920996720089 / 800) (23026228270217 / 20000) := by
  exact
    packedTile65536 1151295744 1151361280 13 3140 33930 30 _ _ (1043207 / 50000) (2086417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151361280 :
    ThetaLowerSegment 1151361280 1151426816 (23026228270217 / 20000) (23027541880249 / 20000) := by
  exact
    packedTile65536 1151361280 1151426816 13 3148 33931 30 _ _ (104321 / 5000) (2086423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151426816 :
    ThetaLowerSegment 1151426816 1151492352 (23027541880249 / 20000) (23028857162569 / 20000) := by
  exact
    packedTile65536 1151426816 1151492352 13 3152 33932 30 _ _ (83457 / 4000) (521607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151492352 :
    ThetaLowerSegment 1151492352 1151557888 (23028857162569 / 20000)
      (115150866416219 / 100000) := by
  exact
    packedTile65536 1151492352 1151557888 13 3154 33933 30 _ _ (2086431 / 100000) (1043217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151557888 :
    ThetaLowerSegment 1151557888 1151623424 (115150866416219 / 100000)
      (115157459557139 / 100000) := by
  exact
    packedTile65536 1151557888 1151623424 13 3160 33934 30 _ _ (2086437 / 100000) (52161 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151623424 :
    ThetaLowerSegment 1151623424 1151688960 (115157459557139 / 100000)
      (115164044368091 / 100000) := by
  exact
    packedTile65536 1151623424 1151688960 13 3156 33935 30 _ _ (1043221 / 50000) (417289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151688960 :
    ThetaLowerSegment 1151688960 1151754496 (115164044368091 / 100000)
      (115170618765739 / 100000) := by
  exact
    packedTile65536 1151688960 1151754496 13 3151 33936 30 _ _ (130403 / 6250) (2086451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151754496 :
    ThetaLowerSegment 1151754496 1151820032 (115170618765739 / 100000)
      (115177284986269 / 100000) := by
  exact
    packedTile65536 1151754496 1151820032 13 3195 33937 30 _ _ (1043227 / 50000) (2086457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151820032 :
    ThetaLowerSegment 1151820032 1151885568 (115177284986269 / 100000)
      (115183836467529 / 100000) := by
  exact
    packedTile65536 1151820032 1151885568 13 3140 33938 30 _ _ (2086459 / 100000) (1043231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151885568 :
    ThetaLowerSegment 1151885568 1151951104 (115183836467529 / 100000)
      (115190371275909 / 100000) := by
  exact
    packedTile65536 1151885568 1151951104 13 3132 33939 30 _ _ (417293 / 20000) (521617 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1151951104 :
    ThetaLowerSegment 1151951104 1152016640 (115190371275909 / 100000)
      (115197031291341 / 100000) := by
  exact
    packedTile65536 1151951104 1152016640 13 3192 33940 30 _ _ (2086471 / 100000) (1043237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152016640 :
    ThetaLowerSegment 1152016640 1152082176 (115197031291341 / 100000)
      (115203543182937 / 100000) := by
  exact
    packedTile65536 1152016640 1152082176 13 3121 33941 30 _ _ (521619 / 25000) (2086479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152082176 :
    ThetaLowerSegment 1152082176 1152147712 (115203543182937 / 100000)
      (115210121860683 / 100000) := by
  exact
    packedTile65536 1152082176 1152147712 13 3153 33942 30 _ _ (1043241 / 50000) (417297 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152147712 :
    ThetaLowerSegment 1152147712 1152213248 (115210121860683 / 100000)
      (115216756892523 / 100000) := by
  exact
    packedTile65536 1152147712 1152213248 13 3180 33943 30 _ _ (260811 / 12500) (2086491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152213248 :
    ThetaLowerSegment 1152213248 1152278784 (115216756892523 / 100000)
      (23044662948633 / 20000) := by
  exact
    packedTile65536 1152213248 1152278784 13 3143 33944 30 _ _ (1043247 / 50000) (2086497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152278784 :
    ThetaLowerSegment 1152278784 1152344320 (23044662948633 / 20000) (57614911266773 / 50000) := by
  exact
    packedTile65536 1152278784 1152344320 13 3119 33945 30 _ _ (2086499 / 100000) (1043251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152344320 :
    ThetaLowerSegment 1152344320 1152409856 (57614911266773 / 50000)
      (115236405456821 / 100000) := by
  exact
    packedTile65536 1152344320 1152409856 13 3155 33946 30 _ _ (417301 / 20000) (521627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152409856 :
    ThetaLowerSegment 1152409856 1152475392 (115236405456821 / 100000)
      (57621444123249 / 50000) := by
  exact
    packedTile65536 1152409856 1152475392 13 3107 33947 30 _ _ (2086511 / 100000) (1043257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152475392 :
    ThetaLowerSegment 1152475392 1152540928 (57621444123249 / 50000) (57624705347757 / 50000) := by
  exact
    packedTile65536 1152475392 1152540928 13 3126 33948 30 _ _ (521629 / 25000) (2086519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152540928 :
    ThetaLowerSegment 1152540928 1152606464 (57624705347757 / 50000) (28814003634411 / 25000) := by
  exact
    packedTile65536 1152540928 1152606464 13 3165 33949 30 _ _ (1043261 / 50000) (83461 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152606464 :
    ThetaLowerSegment 1152606464 1152672000 (28814003634411 / 25000) (28815643645419 / 25000) := by
  exact
    packedTile65536 1152606464 1152672000 13 3144 33950 30 _ _ (65204 / 3125) (2086531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152672000 :
    ThetaLowerSegment 1152672000 1152737536 (28815643645419 / 25000)
      (115269178458621 / 100000) := by
  exact
    packedTile65536 1152672000 1152737536 13 3165 33951 30 _ _ (2086533 / 100000) (260817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152737536 :
    ThetaLowerSegment 1152737536 1152803072 (115269178458621 / 100000)
      (115275746883393 / 100000) := by
  exact
    packedTile65536 1152737536 1152803072 13 3148 33951 30 _ _ (2086539 / 100000) (1043271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152803072 :
    ThetaLowerSegment 1152803072 1152868608 (115275746883393 / 100000) (7205138839533 / 6250) := by
  exact
    packedTile65536 1152803072 1152868608 13 3103 33952 30 _ _ (417309 / 20000) (521637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152868608 :
    ThetaLowerSegment 1152868608 1152934144 (7205138839533 / 6250) (57644462758839 / 50000) := by
  exact
    packedTile65536 1152868608 1152934144 13 3213 33953 30 _ _ (41731 / 2000) (2086553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152934144 :
    ThetaLowerSegment 1152934144 1152999680 (57644462758839 / 50000) (57647734478647 / 50000) := by
  exact
    packedTile65536 1152934144 1152999680 13 3136 33954 30 _ _ (521639 / 25000) (2086559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1152999680 :
    ThetaLowerSegment 1152999680 1153065216 (57647734478647 / 50000) (3603189518118 / 3125) := by
  exact
    packedTile65536 1152999680 1153065216 13 3161 33955 30 _ _ (1043281 / 50000) (417313 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153065216 :
    ThetaLowerSegment 1153065216 1153130752 (3603189518118 / 3125) (28827137407503 / 25000) := by
  exact
    packedTile65536 1153065216 1153130752 13 3108 33956 30 _ _ (2086567 / 100000) (208657 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153130752 :
    ThetaLowerSegment 1153130752 1153196288 (28827137407503 / 25000) (14414398116519 / 12500) := by
  exact
    packedTile65536 1153130752 1153196288 13 3180 33957 30 _ _ (2086573 / 100000) (130411 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153196288 :
    ThetaLowerSegment 1153196288 1153261824 (14414398116519 / 12500) (7207621590507 / 6250) := by
  exact
    packedTile65536 1153196288 1153261824 13 3240 33958 30 _ _ (2086579 / 100000) (1043291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153261824 :
    ThetaLowerSegment 1153261824 1153327360 (7207621590507 / 6250) (115328415948197 / 100000) := by
  exact
    packedTile65536 1153261824 1153327360 13 3101 33959 30 _ _ (417317 / 20000) (521647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153327360 :
    ThetaLowerSegment 1153327360 1153392896 (115328415948197 / 100000)
      (115334944888307 / 100000) := by
  exact
    packedTile65536 1153327360 1153392896 13 3129 33960 30 _ _ (208659 / 10000) (2086593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153392896 :
    ThetaLowerSegment 1153392896 1153458432 (115334944888307 / 100000)
      (23068302698503 / 20000) := by
  exact
    packedTile65536 1153392896 1153458432 13 3148 33961 30 _ _ (521649 / 25000) (2086599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153458432 :
    ThetaLowerSegment 1153458432 1153523968 (23068302698503 / 20000) (23069590131937 / 20000) := by
  exact
    packedTile65536 1153458432 1153523968 13 3085 33962 30 _ _ (1043301 / 50000) (417321 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153523968 :
    ThetaLowerSegment 1153523968 1153589504 (23069590131937 / 20000) (3604829314937 / 3125) := by
  exact
    packedTile65536 1153523968 1153589504 13 3157 33963 30 _ _ (2086607 / 100000) (208661 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153589504 :
    ThetaLowerSegment 1153589504 1153655040 (3604829314937 / 3125) (115361142208129 / 100000) := by
  exact
    packedTile65536 1153589504 1153655040 13 3165 33964 30 _ _ (2086613 / 100000) (260827 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153655040 :
    ThetaLowerSegment 1153655040 1153720576 (115361142208129 / 100000)
      (14420966208039 / 12500) := by
  exact
    packedTile65536 1153655040 1153720576 13 3157 33965 30 _ _ (2086619 / 100000) (1043311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153720576 :
    ThetaLowerSegment 1153720576 1153786112 (14420966208039 / 12500) (14421793032799 / 12500) := by
  exact
    packedTile65536 1153720576 1153786112 13 3170 33966 30 _ _ (65207 / 3125) (2086627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153786112 :
    ThetaLowerSegment 1153786112 1153851648 (14421793032799 / 12500) (57690463790021 / 50000) := by
  exact
    packedTile65536 1153786112 1153851648 13 3155 33967 30 _ _ (208663 / 10000) (2086633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153851648 :
    ThetaLowerSegment 1153851648 1153917184 (57690463790021 / 50000) (57693702249093 / 50000) := by
  exact
    packedTile65536 1153851648 1153917184 13 3104 33968 30 _ _ (521659 / 25000) (2086639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153917184 :
    ThetaLowerSegment 1153917184 1153982720 (57693702249093 / 50000)
      (115394000370387 / 100000) := by
  exact
    packedTile65536 1153917184 1153982720 13 3161 33969 30 _ _ (2086641 / 100000) (521661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1153982720 :
    ThetaLowerSegment 1153982720 1154048256 (115394000370387 / 100000)
      (57700231358073 / 50000) := by
  exact
    packedTile65536 1153982720 1154048256 13 3097 33970 30 _ _ (2086647 / 100000) (41733 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154048256 :
    ThetaLowerSegment 1154048256 1154113792 (57700231358073 / 50000) (4616285015967 / 4000) := by
  exact
    packedTile65536 1154048256 1154113792 13 3193 33971 30 _ _ (2086653 / 100000) (65208 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154113792 :
    ThetaLowerSegment 1154113792 1154179328 (4616285015967 / 4000) (115413723411771 / 100000) := by
  exact
    packedTile65536 1154113792 1154179328 13 3162 33972 30 _ _ (1043329 / 50000) (2086661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154179328 :
    ThetaLowerSegment 1154179328 1154244864 (115413723411771 / 100000)
      (23084049264687 / 20000) := by
  exact
    packedTile65536 1154179328 1154244864 13 3126 33973 30 _ _ (260833 / 12500) (2086667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154244864 :
    ThetaLowerSegment 1154244864 1154310400 (23084049264687 / 20000) (23085371796133 / 20000) := by
  exact
    packedTile65536 1154244864 1154310400 13 3169 33974 30 _ _ (208667 / 10000) (2086673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154310400 :
    ThetaLowerSegment 1154310400 1154375936 (23085371796133 / 20000) (23086672211993 / 20000) := by
  exact
    packedTile65536 1154310400 1154375936 13 3116 33975 30 _ _ (83467 / 4000) (1043339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154375936 :
    ThetaLowerSegment 1154375936 1154441472 (23086672211993 / 20000)
      (115439942451839 / 100000) := by
  exact
    packedTile65536 1154375936 1154441472 13 3154 33976 30 _ _ (2086681 / 100000) (521671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154441472 :
    ThetaLowerSegment 1154441472 1154507008 (115439942451839 / 100000) (7215403176787 / 6250) := by
  exact
    packedTile65536 1154441472 1154507008 13 3119 33977 30 _ _ (2086687 / 100000) (208669 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154507008 :
    ThetaLowerSegment 1154507008 1154572544 (7215403176787 / 6250) (28863259628809 / 25000) := by
  exact
    packedTile65536 1154507008 1154572544 13 3157 33978 30 _ _ (521673 / 25000) (417339 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154572544 :
    ThetaLowerSegment 1154572544 1154638080 (28863259628809 / 25000) (57729760942961 / 50000) := by
  exact
    packedTile65536 1154572544 1154638080 13 3107 33979 30 _ _ (1043349 / 50000) (2086701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154638080 :
    ThetaLowerSegment 1154638080 1154703616 (57729760942961 / 50000) (57732989074049 / 50000) := by
  exact
    packedTile65536 1154638080 1154703616 13 3094 33979 30 _ _ (130419 / 6250) (2086707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154703616 :
    ThetaLowerSegment 1154703616 1154769152 (57732989074049 / 50000)
      (115472482420051 / 100000) := by
  exact
    packedTile65536 1154703616 1154769152 13 3117 33980 30 _ _ (2086709 / 100000) (260839 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154769152 :
    ThetaLowerSegment 1154769152 1154834688 (115472482420051 / 100000)
      (115479088959741 / 100000) := by
  exact
    packedTile65536 1154769152 1154834688 13 3166 33981 30 _ _ (417343 / 20000) (1043359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154834688 :
    ThetaLowerSegment 1154834688 1154900224 (115479088959741 / 100000)
      (115485624569913 / 100000) := by
  exact
    packedTile65536 1154834688 1154900224 13 3132 33982 30 _ _ (2086721 / 100000) (521681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154900224 :
    ThetaLowerSegment 1154900224 1154965760 (115485624569913 / 100000)
      (115492245751511 / 100000) := by
  exact
    packedTile65536 1154900224 1154965760 13 3173 33983 30 _ _ (1043363 / 50000) (2086729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1154965760 :
    ThetaLowerSegment 1154965760 1155031296 (115492245751511 / 100000)
      (115498731314567 / 100000) := by
  exact
    packedTile65536 1154965760 1155031296 13 3108 33984 30 _ _ (521683 / 25000) (417347 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155031296 :
    ThetaLowerSegment 1155031296 1155096832 (115498731314567 / 100000) (924042286069 / 800) := by
  exact
    packedTile65536 1155031296 1155096832 13 3141 33985 30 _ _ (1043369 / 50000) (2086741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155096832 :
    ThetaLowerSegment 1155096832 1155162368 (924042286069 / 800) (115511819354089 / 100000) := by
  exact
    packedTile65536 1155096832 1155162368 13 3131 33986 30 _ _ (260843 / 12500) (2086747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155162368 :
    ThetaLowerSegment 1155162368 1155227904 (115511819354089 / 100000)
      (28879594501549 / 25000) := by
  exact
    packedTile65536 1155162368 1155227904 13 3143 33987 30 _ _ (2086749 / 100000) (65211 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155227904 :
    ThetaLowerSegment 1155227904 1155293440 (28879594501549 / 25000)
      (115525007626831 / 100000) := by
  exact
    packedTile65536 1155227904 1155293440 13 3177 33988 30 _ _ (417351 / 20000) (1043379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155293440 :
    ThetaLowerSegment 1155293440 1155358976 (115525007626831 / 100000)
      (23106334548293 / 20000) := by
  exact
    packedTile65536 1155293440 1155358976 13 3194 33989 30 _ _ (2086761 / 100000) (521691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155358976 :
    ThetaLowerSegment 1155358976 1155424512 (23106334548293 / 20000)
      (115538175104321 / 100000) := by
  exact
    packedTile65536 1155358976 1155424512 13 3116 33990 30 _ _ (1043383 / 50000) (2086769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155424512 :
    ThetaLowerSegment 1155424512 1155490048 (115538175104321 / 100000)
      (115544704613909 / 100000) := by
  exact
    packedTile65536 1155424512 1155490048 13 3129 33991 30 _ _ (521693 / 25000) (83471 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155490048 :
    ThetaLowerSegment 1155490048 1155555584 (115544704613909 / 100000)
      (115551315526613 / 100000) := by
  exact
    packedTile65536 1155490048 1155555584 13 3168 33992 30 _ _ (1043389 / 50000) (2086781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155555584 :
    ThetaLowerSegment 1155555584 1155621120 (115551315526613 / 100000)
      (115557809595309 / 100000) := by
  exact
    packedTile65536 1155555584 1155621120 13 3112 33993 30 _ _ (2086783 / 100000) (1043393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155621120 :
    ThetaLowerSegment 1155621120 1155686656 (115557809595309 / 100000)
      (115564408022127 / 100000) := by
  exact
    packedTile65536 1155621120 1155686656 13 3162 33994 30 _ _ (2086789 / 100000) (260849 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155686656 :
    ThetaLowerSegment 1155686656 1155752192 (115564408022127 / 100000)
      (115570852045087 / 100000) := by
  exact
    packedTile65536 1155686656 1155752192 13 3088 33995 30 _ _ (417359 / 20000) (1043399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155752192 :
    ThetaLowerSegment 1155752192 1155817728 (115570852045087 / 100000)
      (115577325298687 / 100000) := by
  exact
    packedTile65536 1155752192 1155817728 13 3102 33996 30 _ _ (5217 / 250) (2086803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155817728 :
    ThetaLowerSegment 1155817728 1155883264 (115577325298687 / 100000)
      (115583888303557 / 100000) := by
  exact
    packedTile65536 1155817728 1155883264 13 3145 33997 30 _ _ (1043403 / 50000) (2086809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155883264 :
    ThetaLowerSegment 1155883264 1155948800 (115583888303557 / 100000)
      (115590482629477 / 100000) := by
  exact
    packedTile65536 1155883264 1155948800 13 3160 33998 30 _ _ (521703 / 25000) (417363 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1155948800 :
    ThetaLowerSegment 1155948800 1156014336 (115590482629477 / 100000)
      (115597031061223 / 100000) := by
  exact
    packedTile65536 1155948800 1156014336 13 3138 33999 30 _ _ (2086817 / 100000) (104341 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156014336 :
    ThetaLowerSegment 1156014336 1156079872 (115597031061223 / 100000)
      (115603658811071 / 100000) := by
  exact
    packedTile65536 1156014336 1156079872 13 3176 34000 30 _ _ (2086823 / 100000) (1043413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156079872 :
    ThetaLowerSegment 1156079872 1156145408 (115603658811071 / 100000)
      (11561040135557 / 10000) := by
  exact
    packedTile65536 1156079872 1156145408 13 3231 34001 30 _ _ (2086829 / 100000) (130427 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156145408 :
    ThetaLowerSegment 1156145408 1156210944 (11561040135557 / 10000) (11561699575101 / 10000) := by
  exact
    packedTile65536 1156145408 1156210944 13 3160 34002 30 _ _ (1043417 / 50000) (2086837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156210944 :
    ThetaLowerSegment 1156210944 1156276480 (11561699575101 / 10000) (11562353590757 / 10000) := by
  exact
    packedTile65536 1156210944 1156276480 13 3134 34003 30 _ _ (52171 / 2500) (2086843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156276480 :
    ThetaLowerSegment 1156276480 1156342016 (11562353590757 / 10000) (28907513281907 / 25000) := by
  exact
    packedTile65536 1156276480 1156342016 13 3123 34004 30 _ _ (1043423 / 50000) (2086849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156342016 :
    ThetaLowerSegment 1156342016 1156407552 (28907513281907 / 25000)
      (115636637142533 / 100000) := by
  exact
    packedTile65536 1156342016 1156407552 13 3155 34005 30 _ _ (2086851 / 100000) (1043427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156407552 :
    ThetaLowerSegment 1156407552 1156473088 (115636637142533 / 100000)
      (115643298390077 / 100000) := by
  exact
    packedTile65536 1156407552 1156473088 13 3192 34005 30 _ _ (2086857 / 100000) (104343 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156473088 :
    ThetaLowerSegment 1156473088 1156538624 (115643298390077 / 100000)
      (115649705059487 / 100000) := by
  exact
    packedTile65536 1156473088 1156538624 13 3070 34006 30 _ _ (2086863 / 100000) (1043433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156538624 :
    ThetaLowerSegment 1156538624 1156604160 (115649705059487 / 100000)
      (115656264085611 / 100000) := by
  exact
    packedTile65536 1156538624 1156604160 13 3143 34007 30 _ _ (521717 / 25000) (2086871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156604160 :
    ThetaLowerSegment 1156604160 1156669696 (115656264085611 / 100000)
      (115662831478089 / 100000) := by
  exact
    packedTile65536 1156604160 1156669696 13 3147 34008 30 _ _ (1043437 / 50000) (2086877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156669696 :
    ThetaLowerSegment 1156669696 1156735232 (115662831478089 / 100000)
      (115669304979849 / 100000) := by
  exact
    packedTile65536 1156669696 1156735232 13 3102 34009 30 _ _ (13043 / 625) (2086883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156735232 :
    ThetaLowerSegment 1156735232 1156800768 (115669304979849 / 100000)
      (57837929942817 / 50000) := by
  exact
    packedTile65536 1156735232 1156800768 13 3141 34010 30 _ _ (417377 / 20000) (260861 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156800768 :
    ThetaLowerSegment 1156800768 1156866304 (57837929942817 / 50000) (11568240437581 / 10000) := by
  exact
    packedTile65536 1156800768 1156866304 13 3136 34011 30 _ _ (2086891 / 100000) (1043447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156866304 :
    ThetaLowerSegment 1156866304 1156931840 (11568240437581 / 10000) (57844524527929 / 50000) := by
  exact
    packedTile65536 1156866304 1156931840 13 3184 34012 30 _ _ (2086897 / 100000) (20869 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156931840 :
    ThetaLowerSegment 1156931840 1156997376 (57844524527929 / 50000) (57847813485481 / 50000) := by
  exact
    packedTile65536 1156931840 1156997376 13 3152 34013 30 _ _ (1043451 / 50000) (417381 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1156997376 :
    ThetaLowerSegment 1156997376 1157062912 (57847813485481 / 50000) (57851098278673 / 50000) := by
  exact
    packedTile65536 1156997376 1157062912 13 3148 34014 30 _ _ (521727 / 25000) (2086911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157062912 :
    ThetaLowerSegment 1157062912 1157128448 (57851098278673 / 50000) (14463587161807 / 12500) := by
  exact
    packedTile65536 1157062912 1157128448 13 3115 34015 30 _ _ (1043457 / 50000) (2086917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157128448 :
    ThetaLowerSegment 1157128448 1157193984 (14463587161807 / 12500) (28928833424219 / 25000) := by
  exact
    packedTile65536 1157128448 1157193984 13 3180 34016 30 _ _ (2086919 / 100000) (1043461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157193984 :
    ThetaLowerSegment 1157193984 1157259520 (28928833424219 / 25000) (14465250438647 / 12500) := by
  exact
    packedTile65536 1157193984 1157259520 13 3196 34017 30 _ _ (83477 / 4000) (130433 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157259520 :
    ThetaLowerSegment 1157259520 1157325056 (14465250438647 / 12500) (23145702529393 / 20000) := by
  exact
    packedTile65536 1157259520 1157325056 13 3119 34018 30 _ _ (2086931 / 100000) (1043467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157325056 :
    ThetaLowerSegment 1157325056 1157390592 (23145702529393 / 20000)
      (115734973800821 / 100000) := by
  exact
    packedTile65536 1157325056 1157390592 13 3096 34019 30 _ _ (260867 / 12500) (2086939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157390592 :
    ThetaLowerSegment 1157390592 1157456128 (115734973800821 / 100000)
      (115741493407629 / 100000) := by
  exact
    packedTile65536 1157390592 1157456128 13 3124 34020 30 _ _ (1043471 / 50000) (417389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157456128 :
    ThetaLowerSegment 1157456128 1157521664 (115741493407629 / 100000)
      (115748006772337 / 100000) := by
  exact
    packedTile65536 1157456128 1157521664 13 3121 34021 30 _ _ (521737 / 25000) (2086951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157521664 :
    ThetaLowerSegment 1157521664 1157587200 (115748006772337 / 100000)
      (28938651951169 / 25000) := by
  exact
    packedTile65536 1157521664 1157587200 13 3163 34022 30 _ _ (2086953 / 100000) (521739 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157587200 :
    ThetaLowerSegment 1157587200 1157652736 (28938651951169 / 25000) (28940304822697 / 25000) := by
  exact
    packedTile65536 1157587200 1157652736 13 3168 34023 30 _ _ (2086959 / 100000) (1043481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157652736 :
    ThetaLowerSegment 1157652736 1157718272 (28940304822697 / 25000) (57883930006709 / 50000) := by
  exact
    packedTile65536 1157652736 1157718272 13 3182 34024 30 _ _ (417393 / 20000) (260871 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157718272 :
    ThetaLowerSegment 1157718272 1157783808 (57883930006709 / 50000) (57887166897179 / 50000) := by
  exact
    packedTile65536 1157718272 1157783808 13 3102 34025 30 _ _ (208697 / 10000) (2086973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157783808 :
    ThetaLowerSegment 1157783808 1157849344 (57887166897179 / 50000) (57890446579963 / 50000) := by
  exact
    packedTile65536 1157783808 1157849344 13 3143 34026 30 _ _ (65218 / 3125) (2086979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157849344 :
    ThetaLowerSegment 1157849344 1157914880 (57890446579963 / 50000) (28946872527507 / 25000) := by
  exact
    packedTile65536 1157849344 1157914880 13 3161 34027 30 _ _ (1043491 / 50000) (417397 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157914880 :
    ThetaLowerSegment 1157914880 1157980416 (28946872527507 / 25000)
      (115793966030689 / 100000) := by
  exact
    packedTile65536 1157914880 1157980416 13 3103 34028 30 _ _ (2086987 / 100000) (208699 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1157980416 :
    ThetaLowerSegment 1157980416 1158045952 (115793966030689 / 100000)
      (57900281507781 / 50000) := by
  exact
    packedTile65536 1157980416 1158045952 13 3161 34029 30 _ _ (2086993 / 100000) (521749 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158045952 :
    ThetaLowerSegment 1158045952 1158111488 (57900281507781 / 50000) (11580710784129 / 10000) := by
  exact
    packedTile65536 1158045952 1158111488 13 3136 34030 30 _ _ (1043499 / 50000) (2087001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158111488 :
    ThetaLowerSegment 1158111488 1158177024 (11580710784129 / 10000) (57906810690387 / 50000) := by
  exact
    packedTile65536 1158111488 1158177024 13 3121 34031 30 _ _ (521751 / 25000) (2087007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158177024 :
    ThetaLowerSegment 1158177024 1158242560 (57906810690387 / 50000) (28955013908151 / 25000) := by
  exact
    packedTile65536 1158177024 1158242560 13 3083 34032 30 _ _ (208701 / 10000) (2087013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158242560 :
    ThetaLowerSegment 1158242560 1158308096 (28955013908151 / 25000)
      (115826640164929 / 100000) := by
  exact
    packedTile65536 1158242560 1158308096 13 3155 34032 30 _ _ (417403 / 20000) (1043509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158308096 :
    ThetaLowerSegment 1158308096 1158373632 (115826640164929 / 100000)
      (57916585226819 / 50000) := by
  exact
    packedTile65536 1158308096 1158373632 13 3129 34033 30 _ _ (2087021 / 100000) (130439 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158373632 :
    ThetaLowerSegment 1158373632 1158439168 (57916585226819 / 50000) (57919832640831 / 50000) := by
  exact
    packedTile65536 1158373632 1158439168 13 3112 34034 30 _ _ (2087027 / 100000) (208703 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158439168 :
    ThetaLowerSegment 1158439168 1158504704 (57919832640831 / 50000) (57923122846779 / 50000) := by
  exact
    packedTile65536 1158439168 1158504704 13 3153 34035 30 _ _ (260879 / 12500) (417407 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158504704 :
    ThetaLowerSegment 1158504704 1158570240 (57923122846779 / 50000) (57926437063123 / 50000) := by
  exact
    packedTile65536 1158504704 1158570240 13 3176 34036 30 _ _ (1043519 / 50000) (2087041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158570240 :
    ThetaLowerSegment 1158570240 1158635776 (57926437063123 / 50000) (57929639632141 / 50000) := by
  exact
    packedTile65536 1158570240 1158635776 13 3069 34037 30 _ _ (521761 / 25000) (2087047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158635776 :
    ThetaLowerSegment 1158635776 1158701312 (57929639632141 / 50000) (57932912124973 / 50000) := by
  exact
    packedTile65536 1158635776 1158701312 13 3136 34038 30 _ _ (2087049 / 100000) (521763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158701312 :
    ThetaLowerSegment 1158701312 1158766848 (57932912124973 / 50000)
      (115872262814621 / 100000) := by
  exact
    packedTile65536 1158701312 1158766848 13 3085 34039 30 _ _ (417411 / 20000) (1043529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158766848 :
    ThetaLowerSegment 1158766848 1158832384 (115872262814621 / 100000)
      (57939421658977 / 50000) := by
  exact
    packedTile65536 1158766848 1158832384 13 3153 34040 30 _ _ (2087061 / 100000) (260883 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158832384 :
    ThetaLowerSegment 1158832384 1158897920 (57939421658977 / 50000) (57942685830201 / 50000) := by
  exact
    packedTile65536 1158832384 1158897920 13 3128 34041 30 _ _ (1043533 / 50000) (2087069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158897920 :
    ThetaLowerSegment 1158897920 1158963456 (57942685830201 / 50000) (11589188123797 / 10000) := by
  exact
    packedTile65536 1158897920 1158963456 13 3119 34042 30 _ _ (65221 / 3125) (83483 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1158963456 :
    ThetaLowerSegment 1158963456 1159028992 (11589188123797 / 10000) (28974635275967 / 25000) := by
  exact
    packedTile65536 1158963456 1159028992 13 3191 34043 30 _ _ (1043539 / 50000) (2087081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159028992 :
    ThetaLowerSegment 1159028992 1159094528 (28974635275967 / 25000)
      (115905109154069 / 100000) := by
  exact
    packedTile65536 1159028992 1159094528 13 3147 34044 30 _ _ (2087083 / 100000) (1043543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159094528 :
    ThetaLowerSegment 1159094528 1159160064 (115905109154069 / 100000)
      (28977929741233 / 25000) := by
  exact
    packedTile65536 1159094528 1159160064 13 3167 34045 30 _ _ (2087089 / 100000) (521773 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159160064 :
    ThetaLowerSegment 1159160064 1159225600 (28977929741233 / 25000) (57959063173291 / 50000) := by
  exact
    packedTile65536 1159160064 1159225600 13 3070 34046 30 _ _ (417419 / 20000) (1043549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159225600 :
    ThetaLowerSegment 1159225600 1159291136 (57959063173291 / 50000) (57962322179941 / 50000) := by
  exact
    packedTile65536 1159225600 1159291136 13 3123 34047 30 _ _ (20871 / 1000) (2087103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159291136 :
    ThetaLowerSegment 1159291136 1159356672 (57962322179941 / 50000) (57965623981633 / 50000) := by
  exact
    packedTile65536 1159291136 1159356672 13 3164 34048 30 _ _ (1043553 / 50000) (2087109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159356672 :
    ThetaLowerSegment 1159356672 1159422208 (57965623981633 / 50000) (57968859005233 / 50000) := by
  exact
    packedTile65536 1159356672 1159422208 13 3100 34049 30 _ _ (260889 / 12500) (417423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159422208 :
    ThetaLowerSegment 1159422208 1159487744 (57968859005233 / 50000) (57972164998561 / 50000) := by
  exact
    packedTile65536 1159422208 1159487744 13 3168 34050 30 _ _ (2087117 / 100000) (26089 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159487744 :
    ThetaLowerSegment 1159487744 1159553280 (57972164998561 / 50000) (7246924744011 / 6250) := by
  exact
    packedTile65536 1159487744 1159553280 13 3098 34051 30 _ _ (2087123 / 100000) (1043563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159553280 :
    ThetaLowerSegment 1159553280 1159618816 (7246924744011 / 6250) (4638293228203 / 4000) := by
  exact
    packedTile65536 1159553280 1159618816 13 3131 34052 30 _ _ (2087129 / 100000) (521783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159618816 :
    ThetaLowerSegment 1159618816 1159684352 (4638293228203 / 4000) (115963846737423 / 100000) := by
  exact
    packedTile65536 1159618816 1159684352 13 3122 34053 30 _ _ (1043567 / 50000) (2087137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159684352 :
    ThetaLowerSegment 1159684352 1159749888 (115963846737423 / 100000)
      (115970429576983 / 100000) := by
  exact
    packedTile65536 1159684352 1159749888 13 3154 34054 30 _ _ (104357 / 5000) (2087143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159749888 :
    ThetaLowerSegment 1159749888 1159815424 (115970429576983 / 100000)
      (115977035394073 / 100000) := by
  exact
    packedTile65536 1159749888 1159815424 13 3165 34055 30 _ _ (1043573 / 50000) (2087149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159815424 :
    ThetaLowerSegment 1159815424 1159880960 (115977035394073 / 100000)
      (57991797654833 / 50000) := by
  exact
    packedTile65536 1159815424 1159880960 13 3143 34056 30 _ _ (2087151 / 100000) (1043577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159880960 :
    ThetaLowerSegment 1159880960 1159946496 (57991797654833 / 50000)
      (115990126023919 / 100000) := by
  exact
    packedTile65536 1159880960 1159946496 13 3129 34057 30 _ _ (2087157 / 100000) (52179 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1159946496 :
    ThetaLowerSegment 1159946496 1160012032 (115990126023919 / 100000)
      (115996656753817 / 100000) := by
  exact
    packedTile65536 1159946496 1160012032 13 3129 34057 30 _ _ (1043581 / 50000) (417433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160012032 :
    ThetaLowerSegment 1160012032 1160077568 (115996656753817 / 100000)
      (116003273076377 / 100000) := by
  exact
    packedTile65536 1160012032 1160077568 13 3170 34058 30 _ _ (65224 / 3125) (2087171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160077568 :
    ThetaLowerSegment 1160077568 1160143104 (116003273076377 / 100000)
      (116009901941001 / 100000) := by
  exact
    packedTile65536 1160077568 1160143104 13 3176 34059 30 _ _ (1043587 / 50000) (2087177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160143104 :
    ThetaLowerSegment 1160143104 1160208640 (116009901941001 / 100000)
      (23203281118153 / 20000) := by
  exact
    packedTile65536 1160143104 1160208640 13 3116 34060 30 _ _ (2087179 / 100000) (1043591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160208640 :
    ThetaLowerSegment 1160208640 1160274176 (23203281118153 / 20000) (2900570174679 / 2500) := by
  exact
    packedTile65536 1160208640 1160274176 13 3067 34061 30 _ _ (417437 / 20000) (521797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160274176 :
    ThetaLowerSegment 1160274176 1160339712 (2900570174679 / 2500) (116029325284653 / 100000) := by
  exact
    packedTile65536 1160274176 1160339712 13 3123 34062 30 _ _ (2087191 / 100000) (1043597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160339712 :
    ThetaLowerSegment 1160339712 1160405248 (116029325284653 / 100000)
      (116035993875873 / 100000) := by
  exact
    packedTile65536 1160339712 1160405248 13 3195 34063 30 _ _ (521799 / 25000) (2087199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160405248 :
    ThetaLowerSegment 1160405248 1160470784 (116035993875873 / 100000)
      (116042422458033 / 100000) := by
  exact
    packedTile65536 1160405248 1160470784 13 3080 34064 30 _ _ (1043601 / 50000) (417441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160470784 :
    ThetaLowerSegment 1160470784 1160536320 (116042422458033 / 100000)
      (116049024296937 / 100000) := by
  exact
    packedTile65536 1160470784 1160536320 13 3163 34065 30 _ _ (260901 / 12500) (2087211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160536320 :
    ThetaLowerSegment 1160536320 1160601856 (116049024296937 / 100000) (3626737795436 / 3125) := by
  exact
    packedTile65536 1160536320 1160601856 13 3155 34066 30 _ _ (2087213 / 100000) (130451 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160601856 :
    ThetaLowerSegment 1160601856 1160667392 (3626737795436 / 3125) (58031046178083 / 50000) := by
  exact
    packedTile65536 1160601856 1160667392 13 3106 34067 30 _ _ (2087219 / 100000) (1043611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160667392 :
    ThetaLowerSegment 1160667392 1160732928 (58031046178083 / 50000)
      (116068514747491 / 100000) := by
  exact
    packedTile65536 1160667392 1160732928 13 3077 34068 30 _ _ (83489 / 4000) (521807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160732928 :
    ThetaLowerSegment 1160732928 1160798464 (116068514747491 / 100000)
      (116075062388001 / 100000) := by
  exact
    packedTile65536 1160732928 1160798464 13 3137 34069 30 _ _ (208723 / 10000) (2087233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160798464 :
    ThetaLowerSegment 1160798464 1160864000 (116075062388001 / 100000)
      (116081699798481 / 100000) := by
  exact
    packedTile65536 1160798464 1160864000 13 3180 34070 30 _ _ (521809 / 25000) (2087239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160864000 :
    ThetaLowerSegment 1160864000 1160929536 (116081699798481 / 100000)
      (116088264174571 / 100000) := by
  exact
    packedTile65536 1160864000 1160929536 13 3145 34071 30 _ _ (1043621 / 50000) (417449 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160929536 :
    ThetaLowerSegment 1160929536 1160995072 (116088264174571 / 100000)
      (116094889096549 / 100000) := by
  exact
    packedTile65536 1160929536 1160995072 13 3174 34072 30 _ _ (2087247 / 100000) (8349 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1160995072 :
    ThetaLowerSegment 1160995072 1161060608 (116094889096549 / 100000)
      (58050689183063 / 50000) := by
  exact
    packedTile65536 1160995072 1161060608 13 3109 34073 30 _ _ (2087253 / 100000) (260907 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161060608 :
    ThetaLowerSegment 1161060608 1161126144 (58050689183063 / 50000) (58053980788929 / 50000) := by
  exact
    packedTile65536 1161060608 1161126144 13 3154 34074 30 _ _ (1043629 / 50000) (2087261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161126144 :
    ThetaLowerSegment 1161126144 1161191680 (58053980788929 / 50000) (58057259880673 / 50000) := by
  exact
    packedTile65536 1161126144 1161191680 13 3142 34075 30 _ _ (65227 / 3125) (2087267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161191680 :
    ThetaLowerSegment 1161191680 1161257216 (58057259880673 / 50000) (3628785708408 / 3125) := by
  exact
    packedTile65536 1161191680 1161257216 13 3173 34076 30 _ _ (208727 / 10000) (2087273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161257216 :
    ThetaLowerSegment 1161257216 1161322752 (3628785708408 / 3125) (58063846269003 / 50000) := by
  exact
    packedTile65536 1161257216 1161322752 13 3138 34077 30 _ _ (83491 / 4000) (1043639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161322752 :
    ThetaLowerSegment 1161322752 1161339136 (58063846269003 / 50000) (58064681181403 / 50000) := by
  exact
    packedTile65536 1161322752 1161339136 11 800 34078 30 _ _ (2087281 / 100000) (521821 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1161339136 :
    ThetaLowerSegment 1161339136 1161341184 (58064681181403 / 50000) (3629048640001 / 3125) := by
  exact
    packedTile65536 1161339136 1161341184 8 93 34078 30 _ _ (1043641 / 50000) (417457 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1129341184_1161341184 :
    ThetaLowerSegment 1129341184 1161341184 (56465729480737 / 50000) (3629048640001 / 3125) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1129341184 cell1129472256)
                    (ThetaLowerSegment.join cell1129603328 cell1129734400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1129865472 cell1129996544)
                    (ThetaLowerSegment.join cell1130127616 cell1130258688)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1130389760 cell1130520832)
                    (ThetaLowerSegment.join cell1130651904 cell1130782976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1130914048 cell1131045120)
                    (ThetaLowerSegment.join cell1131176192 cell1131307264))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1131438336 cell1131569408)
                    (ThetaLowerSegment.join cell1131700480 cell1131831552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1131962624 cell1132093696)
                    (ThetaLowerSegment.join cell1132224768 cell1132355840)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1132486912 cell1132617984)
                    (ThetaLowerSegment.join cell1132749056 cell1132880128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1133011200 cell1133142272)
                    (ThetaLowerSegment.join cell1133273344 cell1133404416)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1133535488 cell1133666560)
                    (ThetaLowerSegment.join cell1133797632 cell1133928704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1134059776 cell1134190848)
                    (ThetaLowerSegment.join cell1134321920 cell1134452992)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1134584064 cell1134715136)
                    (ThetaLowerSegment.join cell1134846208 cell1134977280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1135042816 cell1135108352)
                    (ThetaLowerSegment.join cell1135173888 cell1135239424))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1135304960 cell1135370496)
                    (ThetaLowerSegment.join cell1135436032 cell1135501568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1135567104 cell1135632640)
                    (ThetaLowerSegment.join cell1135698176 cell1135763712)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1135829248 cell1135894784)
                    (ThetaLowerSegment.join cell1135960320 cell1136025856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1136091392 cell1136156928)
                    (ThetaLowerSegment.join cell1136222464 cell1136288000))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1136353536 cell1136419072)
                    (ThetaLowerSegment.join cell1136484608 cell1136550144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1136615680 cell1136681216)
                    (ThetaLowerSegment.join cell1136746752 cell1136812288)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1136877824 cell1136943360)
                    (ThetaLowerSegment.join cell1137008896 cell1137074432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1137139968 cell1137205504)
                    (ThetaLowerSegment.join cell1137271040 cell1137336576))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1137402112 cell1137467648)
                    (ThetaLowerSegment.join cell1137533184 cell1137598720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1137664256 cell1137729792)
                    (ThetaLowerSegment.join cell1137795328 cell1137860864)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1137926400 cell1137991936)
                    (ThetaLowerSegment.join cell1138057472 cell1138123008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1138188544 cell1138254080)
                    (ThetaLowerSegment.join cell1138319616 cell1138385152)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1138450688 cell1138516224)
                    (ThetaLowerSegment.join cell1138581760 cell1138647296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1138712832 cell1138778368)
                    (ThetaLowerSegment.join cell1138843904 cell1138909440)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1138974976 cell1139040512)
                    (ThetaLowerSegment.join cell1139106048 cell1139171584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1139237120 cell1139302656)
                    (ThetaLowerSegment.join cell1139368192 cell1139433728))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1139499264 cell1139564800)
                    (ThetaLowerSegment.join cell1139630336 cell1139695872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1139761408 cell1139826944)
                    (ThetaLowerSegment.join cell1139892480 cell1139958016)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1140023552 cell1140089088)
                    (ThetaLowerSegment.join cell1140154624 cell1140220160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1140285696 cell1140351232)
                    (ThetaLowerSegment.join cell1140416768 cell1140482304)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1140547840 cell1140613376)
                    (ThetaLowerSegment.join cell1140678912 cell1140744448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1140809984 cell1140875520)
                    (ThetaLowerSegment.join cell1140941056 cell1141006592)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1141072128 cell1141137664)
                    (ThetaLowerSegment.join cell1141203200 cell1141268736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1141334272 cell1141399808)
                    (ThetaLowerSegment.join cell1141465344 cell1141530880))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1141596416 cell1141661952)
                    (ThetaLowerSegment.join cell1141727488 cell1141793024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1141858560 cell1141924096)
                    (ThetaLowerSegment.join cell1141989632 cell1142055168)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1142120704 cell1142186240)
                    (ThetaLowerSegment.join cell1142251776 cell1142317312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1142382848 cell1142448384)
                    (ThetaLowerSegment.join cell1142513920 cell1142579456)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1142644992 cell1142710528)
                    (ThetaLowerSegment.join cell1142776064 cell1142841600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1142907136 cell1142972672)
                    (ThetaLowerSegment.join cell1143038208 cell1143103744)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1143169280 cell1143234816)
                    (ThetaLowerSegment.join cell1143300352 cell1143365888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1143431424 cell1143496960)
                    (ThetaLowerSegment.join cell1143562496 cell1143628032))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1143693568 cell1143759104)
                    (ThetaLowerSegment.join cell1143824640 cell1143890176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1143955712 cell1144021248)
                    (ThetaLowerSegment.join cell1144086784 cell1144152320)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1144217856 cell1144283392)
                    (ThetaLowerSegment.join cell1144348928 cell1144414464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1144480000 cell1144545536)
                    (ThetaLowerSegment.join cell1144611072 cell1144676608))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1144742144 cell1144807680)
                    (ThetaLowerSegment.join cell1144873216 cell1144938752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1145004288 cell1145069824)
                    (ThetaLowerSegment.join cell1145135360 cell1145200896)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1145266432 cell1145331968)
                    (ThetaLowerSegment.join cell1145397504 cell1145463040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1145528576 cell1145594112)
                    (ThetaLowerSegment.join cell1145659648 cell1145725184))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1145790720 cell1145856256)
                    (ThetaLowerSegment.join cell1145921792 cell1145987328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1146052864 cell1146118400)
                    (ThetaLowerSegment.join cell1146183936 cell1146249472)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1146315008 cell1146380544)
                    (ThetaLowerSegment.join cell1146446080 cell1146511616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1146577152 cell1146642688)
                    (ThetaLowerSegment.join cell1146708224 cell1146773760)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1146839296 cell1146904832)
                    (ThetaLowerSegment.join cell1146970368 cell1147035904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1147101440 cell1147166976)
                    (ThetaLowerSegment.join cell1147232512 cell1147298048)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1147363584 cell1147429120)
                    (ThetaLowerSegment.join cell1147494656 cell1147560192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1147625728 cell1147691264)
                    (ThetaLowerSegment.join cell1147756800 cell1147822336))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1147887872 cell1147953408)
                    (ThetaLowerSegment.join cell1148018944 cell1148084480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1148150016 cell1148215552)
                    (ThetaLowerSegment.join cell1148281088 cell1148346624)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1148412160 cell1148477696)
                    (ThetaLowerSegment.join cell1148543232 cell1148608768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1148674304 cell1148739840)
                    (ThetaLowerSegment.join cell1148805376 cell1148870912))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1148936448 cell1149001984)
                    (ThetaLowerSegment.join cell1149067520 cell1149133056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1149198592 cell1149264128)
                    (ThetaLowerSegment.join cell1149329664 cell1149395200)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1149460736 cell1149526272)
                    (ThetaLowerSegment.join cell1149591808 cell1149657344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1149722880 cell1149788416)
                    (ThetaLowerSegment.join cell1149853952 cell1149919488))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1149985024 cell1150050560)
                    (ThetaLowerSegment.join cell1150116096 cell1150181632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1150247168 cell1150312704)
                    (ThetaLowerSegment.join cell1150378240 cell1150443776)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1150509312 cell1150574848)
                    (ThetaLowerSegment.join cell1150640384 cell1150705920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1150771456 cell1150836992)
                    (ThetaLowerSegment.join cell1150902528 cell1150968064)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1151033600 cell1151099136)
                    (ThetaLowerSegment.join cell1151164672 cell1151230208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1151295744 cell1151361280)
                    (ThetaLowerSegment.join cell1151426816 cell1151492352)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1151557888 cell1151623424)
                    (ThetaLowerSegment.join cell1151688960 cell1151754496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1151820032 cell1151885568)
                    (ThetaLowerSegment.join cell1151951104 cell1152016640))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1152082176 cell1152147712)
                    (ThetaLowerSegment.join cell1152213248 cell1152278784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1152344320 cell1152409856)
                    (ThetaLowerSegment.join cell1152475392 cell1152540928)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1152606464 cell1152672000)
                    (ThetaLowerSegment.join cell1152737536 cell1152803072))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1152868608 cell1152934144)
                    (ThetaLowerSegment.join cell1152999680 cell1153065216))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1153130752 cell1153196288)
                    (ThetaLowerSegment.join cell1153261824 cell1153327360))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1153392896 cell1153458432)
                    (ThetaLowerSegment.join cell1153523968 cell1153589504)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1153655040 cell1153720576)
                    (ThetaLowerSegment.join cell1153786112 cell1153851648))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1153917184 cell1153982720)
                    (ThetaLowerSegment.join cell1154048256 cell1154113792))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1154179328 cell1154244864)
                    (ThetaLowerSegment.join cell1154310400 cell1154375936))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1154441472 cell1154507008)
                    (ThetaLowerSegment.join cell1154572544 cell1154638080)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1154703616 cell1154769152)
                    (ThetaLowerSegment.join cell1154834688 cell1154900224))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1154965760 cell1155031296)
                    (ThetaLowerSegment.join cell1155096832 cell1155162368)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1155227904 cell1155293440)
                    (ThetaLowerSegment.join cell1155358976 cell1155424512))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1155490048 cell1155555584)
                    (ThetaLowerSegment.join cell1155621120 cell1155686656)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1155752192 cell1155817728)
                    (ThetaLowerSegment.join cell1155883264 cell1155948800))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1156014336 cell1156079872)
                    (ThetaLowerSegment.join cell1156145408 cell1156210944))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1156276480 cell1156342016)
                    (ThetaLowerSegment.join cell1156407552 cell1156473088))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1156538624 cell1156604160)
                    (ThetaLowerSegment.join cell1156669696 cell1156735232)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1156800768 cell1156866304)
                    (ThetaLowerSegment.join cell1156931840 cell1156997376))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1157062912 cell1157128448)
                    (ThetaLowerSegment.join cell1157193984 cell1157259520)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1157325056 cell1157390592)
                  (ThetaLowerSegment.join cell1157456128 cell1157521664))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1157587200 cell1157652736)
                  (ThetaLowerSegment.join cell1157718272 cell1157783808)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1157849344 cell1157914880)
                  (ThetaLowerSegment.join cell1157980416 cell1158045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1158111488 cell1158177024)
                  (ThetaLowerSegment.join cell1158242560 cell1158308096))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1158373632 cell1158439168)
                  (ThetaLowerSegment.join cell1158504704 cell1158570240))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1158635776 cell1158701312)
                  (ThetaLowerSegment.join cell1158766848 cell1158832384)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1158897920 cell1158963456)
                  (ThetaLowerSegment.join cell1159028992 cell1159094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1159160064 cell1159225600)
                  (ThetaLowerSegment.join cell1159291136 cell1159356672)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1159422208 cell1159487744)
                  (ThetaLowerSegment.join cell1159553280 cell1159618816))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1159684352 cell1159749888)
                  (ThetaLowerSegment.join cell1159815424 cell1159880960)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1159946496 cell1160012032)
                  (ThetaLowerSegment.join cell1160077568 cell1160143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1160208640 cell1160274176)
                  (ThetaLowerSegment.join cell1160339712 cell1160405248))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1160470784 cell1160536320)
                  (ThetaLowerSegment.join cell1160601856 cell1160667392))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1160732928 cell1160798464)
                  (ThetaLowerSegment.join cell1160864000 cell1160929536)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1160995072 cell1161060608)
                  (ThetaLowerSegment.join cell1161126144 cell1161191680))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1161257216 cell1161322752)
                  cell1161339136)))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
