/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1481341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1449341184 :
    ThetaLowerSegment 1449341184 1449472256 (144929050023839 / 100000)
      (144942187591247 / 100000) := by
  exact
    packedTile65536 1449341184 1449472256 14 6228 38070 30 _ _ (527359 / 25000) (2109439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449472256 :
    ThetaLowerSegment 1449472256 1449603328 (144942187591247 / 100000)
      (72477653114851 / 50000) := by
  exact
    packedTile65536 1449472256 1449603328 14 6219 38071 30 _ _ (421889 / 20000) (263681 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449603328 :
    ThetaLowerSegment 1449603328 1449734400 (72477653114851 / 50000) (72484095387367 / 50000) := by
  exact
    packedTile65536 1449603328 1449734400 14 6108 38073 30 _ _ (1054727 / 50000) (2109457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449734400 :
    ThetaLowerSegment 1449734400 1449865472 (72484095387367 / 50000) (72490660036223 / 50000) := by
  exact
    packedTile65536 1449734400 1449865472 14 6224 38075 30 _ _ (2109463 / 100000) (1054733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449865472 :
    ThetaLowerSegment 1449865472 1449996544 (72490660036223 / 50000) (72497240534127 / 50000) := by
  exact
    packedTile65536 1449865472 1449996544 14 6239 38077 30 _ _ (65921 / 3125) (84379 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1449996544 :
    ThetaLowerSegment 1449996544 1450127616 (72497240534127 / 50000) (72503847428619 / 50000) := by
  exact
    packedTile65536 1449996544 1450127616 14 6264 38078 30 _ _ (2109481 / 100000) (527371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1450127616 :
    ThetaLowerSegment 1450127616 1450258688 (72503847428619 / 50000) (72510380519149 / 50000) := by
  exact
    packedTile65536 1450127616 1450258688 14 6194 38080 30 _ _ (210949 / 10000) (2109493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1450258688 :
    ThetaLowerSegment 1450258688 1450389760 (72510380519149 / 50000) (29006781909113 / 20000) := by
  exact
    packedTile65536 1450258688 1450389760 14 6233 38082 30 _ _ (2109499 / 100000) (1054751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1450389760 :
    ThetaLowerSegment 1450389760 1450520832 (29006781909113 / 20000)
      (145046853486653 / 100000) := by
  exact
    packedTile65536 1450389760 1450520832 14 6136 38083 30 _ _ (527377 / 25000) (2109511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1450520832 :
    ThetaLowerSegment 1450520832 1450651904 (145046853486653 / 100000)
      (72529950424649 / 50000) := by
  exact
    packedTile65536 1450520832 1450651904 14 6185 38085 30 _ _ (2109517 / 100000) (26369 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1450651904 :
    ThetaLowerSegment 1450651904 1450782976 (72529950424649 / 50000) (18134120642977 / 12500) := by
  exact
    packedTile65536 1450651904 1450782976 14 6193 38087 30 _ _ (1054763 / 50000) (2109529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1450782976 :
    ThetaLowerSegment 1450782976 1450914048 (18134120642977 / 12500) (72543104402273 / 50000) := by
  exact
    packedTile65536 1450782976 1450914048 14 6278 38089 30 _ _ (421907 / 20000) (1054769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1450914048 :
    ThetaLowerSegment 1450914048 1451045120 (72543104402273 / 50000) (72549654536393 / 50000) := by
  exact
    packedTile65536 1450914048 1451045120 14 6210 38090 30 _ _ (263693 / 12500) (2109547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1451045120 :
    ThetaLowerSegment 1451045120 1451176192 (72549654536393 / 50000) (36278098130123 / 25000) := by
  exact
    packedTile65536 1451045120 1451176192 14 6202 38092 30 _ _ (2109553 / 100000) (527389 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1451176192 :
    ThetaLowerSegment 1451176192 1451307264 (36278098130123 / 25000)
      (145125524550167 / 100000) := by
  exact
    packedTile65536 1451176192 1451307264 14 6225 38094 30 _ _ (2109563 / 100000) (1054783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1451307264 :
    ThetaLowerSegment 1451307264 1451438336 (145125524550167 / 100000)
      (29027718247827 / 20000) := by
  exact
    packedTile65536 1451307264 1451438336 14 6194 38096 30 _ _ (527393 / 25000) (84383 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1451438336 :
    ThetaLowerSegment 1451438336 1451569408 (29027718247827 / 20000) (5806057543497 / 4000) := by
  exact
    packedTile65536 1451438336 1451569408 14 6090 38097 30 _ _ (2109581 / 100000) (131849 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1451569408 :
    ThetaLowerSegment 1451569408 1451700480 (5806057543497 / 4000) (29032928080329 / 20000) := by
  exact
    packedTile65536 1451569408 1451700480 14 6258 38099 30 _ _ (210959 / 10000) (2109593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1451700480 :
    ThetaLowerSegment 1451700480 1451831552 (29032928080329 / 20000) (14517787813537 / 10000) := by
  exact
    packedTile65536 1451700480 1451831552 14 6275 38101 30 _ _ (2109599 / 100000) (1054801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1451831552 :
    ThetaLowerSegment 1451831552 1451962624 (14517787813537 / 10000) (72595432441109 / 50000) := by
  exact
    packedTile65536 1451831552 1451962624 14 6156 38102 30 _ _ (263701 / 12500) (2109611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1451962624 :
    ThetaLowerSegment 1451962624 1452093696 (72595432441109 / 50000)
      (145203900205661 / 100000) := by
  exact
    packedTile65536 1451962624 1452093696 14 6179 38104 30 _ _ (2109617 / 100000) (105481 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1452093696 :
    ThetaLowerSegment 1452093696 1452224768 (145203900205661 / 100000)
      (29043374459187 / 20000) := by
  exact
    packedTile65536 1452093696 1452224768 14 6149 38106 30 _ _ (1054813 / 50000) (2109629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1452224768 :
    ThetaLowerSegment 1452224768 1452355840 (29043374459187 / 20000) (29046014878353 / 20000) := by
  exact
    packedTile65536 1452224768 1452355840 14 6258 38108 30 _ _ (421927 / 20000) (1054819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1452355840 :
    ThetaLowerSegment 1452355840 1452486912 (29046014878353 / 20000)
      (145243221693173 / 100000) := by
  exact
    packedTile65536 1452355840 1452486912 14 6232 38109 30 _ _ (527411 / 25000) (2109647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1452486912 :
    ThetaLowerSegment 1452486912 1452617984 (145243221693173 / 100000)
      (145256335296221 / 100000) := by
  exact
    packedTile65536 1452486912 1452617984 14 6216 38111 30 _ _ (2109653 / 100000) (263707 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1452617984 :
    ThetaLowerSegment 1452617984 1452749056 (145256335296221 / 100000)
      (145269337143127 / 100000) := by
  exact
    packedTile65536 1452617984 1452749056 14 6163 38113 30 _ _ (1054831 / 50000) (421933 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1452749056 :
    ThetaLowerSegment 1452749056 1452880128 (145269337143127 / 100000)
      (145282526806219 / 100000) := by
  exact
    packedTile65536 1452749056 1452880128 14 6252 38114 30 _ _ (2109671 / 100000) (1054837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1452880128 :
    ThetaLowerSegment 1452880128 1453011200 (145282526806219 / 100000)
      (145295670112619 / 100000) := by
  exact
    packedTile65536 1452880128 1453011200 14 6230 38116 30 _ _ (26371 / 1250) (2109683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1453011200 :
    ThetaLowerSegment 1453011200 1453142272 (145295670112619 / 100000)
      (72654314966073 / 50000) := by
  exact
    packedTile65536 1453011200 1453142272 14 6143 38118 30 _ _ (2109689 / 100000) (527423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1453142272 :
    ThetaLowerSegment 1453142272 1453273344 (72654314966073 / 50000) (72660871907457 / 50000) := by
  exact
    packedTile65536 1453142272 1453273344 14 6216 38120 30 _ _ (1054849 / 50000) (2109701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1453273344 :
    ThetaLowerSegment 1453273344 1453404416 (72660871907457 / 50000)
      (145334796572123 / 100000) := by
  exact
    packedTile65536 1453273344 1453404416 14 6187 38121 30 _ _ (2109707 / 100000) (210971 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1453404416 :
    ThetaLowerSegment 1453404416 1453535488 (145334796572123 / 100000)
      (145347963309679 / 100000) := by
  exact
    packedTile65536 1453404416 1453535488 14 6241 38123 30 _ _ (527429 / 25000) (2109719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1453535488 :
    ThetaLowerSegment 1453535488 1453666560 (145347963309679 / 100000)
      (72680533405827 / 50000) := by
  exact
    packedTile65536 1453535488 1453666560 14 6211 38125 30 _ _ (84389 / 4000) (65929 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1453666560 :
    ThetaLowerSegment 1453666560 1453797632 (72680533405827 / 50000) (72687006069739 / 50000) := by
  exact
    packedTile65536 1453666560 1453797632 14 6136 38126 30 _ _ (1054867 / 50000) (2109737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1453797632 :
    ThetaLowerSegment 1453797632 1453928704 (72687006069739 / 50000)
      (145387157948111 / 100000) := by
  exact
    packedTile65536 1453797632 1453928704 14 6231 38128 30 _ _ (2109743 / 100000) (1054873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1453928704 :
    ThetaLowerSegment 1453928704 1454059776 (145387157948111 / 100000)
      (29080067513771 / 20000) := by
  exact
    packedTile65536 1453928704 1454059776 14 6247 38130 30 _ _ (263719 / 12500) (421951 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1454059776 :
    ThetaLowerSegment 1454059776 1454190848 (29080067513771 / 20000) (36353365598009 / 25000) := by
  exact
    packedTile65536 1454059776 1454190848 14 6221 38132 30 _ _ (2109761 / 100000) (527441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1454190848 :
    ThetaLowerSegment 1454190848 1454321920 (36353365598009 / 25000) (36356629412199 / 25000) := by
  exact
    packedTile65536 1454190848 1454321920 14 6188 38133 30 _ _ (210977 / 10000) (2109773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1454321920 :
    ThetaLowerSegment 1454321920 1454452992 (36356629412199 / 25000)
      (145439562412353 / 100000) := by
  exact
    packedTile65536 1454321920 1454452992 14 6183 38135 30 _ _ (2109779 / 100000) (1054891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1454452992 :
    ThetaLowerSegment 1454452992 1454584064 (145439562412353 / 100000)
      (145452742257989 / 100000) := by
  exact
    packedTile65536 1454452992 1454584064 14 6247 38137 30 _ _ (527447 / 25000) (2109791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1454584064 :
    ThetaLowerSegment 1454584064 1454715136 (145452742257989 / 100000)
      (36366423575443 / 25000) := by
  exact
    packedTile65536 1454584064 1454715136 14 6139 38139 30 _ _ (2109797 / 100000) (10549 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1454715136 :
    ThetaLowerSegment 1454715136 1454846208 (36366423575443 / 25000) (3636970326887 / 2500) := by
  exact
    packedTile65536 1454715136 1454846208 14 6218 38140 30 _ _ (1054903 / 50000) (2109809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1454846208 :
    ThetaLowerSegment 1454846208 1454977280 (3636970326887 / 2500) (29098412120773 / 20000) := by
  exact
    packedTile65536 1454846208 1454977280 14 6279 38142 30 _ _ (421963 / 20000) (1054909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1454977280 :
    ThetaLowerSegment 1454977280 1455108352 (29098412120773 / 20000) (29101026192709 / 20000) := by
  exact
    packedTile65536 1454977280 1455108352 14 6195 38144 30 _ _ (65932 / 3125) (2109827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1455108352 :
    ThetaLowerSegment 1455108352 1455239424 (29101026192709 / 20000) (4547449858863 / 3125) := by
  exact
    packedTile65536 1455108352 1455239424 14 6287 38145 30 _ _ (2109833 / 100000) (527459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1455239424 :
    ThetaLowerSegment 1455239424 1455370496 (4547449858863 / 3125) (4547864442816 / 3125) := by
  exact
    packedTile65536 1455239424 1455370496 14 6288 38147 30 _ _ (1054921 / 50000) (421969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1455370496 :
    ThetaLowerSegment 1455370496 1455501568 (4547864442816 / 3125) (72772449687643 / 50000) := by
  exact
    packedTile65536 1455370496 1455501568 14 6274 38149 30 _ _ (2109851 / 100000) (1054927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1455501568 :
    ThetaLowerSegment 1455501568 1455632640 (72772449687643 / 50000) (72778980759273 / 50000) := by
  exact
    packedTile65536 1455501568 1455632640 14 6191 38151 30 _ _ (105493 / 5000) (2109863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1455632640 :
    ThetaLowerSegment 1455632640 1455763712 (72778980759273 / 50000) (18196386140433 / 12500) := by
  exact
    packedTile65536 1455632640 1455763712 14 6222 38152 30 _ _ (2109869 / 100000) (131867 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1455763712 :
    ThetaLowerSegment 1455763712 1455894784 (18196386140433 / 12500) (14558410074109 / 10000) := by
  exact
    packedTile65536 1455763712 1455894784 14 6167 38154 30 _ _ (1054939 / 50000) (2109881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1455894784 :
    ThetaLowerSegment 1455894784 1456025856 (14558410074109 / 10000)
      (145597167271281 / 100000) := by
  exact
    packedTile65536 1455894784 1456025856 14 6193 38156 30 _ _ (2109887 / 100000) (210989 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1456025856 :
    ThetaLowerSegment 1456025856 1456156928 (145597167271281 / 100000)
      (145610185329601 / 100000) := by
  exact
    packedTile65536 1456025856 1456156928 14 6170 38157 30 _ _ (263737 / 12500) (2109899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1456156928 :
    ThetaLowerSegment 1456156928 1456288000 (145610185329601 / 100000)
      (145623368016041 / 100000) := by
  exact
    packedTile65536 1456156928 1456288000 14 6248 38159 30 _ _ (421981 / 20000) (527477 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1456288000 :
    ThetaLowerSegment 1456288000 1456419072 (145623368016041 / 100000)
      (145636487461293 / 100000) := by
  exact
    packedTile65536 1456288000 1456419072 14 6218 38161 30 _ _ (1054957 / 50000) (2109917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1456419072 :
    ThetaLowerSegment 1456419072 1456550144 (145636487461293 / 100000)
      (72824808756061 / 50000) := by
  exact
    packedTile65536 1456419072 1456550144 14 6223 38163 30 _ _ (2109923 / 100000) (1054963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1456550144 :
    ThetaLowerSegment 1456550144 1456681216 (72824808756061 / 50000) (72831366424717 / 50000) := by
  exact
    packedTile65536 1456550144 1456681216 14 6216 38164 30 _ _ (527483 / 25000) (421987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1456681216 :
    ThetaLowerSegment 1456681216 1456812288 (72831366424717 / 50000)
      (145675896771333 / 100000) := by
  exact
    packedTile65536 1456681216 1456812288 14 6239 38166 30 _ _ (2109941 / 100000) (263743 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1456812288 :
    ThetaLowerSegment 1456812288 1456943360 (145675896771333 / 100000)
      (145689026990183 / 100000) := by
  exact
    packedTile65536 1456812288 1456943360 14 6223 38168 30 _ _ (42199 / 2000) (2109953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1456943360 :
    ThetaLowerSegment 1456943360 1457074432 (145689026990183 / 100000)
      (145702121395737 / 100000) := by
  exact
    packedTile65536 1456943360 1457074432 14 6206 38169 30 _ _ (2109959 / 100000) (1054981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1457074432 :
    ThetaLowerSegment 1457074432 1457205504 (145702121395737 / 100000)
      (145715192647497 / 100000) := by
  exact
    packedTile65536 1457074432 1457205504 14 6195 38171 30 _ _ (131873 / 6250) (2109971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1457205504 :
    ThetaLowerSegment 1457205504 1457336576 (145715192647497 / 100000)
      (18216038269319 / 12500) := by
  exact
    packedTile65536 1457205504 1457336576 14 6215 38173 30 _ _ (2109977 / 100000) (105499 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1457336576 :
    ThetaLowerSegment 1457336576 1457467648 (18216038269319 / 12500) (36435318532127 / 25000) := by
  exact
    packedTile65536 1457336576 1457467648 14 6146 38175 30 _ _ (1054993 / 50000) (2109989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1457467648 :
    ThetaLowerSegment 1457467648 1457598720 (36435318532127 / 25000) (9109660443563 / 6250) := by
  exact
    packedTile65536 1457467648 1457598720 14 6300 38176 30 _ _ (421999 / 20000) (1054999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1457598720 :
    ThetaLowerSegment 1457598720 1457729792 (9109660443563 / 6250) (18220952447719 / 12500) := by
  exact
    packedTile65536 1457598720 1457729792 14 6186 38178 30 _ _ (527501 / 25000) (2110007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1457729792 :
    ThetaLowerSegment 1457729792 1457860864 (18220952447719 / 12500)
      (145780792392911 / 100000) := by
  exact
    packedTile65536 1457729792 1457860864 14 6243 38180 30 _ _ (2110013 / 100000) (65938 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1457860864 :
    ThetaLowerSegment 1457860864 1457991936 (145780792392911 / 100000)
      (145793967370279 / 100000) := by
  exact
    packedTile65536 1457860864 1457991936 14 6244 38181 30 _ _ (1055011 / 50000) (84401 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1457991936 :
    ThetaLowerSegment 1457991936 1458123008 (145793967370279 / 100000)
      (36451763973143 / 25000) := by
  exact
    packedTile65536 1457991936 1458123008 14 6203 38183 30 _ _ (2110031 / 100000) (1055017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1458123008 :
    ThetaLowerSegment 1458123008 1458254080 (36451763973143 / 25000) (36455043502813 / 25000) := by
  exact
    packedTile65536 1458123008 1458254080 14 6217 38185 30 _ _ (52751 / 2500) (2110043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1458254080 :
    ThetaLowerSegment 1458254080 1458385152 (36455043502813 / 25000)
      (145833342827061 / 100000) := by
  exact
    packedTile65536 1458254080 1458385152 14 6241 38187 30 _ _ (2110049 / 100000) (527513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1458385152 :
    ThetaLowerSegment 1458385152 1458516224 (145833342827061 / 100000)
      (145846551790141 / 100000) := by
  exact
    packedTile65536 1458385152 1458516224 14 6260 38188 30 _ _ (1055029 / 50000) (2110061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1458516224 :
    ThetaLowerSegment 1458516224 1458647296 (145846551790141 / 100000) (9116219884491 / 6250) := by
  exact
    packedTile65536 1458516224 1458647296 14 6145 38190 30 _ _ (2110067 / 100000) (211007 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1458647296 :
    ThetaLowerSegment 1458647296 1458778368 (9116219884491 / 6250) (18234075605401 / 12500) := by
  exact
    packedTile65536 1458647296 1458778368 14 6202 38192 30 _ _ (527519 / 25000) (2110079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1458778368 :
    ThetaLowerSegment 1458778368 1458909440 (18234075605401 / 12500)
      (145885727461823 / 100000) := by
  exact
    packedTile65536 1458778368 1458909440 14 6219 38193 30 _ _ (422017 / 20000) (263761 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1458909440 :
    ThetaLowerSegment 1458909440 1459040512 (145885727461823 / 100000)
      (145898736191333 / 100000) := by
  exact
    packedTile65536 1458909440 1459040512 14 6165 38195 30 _ _ (1055047 / 50000) (2110097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1459040512 :
    ThetaLowerSegment 1459040512 1459171584 (145898736191333 / 100000)
      (18238972342247 / 12500) := by
  exact
    packedTile65536 1459040512 1459171584 14 6181 38197 30 _ _ (2110103 / 100000) (1055053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1459171584 :
    ThetaLowerSegment 1459171584 1459302656 (18238972342247 / 12500) (18240619020899 / 12500) := by
  exact
    packedTile65536 1459171584 1459302656 14 6243 38199 30 _ _ (65941 / 3125) (422023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1459302656 :
    ThetaLowerSegment 1459302656 1459433728 (18240619020899 / 12500) (36484548821647 / 25000) := by
  exact
    packedTile65536 1459302656 1459433728 14 6276 38200 30 _ _ (2110121 / 100000) (527531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1459433728 :
    ThetaLowerSegment 1459433728 1459564800 (36484548821647 / 25000) (72975697074869 / 50000) := by
  exact
    packedTile65536 1459433728 1459564800 14 6255 38202 30 _ _ (211013 / 10000) (2110133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1459564800 :
    ThetaLowerSegment 1459564800 1459695872 (72975697074869 / 50000)
      (145964571967793 / 100000) := by
  exact
    packedTile65536 1459564800 1459695872 14 6245 38204 30 _ _ (2110139 / 100000) (1055071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1459695872 :
    ThetaLowerSegment 1459695872 1459826944 (145964571967793 / 100000)
      (145977391116893 / 100000) := by
  exact
    packedTile65536 1459695872 1459826944 14 6075 38205 30 _ _ (527537 / 25000) (2110151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1459826944 :
    ThetaLowerSegment 1459826944 1459958016 (145977391116893 / 100000)
      (29198093129933 / 20000) := by
  exact
    packedTile65536 1459826944 1459958016 14 6196 38207 30 _ _ (2110157 / 100000) (26377 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1459958016 :
    ThetaLowerSegment 1459958016 1460089088 (29198093129933 / 20000)
      (146003571890691 / 100000) := by
  exact
    packedTile65536 1459958016 1460089088 14 6211 38209 30 _ _ (1055083 / 50000) (2110169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1460089088 :
    ThetaLowerSegment 1460089088 1460220160 (146003571890691 / 100000)
      (146016760484441 / 100000) := by
  exact
    packedTile65536 1460089088 1460220160 14 6250 38211 30 _ _ (84407 / 4000) (1055089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1460220160 :
    ThetaLowerSegment 1460220160 1460351232 (146016760484441 / 100000)
      (146029799311377 / 100000) := by
  exact
    packedTile65536 1460220160 1460351232 14 6179 38212 30 _ _ (263773 / 12500) (2110187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1460351232 :
    ThetaLowerSegment 1460351232 1460482304 (146029799311377 / 100000)
      (146043026001101 / 100000) := by
  exact
    packedTile65536 1460351232 1460482304 14 6268 38214 30 _ _ (2110193 / 100000) (527549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1460482304 :
    ThetaLowerSegment 1460482304 1460613376 (146043026001101 / 100000)
      (146056212653399 / 100000) := by
  exact
    packedTile65536 1460482304 1460613376 14 6249 38216 30 _ _ (1055101 / 50000) (422041 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1460613376 :
    ThetaLowerSegment 1460613376 1460744448 (146056212653399 / 100000)
      (146069241096113 / 100000) := by
  exact
    packedTile65536 1460613376 1460744448 14 6174 38217 30 _ _ (2110211 / 100000) (1055107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1460744448 :
    ThetaLowerSegment 1460744448 1460875520 (146069241096113 / 100000)
      (146082419420013 / 100000) := by
  exact
    packedTile65536 1460744448 1460875520 14 6245 38219 30 _ _ (105511 / 5000) (2110223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1460875520 :
    ThetaLowerSegment 1460875520 1461006592 (146082419420013 / 100000)
      (146095599910347 / 100000) := by
  exact
    packedTile65536 1460875520 1461006592 14 6246 38221 30 _ _ (2110229 / 100000) (263779 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1461006592 :
    ThetaLowerSegment 1461006592 1461137664 (146095599910347 / 100000)
      (146108753023801 / 100000) := by
  exact
    packedTile65536 1461006592 1461137664 14 6233 38223 30 _ _ (1055119 / 50000) (2110241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1461137664 :
    ThetaLowerSegment 1461137664 1461268736 (146108753023801 / 100000)
      (73060929883959 / 50000) := by
  exact
    packedTile65536 1461137664 1461268736 14 6211 38224 30 _ _ (2110247 / 100000) (8441 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1461268736 :
    ThetaLowerSegment 1461268736 1461399808 (73060929883959 / 50000) (14613500033203 / 10000) := by
  exact
    packedTile65536 1461268736 1461399808 14 6227 38226 30 _ _ (131891 / 6250) (2110259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1461399808 :
    ThetaLowerSegment 1461399808 1461530880 (14613500033203 / 10000) (5845921924021 / 4000) := by
  exact
    packedTile65536 1461399808 1461530880 14 6183 38228 30 _ _ (422053 / 20000) (527567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1461530880 :
    ThetaLowerSegment 1461530880 1461661952 (5845921924021 / 4000) (146161176115079 / 100000) := by
  exact
    packedTile65536 1461530880 1461661952 14 6221 38229 30 _ _ (1055137 / 50000) (2110277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1461661952 :
    ThetaLowerSegment 1461661952 1461793024 (146161176115079 / 100000)
      (29234849018301 / 20000) := by
  exact
    packedTile65536 1461661952 1461793024 14 6193 38231 30 _ _ (1055141 / 50000) (422057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1461793024 :
    ThetaLowerSegment 1461793024 1461924096 (29234849018301 / 20000) (29237482661469 / 20000) := by
  exact
    packedTile65536 1461793024 1461924096 14 6240 38233 30 _ _ (2110291 / 100000) (1055147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1461924096 :
    ThetaLowerSegment 1461924096 1462055168 (29237482661469 / 20000) (29240116315869 / 20000) := by
  exact
    packedTile65536 1461924096 1462055168 14 6240 38235 30 _ _ (21103 / 1000) (2110303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462055168 :
    ThetaLowerSegment 1462055168 1462186240 (29240116315869 / 20000)
      (146213669715763 / 100000) := by
  exact
    packedTile65536 1462055168 1462186240 14 6202 38236 30 _ _ (2110309 / 100000) (263789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462186240 :
    ThetaLowerSegment 1462186240 1462317312 (146213669715763 / 100000)
      (146226700929413 / 100000) := by
  exact
    packedTile65536 1462186240 1462317312 14 6175 38238 30 _ _ (1055159 / 50000) (2110321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462317312 :
    ThetaLowerSegment 1462317312 1462448384 (146226700929413 / 100000)
      (146239827163353 / 100000) := by
  exact
    packedTile65536 1462317312 1462448384 14 6220 38240 30 _ _ (2110327 / 100000) (211033 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462448384 :
    ThetaLowerSegment 1462448384 1462579456 (146239827163353 / 100000)
      (146252744530009 / 100000) := by
  exact
    packedTile65536 1462448384 1462579456 14 6121 38241 30 _ _ (65948 / 3125) (2110339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462579456 :
    ThetaLowerSegment 1462579456 1462710528 (146252744530009 / 100000)
      (146265963731089 / 100000) := by
  exact
    packedTile65536 1462579456 1462710528 14 6264 38243 30 _ _ (422069 / 20000) (527587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462710528 :
    ThetaLowerSegment 1462710528 1462841600 (146265963731089 / 100000)
      (146279028932703 / 100000) := by
  exact
    packedTile65536 1462710528 1462841600 14 6191 38245 30 _ _ (1055177 / 50000) (2110357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462841600 :
    ThetaLowerSegment 1462841600 1462972672 (146279028932703 / 100000)
      (18286510718573 / 12500) := by
  exact
    packedTile65536 1462841600 1462972672 14 6187 38247 30 _ _ (2110363 / 100000) (1055183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1462972672 :
    ThetaLowerSegment 1462972672 1463103744 (18286510718573 / 12500) (4572038015099 / 3125) := by
  exact
    packedTile65536 1462972672 1463103744 14 6222 38248 30 _ _ (527593 / 25000) (16883 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1463103744 :
    ThetaLowerSegment 1463103744 1463234816 (4572038015099 / 3125) (14631860051947 / 10000) := by
  exact
    packedTile65536 1463103744 1463234816 14 6342 38250 30 _ _ (2110381 / 100000) (131899 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1463234816 :
    ThetaLowerSegment 1463234816 1463365888 (14631860051947 / 10000) (14633173980761 / 10000) := by
  exact
    packedTile65536 1463234816 1463365888 14 6226 38252 30 _ _ (211039 / 10000) (2110393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1463365888 :
    ThetaLowerSegment 1463365888 1463496960 (14633173980761 / 10000) (29268962745883 / 20000) := by
  exact
    packedTile65536 1463365888 1463496960 14 6195 38253 30 _ _ (2110399 / 100000) (1055201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1463496960 :
    ThetaLowerSegment 1463496960 1463628032 (29268962745883 / 20000)
      (146357965792071 / 100000) := by
  exact
    packedTile65536 1463496960 1463628032 14 6232 38255 30 _ _ (263801 / 12500) (2110411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1463628032 :
    ThetaLowerSegment 1463628032 1463759104 (146357965792071 / 100000)
      (36592790557393 / 25000) := by
  exact
    packedTile65536 1463628032 1463759104 14 6253 38257 30 _ _ (2110417 / 100000) (105521 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1463759104 :
    ThetaLowerSegment 1463759104 1463890176 (36592790557393 / 25000) (73192109717617 / 50000) := by
  exact
    packedTile65536 1463759104 1463890176 14 6187 38259 30 _ _ (1055213 / 50000) (2110429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1463890176 :
    ThetaLowerSegment 1463890176 1464021248 (73192109717617 / 50000) (36599333419581 / 25000) := by
  exact
    packedTile65536 1463890176 1464021248 14 6214 38260 30 _ _ (422087 / 20000) (1055219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1464021248 :
    ThetaLowerSegment 1464021248 1464152320 (36599333419581 / 25000) (36602663700213 / 25000) := by
  exact
    packedTile65536 1464021248 1464152320 14 6312 38262 30 _ _ (527611 / 25000) (2110447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1464152320 :
    ThetaLowerSegment 1464152320 1464283392 (36602663700213 / 25000)
      (146423775487153 / 100000) := by
  exact
    packedTile65536 1464152320 1464283392 14 6217 38264 30 _ _ (2110453 / 100000) (263807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1464283392 :
    ThetaLowerSegment 1464283392 1464414464 (146423775487153 / 100000)
      (146436811810927 / 100000) := by
  exact
    packedTile65536 1464283392 1464414464 14 6177 38265 30 _ _ (1055231 / 50000) (422093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1464414464 :
    ThetaLowerSegment 1464414464 1464545536 (146436811810927 / 100000)
      (73224886106669 / 50000) := by
  exact
    packedTile65536 1464414464 1464545536 14 6141 38267 30 _ _ (2110471 / 100000) (1055237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1464545536 :
    ThetaLowerSegment 1464545536 1464676608 (73224886106669 / 50000) (73231385329829 / 50000) := by
  exact
    packedTile65536 1464545536 1464676608 14 6159 38269 30 _ _ (26381 / 1250) (2110483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1464676608 :
    ThetaLowerSegment 1464676608 1464807680 (73231385329829 / 50000) (36618964978109 / 25000) := by
  exact
    packedTile65536 1464676608 1464807680 14 6202 38271 30 _ _ (2110489 / 100000) (527623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1464807680 :
    ThetaLowerSegment 1464807680 1464938752 (36618964978109 / 25000)
      (146488883789423 / 100000) := by
  exact
    packedTile65536 1464807680 1464938752 14 6171 38272 30 _ _ (2110497 / 100000) (4221 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1464938752 :
    ThetaLowerSegment 1464938752 1465069824 (146488883789423 / 100000)
      (146502051236357 / 100000) := by
  exact
    packedTile65536 1464938752 1465069824 14 6239 38274 30 _ _ (1055253 / 50000) (2110509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1465069824 :
    ThetaLowerSegment 1465069824 1465200896 (146502051236357 / 100000) (9157202490287 / 6250) := by
  exact
    packedTile65536 1465069824 1465200896 14 6249 38276 30 _ _ (422103 / 20000) (1055259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1465200896 :
    ThetaLowerSegment 1465200896 1465331968 (9157202490287 / 6250) (18316033777471 / 12500) := by
  exact
    packedTile65536 1465200896 1465331968 14 6174 38277 30 _ _ (527631 / 25000) (2110527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1465331968 :
    ThetaLowerSegment 1465331968 1465463040 (18316033777471 / 12500) (73270641883123 / 50000) := by
  exact
    packedTile65536 1465331968 1465463040 14 6166 38279 30 _ _ (2110533 / 100000) (263817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1465463040 :
    ThetaLowerSegment 1465463040 1465594112 (73270641883123 / 50000) (73277275316629 / 50000) := by
  exact
    packedTile65536 1465463040 1465594112 14 6286 38281 30 _ _ (1055271 / 50000) (422109 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1465594112 :
    ThetaLowerSegment 1465594112 1465725184 (73277275316629 / 50000)
      (146567532632459 / 100000) := by
  exact
    packedTile65536 1465594112 1465725184 14 6151 38283 30 _ _ (2110551 / 100000) (1055277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1465725184 :
    ThetaLowerSegment 1465725184 1465856256 (146567532632459 / 100000)
      (146580599109419 / 100000) := by
  exact
    packedTile65536 1465725184 1465856256 14 6191 38284 30 _ _ (13191 / 625) (2110563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1465856256 :
    ThetaLowerSegment 1465856256 1465987328 (146580599109419 / 100000)
      (73296832821049 / 50000) := by
  exact
    packedTile65536 1465856256 1465987328 14 6191 38286 30 _ _ (2110569 / 100000) (527643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1465987328 :
    ThetaLowerSegment 1465987328 1466118400 (73296832821049 / 50000) (73303381944583 / 50000) := by
  exact
    packedTile65536 1465987328 1466118400 14 6206 38288 30 _ _ (1055289 / 50000) (2110581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1466118400 :
    ThetaLowerSegment 1466118400 1466249472 (73303381944583 / 50000)
      (146619813648587 / 100000) := by
  exact
    packedTile65536 1466118400 1466249472 14 6183 38289 30 _ _ (2110587 / 100000) (211059 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1466249472 :
    ThetaLowerSegment 1466249472 1466380544 (146619813648587 / 100000)
      (146632907786171 / 100000) := by
  exact
    packedTile65536 1466249472 1466380544 14 6204 38291 30 _ _ (527649 / 25000) (2110599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1466380544 :
    ThetaLowerSegment 1466380544 1466511616 (146632907786171 / 100000)
      (146645963988701 / 100000) := by
  exact
    packedTile65536 1466380544 1466511616 14 6186 38293 30 _ _ (422121 / 20000) (131913 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1466511616 :
    ThetaLowerSegment 1466511616 1466642688 (146645963988701 / 100000)
      (29331820934293 / 20000) := by
  exact
    packedTile65536 1466511616 1466642688 14 6226 38295 30 _ _ (1055307 / 50000) (2110617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1466642688 :
    ThetaLowerSegment 1466642688 1466773760 (29331820934293 / 20000) (73336165972903 / 50000) := by
  exact
    packedTile65536 1466642688 1466773760 14 6267 38296 30 _ _ (2110623 / 100000) (1055313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1466773760 :
    ThetaLowerSegment 1466773760 1466904832 (73336165972903 / 50000) (73342649834407 / 50000) := by
  exact
    packedTile65536 1466773760 1466904832 14 6144 38298 30 _ _ (263829 / 12500) (422127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1466904832 :
    ThetaLowerSegment 1466904832 1467035904 (73342649834407 / 50000) (29339673329449 / 20000) := by
  exact
    packedTile65536 1466904832 1467035904 14 6191 38300 30 _ _ (2110641 / 100000) (527661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1467035904 :
    ThetaLowerSegment 1467035904 1467166976 (29339673329449 / 20000)
      (146711482220131 / 100000) := by
  exact
    packedTile65536 1467035904 1467166976 14 6214 38301 30 _ _ (2110649 / 100000) (527663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1467166976 :
    ThetaLowerSegment 1467166976 1467298048 (146711482220131 / 100000)
      (146724540861177 / 100000) := by
  exact
    packedTile65536 1467166976 1467298048 14 6187 38303 30 _ _ (1055329 / 50000) (2110661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1467298048 :
    ThetaLowerSegment 1467298048 1467429120 (146724540861177 / 100000)
      (73368804000287 / 50000) := by
  exact
    packedTile65536 1467298048 1467429120 14 6191 38305 30 _ _ (2110667 / 100000) (211067 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1467429120 :
    ThetaLowerSegment 1467429120 1467560192 (73368804000287 / 50000) (73375328099803 / 50000) := by
  exact
    packedTile65536 1467429120 1467560192 14 6182 38307 30 _ _ (527669 / 25000) (2110679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1467560192 :
    ThetaLowerSegment 1467560192 1467691264 (73375328099803 / 50000)
      (146763812099211 / 100000) := by
  exact
    packedTile65536 1467560192 1467691264 14 6233 38308 30 _ _ (422137 / 20000) (65959 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1467691264 :
    ThetaLowerSegment 1467691264 1467822336 (146763812099211 / 100000)
      (146776887848541 / 100000) := by
  exact
    packedTile65536 1467691264 1467822336 14 6195 38310 30 _ _ (1055347 / 50000) (2110697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1467822336 :
    ThetaLowerSegment 1467822336 1467953408 (146776887848541 / 100000)
      (146789919328863 / 100000) := by
  exact
    packedTile65536 1467822336 1467953408 14 6174 38312 30 _ _ (2110703 / 100000) (1055353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1467953408 :
    ThetaLowerSegment 1467953408 1468084480 (146789919328863 / 100000)
      (146803157714527 / 100000) := by
  exact
    packedTile65536 1467953408 1468084480 14 6272 38313 30 _ _ (263839 / 12500) (422143 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1468084480 :
    ThetaLowerSegment 1468084480 1468215552 (146803157714527 / 100000) (5872644532801 / 4000) := by
  exact
    packedTile65536 1468084480 1468215552 14 6138 38315 30 _ _ (2110721 / 100000) (527681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1468215552 :
    ThetaLowerSegment 1468215552 1468346624 (5872644532801 / 4000) (29365857277191 / 20000) := by
  exact
    packedTile65536 1468215552 1468346624 14 6241 38317 30 _ _ (211073 / 10000) (2110733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1468346624 :
    ThetaLowerSegment 1468346624 1468477696 (29365857277191 / 20000) (73421179096291 / 50000) := by
  exact
    packedTile65536 1468346624 1468477696 14 6193 38319 30 _ _ (2110739 / 100000) (1055371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1468477696 :
    ThetaLowerSegment 1468477696 1468608768 (73421179096291 / 50000) (2937111682791 / 2000) := by
  exact
    packedTile65536 1468477696 1468608768 14 6266 38320 30 _ _ (527687 / 25000) (2110751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1468608768 :
    ThetaLowerSegment 1468608768 1468739840 (2937111682791 / 2000) (36717158209831 / 25000) := by
  exact
    packedTile65536 1468608768 1468739840 14 6182 38322 30 _ _ (2110757 / 100000) (52769 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1468739840 :
    ThetaLowerSegment 1468739840 1468870912 (36717158209831 / 25000) (14688167948397 / 10000) := by
  exact
    packedTile65536 1468739840 1468870912 14 6181 38324 30 _ _ (1055383 / 50000) (2110769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1468870912 :
    ThetaLowerSegment 1468870912 1469001984 (14688167948397 / 10000) (18361833384549 / 12500) := by
  exact
    packedTile65536 1468870912 1469001984 14 6153 38325 30 _ _ (1055387 / 50000) (2110777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1469001984 :
    ThetaLowerSegment 1469001984 1469133056 (18361833384549 / 12500) (14690768216437 / 10000) := by
  exact
    packedTile65536 1469001984 1469133056 14 6166 38327 30 _ _ (2110783 / 100000) (1055393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1469133056 :
    ThetaLowerSegment 1469133056 1469264128 (14690768216437 / 10000) (73460398257533 / 50000) := by
  exact
    packedTile65536 1469133056 1469264128 14 6213 38329 30 _ _ (263849 / 12500) (422159 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1469264128 :
    ThetaLowerSegment 1469264128 1469395200 (73460398257533 / 50000)
      (146933906700077 / 100000) := by
  exact
    packedTile65536 1469264128 1469395200 14 6211 38330 30 _ _ (2110801 / 100000) (527701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1469395200 :
    ThetaLowerSegment 1469395200 1469526272 (146933906700077 / 100000)
      (146947044381517 / 100000) := by
  exact
    packedTile65536 1469395200 1469526272 14 6224 38332 30 _ _ (211081 / 10000) (2110813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1469526272 :
    ThetaLowerSegment 1469526272 1469657344 (146947044381517 / 100000)
      (146959975258711 / 100000) := by
  exact
    packedTile65536 1469526272 1469657344 14 6126 38334 30 _ _ (2110819 / 100000) (1055411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1469657344 :
    ThetaLowerSegment 1469657344 1469788416 (146959975258711 / 100000)
      (146973009621611 / 100000) := by
  exact
    packedTile65536 1469657344 1469788416 14 6175 38336 30 _ _ (527707 / 25000) (2110831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1469788416 :
    ThetaLowerSegment 1469788416 1469919488 (146973009621611 / 100000)
      (29397199098167 / 20000) := by
  exact
    packedTile65536 1469788416 1469919488 14 6152 38337 30 _ _ (2110837 / 100000) (52771 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1469919488 :
    ThetaLowerSegment 1469919488 1470050560 (29397199098167 / 20000)
      (146999154504799 / 100000) := by
  exact
    packedTile65536 1469919488 1470050560 14 6234 38339 30 _ _ (1055423 / 50000) (2110849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470050560 :
    ThetaLowerSegment 1470050560 1470181632 (146999154504799 / 100000)
      (73506155732007 / 50000) := by
  exact
    packedTile65536 1470050560 1470181632 14 6233 38341 30 _ _ (422171 / 20000) (1055429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470181632 :
    ThetaLowerSegment 1470181632 1470312704 (73506155732007 / 50000) (73512709964727 / 50000) := by
  exact
    packedTile65536 1470181632 1470312704 14 6210 38342 30 _ _ (131929 / 6250) (2110867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470312704 :
    ThetaLowerSegment 1470312704 1470443776 (73512709964727 / 50000) (2940768120403 / 2000) := by
  exact
    packedTile65536 1470312704 1470443776 14 6152 38344 30 _ _ (2110873 / 100000) (527719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470443776 :
    ThetaLowerSegment 1470443776 1470574848 (2940768120403 / 2000) (919072427989 / 625) := by
  exact
    packedTile65536 1470443776 1470574848 14 6245 38346 30 _ _ (1055441 / 50000) (422177 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470574848 :
    ThetaLowerSegment 1470574848 1470705920 (919072427989 / 625) (7353234855257 / 5000) := by
  exact
    packedTile65536 1470574848 1470705920 14 6210 38348 30 _ _ (211089 / 10000) (2110893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470705920 :
    ThetaLowerSegment 1470705920 1470836992 (7353234855257 / 5000) (147077693910283 / 100000) := by
  exact
    packedTile65536 1470705920 1470836992 14 6157 38349 30 _ _ (2110899 / 100000) (1055451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470836992 :
    ThetaLowerSegment 1470836992 1470968064 (147077693910283 / 100000)
      (147090901861639 / 100000) := by
  exact
    packedTile65536 1470836992 1470968064 14 6257 38351 30 _ _ (527727 / 25000) (2110911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1470968064 :
    ThetaLowerSegment 1470968064 1471099136 (147090901861639 / 100000)
      (73551985274393 / 50000) := by
  exact
    packedTile65536 1470968064 1471099136 14 6191 38353 30 _ _ (2110917 / 100000) (52773 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1471099136 :
    ThetaLowerSegment 1471099136 1471230208 (73551985274393 / 50000) (18389620940021 / 12500) := by
  exact
    packedTile65536 1471099136 1471230208 14 6157 38354 30 _ _ (1055463 / 50000) (2110929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1471230208 :
    ThetaLowerSegment 1471230208 1471361280 (18389620940021 / 12500)
      (147130108090543 / 100000) := by
  exact
    packedTile65536 1471230208 1471361280 14 6225 38356 30 _ _ (422187 / 20000) (1055469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1471361280 :
    ThetaLowerSegment 1471361280 1471492352 (147130108090543 / 100000)
      (147143198054287 / 100000) := by
  exact
    packedTile65536 1471361280 1471492352 14 6201 38358 30 _ _ (65967 / 3125) (2110947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1471492352 :
    ThetaLowerSegment 1471492352 1471623424 (147143198054287 / 100000)
      (147156302850511 / 100000) := by
  exact
    packedTile65536 1471492352 1471623424 14 6208 38360 30 _ _ (2110953 / 100000) (527739 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1471623424 :
    ThetaLowerSegment 1471623424 1471754496 (147156302850511 / 100000)
      (147169549137061 / 100000) := by
  exact
    packedTile65536 1471623424 1471754496 14 6275 38361 30 _ _ (1055481 / 50000) (422193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1471754496 :
    ThetaLowerSegment 1471754496 1471885568 (147169549137061 / 100000)
      (147182569606189 / 100000) := by
  exact
    packedTile65536 1471754496 1471885568 14 6168 38363 30 _ _ (2110971 / 100000) (1055487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1471885568 :
    ThetaLowerSegment 1471885568 1472016640 (147182569606189 / 100000)
      (147195710456689 / 100000) := by
  exact
    packedTile65536 1471885568 1472016640 14 6225 38365 30 _ _ (105549 / 5000) (2110983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1472016640 :
    ThetaLowerSegment 1472016640 1472147712 (147195710456689 / 100000)
      (147208910464653 / 100000) := by
  exact
    packedTile65536 1472016640 1472147712 14 6253 38366 30 _ _ (527747 / 25000) (2110991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1472147712 :
    ThetaLowerSegment 1472147712 1472278784 (147208910464653 / 100000)
      (18402777009843 / 12500) := by
  exact
    packedTile65536 1472147712 1472278784 14 6303 38368 30 _ _ (2110997 / 100000) (2111 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1472278784 :
    ThetaLowerSegment 1472278784 1472409856 (18402777009843 / 12500) (73617634214421 / 50000) := by
  exact
    packedTile65536 1472278784 1472409856 14 6183 38370 30 _ _ (1055503 / 50000) (2111009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1472409856 :
    ThetaLowerSegment 1472409856 1472540928 (73617634214421 / 50000) (73624233247311 / 50000) := by
  exact
    packedTile65536 1472409856 1472540928 14 6252 38371 30 _ _ (422203 / 20000) (1055509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1472540928 :
    ThetaLowerSegment 1472540928 1472672000 (73624233247311 / 50000) (73630778477223 / 50000) := by
  exact
    packedTile65536 1472540928 1472672000 14 6201 38373 30 _ _ (131939 / 6250) (2111027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1472672000 :
    ThetaLowerSegment 1472672000 1472803072 (73630778477223 / 50000)
      (147274748799663 / 100000) := by
  exact
    packedTile65536 1472672000 1472803072 14 6249 38375 30 _ _ (2111033 / 100000) (527759 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1472803072 :
    ThetaLowerSegment 1472803072 1472934144 (147274748799663 / 100000)
      (147287830926937 / 100000) := by
  exact
    packedTile65536 1472803072 1472934144 14 6197 38377 30 _ _ (1055521 / 50000) (422209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1472934144 :
    ThetaLowerSegment 1472934144 1473065216 (147287830926937 / 100000)
      (36825238832751 / 25000) := by
  exact
    packedTile65536 1472934144 1473065216 14 6217 38378 30 _ _ (2111051 / 100000) (1055527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1473065216 :
    ThetaLowerSegment 1473065216 1473196288 (36825238832751 / 25000) (36828509920221 / 25000) := by
  exact
    packedTile65536 1473065216 1473196288 14 6198 38380 30 _ _ (105553 / 5000) (2111063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1473196288 :
    ThetaLowerSegment 1473196288 1473327360 (36828509920221 / 25000) (1841591320481 / 1250) := by
  exact
    packedTile65536 1473196288 1473327360 14 6284 38382 30 _ _ (2111069 / 100000) (65971 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1473327360 :
    ThetaLowerSegment 1473327360 1473458432 (1841591320481 / 1250) (29468055641329 / 20000) := by
  exact
    packedTile65536 1473327360 1473458432 14 6145 38383 30 _ _ (2111077 / 100000) (52777 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1473458432 :
    ThetaLowerSegment 1473458432 1473589504 (29468055641329 / 20000)
      (147353160053417 / 100000) := by
  exact
    packedTile65536 1473458432 1473589504 14 6102 38385 30 _ _ (1055543 / 50000) (2111089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1473589504 :
    ThetaLowerSegment 1473589504 1473720576 (147353160053417 / 100000)
      (147366345952787 / 100000) := by
  exact
    packedTile65536 1473589504 1473720576 14 6246 38387 30 _ _ (422219 / 20000) (1055549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1473720576 :
    ThetaLowerSegment 1473720576 1473851648 (147366345952787 / 100000)
      (147379373575571 / 100000) := by
  exact
    packedTile65536 1473720576 1473851648 14 6171 38389 30 _ _ (65972 / 3125) (2111107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1473851648 :
    ThetaLowerSegment 1473851648 1473982720 (147379373575571 / 100000)
      (147392483587301 / 100000) := by
  exact
    packedTile65536 1473851648 1473982720 14 6210 38390 30 _ _ (2111113 / 100000) (527779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1473982720 :
    ThetaLowerSegment 1473982720 1474113792 (147392483587301 / 100000)
      (29481104797579 / 20000) := by
  exact
    packedTile65536 1473982720 1474113792 14 6177 38392 30 _ _ (1055561 / 50000) (16889 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474113792 :
    ThetaLowerSegment 1474113792 1474244864 (29481104797579 / 20000) (14741837022003 / 10000) := by
  exact
    packedTile65536 1474113792 1474244864 14 6085 38394 30 _ _ (2111131 / 100000) (1055567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474244864 :
    ThetaLowerSegment 1474244864 1474310400 (14741837022003 / 10000) (14742505620041 / 10000) := by
  exact
    packedTile65536 1474244864 1474310400 13 3167 38395 30 _ _ (105557 / 5000) (2111143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474310400 :
    ThetaLowerSegment 1474310400 1474441472 (14742505620041 / 10000) (73719122258489 / 50000) := by
  exact
    packedTile65536 1474310400 1474441472 14 6247 38396 30 _ _ (263893 / 12500) (2111147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474441472 :
    ThetaLowerSegment 1474441472 1474572544 (73719122258489 / 50000) (29490300089333 / 20000) := by
  exact
    packedTile65536 1474441472 1474572544 14 6279 38398 30 _ _ (2111153 / 100000) (527789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474572544 :
    ThetaLowerSegment 1474572544 1474703616 (29490300089333 / 20000)
      (147464604429199 / 100000) := by
  exact
    packedTile65536 1474572544 1474703616 14 6207 38400 30 _ _ (1055581 / 50000) (422233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474703616 :
    ThetaLowerSegment 1474703616 1474834688 (147464604429199 / 100000)
      (73738860567311 / 50000) := by
  exact
    packedTile65536 1474703616 1474834688 14 6213 38401 30 _ _ (2111171 / 100000) (1055587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474834688 :
    ThetaLowerSegment 1474834688 1474965760 (73738860567311 / 50000) (73745407336491 / 50000) := by
  exact
    packedTile65536 1474834688 1474965760 14 6202 38403 30 _ _ (105559 / 5000) (2111183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1474965760 :
    ThetaLowerSegment 1474965760 1475096832 (73745407336491 / 50000)
      (147503965269263 / 100000) := by
  exact
    packedTile65536 1474965760 1475096832 14 6229 38405 30 _ _ (2111189 / 100000) (263899 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1475096832 :
    ThetaLowerSegment 1475096832 1475227904 (147503965269263 / 100000)
      (73758547401703 / 50000) := by
  exact
    packedTile65536 1475096832 1475227904 14 6219 38406 30 _ _ (2111197 / 100000) (2639 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1475227904 :
    ThetaLowerSegment 1475227904 1475358976 (73758547401703 / 50000) (1844127804919 / 1250) := by
  exact
    packedTile65536 1475227904 1475358976 14 6219 38408 30 _ _ (1055603 / 50000) (2111209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1475358976 :
    ThetaLowerSegment 1475358976 1475490048 (1844127804919 / 1250) (29508696986987 / 20000) := by
  exact
    packedTile65536 1475358976 1475490048 14 6281 38410 30 _ _ (422243 / 20000) (1055609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1475490048 :
    ThetaLowerSegment 1475490048 1475621120 (29508696986987 / 20000) (5902270159111 / 4000) := by
  exact
    packedTile65536 1475490048 1475621120 14 6285 38412 30 _ _ (263903 / 12500) (2111227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1475621120 :
    ThetaLowerSegment 1475621120 1475752192 (5902270159111 / 4000) (73784882753377 / 50000) := by
  exact
    packedTile65536 1475621120 1475752192 14 6163 38413 30 _ _ (2111233 / 100000) (527809 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1475752192 :
    ThetaLowerSegment 1475752192 1475883264 (73784882753377 / 50000) (73791493052079 / 50000) := by
  exact
    packedTile65536 1475752192 1475883264 14 6262 38415 30 _ _ (1055621 / 50000) (422249 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1475883264 :
    ThetaLowerSegment 1475883264 1476014336 (73791493052079 / 50000) (73798063265191 / 50000) := by
  exact
    packedTile65536 1475883264 1476014336 14 6224 38417 30 _ _ (2111251 / 100000) (1055627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1476014336 :
    ThetaLowerSegment 1476014336 1476145408 (73798063265191 / 50000) (73804647229501 / 50000) := by
  exact
    packedTile65536 1476014336 1476145408 14 6237 38418 30 _ _ (105563 / 5000) (2111263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1476145408 :
    ThetaLowerSegment 1476145408 1476276480 (73804647229501 / 50000)
      (147622466666293 / 100000) := by
  exact
    packedTile65536 1476145408 1476276480 14 6239 38420 30 _ _ (2111269 / 100000) (263909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1476276480 :
    ThetaLowerSegment 1476276480 1476407552 (147622466666293 / 100000)
      (29527080069839 / 20000) := by
  exact
    packedTile65536 1476276480 1476407552 14 6126 38422 30 _ _ (2111277 / 100000) (26391 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1476407552 :
    ThetaLowerSegment 1476407552 1476538624 (29527080069839 / 20000)
      (147648513546541 / 100000) := by
  exact
    packedTile65536 1476407552 1476538624 14 6211 38424 30 _ _ (1055643 / 50000) (2111289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1476538624 :
    ThetaLowerSegment 1476538624 1476669696 (147648513546541 / 100000)
      (147661802037271 / 100000) := by
  exact
    packedTile65536 1476538624 1476669696 14 6294 38425 30 _ _ (422259 / 20000) (1055649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1476669696 :
    ThetaLowerSegment 1476669696 1476800768 (147661802037271 / 100000)
      (147674898455983 / 100000) := by
  exact
    packedTile65536 1476669696 1476800768 14 6203 38427 30 _ _ (263913 / 12500) (2111307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1476800768 :
    ThetaLowerSegment 1476800768 1476931840 (147674898455983 / 100000)
      (29537599408367 / 20000) := by
  exact
    packedTile65536 1476800768 1476931840 14 6204 38429 30 _ _ (2111313 / 100000) (527829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1476931840 :
    ThetaLowerSegment 1476931840 1477062912 (29537599408367 / 20000)
      (147701089349557 / 100000) := by
  exact
    packedTile65536 1476931840 1477062912 14 6201 38430 30 _ _ (1055661 / 50000) (84453 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1477062912 :
    ThetaLowerSegment 1477062912 1477193984 (147701089349557 / 100000) (9232146913723 / 6250) := by
  exact
    packedTile65536 1477062912 1477193984 14 6281 38432 30 _ _ (2111331 / 100000) (1055667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1477193984 :
    ThetaLowerSegment 1477193984 1477325056 (9232146913723 / 6250) (18465943311821 / 12500) := by
  exact
    packedTile65536 1477193984 1477325056 14 6250 38434 30 _ _ (105567 / 5000) (2111343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1477325056 :
    ThetaLowerSegment 1477325056 1477456128 (18465943311821 / 12500) (36935170297619 / 25000) := by
  exact
    packedTile65536 1477325056 1477456128 14 6221 38435 30 _ _ (527837 / 25000) (2111351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1477456128 :
    ThetaLowerSegment 1477456128 1477587200 (36935170297619 / 25000)
      (147753794828803 / 100000) := by
  exact
    packedTile65536 1477456128 1477587200 14 6211 38437 30 _ _ (2111357 / 100000) (13196 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1477587200 :
    ThetaLowerSegment 1477587200 1477718272 (147753794828803 / 100000)
      (147767018314061 / 100000) := by
  exact
    packedTile65536 1477587200 1477718272 14 6263 38439 30 _ _ (1055683 / 50000) (2111369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1477718272 :
    ThetaLowerSegment 1477718272 1477849344 (147767018314061 / 100000)
      (147780113061811 / 100000) := by
  exact
    packedTile65536 1477718272 1477849344 14 6202 38441 30 _ _ (16891 / 800) (1055689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1477849344 :
    ThetaLowerSegment 1477849344 1477980416 (147780113061811 / 100000)
      (147793315545963 / 100000) := by
  exact
    packedTile65536 1477849344 1477980416 14 6253 38442 30 _ _ (263923 / 12500) (2111387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1477980416 :
    ThetaLowerSegment 1477980416 1478111488 (147793315545963 / 100000)
      (147806638435793 / 100000) := by
  exact
    packedTile65536 1477980416 1478111488 14 6310 38444 30 _ _ (2111393 / 100000) (527849 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1478111488 :
    ThetaLowerSegment 1478111488 1478242560 (147806638435793 / 100000)
      (147819564438837 / 100000) := by
  exact
    packedTile65536 1478111488 1478242560 14 6122 38446 30 _ _ (1055701 / 50000) (422281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1478242560 :
    ThetaLowerSegment 1478242560 1478373632 (147819564438837 / 100000)
      (147832720634547 / 100000) := by
  exact
    packedTile65536 1478242560 1478373632 14 6231 38447 30 _ _ (211141 / 10000) (2111413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1478373632 :
    ThetaLowerSegment 1478373632 1478504704 (147832720634547 / 100000)
      (147845955008839 / 100000) := by
  exact
    packedTile65536 1478373632 1478504704 14 6268 38449 30 _ _ (2111419 / 100000) (1055711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1478504704 :
    ThetaLowerSegment 1478504704 1478635776 (147845955008839 / 100000)
      (147859003633879 / 100000) := by
  exact
    packedTile65536 1478504704 1478635776 14 6180 38451 30 _ _ (527857 / 25000) (2111431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1478635776 :
    ThetaLowerSegment 1478635776 1478766848 (147859003633879 / 100000)
      (14787214310633 / 10000) := by
  exact
    packedTile65536 1478635776 1478766848 14 6223 38453 30 _ _ (2111437 / 100000) (26393 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1478766848 :
    ThetaLowerSegment 1478766848 1478897920 (14787214310633 / 10000) (4621410463549 / 3125) := by
  exact
    packedTile65536 1478766848 1478897920 14 6153 38454 30 _ _ (1055723 / 50000) (2111449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1478897920 :
    ThetaLowerSegment 1478897920 1479028992 (4621410463549 / 3125) (147898316647133 / 100000) := by
  exact
    packedTile65536 1478897920 1479028992 14 6243 38456 30 _ _ (422291 / 20000) (1055729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1479028992 :
    ThetaLowerSegment 1479028992 1479160064 (147898316647133 / 100000)
      (147911325376837 / 100000) := by
  exact
    packedTile65536 1479028992 1479160064 14 6161 38458 30 _ _ (263933 / 12500) (2111467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1479160064 :
    ThetaLowerSegment 1479160064 1479291136 (147911325376837 / 100000)
      (29584868943871 / 20000) := by
  exact
    packedTile65536 1479160064 1479291136 14 6166 38459 30 _ _ (2111473 / 100000) (527869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1479291136 :
    ThetaLowerSegment 1479291136 1479422208 (29584868943871 / 20000) (739687654591 / 500) := by
  exact
    packedTile65536 1479291136 1479422208 14 6245 38461 30 _ _ (2111481 / 100000) (527871 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1479422208 :
    ThetaLowerSegment 1479422208 1479553280 (739687654591 / 500) (14795074673411 / 10000) := by
  exact
    packedTile65536 1479422208 1479553280 14 6259 38463 30 _ _ (211149 / 10000) (2111493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1479553280 :
    ThetaLowerSegment 1479553280 1479684352 (14795074673411 / 10000) (73981800770011 / 50000) := by
  exact
    packedTile65536 1479553280 1479684352 14 6088 38464 30 _ _ (2111499 / 100000) (1055751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1479684352 :
    ThetaLowerSegment 1479684352 1479815424 (73981800770011 / 50000) (73988325329731 / 50000) := by
  exact
    packedTile65536 1479684352 1479815424 14 6180 38466 30 _ _ (527877 / 25000) (2111511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1479815424 :
    ThetaLowerSegment 1479815424 1479946496 (73988325329731 / 50000) (29597977551907 / 20000) := by
  exact
    packedTile65536 1479815424 1479946496 14 6269 38468 30 _ _ (2111517 / 100000) (13197 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1479946496 :
    ThetaLowerSegment 1479946496 1480077568 (29597977551907 / 20000)
      (148002939101741 / 100000) := by
  exact
    packedTile65536 1479946496 1480077568 14 6181 38470 30 _ _ (1055763 / 50000) (2111529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1480077568 :
    ThetaLowerSegment 1480077568 1480208640 (148002939101741 / 100000)
      (148015802572961 / 100000) := by
  exact
    packedTile65536 1480077568 1480208640 14 6092 38471 30 _ _ (422307 / 20000) (1055769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1480208640 :
    ThetaLowerSegment 1480208640 1480339712 (148015802572961 / 100000)
      (74014488244869 / 50000) := by
  exact
    packedTile65536 1480208640 1480339712 14 6239 38473 30 _ _ (2111543 / 100000) (1055773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1480339712 :
    ThetaLowerSegment 1480339712 1480470784 (74014488244869 / 50000) (74021102681509 / 50000) := by
  exact
    packedTile65536 1480339712 1480470784 14 6265 38475 30 _ _ (65986 / 3125) (422311 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1480470784 :
    ThetaLowerSegment 1480470784 1480601856 (74021102681509 / 50000) (74027690751829 / 50000) := by
  exact
    packedTile65536 1480470784 1480601856 14 6240 38476 30 _ _ (2111561 / 100000) (527891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1480601856 :
    ThetaLowerSegment 1480601856 1480732928 (74027690751829 / 50000) (74034302077499 / 50000) := by
  exact
    packedTile65536 1480601856 1480732928 14 6262 38478 30 _ _ (211157 / 10000) (2111573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1480732928 :
    ThetaLowerSegment 1480732928 1480864000 (74034302077499 / 50000) (9255108899971 / 6250) := by
  exact
    packedTile65536 1480732928 1480864000 14 6222 38480 30 _ _ (2111579 / 100000) (1055791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1480864000 :
    ThetaLowerSegment 1480864000 1480995072 (9255108899971 / 6250) (37023687973301 / 25000) := by
  exact
    packedTile65536 1480864000 1480995072 14 6161 38481 30 _ _ (527897 / 25000) (2111591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1480995072 :
    ThetaLowerSegment 1480995072 1481126144 (37023687973301 / 25000)
      (148107714987187 / 100000) := by
  exact
    packedTile65536 1480995072 1481126144 14 6139 38483 30 _ _ (2111597 / 100000) (5279 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481126144 :
    ThetaLowerSegment 1481126144 1481257216 (148107714987187 / 100000)
      (148120730920407 / 100000) := by
  exact
    packedTile65536 1481126144 1481257216 14 6164 38485 30 _ _ (422321 / 20000) (263951 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481257216 :
    ThetaLowerSegment 1481257216 1481322752 (148120730920407 / 100000)
      (148127188236019 / 100000) := by
  exact
    packedTile65536 1481257216 1481322752 13 3058 38487 30 _ _ (1055807 / 50000) (2111617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481322752 :
    ThetaLowerSegment 1481322752 1481339136 (148127188236019 / 100000)
      (74064393365801 / 50000) := by
  exact
    packedTile65536 1481322752 1481339136 11 757 38487 30 _ _ (2111619 / 100000) (1055811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1481339136 :
    ThetaLowerSegment 1481339136 1481341184 (74064393365801 / 50000) (74064497890991 / 50000) := by
  exact
    packedTile65536 1481339136 1481341184 8 99 38488 30 _ _ (105581 / 5000) (2111623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1449341184_1481341184 :
    ThetaLowerSegment 1449341184 1481341184 (144929050023839 / 100000)
      (74064497890991 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1449341184 cell1449472256)
                  (ThetaLowerSegment.join cell1449603328 cell1449734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1449865472 cell1449996544)
                  (ThetaLowerSegment.join cell1450127616 cell1450258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1450389760 cell1450520832)
                  (ThetaLowerSegment.join cell1450651904 cell1450782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1450914048 cell1451045120)
                  (ThetaLowerSegment.join cell1451176192 cell1451307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1451438336 cell1451569408)
                  (ThetaLowerSegment.join cell1451700480 cell1451831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1451962624 cell1452093696)
                  (ThetaLowerSegment.join cell1452224768 cell1452355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1452486912 cell1452617984)
                  (ThetaLowerSegment.join cell1452749056 cell1452880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1453011200 cell1453142272)
                  (ThetaLowerSegment.join cell1453273344 cell1453404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1453535488 cell1453666560)
                  (ThetaLowerSegment.join cell1453797632 cell1453928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1454059776 cell1454190848)
                  (ThetaLowerSegment.join cell1454321920 cell1454452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1454584064 cell1454715136)
                  (ThetaLowerSegment.join cell1454846208 cell1454977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1455108352 cell1455239424)
                  (ThetaLowerSegment.join cell1455370496 cell1455501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1455632640 cell1455763712)
                  (ThetaLowerSegment.join cell1455894784 cell1456025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1456156928 cell1456288000)
                  (ThetaLowerSegment.join cell1456419072 cell1456550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1456681216 cell1456812288)
                  (ThetaLowerSegment.join cell1456943360 cell1457074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1457205504 cell1457336576)
                  (ThetaLowerSegment.join cell1457467648 cell1457598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1457729792 cell1457860864)
                  (ThetaLowerSegment.join cell1457991936 cell1458123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1458254080 cell1458385152)
                  (ThetaLowerSegment.join cell1458516224 cell1458647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1458778368 cell1458909440)
                  (ThetaLowerSegment.join cell1459040512 cell1459171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1459302656 cell1459433728)
                  (ThetaLowerSegment.join cell1459564800 cell1459695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1459826944 cell1459958016)
                  (ThetaLowerSegment.join cell1460089088 cell1460220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1460351232 cell1460482304)
                  (ThetaLowerSegment.join cell1460613376 cell1460744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1460875520 cell1461006592)
                  (ThetaLowerSegment.join cell1461137664 cell1461268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1461399808 cell1461530880)
                  (ThetaLowerSegment.join cell1461661952 cell1461793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1461924096 cell1462055168)
                  (ThetaLowerSegment.join cell1462186240 cell1462317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1462448384 cell1462579456)
                  (ThetaLowerSegment.join cell1462710528 cell1462841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1462972672 cell1463103744)
                  (ThetaLowerSegment.join cell1463234816 cell1463365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1463496960 cell1463628032)
                  (ThetaLowerSegment.join cell1463759104 cell1463890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1464021248 cell1464152320)
                  (ThetaLowerSegment.join cell1464283392 cell1464414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1464545536 cell1464676608)
                  (ThetaLowerSegment.join cell1464807680 cell1464938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1465069824 cell1465200896)
                  (ThetaLowerSegment.join cell1465331968 cell1465463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1465594112 cell1465725184)
                  (ThetaLowerSegment.join cell1465856256 cell1465987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1466118400 cell1466249472)
                  (ThetaLowerSegment.join cell1466380544 cell1466511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1466642688 cell1466773760)
                  (ThetaLowerSegment.join cell1466904832 cell1467035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1467166976 cell1467298048)
                  (ThetaLowerSegment.join cell1467429120 cell1467560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1467691264 cell1467822336)
                  (ThetaLowerSegment.join cell1467953408 cell1468084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1468215552 cell1468346624)
                  (ThetaLowerSegment.join cell1468477696 cell1468608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1468739840 cell1468870912)
                  (ThetaLowerSegment.join cell1469001984 cell1469133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1469264128 cell1469395200)
                  (ThetaLowerSegment.join cell1469526272 cell1469657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1469788416 cell1469919488)
                  (ThetaLowerSegment.join cell1470050560 cell1470181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1470312704 cell1470443776)
                  (ThetaLowerSegment.join cell1470574848 cell1470705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1470836992 cell1470968064)
                  (ThetaLowerSegment.join cell1471099136 cell1471230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1471361280 cell1471492352)
                  (ThetaLowerSegment.join cell1471623424 cell1471754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1471885568 cell1472016640)
                  (ThetaLowerSegment.join cell1472147712 cell1472278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1472409856 cell1472540928)
                  (ThetaLowerSegment.join cell1472672000 cell1472803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1472934144 cell1473065216)
                  (ThetaLowerSegment.join cell1473196288 cell1473327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1473458432 cell1473589504)
                  (ThetaLowerSegment.join cell1473720576 cell1473851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1473982720 cell1474113792)
                  (ThetaLowerSegment.join cell1474244864 cell1474310400))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1474441472 cell1474572544)
                  (ThetaLowerSegment.join cell1474703616 cell1474834688))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1474965760 cell1475096832)
                  (ThetaLowerSegment.join cell1475227904 cell1475358976)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1475490048 cell1475621120)
                  (ThetaLowerSegment.join cell1475752192 cell1475883264))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1476014336 cell1476145408)
                  (ThetaLowerSegment.join cell1476276480 cell1476407552))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1476538624 cell1476669696)
                  (ThetaLowerSegment.join cell1476800768 cell1476931840))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1477062912 cell1477193984)
                  (ThetaLowerSegment.join cell1477325056 cell1477456128)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1477587200 cell1477718272)
                  (ThetaLowerSegment.join cell1477849344 cell1477980416))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1478111488 cell1478242560)
                  (ThetaLowerSegment.join cell1478373632 cell1478504704)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1478635776 cell1478766848)
                  (ThetaLowerSegment.join cell1478897920 cell1479028992))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1479160064 cell1479291136)
                  (ThetaLowerSegment.join cell1479422208 cell1479553280)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1479684352 cell1479815424)
                  (ThetaLowerSegment.join cell1479946496 cell1480077568))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1480208640 cell1480339712)
                  (ThetaLowerSegment.join cell1480470784 cell1480601856))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1480732928 cell1480864000)
                (ThetaLowerSegment.join cell1480995072 cell1481126144))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1481257216 cell1481322752)
                cell1481339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
