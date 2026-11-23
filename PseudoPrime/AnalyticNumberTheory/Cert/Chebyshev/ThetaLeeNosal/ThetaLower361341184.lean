/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 361341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell329341184 :
    ThetaLowerSegment 329341184 329406720 (2058225478409 / 6250) (32938203368561 / 100000) := by
  exact
    packedTile32768 329341184 329406720 13 3363 18147 28 _ _ (1961259 / 100000) (980631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329406720 :
    ThetaLowerSegment 329406720 329472256 (32938203368561 / 100000) (32944910942741 / 100000) := by
  exact
    packedTile32768 329406720 329472256 13 3420 18149 28 _ _ (1961279 / 100000) (980641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329472256 :
    ThetaLowerSegment 329472256 329537792 (32944910942741 / 100000) (2059471871241 / 6250) := by
  exact
    packedTile32768 329472256 329537792 13 3385 18151 28 _ _ (1961299 / 100000) (980651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329537792 :
    ThetaLowerSegment 329537792 329603328 (2059471871241 / 6250) (1647906606321 / 5000) := by
  exact
    packedTile32768 329537792 329603328 13 3356 18153 28 _ _ (1961319 / 100000) (980661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329603328 :
    ThetaLowerSegment 329603328 329668864 (1647906606321 / 5000) (32964763413579 / 100000) := by
  exact
    packedTile32768 329603328 329668864 13 3381 18154 28 _ _ (1961339 / 100000) (980671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329668864 :
    ThetaLowerSegment 329668864 329734400 (32964763413579 / 100000) (6594255808971 / 20000) := by
  exact
    packedTile32768 329668864 329734400 13 3322 18156 28 _ _ (980679 / 50000) (1961361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329734400 :
    ThetaLowerSegment 329734400 329799936 (6594255808971 / 20000) (6595579739121 / 20000) := by
  exact
    packedTile32768 329734400 329799936 13 3375 18158 28 _ _ (980689 / 50000) (1961381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329799936 :
    ThetaLowerSegment 329799936 329865472 (6595579739121 / 20000) (6596887991587 / 20000) := by
  exact
    packedTile32768 329799936 329865472 13 3335 18160 28 _ _ (980699 / 50000) (1961401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329865472 :
    ThetaLowerSegment 329865472 329931008 (6596887991587 / 20000) (32990875370393 / 100000) := by
  exact
    packedTile32768 329865472 329931008 13 3281 18162 28 _ _ (980709 / 50000) (1961421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329931008 :
    ThetaLowerSegment 329931008 329996544 (32990875370393 / 100000) (32997448149131 / 100000) := by
  exact
    packedTile32768 329931008 329996544 13 3351 18164 28 _ _ (980719 / 50000) (1961441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell329996544 :
    ThetaLowerSegment 329996544 330062080 (32997448149131 / 100000) (6600795176271 / 20000) := by
  exact
    packedTile32768 329996544 330062080 13 3328 18165 28 _ _ (980729 / 50000) (1961461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330062080 :
    ThetaLowerSegment 330062080 330127616 (6600795176271 / 20000) (33010393837371 / 100000) := by
  exact
    packedTile32768 330062080 330127616 13 3272 18167 28 _ _ (980739 / 50000) (1961481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330127616 :
    ThetaLowerSegment 330127616 330193152 (33010393837371 / 100000) (33016913853399 / 100000) := by
  exact
    packedTile32768 330127616 330193152 13 3324 18169 28 _ _ (1961497 / 100000) (3923 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330193152 :
    ThetaLowerSegment 330193152 330258688 (33016913853399 / 100000) (1320941594313 / 4000) := by
  exact
    packedTile32768 330193152 330258688 13 3378 18171 28 _ _ (1961517 / 100000) (24519 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330258688 :
    ThetaLowerSegment 330258688 330324224 (1320941594313 / 4000) (1651494271501 / 5000) := by
  exact
    packedTile32768 330258688 330324224 13 3235 18173 28 _ _ (1961537 / 100000) (98077 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330324224 :
    ThetaLowerSegment 330324224 330356992 (1651494271501 / 5000) (33033155345539 / 100000) := by
  exact
    packedTile32768 330324224 330356992 12 1667 18174 28 _ _ (1961557 / 100000) (49039 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330356992 :
    ThetaLowerSegment 330356992 330389760 (33033155345539 / 100000) (8259108280999 / 25000) := by
  exact
    packedTile32768 330356992 330389760 12 1671 18175 28 _ _ (1961567 / 100000) (196157 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330389760 :
    ThetaLowerSegment 330389760 330422528 (8259108280999 / 25000) (33039746227549 / 100000) := by
  exact
    packedTile32768 330389760 330422528 12 1689 18176 28 _ _ (1961577 / 100000) (98079 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330422528 :
    ThetaLowerSegment 330422528 330488064 (33039746227549 / 100000) (33046243003693 / 100000) := by
  exact
    packedTile32768 330422528 330488064 13 3312 18177 28 _ _ (1961587 / 100000) (196159 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330488064 :
    ThetaLowerSegment 330488064 330520832 (33046243003693 / 100000) (33049463962387 / 100000) := by
  exact
    packedTile32768 330488064 330520832 12 1642 18179 28 _ _ (1961607 / 100000) (196161 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330520832 :
    ThetaLowerSegment 330520832 330553600 (33049463962387 / 100000) (16526429760707 / 50000) := by
  exact
    packedTile32768 330520832 330553600 12 1731 18180 28 _ _ (1961617 / 100000) (98081 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330553600 :
    ThetaLowerSegment 330553600 330619136 (16526429760707 / 50000) (4132418817731 / 12500) := by
  exact
    packedTile32768 330553600 330619136 13 3309 18181 28 _ _ (980813 / 50000) (1961629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330619136 :
    ThetaLowerSegment 330619136 330651904 (4132418817731 / 12500) (16531298532989 / 50000) := by
  exact
    packedTile32768 330619136 330651904 12 1655 18182 28 _ _ (980823 / 50000) (1961649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330651904 :
    ThetaLowerSegment 330651904 330684672 (16531298532989 / 50000) (16532942400717 / 50000) := by
  exact
    packedTile32768 330651904 330684672 12 1676 18183 28 _ _ (245207 / 12500) (1961659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330684672 :
    ThetaLowerSegment 330684672 330717440 (16532942400717 / 50000) (16534552928503 / 50000) := by
  exact
    packedTile32768 330684672 330717440 12 1642 18184 28 _ _ (980833 / 50000) (1961669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330717440 :
    ThetaLowerSegment 330717440 330750208 (16534552928503 / 50000) (16536198774667 / 50000) := by
  exact
    packedTile32768 330717440 330750208 12 1678 18185 28 _ _ (490419 / 25000) (1961679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330750208 :
    ThetaLowerSegment 330750208 330782976 (16536198774667 / 50000) (4134458459987 / 12500) := by
  exact
    packedTile32768 330750208 330782976 12 1667 18186 28 _ _ (980843 / 50000) (1961689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330782976 :
    ThetaLowerSegment 330782976 330815744 (4134458459987 / 12500) (4134864776271 / 12500) := by
  exact
    packedTile32768 330782976 330815744 12 1657 18187 28 _ _ (61303 / 3125) (1961699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330815744 :
    ThetaLowerSegment 330815744 330848512 (4134864776271 / 12500) (2067635915133 / 6250) := by
  exact
    packedTile32768 330815744 330848512 12 1660 18188 28 _ _ (980853 / 50000) (1961709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330848512 :
    ThetaLowerSegment 330848512 330881280 (2067635915133 / 6250) (4135675453333 / 12500) := by
  exact
    packedTile32768 330848512 330881280 12 1646 18189 28 _ _ (490429 / 25000) (1961719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330881280 :
    ThetaLowerSegment 330881280 330914048 (4135675453333 / 12500) (16544366337843 / 50000) := by
  exact
    packedTile32768 330881280 330914048 12 1697 18190 28 _ _ (980863 / 50000) (1961729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330914048 :
    ThetaLowerSegment 330914048 330946816 (16544366337843 / 50000) (33091932265471 / 100000) := by
  exact
    packedTile32768 330914048 330946816 12 1631 18191 28 _ _ (392347 / 20000) (980869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330946816 :
    ThetaLowerSegment 330946816 330979584 (33091932265471 / 100000) (16547640482093 / 50000) := by
  exact
    packedTile32768 330946816 330979584 12 1707 18191 28 _ _ (392349 / 20000) (490437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell330979584 :
    ThetaLowerSegment 330979584 331012352 (16547640482093 / 50000) (33098527668711 / 100000) := by
  exact
    packedTile32768 330979584 331012352 12 1655 18192 28 _ _ (392351 / 20000) (980879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331012352 :
    ThetaLowerSegment 331012352 331045120 (33098527668711 / 100000) (8275436731269 / 25000) := by
  exact
    packedTile32768 331012352 331045120 12 1641 18193 28 _ _ (392353 / 20000) (245221 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331045120 :
    ThetaLowerSegment 331045120 331077888 (8275436731269 / 25000) (8276256753219 / 25000) := by
  exact
    packedTile32768 331045120 331077888 12 1672 18194 28 _ _ (78471 / 4000) (980889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331077888 :
    ThetaLowerSegment 331077888 331110656 (8276256753219 / 25000) (8277108167909 / 25000) := by
  exact
    packedTile32768 331077888 331110656 12 1736 18195 28 _ _ (392357 / 20000) (490447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331110656 :
    ThetaLowerSegment 331110656 331143424 (8277108167909 / 25000) (16555842663873 / 50000) := by
  exact
    packedTile32768 331110656 331143424 12 1658 18196 28 _ _ (392359 / 20000) (980899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331143424 :
    ThetaLowerSegment 331143424 331176192 (16555842663873 / 50000) (33114975274731 / 100000) := by
  exact
    packedTile32768 331143424 331176192 12 1677 18197 28 _ _ (392361 / 20000) (122613 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331176192 :
    ThetaLowerSegment 331176192 331208960 (33114975274731 / 100000) (8279551596009 / 25000) := by
  exact
    packedTile32768 331176192 331208960 12 1647 18198 28 _ _ (392363 / 20000) (980909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331208960 :
    ThetaLowerSegment 331208960 331241728 (8279551596009 / 25000) (16560772705093 / 50000) := by
  exact
    packedTile32768 331208960 331241728 12 1702 18199 28 _ _ (78473 / 4000) (490457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331241728 :
    ThetaLowerSegment 331241728 331274496 (16560772705093 / 50000) (2070303439009 / 6250) := by
  exact
    packedTile32768 331241728 331274496 12 1687 18200 28 _ _ (980917 / 50000) (1961837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331274496 :
    ThetaLowerSegment 331274496 331307264 (2070303439009 / 6250) (8282035278211 / 25000) := by
  exact
    packedTile32768 331274496 331307264 12 1675 18200 28 _ _ (490461 / 25000) (1961847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331307264 :
    ThetaLowerSegment 331307264 331340032 (8282035278211 / 25000) (16565721456563 / 50000) := by
  exact
    packedTile32768 331307264 331340032 12 1683 18201 28 _ _ (980927 / 50000) (1961857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331340032 :
    ThetaLowerSegment 331340032 331372800 (16565721456563 / 50000) (3313472118787 / 10000) := by
  exact
    packedTile32768 331340032 331372800 12 1671 18202 28 _ _ (245233 / 12500) (1961867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331372800 :
    ThetaLowerSegment 331372800 331405568 (3313472118787 / 10000) (4142249444447 / 12500) := by
  exact
    packedTile32768 331372800 331405568 12 1669 18203 28 _ _ (980937 / 50000) (1961877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331405568 :
    ThetaLowerSegment 331405568 331438336 (4142249444447 / 12500) (8285334161007 / 25000) := by
  exact
    packedTile32768 331405568 331438336 12 1703 18204 28 _ _ (490471 / 25000) (1961887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331438336 :
    ThetaLowerSegment 331438336 331503872 (8285334161007 / 25000) (16573929970789 / 50000) := by
  exact
    packedTile32768 331438336 331503872 13 3325 18205 28 _ _ (980947 / 50000) (1961897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331503872 :
    ThetaLowerSegment 331503872 331569408 (16573929970789 / 50000) (8288593864493 / 25000) := by
  exact
    packedTile32768 331503872 331569408 13 3321 18207 28 _ _ (980957 / 50000) (1961917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331569408 :
    ThetaLowerSegment 331569408 331602176 (8288593864493 / 25000) (33157646000283 / 100000) := by
  exact
    packedTile32768 331569408 331602176 12 1667 18209 28 _ _ (1961933 / 100000) (122621 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331602176 :
    ThetaLowerSegment 331602176 331634944 (33157646000283 / 100000) (207256120884 / 625) := by
  exact
    packedTile32768 331602176 331634944 12 1699 18209 28 _ _ (1961943 / 100000) (980973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331634944 :
    ThetaLowerSegment 331634944 331700480 (207256120884 / 625) (16583799485431 / 50000) := by
  exact
    packedTile32768 331634944 331700480 13 3374 18210 28 _ _ (1961953 / 100000) (490489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331700480 :
    ThetaLowerSegment 331700480 331766016 (16583799485431 / 50000) (132696733409 / 400) := by
  exact
    packedTile32768 331700480 331766016 13 3356 18212 28 _ _ (1961973 / 100000) (245247 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331766016 :
    ThetaLowerSegment 331766016 331831552 (132696733409 / 400) (33180655967157 / 100000) := by
  exact
    packedTile32768 331766016 331831552 13 3299 18214 28 _ _ (1961993 / 100000) (490499 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331831552 :
    ThetaLowerSegment 331831552 331897088 (33180655967157 / 100000) (6637413956877 / 20000) := by
  exact
    packedTile32768 331831552 331897088 13 3269 18216 28 _ _ (490503 / 25000) (392403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331897088 :
    ThetaLowerSegment 331897088 331929856 (6637413956877 / 20000) (33190332643601 / 100000) := by
  exact
    packedTile32768 331897088 331929856 12 1663 18218 28 _ _ (122627 / 6250) (392407 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331929856 :
    ThetaLowerSegment 331929856 331962624 (33190332643601 / 100000) (33193558240649 / 100000) := by
  exact
    packedTile32768 331929856 331962624 12 1644 18218 28 _ _ (981021 / 50000) (392409 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331962624 :
    ThetaLowerSegment 331962624 331995392 (33193558240649 / 100000) (6639377960989 / 20000) := by
  exact
    packedTile32768 331962624 331995392 12 1698 18219 28 _ _ (490513 / 25000) (392411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell331995392 :
    ThetaLowerSegment 331995392 332028160 (6639377960989 / 20000) (33200142903741 / 100000) := by
  exact
    packedTile32768 331995392 332028160 12 1658 18220 28 _ _ (981031 / 50000) (392413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332028160 :
    ThetaLowerSegment 332028160 332060928 (33200142903741 / 100000) (33203417601909 / 100000) := by
  exact
    packedTile32768 332028160 332060928 12 1669 18221 28 _ _ (245259 / 12500) (78483 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332060928 :
    ThetaLowerSegment 332060928 332093696 (33203417601909 / 100000) (16603322612577 / 50000) := by
  exact
    packedTile32768 332060928 332093696 12 1645 18222 28 _ _ (1962081 / 100000) (490521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332093696 :
    ThetaLowerSegment 332093696 332126464 (16603322612577 / 50000) (33209876789031 / 100000) := by
  exact
    packedTile32768 332093696 332126464 12 1647 18223 28 _ _ (1962091 / 100000) (981047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332126464 :
    ThetaLowerSegment 332126464 332159232 (33209876789031 / 100000) (6642636193423 / 20000) := by
  exact
    packedTile32768 332126464 332159232 12 1684 18224 28 _ _ (1962101 / 100000) (245263 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332159232 :
    ThetaLowerSegment 332159232 332192000 (6642636193423 / 20000) (2076031181051 / 6250) := by
  exact
    packedTile32768 332159232 332192000 12 1691 18225 28 _ _ (1962111 / 100000) (981057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332192000 :
    ThetaLowerSegment 332192000 332224768 (2076031181051 / 6250) (16609860349749 / 50000) := by
  exact
    packedTile32768 332192000 332224768 12 1642 18226 28 _ _ (1962121 / 100000) (490531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332224768 :
    ThetaLowerSegment 332224768 332257536 (16609860349749 / 50000) (16611504615527 / 50000) := by
  exact
    packedTile32768 332224768 332257536 12 1676 18227 28 _ _ (1962131 / 100000) (981067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332257536 :
    ThetaLowerSegment 332257536 332290304 (16611504615527 / 50000) (33226342908613 / 100000) := by
  exact
    packedTile32768 332257536 332290304 12 1699 18227 28 _ _ (1962141 / 100000) (61317 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332290304 :
    ThetaLowerSegment 332290304 332323072 (33226342908613 / 100000) (33229547099563 / 100000) := by
  exact
    packedTile32768 332290304 332323072 12 1633 18228 28 _ _ (39243 / 2000) (1962153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332323072 :
    ThetaLowerSegment 332323072 332355840 (33229547099563 / 100000) (33232778777083 / 100000) := by
  exact
    packedTile32768 332323072 332355840 12 1647 18229 28 _ _ (24527 / 1250) (1962163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332355840 :
    ThetaLowerSegment 332355840 332388608 (33232778777083 / 100000) (33236086995703 / 100000) := by
  exact
    packedTile32768 332355840 332388608 12 1686 18230 28 _ _ (196217 / 10000) (1962173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332388608 :
    ThetaLowerSegment 332388608 332421376 (33236086995703 / 100000) (33239375609383 / 100000) := by
  exact
    packedTile32768 332388608 332421376 12 1676 18231 28 _ _ (98109 / 5000) (1962183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332421376 :
    ThetaLowerSegment 332421376 332454144 (33239375609383 / 100000) (33242719181143 / 100000) := by
  exact
    packedTile32768 332421376 332454144 12 1704 18232 28 _ _ (196219 / 10000) (1962193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332454144 :
    ThetaLowerSegment 332454144 332486912 (33242719181143 / 100000) (33245952886743 / 100000) := by
  exact
    packedTile32768 332454144 332486912 12 1648 18233 28 _ _ (9811 / 500) (1962203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332486912 :
    ThetaLowerSegment 332486912 332519680 (33245952886743 / 100000) (33249247437333 / 100000) := by
  exact
    packedTile32768 332486912 332519680 12 1679 18234 28 _ _ (196221 / 10000) (1962213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332519680 :
    ThetaLowerSegment 332519680 332552448 (33249247437333 / 100000) (33252543965253 / 100000) := by
  exact
    packedTile32768 332519680 332552448 12 1680 18235 28 _ _ (1962219 / 100000) (981111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332552448 :
    ThetaLowerSegment 332552448 332585216 (33252543965253 / 100000) (33255832661057 / 100000) := by
  exact
    packedTile32768 332552448 332585216 12 1676 18236 28 _ _ (1962229 / 100000) (245279 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332585216 :
    ThetaLowerSegment 332585216 332617984 (33255832661057 / 100000) (2078699623529 / 6250) := by
  exact
    packedTile32768 332585216 332617984 12 1713 18236 28 _ _ (1962239 / 100000) (981121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332617984 :
    ThetaLowerSegment 332617984 332650752 (2078699623529 / 6250) (4157801508103 / 12500) := by
  exact
    packedTile32768 332617984 332650752 12 1640 18237 28 _ _ (1962249 / 100000) (490563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332650752 :
    ThetaLowerSegment 332650752 332683520 (4157801508103 / 12500) (8316433051763 / 25000) := by
  exact
    packedTile32768 332650752 332683520 12 1692 18238 28 _ _ (1962259 / 100000) (981131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332683520 :
    ThetaLowerSegment 332683520 332716288 (8316433051763 / 25000) (1330764056917 / 4000) := by
  exact
    packedTile32768 332683520 332716288 12 1717 18239 28 _ _ (1962269 / 100000) (61321 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332716288 :
    ThetaLowerSegment 332716288 332781824 (1330764056917 / 4000) (415946306147 / 1250) := by
  exact
    packedTile32768 332716288 332781824 13 3365 18240 28 _ _ (1962279 / 100000) (981141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332781824 :
    ThetaLowerSegment 332781824 332847360 (415946306147 / 1250) (16641147925371 / 50000) := by
  exact
    packedTile32768 332781824 332847360 13 3359 18242 28 _ _ (981149 / 50000) (1962301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332847360 :
    ThetaLowerSegment 332847360 332912896 (16641147925371 / 50000) (4161112871931 / 12500) := by
  exact
    packedTile32768 332847360 332912896 13 3367 18244 28 _ _ (981159 / 50000) (1962321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332912896 :
    ThetaLowerSegment 332912896 332978432 (4161112871931 / 12500) (16647733498029 / 50000) := by
  exact
    packedTile32768 332912896 332978432 13 3345 18245 28 _ _ (981169 / 50000) (1962341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell332978432 :
    ThetaLowerSegment 332978432 333043968 (16647733498029 / 50000) (16650983161221 / 50000) := by
  exact
    packedTile32768 332978432 333043968 13 3312 18247 28 _ _ (1962357 / 100000) (49059 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333043968 :
    ThetaLowerSegment 333043968 333109504 (16650983161221 / 50000) (6661695890341 / 20000) := by
  exact
    packedTile32768 333043968 333109504 13 3319 18249 28 _ _ (1962377 / 100000) (98119 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333109504 :
    ThetaLowerSegment 333109504 333175040 (6661695890341 / 20000) (333150240457 / 1000) := by
  exact
    packedTile32768 333109504 333175040 13 3335 18251 28 _ _ (1962397 / 100000) (2453 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333175040 :
    ThetaLowerSegment 333175040 333240576 (333150240457 / 1000) (8330412781133 / 25000) := by
  exact
    packedTile32768 333175040 333240576 13 3377 18253 28 _ _ (122651 / 6250) (1962419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333240576 :
    ThetaLowerSegment 333240576 333306112 (8330412781133 / 25000) (1666411068013 / 5000) := by
  exact
    packedTile32768 333240576 333306112 13 3348 18254 28 _ _ (490609 / 25000) (1962439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333306112 :
    ThetaLowerSegment 333306112 333371648 (1666411068013 / 5000) (8333690556527 / 25000) := by
  exact
    packedTile32768 333306112 333371648 13 3333 18256 28 _ _ (245307 / 12500) (1962459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333371648 :
    ThetaLowerSegment 333371648 333437184 (8333690556527 / 25000) (33341150082233 / 100000) := by
  exact
    packedTile32768 333371648 333437184 13 3255 18258 28 _ _ (78499 / 4000) (981239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333437184 :
    ThetaLowerSegment 333437184 333502720 (33341150082233 / 100000) (33347642015693 / 100000) := by
  exact
    packedTile32768 333437184 333502720 13 3308 18260 28 _ _ (392499 / 20000) (981249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333502720 :
    ThetaLowerSegment 333502720 333535488 (33347642015693 / 100000) (33350888015503 / 100000) := by
  exact
    packedTile32768 333502720 333535488 12 1654 18262 28 _ _ (392503 / 20000) (981259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333535488 :
    ThetaLowerSegment 333535488 333568256 (33350888015503 / 100000) (33354126180103 / 100000) := by
  exact
    packedTile32768 333535488 333568256 12 1650 18262 28 _ _ (490631 / 25000) (1962527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333568256 :
    ThetaLowerSegment 333568256 333601024 (33354126180103 / 100000) (6671487787499 / 20000) := by
  exact
    packedTile32768 333568256 333601024 12 1688 18263 28 _ _ (981267 / 50000) (1962537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333601024 :
    ThetaLowerSegment 333601024 333633792 (6671487787499 / 20000) (33360671247463 / 100000) := by
  exact
    packedTile32768 333601024 333633792 12 1647 18264 28 _ _ (122659 / 6250) (1962547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333633792 :
    ThetaLowerSegment 333633792 333666560 (33360671247463 / 100000) (33363962450521 / 100000) := by
  exact
    packedTile32768 333633792 333666560 12 1677 18265 28 _ _ (981277 / 50000) (1962557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333666560 :
    ThetaLowerSegment 333666560 333699328 (33363962450521 / 100000) (33367328247781 / 100000) := by
  exact
    packedTile32768 333666560 333699328 12 1715 18266 28 _ _ (490641 / 25000) (1962567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333699328 :
    ThetaLowerSegment 333699328 333732096 (33367328247781 / 100000) (33370621446953 / 100000) := by
  exact
    packedTile32768 333699328 333732096 12 1678 18267 28 _ _ (981287 / 50000) (1962577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333732096 :
    ThetaLowerSegment 333732096 333764864 (33370621446953 / 100000) (33373883259899 / 100000) := by
  exact
    packedTile32768 333732096 333764864 12 1662 18268 28 _ _ (1962583 / 100000) (981293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333764864 :
    ThetaLowerSegment 333764864 333797632 (33373883259899 / 100000) (16688589226773 / 50000) := by
  exact
    packedTile32768 333764864 333797632 12 1679 18269 28 _ _ (1962593 / 100000) (490649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333797632 :
    ThetaLowerSegment 333797632 333830400 (16688589226773 / 50000) (33380524691661 / 100000) := by
  exact
    packedTile32768 333797632 333830400 12 1705 18270 28 _ _ (1962603 / 100000) (981303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333830400 :
    ThetaLowerSegment 333830400 333895936 (33380524691661 / 100000) (41733759003 / 125) := by
  exact
    packedTile32768 333830400 333895936 13 3303 18271 28 _ _ (1962613 / 100000) (245327 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333895936 :
    ThetaLowerSegment 333895936 333928704 (41733759003 / 125) (4173795658219 / 12500) := by
  exact
    packedTile32768 333895936 333928704 12 1711 18272 28 _ _ (245329 / 12500) (392527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333928704 :
    ThetaLowerSegment 333928704 333994240 (4173795658219 / 12500) (16698435711991 / 50000) := by
  exact
    packedTile32768 333928704 333994240 13 3315 18273 28 _ _ (981321 / 50000) (392529 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell333994240 :
    ThetaLowerSegment 333994240 334059776 (16698435711991 / 50000) (1043856532847 / 3125) := by
  exact
    packedTile32768 333994240 334059776 13 3331 18275 28 _ _ (981331 / 50000) (392533 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334059776 :
    ThetaLowerSegment 334059776 334125312 (1043856532847 / 3125) (3340995067021 / 10000) := by
  exact
    packedTile32768 334059776 334125312 13 3333 18277 28 _ _ (981341 / 50000) (392537 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334125312 :
    ThetaLowerSegment 334125312 334190848 (3340995067021 / 10000) (33416390292191 / 100000) := by
  exact
    packedTile32768 334125312 334190848 13 3281 18279 28 _ _ (1962701 / 100000) (122669 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334190848 :
    ThetaLowerSegment 334190848 334223616 (33416390292191 / 100000) (1336785465309 / 4000) := by
  exact
    packedTile32768 334190848 334223616 12 1654 18280 28 _ _ (1962721 / 100000) (490681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334223616 :
    ThetaLowerSegment 334223616 334256384 (1336785465309 / 4000) (16711489581809 / 50000) := by
  exact
    packedTile32768 334223616 334256384 12 1703 18281 28 _ _ (1962731 / 100000) (981367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334256384 :
    ThetaLowerSegment 334256384 334289152 (16711489581809 / 50000) (16713137302039 / 50000) := by
  exact
    packedTile32768 334256384 334289152 12 1679 18282 28 _ _ (98137 / 5000) (1962743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334289152 :
    ThetaLowerSegment 334289152 334321920 (16713137302039 / 50000) (16714778161039 / 50000) := by
  exact
    packedTile32768 334289152 334321920 12 1672 18283 28 _ _ (7851 / 400) (1962753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334321920 :
    ThetaLowerSegment 334321920 334354688 (16714778161039 / 50000) (16716404307699 / 50000) := by
  exact
    packedTile32768 334321920 334354688 12 1657 18284 28 _ _ (49069 / 2500) (1962763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334354688 :
    ThetaLowerSegment 334354688 334387456 (16716404307699 / 50000) (16718027518489 / 50000) := by
  exact
    packedTile32768 334354688 334387456 12 1654 18285 28 _ _ (196277 / 10000) (1962773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334387456 :
    ThetaLowerSegment 334387456 334420224 (16718027518489 / 50000) (16719704713999 / 50000) := by
  exact
    packedTile32768 334387456 334420224 12 1709 18286 28 _ _ (98139 / 5000) (1962783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334420224 :
    ThetaLowerSegment 334420224 334452992 (16719704713999 / 50000) (1672135149397 / 5000) := by
  exact
    packedTile32768 334420224 334452992 12 1678 18287 28 _ _ (1962789 / 100000) (245349 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334452992 :
    ThetaLowerSegment 334452992 334485760 (1672135149397 / 5000) (16722982579939 / 50000) := by
  exact
    packedTile32768 334452992 334485760 12 1662 18288 28 _ _ (1962799 / 100000) (981401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334485760 :
    ThetaLowerSegment 334485760 334518528 (16722982579939 / 50000) (4181150474341 / 12500) := by
  exact
    packedTile32768 334485760 334518528 12 1650 18288 28 _ _ (1962809 / 100000) (490703 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334518528 :
    ThetaLowerSegment 334518528 334551296 (4181150474341 / 12500) (2090778388937 / 6250) := by
  exact
    packedTile32768 334518528 334551296 12 1656 18289 28 _ _ (1962819 / 100000) (981411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334551296 :
    ThetaLowerSegment 334551296 334584064 (2090778388937 / 6250) (33455769441173 / 100000) := by
  exact
    packedTile32768 334551296 334584064 12 1689 18290 28 _ _ (1962829 / 100000) (122677 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334584064 :
    ThetaLowerSegment 334584064 334616832 (33455769441173 / 100000) (6691818897749 / 20000) := by
  exact
    packedTile32768 334584064 334616832 12 1694 18291 28 _ _ (981419 / 50000) (1962841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334616832 :
    ThetaLowerSegment 334616832 334682368 (6691818897749 / 20000) (33465599367017 / 100000) := by
  exact
    packedTile32768 334616832 334682368 13 3314 18292 28 _ _ (61339 / 3125) (1962851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334682368 :
    ThetaLowerSegment 334682368 334715136 (33465599367017 / 100000) (33468926428277 / 100000) := by
  exact
    packedTile32768 334682368 334715136 12 1695 18294 28 _ _ (490717 / 25000) (1962871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334715136 :
    ThetaLowerSegment 334715136 334780672 (33468926428277 / 100000) (6695100806491 / 20000) := by
  exact
    packedTile32768 334715136 334780672 13 3351 18295 28 _ _ (981439 / 50000) (1962881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334780672 :
    ThetaLowerSegment 334780672 334846208 (6695100806491 / 20000) (1046316157264 / 3125) := by
  exact
    packedTile32768 334780672 334846208 13 3369 18297 28 _ _ (1962897 / 100000) (19629 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334846208 :
    ThetaLowerSegment 334846208 334911744 (1046316157264 / 3125) (33488741877323 / 100000) := by
  exact
    packedTile32768 334846208 334911744 13 3375 18298 28 _ _ (1962917 / 100000) (49073 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334911744 :
    ThetaLowerSegment 334911744 334977280 (33488741877323 / 100000) (33495237232547 / 100000) := by
  exact
    packedTile32768 334911744 334977280 13 3309 18300 28 _ _ (245367 / 12500) (1962939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell334977280 :
    ThetaLowerSegment 334977280 335042816 (33495237232547 / 100000) (6700371656627 / 20000) := by
  exact
    packedTile32768 334977280 335042816 13 3373 18302 28 _ _ (490739 / 25000) (1962959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335042816 :
    ThetaLowerSegment 335042816 335108352 (6700371656627 / 20000) (6701688420257 / 20000) := by
  exact
    packedTile32768 335042816 335108352 13 3354 18304 28 _ _ (78519 / 4000) (981489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335108352 :
    ThetaLowerSegment 335108352 335173888 (6701688420257 / 20000) (209468900147 / 625) := by
  exact
    packedTile32768 335108352 335173888 13 3353 18305 28 _ _ (392599 / 20000) (981499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335173888 :
    ThetaLowerSegment 335173888 335239424 (209468900147 / 625) (3352159227171 / 10000) := by
  exact
    packedTile32768 335173888 335239424 13 3346 18307 28 _ _ (392603 / 20000) (981509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335239424 :
    ThetaLowerSegment 335239424 335304960 (3352159227171 / 10000) (16764070476567 / 50000) := by
  exact
    packedTile32768 335239424 335304960 13 3336 18309 28 _ _ (981517 / 50000) (1963037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335304960 :
    ThetaLowerSegment 335304960 335370496 (16764070476567 / 50000) (209592092822 / 625) := by
  exact
    packedTile32768 335304960 335370496 13 3359 18311 28 _ _ (981527 / 50000) (1963057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335370496 :
    ThetaLowerSegment 335370496 335436032 (209592092822 / 625) (16770702686787 / 50000) := by
  exact
    packedTile32768 335370496 335436032 13 3398 18313 28 _ _ (1963073 / 100000) (490769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335436032 :
    ThetaLowerSegment 335436032 335501568 (16770702686787 / 50000) (33547846281707 / 100000) := by
  exact
    packedTile32768 335436032 335501568 13 3281 18314 28 _ _ (1963093 / 100000) (245387 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335501568 :
    ThetaLowerSegment 335501568 335567104 (33547846281707 / 100000) (33554397186451 / 100000) := by
  exact
    packedTile32768 335501568 335567104 13 3337 18316 28 _ _ (245389 / 12500) (392623 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335567104 :
    ThetaLowerSegment 335567104 335632640 (33554397186451 / 100000) (33560836259411 / 100000) := by
  exact
    packedTile32768 335567104 335632640 13 3280 18318 28 _ _ (490783 / 25000) (392627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335632640 :
    ThetaLowerSegment 335632640 335698176 (33560836259411 / 100000) (33567412815261 / 100000) := by
  exact
    packedTile32768 335632640 335698176 13 3350 18320 28 _ _ (1963151 / 100000) (981577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335698176 :
    ThetaLowerSegment 335698176 335763712 (33567412815261 / 100000) (33573875574193 / 100000) := by
  exact
    packedTile32768 335698176 335763712 13 3292 18322 28 _ _ (1963171 / 100000) (981587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335763712 :
    ThetaLowerSegment 335763712 335829248 (33573875574193 / 100000) (33580371769903 / 100000) := by
  exact
    packedTile32768 335763712 335829248 13 3309 18323 28 _ _ (196319 / 10000) (1963193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335829248 :
    ThetaLowerSegment 335829248 335894784 (33580371769903 / 100000) (33586942633773 / 100000) := by
  exact
    packedTile32768 335829248 335894784 13 3347 18325 28 _ _ (196321 / 10000) (1963213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335894784 :
    ThetaLowerSegment 335894784 335960320 (33586942633773 / 100000) (16796707699893 / 50000) := by
  exact
    packedTile32768 335894784 335960320 13 3297 18327 28 _ _ (1963229 / 100000) (61351 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335960320 :
    ThetaLowerSegment 335960320 335993088 (16796707699893 / 50000) (33596680282873 / 100000) := by
  exact
    packedTile32768 335960320 335993088 12 1663 18329 28 _ _ (1963249 / 100000) (490813 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell335993088 :
    ThetaLowerSegment 335993088 336025856 (33596680282873 / 100000) (16799949032187 / 50000) := by
  exact
    packedTile32768 335993088 336025856 12 1639 18330 28 _ _ (1963259 / 100000) (981631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336025856 :
    ThetaLowerSegment 336025856 336058624 (16799949032187 / 50000) (16801608975281 / 50000) := by
  exact
    packedTile32768 336025856 336058624 12 1691 18331 28 _ _ (490817 / 25000) (1963271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336058624 :
    ThetaLowerSegment 336058624 336091392 (16801608975281 / 50000) (16803269908469 / 50000) := by
  exact
    packedTile32768 336058624 336091392 12 1692 18331 28 _ _ (981639 / 50000) (1963281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336091392 :
    ThetaLowerSegment 336091392 336156928 (16803269908469 / 50000) (16806590810121 / 50000) := by
  exact
    packedTile32768 336091392 336156928 13 3383 18332 28 _ _ (245411 / 12500) (1963291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336156928 :
    ThetaLowerSegment 336156928 336222464 (16806590810121 / 50000) (4202464929069 / 12500) := by
  exact
    packedTile32768 336156928 336222464 13 3330 18334 28 _ _ (1963307 / 100000) (196331 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336222464 :
    ThetaLowerSegment 336222464 336288000 (4202464929069 / 12500) (33626369221101 / 100000) := by
  exact
    packedTile32768 336222464 336288000 13 3387 18336 28 _ _ (1963327 / 100000) (196333 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336288000 :
    ThetaLowerSegment 336288000 336353536 (33626369221101 / 100000) (33632779545791 / 100000) := by
  exact
    packedTile32768 336288000 336353536 13 3265 18338 28 _ _ (981673 / 50000) (1963349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336353536 :
    ThetaLowerSegment 336353536 336419072 (33632779545791 / 100000) (33639270433787 / 100000) := by
  exact
    packedTile32768 336353536 336419072 13 3306 18339 28 _ _ (981683 / 50000) (1963369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336419072 :
    ThetaLowerSegment 336419072 336451840 (33639270433787 / 100000) (33642600334747 / 100000) := by
  exact
    packedTile32768 336419072 336451840 12 1696 18341 28 _ _ (392677 / 20000) (490847 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336451840 :
    ThetaLowerSegment 336451840 336517376 (33642600334747 / 100000) (33649118806147 / 100000) := by
  exact
    packedTile32768 336451840 336517376 13 3320 18342 28 _ _ (392679 / 20000) (981699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336517376 :
    ThetaLowerSegment 336517376 336550144 (33649118806147 / 100000) (4206545050539 / 12500) := by
  exact
    packedTile32768 336517376 336550144 12 1651 18344 28 _ _ (392683 / 20000) (981709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336550144 :
    ThetaLowerSegment 336550144 336582912 (4206545050539 / 12500) (4206958105863 / 12500) := by
  exact
    packedTile32768 336550144 336582912 12 1683 18345 28 _ _ (61357 / 3125) (1963427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336582912 :
    ThetaLowerSegment 336582912 336615680 (4206958105863 / 12500) (8414739872289 / 25000) := by
  exact
    packedTile32768 336582912 336615680 12 1678 18346 28 _ _ (981717 / 50000) (1963437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336615680 :
    ThetaLowerSegment 336615680 336681216 (8414739872289 / 25000) (1683275476917 / 5000) := by
  exact
    packedTile32768 336615680 336681216 13 3336 18347 28 _ _ (490861 / 25000) (1963447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336681216 :
    ThetaLowerSegment 336681216 336746752 (1683275476917 / 5000) (16836047496621 / 50000) := by
  exact
    packedTile32768 336681216 336746752 13 3354 18348 28 _ _ (1963463 / 100000) (981733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336746752 :
    ThetaLowerSegment 336746752 336812288 (16836047496621 / 50000) (33678619647251 / 100000) := by
  exact
    packedTile32768 336746752 336812288 13 3323 18350 28 _ _ (1963483 / 100000) (981743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336812288 :
    ThetaLowerSegment 336812288 336877824 (33678619647251 / 100000) (33685165962919 / 100000) := by
  exact
    packedTile32768 336812288 336877824 13 3334 18352 28 _ _ (981751 / 50000) (392701 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336877824 :
    ThetaLowerSegment 336877824 336943360 (33685165962919 / 100000) (33691620059733 / 100000) := by
  exact
    packedTile32768 336877824 336943360 13 3287 18354 28 _ _ (981761 / 50000) (78541 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336943360 :
    ThetaLowerSegment 336943360 336976128 (33691620059733 / 100000) (269559067719 / 800) := by
  exact
    packedTile32768 336943360 336976128 12 1662 18356 28 _ _ (1963541 / 100000) (245443 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell336976128 :
    ThetaLowerSegment 336976128 337008896 (269559067719 / 800) (6739616810601 / 20000) := by
  exact
    packedTile32768 336976128 337008896 12 1630 18356 28 _ _ (1963551 / 100000) (981777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337008896 :
    ThetaLowerSegment 337008896 337041664 (6739616810601 / 20000) (6740285991849 / 20000) := by
  exact
    packedTile32768 337008896 337041664 12 1704 18357 28 _ _ (49089 / 2500) (1963563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337041664 :
    ThetaLowerSegment 337041664 337074432 (6740285991849 / 20000) (6740934755377 / 20000) := by
  exact
    packedTile32768 337041664 337074432 12 1652 18358 28 _ _ (196357 / 10000) (1963573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337074432 :
    ThetaLowerSegment 337074432 337107200 (6740934755377 / 20000) (6741596874553 / 20000) := by
  exact
    packedTile32768 337074432 337107200 12 1686 18359 28 _ _ (98179 / 5000) (1963583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337107200 :
    ThetaLowerSegment 337107200 337139968 (6741596874553 / 20000) (6742253891767 / 20000) := by
  exact
    packedTile32768 337107200 337139968 12 1673 18360 28 _ _ (196359 / 10000) (1963593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337139968 :
    ThetaLowerSegment 337139968 337172736 (6742253891767 / 20000) (33714658630709 / 100000) := by
  exact
    packedTile32768 337139968 337172736 12 1726 18361 28 _ _ (1963599 / 100000) (981801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337172736 :
    ThetaLowerSegment 337172736 337238272 (33714658630709 / 100000) (33721252429731 / 100000) := by
  exact
    packedTile32768 337172736 337238272 13 3358 18362 28 _ _ (1963609 / 100000) (490903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337238272 :
    ThetaLowerSegment 337238272 337303808 (33721252429731 / 100000) (4215975632463 / 12500) := by
  exact
    packedTile32768 337238272 337303808 13 3337 18364 28 _ _ (1963629 / 100000) (122727 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337303808 :
    ThetaLowerSegment 337303808 337369344 (4215975632463 / 12500) (4216784409983 / 12500) := by
  exact
    packedTile32768 337303808 337369344 13 3295 18365 28 _ _ (61364 / 3125) (1963651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337369344 :
    ThetaLowerSegment 337369344 337402112 (4216784409983 / 12500) (33737513366747 / 100000) := by
  exact
    packedTile32768 337369344 337402112 12 1649 18367 28 _ _ (1963667 / 100000) (196367 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337402112 :
    ThetaLowerSegment 337402112 337434880 (33737513366747 / 100000) (4217609643181 / 12500) := by
  exact
    packedTile32768 337402112 337434880 12 1713 18368 28 _ _ (1963677 / 100000) (12273 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337434880 :
    ThetaLowerSegment 337434880 337500416 (4217609643181 / 12500) (33747367130983 / 100000) := by
  exact
    packedTile32768 337434880 337500416 13 3305 18369 28 _ _ (1963687 / 100000) (196369 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337500416 :
    ThetaLowerSegment 337500416 337533184 (33747367130983 / 100000) (6750126162071 / 20000) := by
  exact
    packedTile32768 337500416 337533184 12 1662 18371 28 _ _ (981853 / 50000) (1963709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337533184 :
    ThetaLowerSegment 337533184 337565952 (6750126162071 / 20000) (33753955381543 / 100000) := by
  exact
    packedTile32768 337533184 337565952 12 1693 18372 28 _ _ (490929 / 25000) (1963719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337565952 :
    ThetaLowerSegment 337565952 337598720 (33753955381543 / 100000) (33757299606921 / 100000) := by
  exact
    packedTile32768 337565952 337598720 12 1703 18372 28 _ _ (981863 / 50000) (1963729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337598720 :
    ThetaLowerSegment 337598720 337664256 (33757299606921 / 100000) (33763783859891 / 100000) := by
  exact
    packedTile32768 337598720 337664256 13 3302 18373 28 _ _ (392747 / 20000) (981869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337664256 :
    ThetaLowerSegment 337664256 337697024 (33763783859891 / 100000) (16883483553373 / 50000) := by
  exact
    packedTile32768 337664256 337697024 12 1621 18375 28 _ _ (392751 / 20000) (981879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337697024 :
    ThetaLowerSegment 337697024 337729792 (16883483553373 / 50000) (16885115441257 / 50000) := by
  exact
    packedTile32768 337697024 337729792 12 1662 18376 28 _ _ (490941 / 25000) (1963767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337729792 :
    ThetaLowerSegment 337729792 337762560 (16885115441257 / 50000) (16886770902739 / 50000) := by
  exact
    packedTile32768 337729792 337762560 12 1686 18377 28 _ _ (981887 / 50000) (1963777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337762560 :
    ThetaLowerSegment 337762560 337795328 (16886770902739 / 50000) (3377672902691 / 10000) := by
  exact
    packedTile32768 337762560 337795328 12 1623 18378 28 _ _ (245473 / 12500) (1963787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337795328 :
    ThetaLowerSegment 337795328 337828096 (3377672902691 / 10000) (4222512607651 / 12500) := by
  exact
    packedTile32768 337795328 337828096 12 1717 18379 28 _ _ (981897 / 50000) (1963797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337828096 :
    ThetaLowerSegment 337828096 337860864 (4222512607651 / 12500) (16891721626957 / 50000) := by
  exact
    packedTile32768 337828096 337860864 12 1702 18380 28 _ _ (1963803 / 100000) (981903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337860864 :
    ThetaLowerSegment 337860864 337893632 (16891721626957 / 50000) (6757327675533 / 20000) := by
  exact
    packedTile32768 337860864 337893632 12 1627 18380 28 _ _ (1963813 / 100000) (245477 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337893632 :
    ThetaLowerSegment 337893632 337926400 (6757327675533 / 20000) (8447471144271 / 25000) := by
  exact
    packedTile32768 337893632 337926400 12 1653 18381 28 _ _ (1963823 / 100000) (981913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337926400 :
    ThetaLowerSegment 337926400 337959168 (8447471144271 / 25000) (1689661449149 / 5000) := by
  exact
    packedTile32768 337926400 337959168 12 1703 18382 28 _ _ (245479 / 12500) (392767 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337959168 :
    ThetaLowerSegment 337959168 337991936 (1689661449149 / 5000) (2112275895919 / 6250) := by
  exact
    packedTile32768 337959168 337991936 12 1622 18383 28 _ _ (981921 / 50000) (392769 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell337991936 :
    ThetaLowerSegment 337991936 338024704 (2112275895919 / 6250) (4224960764017 / 12500) := by
  exact
    packedTile32768 337991936 338024704 12 1666 18384 28 _ _ (490963 / 25000) (392771 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338024704 :
    ThetaLowerSegment 338024704 338057472 (4224960764017 / 12500) (1690145734981 / 5000) := by
  exact
    packedTile32768 338024704 338057472 12 1644 18385 28 _ _ (1963861 / 100000) (245483 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338057472 :
    ThetaLowerSegment 338057472 338090240 (1690145734981 / 5000) (2112888866149 / 6250) := by
  exact
    packedTile32768 338057472 338090240 12 1684 18386 28 _ _ (1963871 / 100000) (981937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338090240 :
    ThetaLowerSegment 338090240 338123008 (2112888866149 / 6250) (33809538853393 / 100000) := by
  exact
    packedTile32768 338090240 338123008 12 1689 18387 28 _ _ (1963881 / 100000) (490971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338123008 :
    ThetaLowerSegment 338123008 338155776 (33809538853393 / 100000) (8453202182977 / 25000) := by
  exact
    packedTile32768 338123008 338155776 12 1665 18388 28 _ _ (1963891 / 100000) (981947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338155776 :
    ThetaLowerSegment 338155776 338188544 (8453202182977 / 25000) (2113505405063 / 6250) := by
  exact
    packedTile32768 338155776 338188544 12 1669 18389 28 _ _ (19639 / 1000) (1963903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338188544 :
    ThetaLowerSegment 338188544 338221312 (2113505405063 / 6250) (16909648736929 / 50000) := by
  exact
    packedTile32768 338188544 338221312 12 1635 18389 28 _ _ (196391 / 10000) (1963913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338221312 :
    ThetaLowerSegment 338221312 338254080 (16909648736929 / 50000) (16911305303449 / 50000) := by
  exact
    packedTile32768 338221312 338254080 12 1687 18390 28 _ _ (24549 / 1250) (1963923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338254080 :
    ThetaLowerSegment 338254080 338286848 (16911305303449 / 50000) (16912955003809 / 50000) := by
  exact
    packedTile32768 338254080 338286848 12 1680 18391 28 _ _ (1963929 / 100000) (490983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338286848 :
    ThetaLowerSegment 338286848 338319616 (16912955003809 / 50000) (16914569361667 / 50000) := by
  exact
    packedTile32768 338286848 338319616 12 1644 18392 28 _ _ (1963939 / 100000) (981971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338319616 :
    ThetaLowerSegment 338319616 338352384 (16914569361667 / 50000) (16916211223031 / 50000) := by
  exact
    packedTile32768 338319616 338352384 12 1672 18393 28 _ _ (1963949 / 100000) (122747 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338352384 :
    ThetaLowerSegment 338352384 338385152 (16916211223031 / 50000) (1691786192973 / 5000) := by
  exact
    packedTile32768 338352384 338385152 12 1681 18394 28 _ _ (981979 / 50000) (1963961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338385152 :
    ThetaLowerSegment 338385152 338417920 (1691786192973 / 5000) (1691949202317 / 5000) := by
  exact
    packedTile32768 338385152 338417920 12 1660 18395 28 _ _ (61374 / 3125) (1963971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338417920 :
    ThetaLowerSegment 338417920 338450688 (1691949202317 / 5000) (2115144439067 / 6250) := by
  exact
    packedTile32768 338417920 338450688 12 1694 18396 28 _ _ (981989 / 50000) (1963981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338450688 :
    ThetaLowerSegment 338450688 338483456 (2115144439067 / 6250) (33845581063427 / 100000) := by
  exact
    packedTile32768 338450688 338483456 12 1665 18397 28 _ _ (1963987 / 100000) (196399 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338483456 :
    ThetaLowerSegment 338483456 338516224 (33845581063427 / 100000) (33848825586471 / 100000) := by
  exact
    packedTile32768 338483456 338516224 12 1652 18397 28 _ _ (1963997 / 100000) (491 / 25)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338516224 :
    ThetaLowerSegment 338516224 338548992 (33848825586471 / 100000) (33852136902273 / 100000) := by
  exact
    packedTile32768 338516224 338548992 12 1686 18398 28 _ _ (1964007 / 100000) (196401 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338548992 :
    ThetaLowerSegment 338548992 338581760 (33852136902273 / 100000) (33855426629073 / 100000) := by
  exact
    packedTile32768 338548992 338581760 12 1675 18399 28 _ _ (122751 / 6250) (1964019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338581760 :
    ThetaLowerSegment 338581760 338614528 (33855426629073 / 100000) (33858677092103 / 100000) := by
  exact
    packedTile32768 338581760 338614528 12 1655 18400 28 _ _ (982013 / 50000) (1964029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338614528 :
    ThetaLowerSegment 338614528 338647296 (33858677092103 / 100000) (33861894183071 / 100000) := by
  exact
    packedTile32768 338614528 338647296 12 1638 18401 28 _ _ (491009 / 25000) (1964039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338647296 :
    ThetaLowerSegment 338647296 338680064 (33861894183071 / 100000) (1058286630443 / 3125) := by
  exact
    packedTile32768 338647296 338680064 12 1669 18402 28 _ _ (392809 / 20000) (122753 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338680064 :
    ThetaLowerSegment 338680064 338712832 (1058286630443 / 3125) (16934222144903 / 50000) := by
  exact
    packedTile32768 338680064 338712832 12 1666 18403 28 _ _ (392811 / 20000) (982029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338712832 :
    ThetaLowerSegment 338712832 338745600 (16934222144903 / 50000) (33871690889251 / 100000) := by
  exact
    packedTile32768 338712832 338745600 12 1653 18404 28 _ _ (392813 / 20000) (491017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338745600 :
    ThetaLowerSegment 338745600 338778368 (33871690889251 / 100000) (33875019994681 / 100000) := by
  exact
    packedTile32768 338745600 338778368 12 1695 18405 28 _ _ (982037 / 50000) (1964077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338778368 :
    ThetaLowerSegment 338778368 338811136 (33875019994681 / 100000) (33878254841029 / 100000) := by
  exact
    packedTile32768 338778368 338811136 12 1647 18405 28 _ _ (491021 / 25000) (1964087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338811136 :
    ThetaLowerSegment 338811136 338843904 (33878254841029 / 100000) (33881666472307 / 100000) := by
  exact
    packedTile32768 338811136 338843904 12 1737 18406 28 _ _ (982047 / 50000) (1964097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338843904 :
    ThetaLowerSegment 338843904 338876672 (33881666472307 / 100000) (33884948490091 / 100000) := by
  exact
    packedTile32768 338843904 338876672 12 1671 18407 28 _ _ (245513 / 12500) (1964107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338876672 :
    ThetaLowerSegment 338876672 338909440 (33884948490091 / 100000) (33888318907999 / 100000) := by
  exact
    packedTile32768 338876672 338909440 12 1716 18408 28 _ _ (1964113 / 100000) (491029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338909440 :
    ThetaLowerSegment 338909440 338974976 (33888318907999 / 100000) (8473717314551 / 25000) := by
  exact
    packedTile32768 338909440 338974976 13 3335 18409 28 _ _ (1964123 / 100000) (982063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell338974976 :
    ThetaLowerSegment 338974976 339040512 (8473717314551 / 25000) (8475363265547 / 25000) := by
  exact
    packedTile32768 338974976 339040512 13 3352 18411 28 _ _ (982071 / 50000) (392829 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339040512 :
    ThetaLowerSegment 339040512 339106048 (8475363265547 / 25000) (8476985663359 / 25000) := by
  exact
    packedTile32768 339040512 339106048 13 3304 18413 28 _ _ (982081 / 50000) (392833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339106048 :
    ThetaLowerSegment 339106048 339138816 (8476985663359 / 25000) (33911268011869 / 100000) := by
  exact
    packedTile32768 339106048 339138816 12 1693 18414 28 _ _ (1964181 / 100000) (245523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339138816 :
    ThetaLowerSegment 339138816 339204352 (33911268011869 / 100000) (16958913222809 / 50000) := by
  exact
    packedTile32768 339138816 339204352 13 3339 18415 28 _ _ (1964191 / 100000) (982097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339204352 :
    ThetaLowerSegment 339204352 339269888 (16958913222809 / 50000) (16962146312469 / 50000) := by
  exact
    packedTile32768 339204352 339269888 13 3292 18417 28 _ _ (196421 / 10000) (1964213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339269888 :
    ThetaLowerSegment 339269888 339302656 (16962146312469 / 50000) (16963772694081 / 50000) := by
  exact
    packedTile32768 339269888 339302656 12 1656 18419 28 _ _ (1964229 / 100000) (245529 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339302656 :
    ThetaLowerSegment 339302656 339335424 (16963772694081 / 50000) (33930851202399 / 100000) := by
  exact
    packedTile32768 339302656 339335424 12 1683 18420 28 _ _ (1964239 / 100000) (982121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339335424 :
    ThetaLowerSegment 339335424 339368192 (33930851202399 / 100000) (33934131496559 / 100000) := by
  exact
    packedTile32768 339335424 339368192 12 1670 18421 28 _ _ (245531 / 12500) (1964251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339368192 :
    ThetaLowerSegment 339368192 339400960 (33934131496559 / 100000) (6787469397381 / 20000) := by
  exact
    packedTile32768 339368192 339400960 12 1637 18421 28 _ _ (982129 / 50000) (1964261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339400960 :
    ThetaLowerSegment 339400960 339433728 (6787469397381 / 20000) (33940576243497 / 100000) := by
  exact
    packedTile32768 339400960 339433728 12 1644 18422 28 _ _ (491067 / 25000) (1964271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339433728 :
    ThetaLowerSegment 339433728 339466496 (33940576243497 / 100000) (33943880157411 / 100000) := by
  exact
    packedTile32768 339433728 339466496 12 1682 18423 28 _ _ (1964277 / 100000) (49107 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339466496 :
    ThetaLowerSegment 339466496 339499264 (33943880157411 / 100000) (16973594990503 / 50000) := by
  exact
    packedTile32768 339466496 339499264 12 1685 18424 28 _ _ (1964287 / 100000) (196429 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339499264 :
    ThetaLowerSegment 339499264 339532032 (16973594990503 / 50000) (16975221428419 / 50000) := by
  exact
    packedTile32768 339499264 339532032 12 1656 18425 28 _ _ (1964297 / 100000) (19643 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339532032 :
    ThetaLowerSegment 339532032 339564800 (16975221428419 / 50000) (1061052807958 / 3125) := by
  exact
    packedTile32768 339532032 339564800 12 1653 18426 28 _ _ (982153 / 50000) (1964309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339564800 :
    ThetaLowerSegment 339564800 339597568 (1061052807958 / 3125) (2122311378017 / 6250) := by
  exact
    packedTile32768 339564800 339597568 12 1676 18427 28 _ _ (491079 / 25000) (1964319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339597568 :
    ThetaLowerSegment 339597568 339630336 (2122311378017 / 6250) (16980138111487 / 50000) := by
  exact
    packedTile32768 339597568 339630336 12 1677 18428 28 _ _ (982163 / 50000) (1964329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339630336 :
    ThetaLowerSegment 339630336 339663104 (16980138111487 / 50000) (8490875415261 / 25000) := by
  exact
    packedTile32768 339630336 339663104 12 1642 18429 28 _ _ (392867 / 20000) (982169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339663104 :
    ThetaLowerSegment 339663104 339695872 (8490875415261 / 25000) (33966748723329 / 100000) := by
  exact
    packedTile32768 339663104 339695872 12 1653 18429 28 _ _ (392869 / 20000) (491087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339695872 :
    ThetaLowerSegment 339695872 339728640 (33966748723329 / 100000) (33970103841669 / 100000) := by
  exact
    packedTile32768 339695872 339728640 12 1708 18430 28 _ _ (392871 / 20000) (982179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339728640 :
    ThetaLowerSegment 339728640 339761408 (33970103841669 / 100000) (33973341113541 / 100000) := by
  exact
    packedTile32768 339728640 339761408 12 1648 18431 28 _ _ (491091 / 25000) (1964367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339761408 :
    ThetaLowerSegment 339761408 339794176 (33973341113541 / 100000) (33976651083731 / 100000) := by
  exact
    packedTile32768 339761408 339794176 12 1685 18432 28 _ _ (982187 / 50000) (1964377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339794176 :
    ThetaLowerSegment 339794176 339826944 (33976651083731 / 100000) (33979931605011 / 100000) := by
  exact
    packedTile32768 339794176 339826944 12 1670 18433 28 _ _ (61387 / 3125) (1964387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339826944 :
    ThetaLowerSegment 339826944 339859712 (33979931605011 / 100000) (33983255357967 / 100000) := by
  exact
    packedTile32768 339826944 339859712 12 1692 18434 28 _ _ (1964393 / 100000) (491099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339859712 :
    ThetaLowerSegment 339859712 339892480 (33983255357967 / 100000) (679730364627 / 2000) := by
  exact
    packedTile32768 339859712 339892480 12 1661 18435 28 _ _ (1964403 / 100000) (982203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339892480 :
    ThetaLowerSegment 339892480 339925248 (679730364627 / 2000) (679796172429 / 2000) := by
  exact
    packedTile32768 339892480 339925248 12 1675 18436 28 _ _ (491103 / 25000) (392883 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339925248 :
    ThetaLowerSegment 339925248 339958016 (679796172429 / 2000) (8498268863809 / 25000) := by
  exact
    packedTile32768 339925248 339958016 12 1663 18437 28 _ _ (982211 / 50000) (78577 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339958016 :
    ThetaLowerSegment 339958016 339990784 (8498268863809 / 25000) (8499086558629 / 25000) := by
  exact
    packedTile32768 339958016 339990784 12 1665 18437 28 _ _ (122777 / 6250) (392887 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell339990784 :
    ThetaLowerSegment 339990784 340023552 (8499086558629 / 25000) (8499899837203 / 25000) := by
  exact
    packedTile32768 339990784 340023552 12 1656 18438 28 _ _ (1964441 / 100000) (491111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340023552 :
    ThetaLowerSegment 340023552 340056320 (8499899837203 / 25000) (34002956595571 / 100000) := by
  exact
    packedTile32768 340023552 340056320 12 1709 18439 28 _ _ (1964451 / 100000) (982227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340056320 :
    ThetaLowerSegment 340056320 340089088 (34002956595571 / 100000) (8501574535933 / 25000) := by
  exact
    packedTile32768 340056320 340089088 12 1701 18440 28 _ _ (1964461 / 100000) (122779 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340089088 :
    ThetaLowerSegment 340089088 340154624 (8501574535933 / 25000) (17006460186051 / 50000) := by
  exact
    packedTile32768 340089088 340154624 13 3371 18441 28 _ _ (196447 / 10000) (1964473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340154624 :
    ThetaLowerSegment 340154624 340220160 (17006460186051 / 50000) (8504862093093 / 25000) := by
  exact
    packedTile32768 340154624 340220160 13 3323 18443 28 _ _ (196449 / 10000) (1964493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340220160 :
    ThetaLowerSegment 340220160 340285696 (8504862093093 / 25000) (8506512280653 / 25000) := by
  exact
    packedTile32768 340220160 340285696 13 3360 18445 28 _ _ (1964509 / 100000) (61391 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340285696 :
    ThetaLowerSegment 340285696 340351232 (8506512280653 / 25000) (340326224333 / 1000) := by
  exact
    packedTile32768 340285696 340351232 13 3346 18446 28 _ _ (122783 / 6250) (1964531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340351232 :
    ThetaLowerSegment 340351232 340416768 (340326224333 / 1000) (34039197772109 / 100000) := by
  exact
    packedTile32768 340351232 340416768 13 3347 18448 28 _ _ (1964547 / 100000) (39291 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340416768 :
    ThetaLowerSegment 340416768 340482304 (34039197772109 / 100000) (17022890518063 / 50000) := by
  exact
    packedTile32768 340416768 340482304 13 3351 18450 28 _ _ (1964567 / 100000) (196457 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340482304 :
    ThetaLowerSegment 340482304 340547840 (17022890518063 / 50000) (17026128155791 / 50000) := by
  exact
    packedTile32768 340482304 340547840 13 3296 18452 28 _ _ (982293 / 50000) (1964589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340547840 :
    ThetaLowerSegment 340547840 340613376 (17026128155791 / 50000) (34058871136617 / 100000) := by
  exact
    packedTile32768 340547840 340613376 13 3367 18453 28 _ _ (392921 / 20000) (61394 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340613376 :
    ThetaLowerSegment 340613376 340678912 (34058871136617 / 100000) (34065405476041 / 100000) := by
  exact
    packedTile32768 340613376 340678912 13 3326 18455 28 _ _ (122789 / 6250) (1964627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340678912 :
    ThetaLowerSegment 340678912 340744448 (34065405476041 / 100000) (1362880345781 / 4000) := by
  exact
    packedTile32768 340678912 340744448 13 3361 18457 28 _ _ (491161 / 25000) (1964647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340744448 :
    ThetaLowerSegment 340744448 340809984 (1362880345781 / 4000) (17039272539163 / 50000) := by
  exact
    packedTile32768 340744448 340809984 13 3327 18459 28 _ _ (1964663 / 100000) (982333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340809984 :
    ThetaLowerSegment 340809984 340875520 (17039272539163 / 50000) (8521254676379 / 25000) := by
  exact
    packedTile32768 340809984 340875520 13 3295 18461 28 _ _ (982341 / 50000) (392937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340875520 :
    ThetaLowerSegment 340875520 340941056 (8521254676379 / 25000) (3409168690071 / 10000) := by
  exact
    packedTile32768 340875520 340941056 13 3394 18462 28 _ _ (1964701 / 100000) (61397 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell340941056 :
    ThetaLowerSegment 340941056 341006592 (3409168690071 / 10000) (34098274610223 / 100000) := by
  exact
    packedTile32768 340941056 341006592 13 3353 18464 28 _ _ (1964721 / 100000) (491181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341006592 :
    ThetaLowerSegment 341006592 341072128 (34098274610223 / 100000) (34104811300203 / 100000) := by
  exact
    packedTile32768 341006592 341072128 13 3327 18466 28 _ _ (98237 / 5000) (1964743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341072128 :
    ThetaLowerSegment 341072128 341137664 (34104811300203 / 100000) (34111318582011 / 100000) := by
  exact
    packedTile32768 341072128 341137664 13 3312 18468 28 _ _ (1964759 / 100000) (982381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341137664 :
    ThetaLowerSegment 341137664 341203200 (34111318582011 / 100000) (34117790560743 / 100000) := by
  exact
    packedTile32768 341137664 341203200 13 3294 18469 28 _ _ (982389 / 50000) (1964781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341203200 :
    ThetaLowerSegment 341203200 341268736 (34117790560743 / 100000) (17062179438557 / 50000) := by
  exact
    packedTile32768 341203200 341268736 13 3343 18471 28 _ _ (1964797 / 100000) (2456 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341268736 :
    ThetaLowerSegment 341268736 341334272 (17062179438557 / 50000) (6826177592801 / 20000) := by
  exact
    packedTile32768 341268736 341334272 13 3323 18473 28 _ _ (1964817 / 100000) (98241 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341334272 :
    ThetaLowerSegment 341334272 341399808 (6826177592801 / 20000) (6827488138413 / 20000) := by
  exact
    packedTile32768 341334272 341399808 13 3335 18475 28 _ _ (491209 / 25000) (1964839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341399808 :
    ThetaLowerSegment 341399808 341465344 (6827488138413 / 20000) (6828816380393 / 20000) := by
  exact
    packedTile32768 341399808 341465344 13 3380 18477 28 _ _ (392971 / 20000) (982429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341465344 :
    ThetaLowerSegment 341465344 341530880 (6828816380393 / 20000) (6830142670343 / 20000) := by
  exact
    packedTile32768 341465344 341530880 13 3375 18478 28 _ _ (982437 / 50000) (1964877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341530880 :
    ThetaLowerSegment 341530880 341596416 (6830142670343 / 20000) (8539339163737 / 25000) := by
  exact
    packedTile32768 341530880 341596416 13 3381 18480 28 _ _ (1964893 / 100000) (61403 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341596416 :
    ThetaLowerSegment 341596416 341661952 (8539339163737 / 25000) (34163791745023 / 100000) := by
  exact
    packedTile32768 341596416 341661952 13 3275 18482 28 _ _ (1964913 / 100000) (491229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341661952 :
    ThetaLowerSegment 341661952 341727488 (34163791745023 / 100000) (34170380162019 / 100000) := by
  exact
    packedTile32768 341661952 341727488 13 3353 18484 28 _ _ (491233 / 25000) (392987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341727488 :
    ThetaLowerSegment 341727488 341793024 (34170380162019 / 100000) (34176927378751 / 100000) := by
  exact
    packedTile32768 341727488 341793024 13 3332 18485 28 _ _ (1964951 / 100000) (982477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341793024 :
    ThetaLowerSegment 341793024 341858560 (34176927378751 / 100000) (34183447149211 / 100000) := by
  exact
    packedTile32768 341793024 341858560 13 3318 18487 28 _ _ (196497 / 10000) (1964973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341858560 :
    ThetaLowerSegment 341858560 341924096 (34183447149211 / 100000) (34190069162141 / 100000) := by
  exact
    packedTile32768 341858560 341924096 13 3370 18489 28 _ _ (1964989 / 100000) (61406 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341924096 :
    ThetaLowerSegment 341924096 341989632 (34190069162141 / 100000) (34196649973933 / 100000) := by
  exact
    packedTile32768 341924096 341989632 13 3349 18491 28 _ _ (122813 / 6250) (1965011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell341989632 :
    ThetaLowerSegment 341989632 342055168 (34196649973933 / 100000) (34203146356501 / 100000) := by
  exact
    packedTile32768 341989632 342055168 13 3306 18492 28 _ _ (491257 / 25000) (1965031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342055168 :
    ThetaLowerSegment 342055168 342120704 (34203146356501 / 100000) (34209682102823 / 100000) := by
  exact
    packedTile32768 342055168 342120704 13 3326 18494 28 _ _ (1965047 / 100000) (39301 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342120704 :
    ThetaLowerSegment 342120704 342186240 (34209682102823 / 100000) (34216324025903 / 100000) := by
  exact
    packedTile32768 342120704 342186240 13 3380 18496 28 _ _ (982533 / 50000) (1965069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342186240 :
    ThetaLowerSegment 342186240 342251776 (34216324025903 / 100000) (17111427001679 / 50000) := by
  exact
    packedTile32768 342186240 342251776 13 3323 18498 28 _ _ (393017 / 20000) (61409 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342251776 :
    ThetaLowerSegment 342251776 342317312 (17111427001679 / 50000) (17114720515983 / 50000) := by
  exact
    packedTile32768 342251776 342317312 13 3352 18500 28 _ _ (122819 / 6250) (1965107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342317312 :
    ThetaLowerSegment 342317312 342382848 (17114720515983 / 50000) (34235994717171 / 100000) := by
  exact
    packedTile32768 342317312 342382848 13 3335 18501 28 _ _ (1965123 / 100000) (982563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342382848 :
    ThetaLowerSegment 342382848 342448384 (34235994717171 / 100000) (34242518991931 / 100000) := by
  exact
    packedTile32768 342382848 342448384 13 3320 18503 28 _ _ (1965143 / 100000) (982573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342448384 :
    ThetaLowerSegment 342448384 342513920 (34242518991931 / 100000) (34249094423983 / 100000) := by
  exact
    packedTile32768 342448384 342513920 13 3346 18505 28 _ _ (982581 / 50000) (393033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342513920 :
    ThetaLowerSegment 342513920 342579456 (34249094423983 / 100000) (6851100968881 / 20000) := by
  exact
    packedTile32768 342513920 342579456 13 3262 18507 28 _ _ (1965181 / 100000) (61412 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342579456 :
    ThetaLowerSegment 342579456 342644992 (6851100968881 / 20000) (6852407433841 / 20000) := by
  exact
    packedTile32768 342579456 342644992 13 3324 18508 28 _ _ (4913 / 250) (1965203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342644992 :
    ThetaLowerSegment 342644992 342710528 (6852407433841 / 20000) (17134307378599 / 50000) := by
  exact
    packedTile32768 342644992 342710528 13 3347 18510 28 _ _ (1965219 / 100000) (982611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342710528 :
    ThetaLowerSegment 342710528 342776064 (17134307378599 / 50000) (1713755886487 / 5000) := by
  exact
    packedTile32768 342710528 342776064 13 3309 18512 28 _ _ (982619 / 50000) (1965241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342776064 :
    ThetaLowerSegment 342776064 342841600 (1713755886487 / 5000) (34281628626181 / 100000) := by
  exact
    packedTile32768 342776064 342841600 13 3313 18514 28 _ _ (1965257 / 100000) (98263 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342841600 :
    ThetaLowerSegment 342841600 342907136 (34281628626181 / 100000) (34288159238329 / 100000) := by
  exact
    packedTile32768 342841600 342907136 13 3323 18515 28 _ _ (491319 / 25000) (1965279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342907136 :
    ThetaLowerSegment 342907136 342972672 (34288159238329 / 100000) (34294689916937 / 100000) := by
  exact
    packedTile32768 342907136 342972672 13 3323 18517 28 _ _ (122831 / 6250) (1965299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell342972672 :
    ThetaLowerSegment 342972672 343038208 (34294689916937 / 100000) (34301332681637 / 100000) := by
  exact
    packedTile32768 342972672 343038208 13 3380 18519 28 _ _ (393063 / 20000) (982659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343038208 :
    ThetaLowerSegment 343038208 343103744 (34301332681637 / 100000) (34307798630497 / 100000) := by
  exact
    packedTile32768 343038208 343103744 13 3290 18521 28 _ _ (982667 / 50000) (1965337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343103744 :
    ThetaLowerSegment 343103744 343169280 (34307798630497 / 100000) (17157209952377 / 50000) := by
  exact
    packedTile32768 343103744 343169280 13 3369 18523 28 _ _ (1965353 / 100000) (491339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343169280 :
    ThetaLowerSegment 343169280 343234816 (17157209952377 / 50000) (17160532413743 / 50000) := by
  exact
    packedTile32768 343169280 343234816 13 3381 18524 28 _ _ (491343 / 25000) (15723 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343234816 :
    ThetaLowerSegment 343234816 343300352 (17160532413743 / 50000) (17163822478277 / 50000) := by
  exact
    packedTile32768 343234816 343300352 13 3348 18526 28 _ _ (1965391 / 100000) (982697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343300352 :
    ThetaLowerSegment 343300352 343365888 (17163822478277 / 50000) (8583517470461 / 25000) := by
  exact
    packedTile32768 343300352 343365888 13 3269 18528 28 _ _ (196541 / 10000) (1965413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343365888 :
    ThetaLowerSegment 343365888 343431424 (8583517470461 / 25000) (8585144845673 / 25000) := by
  exact
    packedTile32768 343365888 343431424 13 3312 18530 28 _ _ (1965429 / 100000) (245679 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343431424 :
    ThetaLowerSegment 343431424 343496960 (8585144845673 / 25000) (8586789925649 / 25000) := by
  exact
    packedTile32768 343431424 343496960 13 3348 18531 28 _ _ (245681 / 12500) (1965451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343496960 :
    ThetaLowerSegment 343496960 343562496 (8586789925649 / 25000) (34353824601193 / 100000) := by
  exact
    packedTile32768 343496960 343562496 13 3391 18533 28 _ _ (1965467 / 100000) (196547 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343562496 :
    ThetaLowerSegment 343562496 343628032 (34353824601193 / 100000) (34360467943873 / 100000) := by
  exact
    packedTile32768 343562496 343628032 13 3380 18535 28 _ _ (982743 / 50000) (1965489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343628032 :
    ThetaLowerSegment 343628032 343693568 (34360467943873 / 100000) (34366973768733 / 100000) := by
  exact
    packedTile32768 343628032 343693568 13 3310 18537 28 _ _ (982753 / 50000) (1965509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343693568 :
    ThetaLowerSegment 343693568 343759104 (34366973768733 / 100000) (4296700926951 / 12500) := by
  exact
    packedTile32768 343693568 343759104 13 3375 18538 28 _ _ (78621 / 4000) (245691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343759104 :
    ThetaLowerSegment 343759104 343824640 (4296700926951 / 12500) (1074385114983 / 3125) := by
  exact
    packedTile32768 343759104 343824640 13 3417 18540 28 _ _ (245693 / 12500) (1965547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343824640 :
    ThetaLowerSegment 343824640 343890176 (1074385114983 / 3125) (3438680610623 / 10000) := by
  exact
    packedTile32768 343824640 343890176 13 3298 18542 28 _ _ (1965563 / 100000) (982783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343890176 :
    ThetaLowerSegment 343890176 343955712 (3438680610623 / 10000) (17196632504341 / 50000) := by
  exact
    packedTile32768 343890176 343955712 13 3286 18544 28 _ _ (982791 / 50000) (393117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell343955712 :
    ThetaLowerSegment 343955712 344021248 (17196632504341 / 50000) (34399702351957 / 100000) := by
  exact
    packedTile32768 343955712 344021248 13 3275 18546 28 _ _ (1965601 / 100000) (491401 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344021248 :
    ThetaLowerSegment 344021248 344086784 (34399702351957 / 100000) (34406283247717 / 100000) := by
  exact
    packedTile32768 344021248 344086784 13 3348 18547 28 _ _ (98281 / 5000) (1965623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344086784 :
    ThetaLowerSegment 344086784 344152320 (34406283247717 / 100000) (17206423258169 / 50000) := by
  exact
    packedTile32768 344086784 344152320 13 3339 18549 28 _ _ (1965639 / 100000) (982821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344152320 :
    ThetaLowerSegment 344152320 344217856 (17206423258169 / 50000) (4302435076511 / 12500) := by
  exact
    packedTile32768 344152320 344217856 13 3375 18551 28 _ _ (982829 / 50000) (1965661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344217856 :
    ThetaLowerSegment 344217856 344283392 (4302435076511 / 12500) (34426118703317 / 100000) := by
  exact
    packedTile32768 344217856 344283392 13 3377 18553 28 _ _ (1965677 / 100000) (24571 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344283392 :
    ThetaLowerSegment 344283392 344348928 (34426118703317 / 100000) (34432833520853 / 100000) := by
  exact
    packedTile32768 344283392 344348928 13 3416 18554 28 _ _ (61428 / 3125) (1965699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344348928 :
    ThetaLowerSegment 344348928 344414464 (34432833520853 / 100000) (34439410803243 / 100000) := by
  exact
    packedTile32768 344348928 344414464 13 3346 18556 28 _ _ (393143 / 20000) (982859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344414464 :
    ThetaLowerSegment 344414464 344480000 (34439410803243 / 100000) (34445760124063 / 100000) := by
  exact
    packedTile32768 344414464 344480000 13 3230 18558 28 _ _ (982867 / 50000) (1965737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344480000 :
    ThetaLowerSegment 344480000 344545536 (34445760124063 / 100000) (17226177612689 / 50000) := by
  exact
    packedTile32768 344480000 344545536 13 3355 18560 28 _ _ (1965753 / 100000) (491439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344545536 :
    ThetaLowerSegment 344545536 344611072 (17226177612689 / 50000) (17229531219721 / 50000) := by
  exact
    packedTile32768 344545536 344611072 13 3412 18561 28 _ _ (491443 / 25000) (78631 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344611072 :
    ThetaLowerSegment 344611072 344676608 (17229531219721 / 50000) (8616384438749 / 25000) := by
  exact
    packedTile32768 344611072 344676608 13 3294 18563 28 _ _ (1965791 / 100000) (982897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344676608 :
    ThetaLowerSegment 344676608 344742144 (8616384438749 / 25000) (17236011481093 / 50000) := by
  exact
    packedTile32768 344676608 344742144 13 3299 18565 28 _ _ (196581 / 10000) (1965813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344742144 :
    ThetaLowerSegment 344742144 344807680 (17236011481093 / 50000) (3447862028431 / 10000) := by
  exact
    packedTile32768 344742144 344807680 13 3356 18567 28 _ _ (1965829 / 100000) (245729 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344807680 :
    ThetaLowerSegment 344807680 344873216 (3447862028431 / 10000) (17242537081647 / 50000) := by
  exact
    packedTile32768 344807680 344873216 13 3283 18568 28 _ _ (245731 / 12500) (1965851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344873216 :
    ThetaLowerSegment 344873216 344938752 (17242537081647 / 50000) (34491716827887 / 100000) := by
  exact
    packedTile32768 344873216 344938752 13 3379 18570 28 _ _ (1965867 / 100000) (196587 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell344938752 :
    ThetaLowerSegment 344938752 345004288 (34491716827887 / 100000) (34498204251687 / 100000) := by
  exact
    packedTile32768 344938752 345004288 13 3300 18572 28 _ _ (982943 / 50000) (1965889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345004288 :
    ThetaLowerSegment 345004288 345069824 (34498204251687 / 100000) (34504731056287 / 100000) := by
  exact
    packedTile32768 345004288 345069824 13 3320 18574 28 _ _ (393181 / 20000) (491477 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345069824 :
    ThetaLowerSegment 345069824 345135360 (34504731056287 / 100000) (34511273651359 / 100000) := by
  exact
    packedTile32768 345069824 345135360 13 3328 18576 28 _ _ (491481 / 25000) (1965927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345135360 :
    ThetaLowerSegment 345135360 345200896 (34511273651359 / 100000) (17258932729119 / 50000) := by
  exact
    packedTile32768 345135360 345200896 13 3353 18577 28 _ _ (1965943 / 100000) (982973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345200896 :
    ThetaLowerSegment 345200896 345266432 (17258932729119 / 50000) (863109860451 / 2500) := by
  exact
    packedTile32768 345200896 345266432 13 3321 18579 28 _ _ (982981 / 50000) (393193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345266432 :
    ThetaLowerSegment 345266432 345331968 (863109860451 / 2500) (17265380132259 / 50000) := by
  exact
    packedTile32768 345266432 345331968 13 3238 18581 28 _ _ (1965981 / 100000) (61437 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345331968 :
    ThetaLowerSegment 345331968 345397504 (17265380132259 / 50000) (17268680063259 / 50000) := by
  exact
    packedTile32768 345331968 345397504 13 3357 18583 28 _ _ (983 / 50) (1966003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345397504 :
    ThetaLowerSegment 345397504 345463040 (17268680063259 / 50000) (34543842091161 / 100000) := by
  exact
    packedTile32768 345397504 345463040 13 3297 18584 28 _ _ (1966019 / 100000) (983011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345463040 :
    ThetaLowerSegment 345463040 345528576 (34543842091161 / 100000) (34550387031663 / 100000) := by
  exact
    packedTile32768 345463040 345528576 13 3329 18586 28 _ _ (983019 / 50000) (1966041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345528576 :
    ThetaLowerSegment 345528576 345594112 (34550387031663 / 100000) (8639254635481 / 25000) := by
  exact
    packedTile32768 345528576 345594112 13 3373 18588 28 _ _ (1966057 / 100000) (98303 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345594112 :
    ThetaLowerSegment 345594112 345659648 (8639254635481 / 25000) (8640893359827 / 25000) := by
  exact
    packedTile32768 345594112 345659648 13 3334 18590 28 _ _ (491519 / 25000) (1966079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345659648 :
    ThetaLowerSegment 345659648 345725184 (8640893359827 / 25000) (34570216874313 / 100000) := by
  exact
    packedTile32768 345659648 345725184 13 3379 18591 28 _ _ (393219 / 20000) (983049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345725184 :
    ThetaLowerSegment 345725184 345790720 (34570216874313 / 100000) (34576803356213 / 100000) := by
  exact
    packedTile32768 345725184 345790720 13 3350 18593 28 _ _ (983057 / 50000) (1966117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345790720 :
    ThetaLowerSegment 345790720 345856256 (34576803356213 / 100000) (3458338793563 / 10000) := by
  exact
    packedTile32768 345790720 345856256 13 3349 18595 28 _ _ (1966133 / 100000) (245767 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345856256 :
    ThetaLowerSegment 345856256 345921792 (3458338793563 / 10000) (17294949915527 / 50000) := by
  exact
    packedTile32768 345856256 345921792 13 3312 18597 28 _ _ (245769 / 12500) (393231 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345921792 :
    ThetaLowerSegment 345921792 345987328 (17294949915527 / 50000) (34596484537733 / 100000) := by
  exact
    packedTile32768 345921792 345987328 13 3349 18598 28 _ _ (1966171 / 100000) (983087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell345987328 :
    ThetaLowerSegment 345987328 346052864 (34596484537733 / 100000) (34603008356153 / 100000) := by
  exact
    packedTile32768 345987328 346052864 13 3318 18600 28 _ _ (196619 / 10000) (1966193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346052864 :
    ThetaLowerSegment 346052864 346118400 (34603008356153 / 100000) (2163095887739 / 6250) := by
  exact
    packedTile32768 346052864 346118400 13 3319 18602 28 _ _ (1966209 / 100000) (491553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346118400 :
    ThetaLowerSegment 346118400 346183936 (2163095887739 / 6250) (1730805758447 / 5000) := by
  exact
    packedTile32768 346118400 346183936 13 3347 18604 28 _ _ (491557 / 25000) (1966231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346183936 :
    ThetaLowerSegment 346183936 346249472 (1730805758447 / 5000) (34622715860119 / 100000) := by
  exact
    packedTile32768 346183936 346249472 13 3357 18606 28 _ _ (1966247 / 100000) (1573 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346249472 :
    ThetaLowerSegment 346249472 346315008 (34622715860119 / 100000) (34629416894647 / 100000) := by
  exact
    packedTile32768 346249472 346315008 13 3408 18607 28 _ _ (983133 / 50000) (1966269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346315008 :
    ThetaLowerSegment 346315008 346380544 (34629416894647 / 100000) (34635982316923 / 100000) := by
  exact
    packedTile32768 346315008 346380544 13 3339 18609 28 _ _ (491571 / 25000) (1966287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346380544 :
    ThetaLowerSegment 346380544 346446080 (34635982316923 / 100000) (34642451453793 / 100000) := by
  exact
    packedTile32768 346380544 346446080 13 3290 18611 28 _ _ (1966303 / 100000) (983153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346446080 :
    ThetaLowerSegment 346446080 346511616 (34642451453793 / 100000) (34648997339731 / 100000) := by
  exact
    packedTile32768 346446080 346511616 13 3329 18613 28 _ _ (983161 / 50000) (78653 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346511616 :
    ThetaLowerSegment 346511616 346577152 (34648997339731 / 100000) (8663860259797 / 25000) := by
  exact
    packedTile32768 346511616 346577152 13 3277 18614 28 _ _ (1966341 / 100000) (245793 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346577152 :
    ThetaLowerSegment 346577152 346642688 (8663860259797 / 25000) (8665480540437 / 25000) := by
  exact
    packedTile32768 346577152 346642688 13 3296 18616 28 _ _ (49159 / 2500) (1966363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346642688 :
    ThetaLowerSegment 346642688 346708224 (8665480540437 / 25000) (17334266563973 / 50000) := by
  exact
    packedTile32768 346642688 346708224 13 3362 18618 28 _ _ (1966379 / 100000) (983191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346708224 :
    ThetaLowerSegment 346708224 346773760 (17334266563973 / 50000) (693500366171 / 2000) := by
  exact
    packedTile32768 346708224 346773760 13 3298 18620 28 _ _ (983199 / 50000) (1966401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346773760 :
    ThetaLowerSegment 346773760 346839296 (693500366171 / 2000) (6936295597679 / 20000) := by
  exact
    packedTile32768 346773760 346839296 13 3285 18621 28 _ _ (1966417 / 100000) (98321 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346839296 :
    ThetaLowerSegment 346839296 346904832 (6936295597679 / 20000) (34688230729619 / 100000) := by
  exact
    packedTile32768 346839296 346904832 13 3434 18623 28 _ _ (491609 / 25000) (1966439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346904832 :
    ThetaLowerSegment 346904832 346970368 (34688230729619 / 100000) (1084211414362 / 3125) := by
  exact
    packedTile32768 346904832 346970368 13 3323 18625 28 _ _ (393291 / 20000) (983229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell346970368 :
    ThetaLowerSegment 346970368 347035904 (1084211414362 / 3125) (8675341185743 / 25000) := by
  exact
    packedTile32768 346970368 347035904 13 3356 18627 28 _ _ (1966473 / 100000) (491619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347035904 :
    ThetaLowerSegment 347035904 347101440 (8675341185743 / 25000) (4338477100403 / 12500) := by
  exact
    packedTile32768 347035904 347101440 13 3281 18628 28 _ _ (491623 / 25000) (393299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347101440 :
    ThetaLowerSegment 347101440 347166976 (4338477100403 / 12500) (17357143312207 / 50000) := by
  exact
    packedTile32768 347101440 347166976 13 3290 18630 28 _ _ (1966511 / 100000) (983257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347166976 :
    ThetaLowerSegment 347166976 347232512 (17357143312207 / 50000) (17360452982197 / 50000) := by
  exact
    packedTile32768 347166976 347232512 13 3366 18632 28 _ _ (196653 / 10000) (1966533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347232512 :
    ThetaLowerSegment 347232512 347298048 (17360452982197 / 50000) (17363689921851 / 50000) := by
  exact
    packedTile32768 347232512 347298048 13 3292 18634 28 _ _ (1966549 / 100000) (245819 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347298048 :
    ThetaLowerSegment 347298048 347363584 (17363689921851 / 50000) (17367001622363 / 50000) := by
  exact
    packedTile32768 347298048 347363584 13 3368 18635 28 _ _ (245821 / 12500) (1966571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347363584 :
    ThetaLowerSegment 347363584 347429120 (17367001622363 / 50000) (6948117082283 / 20000) := by
  exact
    packedTile32768 347363584 347429120 13 3347 18637 28 _ _ (1966587 / 100000) (196659 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347429120 :
    ThetaLowerSegment 347429120 347494656 (6948117082283 / 20000) (34747161741879 / 100000) := by
  exact
    packedTile32768 347429120 347494656 13 3344 18639 28 _ _ (983303 / 50000) (1966609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347494656 :
    ThetaLowerSegment 347494656 347560192 (34747161741879 / 100000) (34753572936119 / 100000) := by
  exact
    packedTile32768 347494656 347560192 13 3260 18641 28 _ _ (61457 / 3125) (1966627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347560192 :
    ThetaLowerSegment 347560192 347625728 (34753572936119 / 100000) (34760094324307 / 100000) := by
  exact
    packedTile32768 347560192 347625728 13 3316 18642 28 _ _ (1966643 / 100000) (983323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347625728 :
    ThetaLowerSegment 347625728 347691264 (34760094324307 / 100000) (34766784908431 / 100000) := by
  exact
    packedTile32768 347625728 347691264 13 3402 18644 28 _ _ (983331 / 50000) (393333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347691264 :
    ThetaLowerSegment 347691264 347756800 (34766784908431 / 100000) (34773188421767 / 100000) := by
  exact
    packedTile32768 347691264 347756800 13 3256 18646 28 _ _ (1966681 / 100000) (491671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347756800 :
    ThetaLowerSegment 347756800 347822336 (34773188421767 / 100000) (34779733599367 / 100000) := by
  exact
    packedTile32768 347756800 347822336 13 3328 18648 28 _ _ (19667 / 1000) (1966703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347822336 :
    ThetaLowerSegment 347822336 347887872 (34779733599367 / 100000) (1391451468283 / 4000) := by
  exact
    packedTile32768 347822336 347887872 13 3332 18649 28 _ _ (1966719 / 100000) (983361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347887872 :
    ThetaLowerSegment 347887872 347953408 (1391451468283 / 4000) (34792743507929 / 100000) := by
  exact
    packedTile32768 347887872 347953408 13 3283 18651 28 _ _ (983369 / 50000) (1966741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell347953408 :
    ThetaLowerSegment 347953408 348018944 (34792743507929 / 100000) (34799302639189 / 100000) := by
  exact
    packedTile32768 347953408 348018944 13 3335 18653 28 _ _ (491689 / 25000) (1966759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348018944 :
    ThetaLowerSegment 348018944 348084480 (34799302639189 / 100000) (34805836265739 / 100000) := by
  exact
    packedTile32768 348018944 348084480 13 3322 18655 28 _ _ (78671 / 4000) (983389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348084480 :
    ThetaLowerSegment 348084480 348150016 (34805836265739 / 100000) (34812299150823 / 100000) := by
  exact
    packedTile32768 348084480 348150016 13 3286 18657 28 _ _ (983397 / 50000) (1966797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348150016 :
    ThetaLowerSegment 348150016 348215552 (34812299150823 / 100000) (17409456771471 / 50000) := by
  exact
    packedTile32768 348150016 348215552 13 3363 18658 28 _ _ (1966813 / 100000) (61463 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348215552 :
    ThetaLowerSegment 348215552 348281088 (17409456771471 / 50000) (17412721712591 / 50000) := by
  exact
    packedTile32768 348215552 348281088 13 3320 18660 28 _ _ (122927 / 6250) (393367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348281088 :
    ThetaLowerSegment 348281088 348346624 (17412721712591 / 50000) (17416029955973 / 50000) := by
  exact
    packedTile32768 348281088 348346624 13 3364 18662 28 _ _ (1966851 / 100000) (983427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348346624 :
    ThetaLowerSegment 348346624 348412160 (17416029955973 / 50000) (3483850337479 / 10000) := by
  exact
    packedTile32768 348346624 348412160 13 3276 18664 28 _ _ (1966869 / 100000) (245859 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348412160 :
    ThetaLowerSegment 348412160 348477696 (3483850337479 / 10000) (3484505311183 / 10000) := by
  exact
    packedTile32768 348412160 348477696 13 3330 18665 28 _ _ (245861 / 12500) (1966891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348477696 :
    ThetaLowerSegment 348477696 348543232 (3484505311183 / 10000) (34851675687699 / 100000) := by
  exact
    packedTile32768 348477696 348543232 13 3367 18667 28 _ _ (1966907 / 100000) (196691 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348543232 :
    ThetaLowerSegment 348543232 348608768 (34851675687699 / 100000) (34858154741943 / 100000) := by
  exact
    packedTile32768 348543232 348608768 13 3294 18669 28 _ _ (983463 / 50000) (1966929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348608768 :
    ThetaLowerSegment 348608768 348674304 (34858154741943 / 100000) (34864645660443 / 100000) := by
  exact
    packedTile32768 348608768 348674304 13 3300 18671 28 _ _ (393389 / 20000) (491737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348674304 :
    ThetaLowerSegment 348674304 348707072 (34864645660443 / 100000) (17434007534031 / 50000) := by
  exact
    packedTile32768 348674304 348707072 12 1713 18672 28 _ _ (1966963 / 100000) (983483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348707072 :
    ThetaLowerSegment 348707072 348772608 (17434007534031 / 50000) (17437292378941 / 50000) := by
  exact
    packedTile32768 348707072 348772608 13 3340 18673 28 _ _ (1966973 / 100000) (61468 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348772608 :
    ThetaLowerSegment 348772608 348838144 (17437292378941 / 50000) (17440505460373 / 50000) := by
  exact
    packedTile32768 348772608 348838144 13 3267 18675 28 _ _ (122937 / 6250) (393399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348838144 :
    ThetaLowerSegment 348838144 348870912 (17440505460373 / 50000) (17442134144653 / 50000) := by
  exact
    packedTile32768 348838144 348870912 12 1656 18677 28 _ _ (196701 / 10000) (1967013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348870912 :
    ThetaLowerSegment 348870912 348903680 (17442134144653 / 50000) (17443786441453 / 50000) := by
  exact
    packedTile32768 348870912 348903680 12 1680 18678 28 _ _ (98351 / 5000) (1967023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348903680 :
    ThetaLowerSegment 348903680 348936448 (17443786441453 / 50000) (34890788975321 / 100000) := by
  exact
    packedTile32768 348903680 348936448 12 1635 18678 28 _ _ (1967029 / 100000) (245879 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348936448 :
    ThetaLowerSegment 348936448 348969216 (34890788975321 / 100000) (34894093600841 / 100000) := by
  exact
    packedTile32768 348936448 348969216 12 1680 18679 28 _ _ (1967039 / 100000) (983521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell348969216 :
    ThetaLowerSegment 348969216 349001984 (34894093600841 / 100000) (6979472960333 / 20000) := by
  exact
    packedTile32768 348969216 349001984 12 1663 18680 28 _ _ (245881 / 12500) (1967051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349001984 :
    ThetaLowerSegment 349001984 349034752 (6979472960333 / 20000) (34900677325653 / 100000) := by
  exact
    packedTile32768 349001984 349034752 12 1684 18681 28 _ _ (1967057 / 100000) (98353 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349034752 :
    ThetaLowerSegment 349034752 349067520 (34900677325653 / 100000) (3490396429461 / 10000) := by
  exact
    packedTile32768 349034752 349067520 12 1671 18682 28 _ _ (1967067 / 100000) (196707 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349067520 :
    ThetaLowerSegment 349067520 349133056 (3490396429461 / 10000) (17455304538669 / 50000) := by
  exact
    packedTile32768 349067520 349133056 13 3378 18683 28 _ _ (491769 / 25000) (1967079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349133056 :
    ThetaLowerSegment 349133056 349198592 (17455304538669 / 50000) (8729303645587 / 25000) := by
  exact
    packedTile32768 349133056 349198592 13 3358 18685 28 _ _ (393419 / 20000) (983549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349198592 :
    ThetaLowerSegment 349198592 349264128 (8729303645587 / 25000) (17461883519541 / 50000) := by
  exact
    packedTile32768 349198592 349264128 13 3331 18686 28 _ _ (983557 / 50000) (1967117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349264128 :
    ThetaLowerSegment 349264128 349329664 (17461883519541 / 50000) (3493034512849 / 10000) := by
  exact
    packedTile32768 349264128 349329664 13 3344 18688 28 _ _ (491783 / 25000) (393427 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349329664 :
    ThetaLowerSegment 349329664 349395200 (3493034512849 / 10000) (17468453772113 / 50000) := by
  exact
    packedTile32768 349329664 349395200 13 3336 18690 28 _ _ (1967151 / 100000) (983577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349395200 :
    ThetaLowerSegment 349395200 349460736 (17468453772113 / 50000) (4367930556267 / 12500) := by
  exact
    packedTile32768 349395200 349460736 13 3323 18692 28 _ _ (196717 / 10000) (1967173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349460736 :
    ThetaLowerSegment 349460736 349526272 (4367930556267 / 12500) (1747502316821 / 5000) := by
  exact
    packedTile32768 349460736 349526272 13 3356 18693 28 _ _ (1967189 / 100000) (245899 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349526272 :
    ThetaLowerSegment 349526272 349591808 (1747502316821 / 5000) (17478282830209 / 50000) := by
  exact
    packedTile32768 349526272 349591808 13 3314 18695 28 _ _ (1967207 / 100000) (196721 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349591808 :
    ThetaLowerSegment 349591808 349657344 (17478282830209 / 50000) (3496317947423 / 10000) := by
  exact
    packedTile32768 349591808 349657344 13 3362 18697 28 _ _ (983613 / 50000) (1967229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349657344 :
    ThetaLowerSegment 349657344 349722880 (3496317947423 / 10000) (6993952768649 / 20000) := by
  exact
    packedTile32768 349657344 349722880 13 3347 18699 28 _ _ (393449 / 20000) (122953 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349722880 :
    ThetaLowerSegment 349722880 349788416 (6993952768649 / 20000) (34976310897837 / 100000) := by
  exact
    packedTile32768 349722880 349788416 13 3328 18700 28 _ _ (61477 / 3125) (1967267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349788416 :
    ThetaLowerSegment 349788416 349853952 (34976310897837 / 100000) (6996568061359 / 20000) := by
  exact
    packedTile32768 349788416 349853952 13 3319 18702 28 _ _ (983641 / 50000) (393457 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349853952 :
    ThetaLowerSegment 349853952 349919488 (6996568061359 / 20000) (34989501587981 / 100000) := by
  exact
    packedTile32768 349853952 349919488 13 3386 18704 28 _ _ (1967301 / 100000) (245913 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349919488 :
    ThetaLowerSegment 349919488 349985024 (34989501587981 / 100000) (34996210149181 / 100000) := by
  exact
    packedTile32768 349919488 349985024 13 3410 18706 28 _ _ (49183 / 2500) (1967323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell349985024 :
    ThetaLowerSegment 349985024 350050560 (34996210149181 / 100000) (35002796800153 / 100000) := by
  exact
    packedTile32768 349985024 350050560 13 3348 18707 28 _ _ (1967339 / 100000) (983671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350050560 :
    ThetaLowerSegment 350050560 350116096 (35002796800153 / 100000) (35009332360107 / 100000) := by
  exact
    packedTile32768 350050560 350116096 13 3322 18709 28 _ _ (1967357 / 100000) (12296 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350116096 :
    ThetaLowerSegment 350116096 350181632 (35009332360107 / 100000) (7003173990111 / 20000) := by
  exact
    packedTile32768 350116096 350181632 13 3323 18711 28 _ _ (122961 / 6250) (1967379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350181632 :
    ThetaLowerSegment 350181632 350247168 (7003173990111 / 20000) (3502247449557 / 10000) := by
  exact
    packedTile32768 350181632 350247168 13 3357 18713 28 _ _ (393479 / 20000) (983699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350247168 :
    ThetaLowerSegment 350247168 350312704 (3502247449557 / 10000) (35029012208969 / 100000) := by
  exact
    packedTile32768 350247168 350312704 13 3323 18714 28 _ _ (1967413 / 100000) (245927 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350312704 :
    ThetaLowerSegment 350312704 350378240 (35029012208969 / 100000) (35035553920369 / 100000) := by
  exact
    packedTile32768 350312704 350378240 13 3325 18716 28 _ _ (245929 / 12500) (393487 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350378240 :
    ThetaLowerSegment 350378240 350443776 (35035553920369 / 100000) (35042121271807 / 100000) := by
  exact
    packedTile32768 350378240 350443776 13 3338 18718 28 _ _ (1967451 / 100000) (983727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350443776 :
    ThetaLowerSegment 350443776 350509312 (35042121271807 / 100000) (35048617857747 / 100000) := by
  exact
    packedTile32768 350443776 350509312 13 3302 18720 28 _ _ (196747 / 10000) (1967473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350509312 :
    ThetaLowerSegment 350509312 350574848 (35048617857747 / 100000) (35055149917907 / 100000) := by
  exact
    packedTile32768 350509312 350574848 13 3320 18721 28 _ _ (61484 / 3125) (1967491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350574848 :
    ThetaLowerSegment 350574848 350640384 (35055149917907 / 100000) (8765445596001 / 25000) := by
  exact
    packedTile32768 350574848 350640384 13 3371 18723 28 _ _ (1967507 / 100000) (196751 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350640384 :
    ThetaLowerSegment 350640384 350705920 (8765445596001 / 25000) (17534103178197 / 50000) := by
  exact
    packedTile32768 350640384 350705920 13 3265 18725 28 _ _ (983763 / 50000) (1967529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350705920 :
    ThetaLowerSegment 350705920 350771456 (17534103178197 / 50000) (3507463825773 / 10000) := by
  exact
    packedTile32768 350705920 350771456 13 3269 18727 28 _ _ (245943 / 12500) (1967547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350771456 :
    ThetaLowerSegment 350771456 350836992 (3507463825773 / 10000) (17540581348319 / 50000) := by
  exact
    packedTile32768 350771456 350836992 13 3316 18728 28 _ _ (1967563 / 100000) (983783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350836992 :
    ThetaLowerSegment 350836992 350902528 (17540581348319 / 50000) (17543886886079 / 50000) := by
  exact
    packedTile32768 350836992 350902528 13 3360 18730 28 _ _ (983791 / 50000) (393517 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350902528 :
    ThetaLowerSegment 350902528 350968064 (17543886886079 / 50000) (17547159988679 / 50000) := by
  exact
    packedTile32768 350902528 350968064 13 3327 18732 28 _ _ (4919 / 250) (1967603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell350968064 :
    ThetaLowerSegment 350968064 351033600 (17547159988679 / 50000) (7020171675059 / 20000) := by
  exact
    packedTile32768 350968064 351033600 13 3323 18734 28 _ _ (1967619 / 100000) (983811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351033600 :
    ThetaLowerSegment 351033600 351099136 (7020171675059 / 20000) (35107388965817 / 100000) := by
  exact
    packedTile32768 351033600 351099136 13 3319 18735 28 _ _ (983819 / 50000) (1967641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351099136 :
    ThetaLowerSegment 351099136 351164672 (35107388965817 / 100000) (35114057352001 / 100000) := by
  exact
    packedTile32768 351099136 351164672 13 3389 18737 28 _ _ (245957 / 12500) (1967659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351164672 :
    ThetaLowerSegment 351164672 351230208 (35114057352001 / 100000) (35120637257201 / 100000) := by
  exact
    packedTile32768 351164672 351230208 13 3344 18739 28 _ _ (78707 / 4000) (983839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351230208 :
    ThetaLowerSegment 351230208 351295744 (35120637257201 / 100000) (35127248709041 / 100000) := by
  exact
    packedTile32768 351230208 351295744 13 3360 18741 28 _ _ (983847 / 50000) (1967697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351295744 :
    ThetaLowerSegment 351295744 351361280 (35127248709041 / 100000) (7026735444829 / 20000) := by
  exact
    packedTile32768 351295744 351361280 13 3267 18742 28 _ _ (61491 / 3125) (393543 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351361280 :
    ThetaLowerSegment 351361280 351426816 (7026735444829 / 20000) (35140182542831 / 100000) := by
  exact
    packedTile32768 351361280 351426816 13 3306 18744 28 _ _ (1967731 / 100000) (983867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351426816 :
    ThetaLowerSegment 351426816 351492352 (35140182542831 / 100000) (35146737118081 / 100000) := by
  exact
    packedTile32768 351426816 351492352 13 3331 18746 28 _ _ (7871 / 400) (1967753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351492352 :
    ThetaLowerSegment 351492352 351557888 (35146737118081 / 100000) (35153317334273 / 100000) := by
  exact
    packedTile32768 351492352 351557888 13 3344 18748 28 _ _ (245971 / 12500) (1967771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351557888 :
    ThetaLowerSegment 351557888 351623424 (35153317334273 / 100000) (1098743664277 / 3125) := by
  exact
    packedTile32768 351557888 351623424 13 3293 18749 28 _ _ (1967787 / 100000) (196779 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351623424 :
    ThetaLowerSegment 351623424 351688960 (1098743664277 / 3125) (3516641105283 / 10000) := by
  exact
    packedTile32768 351623424 351688960 13 3361 18751 28 _ _ (983903 / 50000) (1967809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351688960 :
    ThetaLowerSegment 351688960 351754496 (3516641105283 / 10000) (17586464242959 / 50000) := by
  exact
    packedTile32768 351688960 351754496 13 3312 18753 28 _ _ (122989 / 6250) (1967827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351754496 :
    ThetaLowerSegment 351754496 351820032 (17586464242959 / 50000) (35179451885463 / 100000) := by
  exact
    packedTile32768 351754496 351820032 13 3315 18755 28 _ _ (1967843 / 100000) (983923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351820032 :
    ThetaLowerSegment 351820032 351885568 (35179451885463 / 100000) (35185973380131 / 100000) := by
  exact
    packedTile32768 351820032 351885568 13 3314 18756 28 _ _ (983931 / 50000) (393573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351885568 :
    ThetaLowerSegment 351885568 351951104 (35185973380131 / 100000) (35192469352011 / 100000) := by
  exact
    packedTile32768 351885568 351951104 13 3301 18758 28 _ _ (49197 / 2500) (1967883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell351951104 :
    ThetaLowerSegment 351951104 352016640 (35192469352011 / 100000) (8799744298501 / 25000) := by
  exact
    packedTile32768 351951104 352016640 13 3307 18760 28 _ _ (1967899 / 100000) (983951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352016640 :
    ThetaLowerSegment 352016640 352082176 (8799744298501 / 25000) (4400691786681 / 12500) := by
  exact
    packedTile32768 352016640 352082176 13 3332 18762 28 _ _ (1967917 / 100000) (24599 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352082176 :
    ThetaLowerSegment 352082176 352147712 (4400691786681 / 12500) (4401506266193 / 12500) := by
  exact
    packedTile32768 352082176 352147712 13 3311 18763 28 _ _ (61498 / 3125) (1967939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352147712 :
    ThetaLowerSegment 352147712 352213248 (4401506266193 / 12500) (35218652618569 / 100000) := by
  exact
    packedTile32768 352147712 352213248 13 3355 18765 28 _ _ (393591 / 20000) (983979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352213248 :
    ThetaLowerSegment 352213248 352278784 (35218652618569 / 100000) (35225186288929 / 100000) := by
  exact
    packedTile32768 352213248 352278784 13 3320 18767 28 _ _ (1967973 / 100000) (245997 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352278784 :
    ThetaLowerSegment 352278784 352344320 (35225186288929 / 100000) (35231731830321 / 100000) := by
  exact
    packedTile32768 352278784 352344320 13 3326 18769 28 _ _ (245999 / 12500) (393599 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352344320 :
    ThetaLowerSegment 352344320 352409856 (35231731830321 / 100000) (35238283335611 / 100000) := by
  exact
    packedTile32768 352344320 352409856 13 3329 18770 28 _ _ (196801 / 10000) (1968013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352409856 :
    ThetaLowerSegment 352409856 352475392 (35238283335611 / 100000) (17622450908569 / 50000) := by
  exact
    packedTile32768 352409856 352475392 13 3363 18772 28 _ _ (1968029 / 100000) (61501 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352475392 :
    ThetaLowerSegment 352475392 352540928 (17622450908569 / 50000) (17625782813833 / 50000) := by
  exact
    packedTile32768 352475392 352540928 13 3386 18774 28 _ _ (123003 / 6250) (1968051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352540928 :
    ThetaLowerSegment 352540928 352606464 (17625782813833 / 50000) (3525824524367 / 10000) := by
  exact
    packedTile32768 352540928 352606464 13 3394 18776 28 _ _ (984033 / 50000) (1968069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352606464 :
    ThetaLowerSegment 352606464 352672000 (3525824524367 / 10000) (881619580551 / 2500) := by
  exact
    packedTile32768 352606464 352672000 13 3322 18777 28 _ _ (393617 / 20000) (246011 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352672000 :
    ThetaLowerSegment 352672000 352737536 (881619580551 / 2500) (7054245751873 / 20000) := by
  exact
    packedTile32768 352672000 352737536 13 3275 18779 28 _ _ (1968103 / 100000) (984053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352737536 :
    ThetaLowerSegment 352737536 352803072 (7054245751873 / 20000) (7055558489247 / 20000) := by
  exact
    packedTile32768 352737536 352803072 13 3335 18781 28 _ _ (984061 / 50000) (3149 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352803072 :
    ThetaLowerSegment 352803072 352868608 (7055558489247 / 20000) (17642189907081 / 50000) := by
  exact
    packedTile32768 352803072 352868608 13 3347 18783 28 _ _ (1968141 / 100000) (123009 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352868608 :
    ThetaLowerSegment 352868608 352934144 (17642189907081 / 50000) (8822747223021 / 25000) := by
  exact
    packedTile32768 352868608 352934144 13 3358 18784 28 _ _ (1968159 / 100000) (984081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352934144 :
    ThetaLowerSegment 352934144 352999680 (8822747223021 / 25000) (8824372938049 / 25000) := by
  exact
    packedTile32768 352934144 352999680 13 3304 18786 28 _ _ (984089 / 50000) (1968181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell352999680 :
    ThetaLowerSegment 352999680 353065216 (8824372938049 / 25000) (8826004572533 / 25000) := by
  exact
    packedTile32768 352999680 353065216 13 3316 18788 28 _ _ (492049 / 25000) (1968199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353065216 :
    ThetaLowerSegment 353065216 353130752 (8826004572533 / 25000) (35310594096447 / 100000) := by
  exact
    packedTile32768 353065216 353130752 13 3341 18790 28 _ _ (393643 / 20000) (984109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353130752 :
    ThetaLowerSegment 353130752 353196288 (35310594096447 / 100000) (8829304300123 / 25000) := by
  exact
    packedTile32768 353130752 353196288 13 3365 18791 28 _ _ (1968233 / 100000) (492059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353196288 :
    ThetaLowerSegment 353196288 353261824 (8829304300123 / 25000) (4415460363539 / 12500) := by
  exact
    packedTile32768 353196288 353261824 13 3285 18793 28 _ _ (492063 / 25000) (393651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353261824 :
    ThetaLowerSegment 353261824 353327360 (4415460363539 / 12500) (17665142244623 / 50000) := by
  exact
    packedTile32768 353261824 353327360 13 3354 18795 28 _ _ (1968271 / 100000) (984137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353327360 :
    ThetaLowerSegment 353327360 353392896 (17665142244623 / 50000) (7067348489091 / 20000) := by
  exact
    packedTile32768 353327360 353392896 13 3281 18797 28 _ _ (1968289 / 100000) (492073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353392896 :
    ThetaLowerSegment 353392896 353458432 (7067348489091 / 20000) (35343239830163 / 100000) := by
  exact
    packedTile32768 353392896 353458432 13 3301 18798 28 _ _ (492077 / 25000) (1968311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353458432 :
    ThetaLowerSegment 353458432 353523968 (35343239830163 / 100000) (35349814039003 / 100000) := by
  exact
    packedTile32768 353458432 353523968 13 3340 18800 28 _ _ (984163 / 50000) (1968329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353523968 :
    ThetaLowerSegment 353523968 353589504 (35349814039003 / 100000) (4419542879921 / 12500) := by
  exact
    packedTile32768 353523968 353589504 13 3317 18802 28 _ _ (393669 / 20000) (492087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353589504 :
    ThetaLowerSegment 353589504 353655040 (4419542879921 / 12500) (3536282682709 / 10000) := by
  exact
    packedTile32768 353589504 353655040 13 3294 18803 28 _ _ (1968363 / 100000) (984183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353655040 :
    ThetaLowerSegment 353655040 353720576 (3536282682709 / 10000) (17684718326923 / 50000) := by
  exact
    packedTile32768 353655040 353720576 13 3358 18805 28 _ _ (984191 / 50000) (393677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353720576 :
    ThetaLowerSegment 353720576 353786112 (17684718326923 / 50000) (17688034096723 / 50000) := by
  exact
    packedTile32768 353720576 353786112 13 3369 18807 28 _ _ (4921 / 250) (1968403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353786112 :
    ThetaLowerSegment 353786112 353851648 (17688034096723 / 50000) (3538267420761 / 10000) := by
  exact
    packedTile32768 353786112 353851648 13 3356 18809 28 _ _ (1968419 / 100000) (984211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353851648 :
    ThetaLowerSegment 353851648 353917184 (3538267420761 / 10000) (35389195639391 / 100000) := by
  exact
    packedTile32768 353851648 353917184 13 3313 18810 28 _ _ (1968437 / 100000) (49211 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353917184 :
    ThetaLowerSegment 353917184 353982720 (35389195639391 / 100000) (35395795872359 / 100000) := by
  exact
    packedTile32768 353917184 353982720 13 3353 18812 28 _ _ (246057 / 12500) (1968459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell353982720 :
    ThetaLowerSegment 353982720 354048256 (35395795872359 / 100000) (7080457973617 / 20000) := by
  exact
    packedTile32768 353982720 354048256 13 3299 18814 28 _ _ (984237 / 50000) (1968477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354048256 :
    ThetaLowerSegment 354048256 354113792 (7080457973617 / 20000) (35408915815523 / 100000) := by
  exact
    packedTile32768 354048256 354113792 13 3366 18816 28 _ _ (1968493 / 100000) (123031 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354113792 :
    ThetaLowerSegment 354113792 354179328 (35408915815523 / 100000) (1416618995767 / 4000) := by
  exact
    packedTile32768 354113792 354179328 13 3332 18817 28 _ _ (1968511 / 100000) (984257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354179328 :
    ThetaLowerSegment 354179328 354244864 (1416618995767 / 4000) (7084417437289 / 20000) := by
  exact
    packedTile32768 354179328 354244864 13 3359 18819 28 _ _ (196853 / 10000) (1968533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354244864 :
    ThetaLowerSegment 354244864 354310400 (7084417437289 / 20000) (35428668042409 / 100000) := by
  exact
    packedTile32768 354244864 354310400 13 3343 18821 28 _ _ (492137 / 25000) (1968551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354310400 :
    ThetaLowerSegment 354310400 354375936 (35428668042409 / 100000) (17717561486801 / 50000) := by
  exact
    packedTile32768 354310400 354375936 13 3279 18823 28 _ _ (1968567 / 100000) (196857 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354375936 :
    ThetaLowerSegment 354375936 354441472 (17717561486801 / 50000) (35441766947977 / 100000) := by
  exact
    packedTile32768 354375936 354441472 13 3375 18824 28 _ _ (393717 / 20000) (492147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354441472 :
    ThetaLowerSegment 354441472 354507008 (35441766947977 / 100000) (35448292870237 / 100000) := by
  exact
    packedTile32768 354441472 354507008 13 3315 18826 28 _ _ (492151 / 25000) (1968607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354507008 :
    ThetaLowerSegment 354507008 354572544 (35448292870237 / 100000) (35454891691181 / 100000) := by
  exact
    packedTile32768 354507008 354572544 13 3352 18828 28 _ _ (984311 / 50000) (15749 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354572544 :
    ThetaLowerSegment 354572544 354638080 (35454891691181 / 100000) (141845623697 / 400) := by
  exact
    packedTile32768 354572544 354638080 13 3309 18830 28 _ _ (1968641 / 100000) (492161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354638080 :
    ThetaLowerSegment 354638080 354703616 (141845623697 / 400) (35467955652743 / 100000) := by
  exact
    packedTile32768 354638080 354703616 13 3327 18831 28 _ _ (1968659 / 100000) (984331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354703616 :
    ThetaLowerSegment 354703616 354769152 (35467955652743 / 100000) (35474462133533 / 100000) := by
  exact
    packedTile32768 354703616 354769152 13 3305 18833 28 _ _ (984339 / 50000) (1968681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354769152 :
    ThetaLowerSegment 354769152 354834688 (35474462133533 / 100000) (7096186647457 / 20000) := by
  exact
    packedTile32768 354769152 354834688 13 3287 18835 28 _ _ (246087 / 12500) (1968699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354834688 :
    ThetaLowerSegment 354834688 354900224 (7096186647457 / 20000) (3548749890181 / 10000) := by
  exact
    packedTile32768 354834688 354900224 13 3335 18837 28 _ _ (393743 / 20000) (984359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354900224 :
    ThetaLowerSegment 354900224 354965760 (3548749890181 / 10000) (35494088251161 / 100000) := by
  exact
    packedTile32768 354900224 354965760 13 3347 18838 28 _ _ (1968733 / 100000) (61523 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell354965760 :
    ThetaLowerSegment 354965760 355031296 (35494088251161 / 100000) (7100143407829 / 20000) := by
  exact
    packedTile32768 354965760 355031296 13 3367 18840 28 _ _ (123047 / 6250) (393751 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355031296 :
    ThetaLowerSegment 355031296 355096832 (7100143407829 / 20000) (7101453821141 / 20000) := by
  exact
    packedTile32768 355031296 355096832 13 3328 18842 28 _ _ (196877 / 10000) (1968773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355096832 :
    ThetaLowerSegment 355096832 355162368 (7101453821141 / 20000) (35513868486433 / 100000) := by
  exact
    packedTile32768 355096832 355162368 13 3352 18844 28 _ _ (1968789 / 100000) (246099 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355162368 :
    ThetaLowerSegment 355162368 355227904 (35513868486433 / 100000) (8880087941971 / 25000) := by
  exact
    packedTile32768 355162368 355227904 13 3293 18845 28 _ _ (1968807 / 100000) (196881 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355227904 :
    ThetaLowerSegment 355227904 355293440 (8880087941971 / 25000) (1776349926223 / 5000) := by
  exact
    packedTile32768 355227904 355293440 13 3376 18847 28 _ _ (984413 / 50000) (1968829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355293440 :
    ThetaLowerSegment 355293440 355358976 (1776349926223 / 5000) (1110422909928 / 3125) := by
  exact
    packedTile32768 355293440 355358976 13 3319 18849 28 _ _ (492211 / 25000) (1968847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355358976 :
    ThetaLowerSegment 355358976 355424512 (1110422909928 / 3125) (222125337429 / 625) := by
  exact
    packedTile32768 355358976 355424512 13 3312 18850 28 _ _ (984431 / 50000) (393773 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355424512 :
    ThetaLowerSegment 355424512 355490048 (222125337429 / 625) (17773301243423 / 50000) := by
  exact
    packedTile32768 355424512 355490048 13 3326 18852 28 _ _ (1968881 / 100000) (492221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355490048 :
    ThetaLowerSegment 355490048 355555584 (17773301243423 / 50000) (4444136005019 / 12500) := by
  exact
    packedTile32768 355490048 355555584 13 3294 18854 28 _ _ (1968899 / 100000) (984451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355555584 :
    ThetaLowerSegment 355555584 355621120 (4444136005019 / 12500) (2222483936437 / 6250) := by
  exact
    packedTile32768 355555584 355621120 13 3380 18856 28 _ _ (984459 / 50000) (1968921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355621120 :
    ThetaLowerSegment 355621120 355686656 (2222483936437 / 6250) (4445784735197 / 12500) := by
  exact
    packedTile32768 355621120 355686656 13 3319 18857 28 _ _ (246117 / 12500) (1968939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355686656 :
    ThetaLowerSegment 355686656 355752192 (4445784735197 / 12500) (35572730147111 / 100000) := by
  exact
    packedTile32768 355686656 355752192 13 3277 18859 28 _ _ (393791 / 20000) (984479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355752192 :
    ThetaLowerSegment 355752192 355817728 (35572730147111 / 100000) (35579298641039 / 100000) := by
  exact
    packedTile32768 355752192 355817728 13 3336 18861 28 _ _ (1968973 / 100000) (123061 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355817728 :
    ThetaLowerSegment 355817728 355883264 (35579298641039 / 100000) (17792966085859 / 50000) := by
  exact
    packedTile32768 355817728 355883264 13 3369 18863 28 _ _ (1968991 / 100000) (984497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355883264 :
    ThetaLowerSegment 355883264 355948800 (17792966085859 / 50000) (2224526007603 / 6250) := by
  exact
    packedTile32768 355883264 355948800 13 3293 18864 28 _ _ (196901 / 10000) (1969013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell355948800 :
    ThetaLowerSegment 355948800 356014336 (2224526007603 / 6250) (8899745707507 / 25000) := by
  exact
    packedTile32768 355948800 356014336 13 3335 18866 28 _ _ (492257 / 25000) (1969031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356014336 :
    ThetaLowerSegment 356014336 356079872 (8899745707507 / 25000) (35605490530363 / 100000) := by
  exact
    packedTile32768 356014336 356079872 13 3305 18868 28 _ _ (1969047 / 100000) (39381 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356079872 :
    ThetaLowerSegment 356079872 356145408 (35605490530363 / 100000) (8903050768237 / 25000) := by
  exact
    packedTile32768 356079872 356145408 13 3409 18870 28 _ _ (393813 / 20000) (492267 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356145408 :
    ThetaLowerSegment 356145408 356210944 (8903050768237 / 25000) (890468707621 / 2500) := by
  exact
    packedTile32768 356145408 356210944 13 3324 18871 28 _ _ (1969083 / 100000) (984543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356210944 :
    ThetaLowerSegment 356210944 356276480 (890468707621 / 2500) (4453158746333 / 12500) := by
  exact
    packedTile32768 356210944 356276480 13 3312 18873 28 _ _ (984551 / 50000) (393821 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356276480 :
    ThetaLowerSegment 356276480 356342016 (4453158746333 / 12500) (4453973469733 / 12500) := by
  exact
    packedTile32768 356276480 356342016 13 3310 18875 28 _ _ (12307 / 625) (1969123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356342016 :
    ThetaLowerSegment 356342016 356407552 (4453973469733 / 12500) (8909595108809 / 25000) := by
  exact
    packedTile32768 356342016 356407552 13 3348 18877 28 _ _ (1969139 / 100000) (984571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356407552 :
    ThetaLowerSegment 356407552 356473088 (8909595108809 / 25000) (17822457049081 / 50000) := by
  exact
    packedTile32768 356407552 356473088 13 3318 18878 28 _ _ (1969157 / 100000) (49229 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356473088 :
    ThetaLowerSegment 356473088 356538624 (17822457049081 / 50000) (35651493111837 / 100000) := by
  exact
    packedTile32768 356473088 356538624 13 3341 18880 28 _ _ (78767 / 4000) (984589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356538624 :
    ThetaLowerSegment 356538624 356604160 (35651493111837 / 100000) (35658032805111 / 100000) := by
  exact
    packedTile32768 356538624 356604160 13 3321 18882 28 _ _ (984597 / 50000) (1969197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356604160 :
    ThetaLowerSegment 356604160 356669696 (35658032805111 / 100000) (7132918843899 / 20000) := by
  exact
    packedTile32768 356604160 356669696 13 3332 18883 28 _ _ (492303 / 25000) (393843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356669696 :
    ThetaLowerSegment 356669696 356735232 (7132918843899 / 20000) (17835574894747 / 50000) := by
  exact
    packedTile32768 356669696 356735232 13 3329 18885 28 _ _ (1969231 / 100000) (984617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356735232 :
    ThetaLowerSegment 356735232 356800768 (17835574894747 / 50000) (1783885763283 / 5000) := by
  exact
    packedTile32768 356735232 356800768 13 3334 18887 28 _ _ (1969249 / 100000) (492313 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356800768 :
    ThetaLowerSegment 356800768 356866304 (1783885763283 / 5000) (35684259139901 / 100000) := by
  exact
    packedTile32768 356800768 356866304 13 3323 18889 28 _ _ (1969267 / 100000) (196927 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356866304 :
    ThetaLowerSegment 356866304 356931840 (35684259139901 / 100000) (35690730213697 / 100000) := by
  exact
    packedTile32768 356866304 356931840 13 3286 18890 28 _ _ (984643 / 50000) (1969289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356931840 :
    ThetaLowerSegment 356931840 356997376 (35690730213697 / 100000) (35697244671329 / 100000) := by
  exact
    packedTile32768 356931840 356997376 13 3308 18892 28 _ _ (246163 / 12500) (1969307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell356997376 :
    ThetaLowerSegment 356997376 357062912 (35697244671329 / 100000) (35703733587319 / 100000) := by
  exact
    packedTile32768 356997376 357062912 13 3295 18894 28 _ _ (984661 / 50000) (78773 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357062912 :
    ThetaLowerSegment 357062912 357128448 (35703733587319 / 100000) (8927592074287 / 25000) := by
  exact
    packedTile32768 357062912 357128448 13 3369 18896 28 _ _ (1969341 / 100000) (61542 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357128448 :
    ThetaLowerSegment 357128448 357193984 (8927592074287 / 25000) (35716900660951 / 100000) := by
  exact
    packedTile32768 357128448 357193984 13 3317 18897 28 _ _ (1969359 / 100000) (984681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357193984 :
    ThetaLowerSegment 357193984 357259520 (35716900660951 / 100000) (8930881903639 / 25000) := by
  exact
    packedTile32768 357193984 357259520 13 3365 18899 28 _ _ (1969377 / 100000) (98469 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357259520 :
    ThetaLowerSegment 357259520 357325056 (8930881903639 / 25000) (8932486961379 / 25000) := by
  exact
    packedTile32768 357259520 357325056 13 3260 18901 28 _ _ (492349 / 25000) (1969399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357325056 :
    ThetaLowerSegment 357325056 357390592 (8932486961379 / 25000) (17868252012361 / 50000) := by
  exact
    packedTile32768 357325056 357390592 13 3329 18903 28 _ _ (984707 / 50000) (1969417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357390592 :
    ThetaLowerSegment 357390592 357456128 (17868252012361 / 50000) (17871532101357 / 50000) := by
  exact
    packedTile32768 357390592 357456128 13 3331 18904 28 _ _ (246179 / 12500) (393887 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357456128 :
    ThetaLowerSegment 357456128 357521664 (17871532101357 / 50000) (35749600810583 / 100000) := by
  exact
    packedTile32768 357456128 357521664 13 3319 18906 28 _ _ (1969451 / 100000) (984727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357521664 :
    ThetaLowerSegment 357521664 357587200 (35749600810583 / 100000) (17878100250601 / 50000) := by
  exact
    packedTile32768 357521664 357587200 13 3351 18908 28 _ _ (1969469 / 100000) (61546 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357587200 :
    ThetaLowerSegment 357587200 357652736 (17878100250601 / 50000) (35762784496243 / 100000) := by
  exact
    packedTile32768 357587200 357652736 13 3343 18909 28 _ _ (1969487 / 100000) (196949 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357652736 :
    ThetaLowerSegment 357652736 357718272 (35762784496243 / 100000) (7153867408541 / 20000) := by
  exact
    packedTile32768 357652736 357718272 13 3327 18911 28 _ _ (984753 / 50000) (1969509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357718272 :
    ThetaLowerSegment 357718272 357783808 (7153867408541 / 20000) (7155165324857 / 20000) := by
  exact
    packedTile32768 357718272 357783808 13 3295 18913 28 _ _ (492381 / 25000) (1969527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357783808 :
    ThetaLowerSegment 357783808 357849344 (7155165324857 / 20000) (35782347777847 / 100000) := by
  exact
    packedTile32768 357783808 357849344 13 3311 18915 28 _ _ (984771 / 50000) (393909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357849344 :
    ThetaLowerSegment 357849344 357914880 (35782347777847 / 100000) (8947232020287 / 25000) := by
  exact
    packedTile32768 357849344 357914880 13 3341 18916 28 _ _ (1969561 / 100000) (492391 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357914880 :
    ThetaLowerSegment 357914880 357980416 (8947232020287 / 25000) (17897735511293 / 50000) := by
  exact
    packedTile32768 357914880 357980416 13 3322 18918 28 _ _ (1969579 / 100000) (984791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell357980416 :
    ThetaLowerSegment 357980416 358045952 (17897735511293 / 50000) (358020928077 / 1000) := by
  exact
    packedTile32768 357980416 358045952 13 3362 18920 28 _ _ (1969597 / 100000) (2462 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358045952 :
    ThetaLowerSegment 358045952 358111488 (358020928077 / 1000) (8952163892053 / 25000) := by
  exact
    packedTile32768 358045952 358111488 13 3332 18922 28 _ _ (123101 / 6250) (1969619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358111488 :
    ThetaLowerSegment 358111488 358177024 (8952163892053 / 25000) (17907608209533 / 50000) := by
  exact
    packedTile32768 358111488 358177024 13 3331 18923 28 _ _ (984817 / 50000) (1969637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358177024 :
    ThetaLowerSegment 358177024 358242560 (17907608209533 / 50000) (17910834499509 / 50000) := by
  exact
    packedTile32768 358177024 358242560 13 3276 18925 28 _ _ (492413 / 25000) (393931 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358242560 :
    ThetaLowerSegment 358242560 358308096 (17910834499509 / 50000) (17914127789421 / 50000) := by
  exact
    packedTile32768 358242560 358308096 13 3344 18927 28 _ _ (1969671 / 100000) (984837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358308096 :
    ThetaLowerSegment 358308096 358373632 (17914127789421 / 50000) (8958691842669 / 25000) := by
  exact
    packedTile32768 358308096 358373632 13 3306 18929 28 _ _ (1969689 / 100000) (492423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358373632 :
    ThetaLowerSegment 358373632 358439168 (8958691842669 / 25000) (17920631732181 / 50000) := by
  exact
    packedTile32768 358373632 358439168 13 3298 18930 28 _ _ (1969707 / 100000) (196971 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358439168 :
    ThetaLowerSegment 358439168 358504704 (17920631732181 / 50000) (35847797042187 / 100000) := by
  exact
    packedTile32768 358439168 358504704 13 3317 18932 28 _ _ (78789 / 4000) (61554 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358504704 :
    ThetaLowerSegment 358504704 358570240 (35847797042187 / 100000) (35854334622523 / 100000) := by
  exact
    packedTile32768 358504704 358570240 13 3319 18934 28 _ _ (123109 / 6250) (1969747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358570240 :
    ThetaLowerSegment 358570240 358635776 (35854334622523 / 100000) (35860933325223 / 100000) := by
  exact
    packedTile32768 358570240 358635776 13 3350 18935 28 _ _ (984881 / 50000) (393953 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358635776 :
    ThetaLowerSegment 358635776 358701312 (35860933325223 / 100000) (35867549816243 / 100000) := by
  exact
    packedTile32768 358635776 358701312 13 3359 18937 28 _ _ (98489 / 5000) (1969783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358701312 :
    ThetaLowerSegment 358701312 358766848 (35867549816243 / 100000) (35874030454953 / 100000) := by
  exact
    packedTile32768 358701312 358766848 13 3290 18939 28 _ _ (1969799 / 100000) (984901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358766848 :
    ThetaLowerSegment 358766848 358832384 (35874030454953 / 100000) (8970140099577 / 25000) := by
  exact
    packedTile32768 358766848 358832384 13 3315 18941 28 _ _ (1969817 / 100000) (98491 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358832384 :
    ThetaLowerSegment 358832384 358897920 (8970140099577 / 25000) (35887204651763 / 100000) := by
  exact
    packedTile32768 358832384 358897920 13 3373 18942 28 _ _ (393967 / 20000) (984919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358897920 :
    ThetaLowerSegment 358897920 358963456 (35887204651763 / 100000) (35893921850493 / 100000) := by
  exact
    packedTile32768 358897920 358963456 13 3410 18944 28 _ _ (1969853 / 100000) (61558 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell358963456 :
    ThetaLowerSegment 358963456 359028992 (35893921850493 / 100000) (35900499253101 / 100000) := by
  exact
    packedTile32768 358963456 359028992 13 3339 18946 28 _ _ (123117 / 6250) (15759 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359028992 :
    ThetaLowerSegment 359028992 359094528 (35900499253101 / 100000) (35907035348121 / 100000) := by
  exact
    packedTile32768 359028992 359094528 13 3318 18948 28 _ _ (196989 / 10000) (1969893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359094528 :
    ThetaLowerSegment 359094528 359160064 (35907035348121 / 100000) (35913516345441 / 100000) := by
  exact
    packedTile32768 359094528 359160064 13 3290 18949 28 _ _ (492477 / 25000) (1969911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359160064 :
    ThetaLowerSegment 359160064 359225600 (35913516345441 / 100000) (35920184544951 / 100000) := by
  exact
    packedTile32768 359160064 359225600 13 3385 18951 28 _ _ (984963 / 50000) (1969929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359225600 :
    ThetaLowerSegment 359225600 359291136 (35920184544951 / 100000) (4490829021867 / 12500) := by
  exact
    packedTile32768 359225600 359291136 13 3273 18953 28 _ _ (393989 / 20000) (492487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359291136 :
    ThetaLowerSegment 359291136 359356672 (4490829021867 / 12500) (17966588196011 / 50000) := by
  exact
    packedTile32768 359291136 359356672 13 3322 18954 28 _ _ (1969963 / 100000) (984983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359356672 :
    ThetaLowerSegment 359356672 359422208 (17966588196011 / 50000) (35939730518809 / 100000) := by
  exact
    packedTile32768 359356672 359422208 13 3327 18956 28 _ _ (1969981 / 100000) (61562 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359422208 :
    ThetaLowerSegment 359422208 359487744 (35939730518809 / 100000) (4493282140687 / 12500) := by
  exact
    packedTile32768 359422208 359487744 13 3313 18958 28 _ _ (1969999 / 100000) (985001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359487744 :
    ThetaLowerSegment 359487744 359553280 (4493282140687 / 12500) (17976409627727 / 50000) := by
  exact
    packedTile32768 359487744 359553280 13 3331 18960 28 _ _ (985009 / 50000) (1970021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359553280 :
    ThetaLowerSegment 359553280 359618816 (17976409627727 / 50000) (3595936174501 / 10000) := by
  exact
    packedTile32768 359553280 359618816 13 3321 18961 28 _ _ (492509 / 25000) (1970039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359618816 :
    ThetaLowerSegment 359618816 359684352 (3595936174501 / 10000) (4495716366199 / 12500) := by
  exact
    packedTile32768 359618816 359684352 13 3233 18963 28 _ _ (985027 / 50000) (1970057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359684352 :
    ThetaLowerSegment 359684352 359749888 (4495716366199 / 12500) (2248268573723 / 6250) := by
  exact
    packedTile32768 359684352 359749888 13 3333 18965 28 _ _ (246259 / 12500) (78803 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359749888 :
    ThetaLowerSegment 359749888 359815424 (2248268573723 / 6250) (8994718334997 / 25000) := by
  exact
    packedTile32768 359749888 359815424 13 3338 18967 28 _ _ (197009 / 10000) (1970093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359815424 :
    ThetaLowerSegment 359815424 359880960 (8994718334997 / 25000) (35985534278517 / 100000) := by
  exact
    packedTile32768 359815424 359880960 13 3381 18968 28 _ _ (1970109 / 100000) (61566 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359880960 :
    ThetaLowerSegment 359880960 359946496 (35985534278517 / 100000) (35991988414569 / 100000) := by
  exact
    packedTile32768 359880960 359946496 13 3276 18970 28 _ _ (1970127 / 100000) (197013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell359946496 :
    ThetaLowerSegment 359946496 360012032 (35991988414569 / 100000) (17999269573347 / 50000) := by
  exact
    packedTile32768 359946496 360012032 13 3325 18972 28 _ _ (394029 / 20000) (492537 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360012032 :
    ThetaLowerSegment 360012032 360077568 (17999269573347 / 50000) (36004983549867 / 100000) := by
  exact
    packedTile32768 360012032 360077568 13 3271 18973 28 _ _ (1970163 / 100000) (985083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360077568 :
    ThetaLowerSegment 360077568 360143104 (36004983549867 / 100000) (7202271023691 / 20000) := by
  exact
    packedTile32768 360077568 360143104 13 3234 18975 28 _ _ (985091 / 50000) (394037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360143104 :
    ThetaLowerSegment 360143104 360175872 (7202271023691 / 20000) (7202920401611 / 20000) := by
  exact
    packedTile32768 360143104 360175872 12 1648 18977 28 _ _ (9851 / 500) (1970203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360175872 :
    ThetaLowerSegment 360175872 360208640 (7202920401611 / 20000) (36017904078339 / 100000) := by
  exact
    packedTile32768 360175872 360208640 12 1676 18978 28 _ _ (1970209 / 100000) (492553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360208640 :
    ThetaLowerSegment 360208640 360241408 (36017904078339 / 100000) (36021182521091 / 100000) := by
  exact
    packedTile32768 360208640 360241408 12 1664 18979 28 _ _ (985109 / 50000) (1970221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360241408 :
    ThetaLowerSegment 360241408 360274176 (36021182521091 / 100000) (36024374288831 / 100000) := by
  exact
    packedTile32768 360241408 360274176 12 1620 18980 28 _ _ (1970227 / 100000) (197023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360274176 :
    ThetaLowerSegment 360274176 360306944 (36024374288831 / 100000) (36027631088939 / 100000) := by
  exact
    packedTile32768 360274176 360306944 12 1653 18980 28 _ _ (492559 / 25000) (1970239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360306944 :
    ThetaLowerSegment 360306944 360339712 (36027631088939 / 100000) (18015441981717 / 50000) := by
  exact
    packedTile32768 360306944 360339712 12 1651 18981 28 _ _ (394049 / 20000) (246281 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360339712 :
    ThetaLowerSegment 360339712 360372480 (18015441981717 / 50000) (3603410335847 / 10000) := by
  exact
    packedTile32768 360339712 360372480 12 1634 18982 28 _ _ (985127 / 50000) (1970257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360372480 :
    ThetaLowerSegment 360372480 360405248 (3603410335847 / 10000) (1801867714621 / 5000) := by
  exact
    packedTile32768 360372480 360405248 12 1650 18983 28 _ _ (1970263 / 100000) (985133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360405248 :
    ThetaLowerSegment 360405248 360438016 (1801867714621 / 5000) (9010149832601 / 25000) := by
  exact
    packedTile32768 360405248 360438016 12 1647 18984 28 _ _ (61571 / 3125) (78811 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360438016 :
    ThetaLowerSegment 360438016 360470784 (9010149832601 / 25000) (18021949776377 / 50000) := by
  exact
    packedTile32768 360438016 360470784 12 1675 18985 28 _ _ (985141 / 50000) (394057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360470784 :
    ThetaLowerSegment 360470784 360503552 (18021949776377 / 50000) (36047203730761 / 100000) := by
  exact
    packedTile32768 360470784 360503552 12 1677 18986 28 _ _ (1970291 / 100000) (985147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360503552 :
    ThetaLowerSegment 360503552 360536320 (36047203730761 / 100000) (36050446844561 / 100000) := by
  exact
    packedTile32768 360503552 360536320 12 1646 18986 28 _ _ (19703 / 1000) (1970303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360536320 :
    ThetaLowerSegment 360536320 360569088 (36050446844561 / 100000) (18026895229467 / 50000) := by
  exact
    packedTile32768 360536320 360569088 12 1697 18987 28 _ _ (1970309 / 100000) (246289 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360569088 :
    ThetaLowerSegment 360569088 360601856 (18026895229467 / 50000) (18028568029449 / 50000) := by
  exact
    packedTile32768 360569088 360601856 12 1698 18988 28 _ _ (985159 / 50000) (1970321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360601856 :
    ThetaLowerSegment 360601856 360634624 (18028568029449 / 50000) (1803018960857 / 5000) := by
  exact
    packedTile32768 360601856 360634624 12 1646 18989 28 _ _ (1970327 / 100000) (197033 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360634624 :
    ThetaLowerSegment 360634624 360667392 (1803018960857 / 5000) (9015913478893 / 25000) := by
  exact
    packedTile32768 360634624 360667392 12 1662 18990 28 _ _ (61573 / 3125) (1970339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360667392 :
    ThetaLowerSegment 360667392 360700160 (9015913478893 / 25000) (36066895133097 / 100000) := by
  exact
    packedTile32768 360667392 360700160 12 1645 18991 28 _ _ (394069 / 20000) (492587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360700160 :
    ThetaLowerSegment 360700160 360732928 (36066895133097 / 100000) (36070136365427 / 100000) := by
  exact
    packedTile32768 360700160 360732928 12 1645 18992 28 _ _ (985177 / 50000) (1970357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360732928 :
    ThetaLowerSegment 360732928 360765696 (36070136365427 / 100000) (18036714421 / 50) := by
  exact
    packedTile32768 360732928 360765696 12 1671 18992 28 _ _ (1970363 / 100000) (985183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360765696 :
    ThetaLowerSegment 360765696 360798464 (18036714421 / 50) (4509598787079 / 12500) := by
  exact
    packedTile32768 360765696 360798464 12 1706 18993 28 _ _ (492593 / 25000) (15763 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360798464 :
    ThetaLowerSegment 360798464 360831232 (4509598787079 / 12500) (9020004445587 / 25000) := by
  exact
    packedTile32768 360798464 360831232 12 1638 18994 28 _ _ (985191 / 50000) (394077 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360831232 :
    ThetaLowerSegment 360831232 360864000 (9020004445587 / 25000) (36083369417439 / 100000) := by
  exact
    packedTile32768 360831232 360864000 12 1701 18995 28 _ _ (1970391 / 100000) (985197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360864000 :
    ThetaLowerSegment 360864000 360896768 (36083369417439 / 100000) (36086701363839 / 100000) := by
  exact
    packedTile32768 360864000 360896768 12 1691 18996 28 _ _ (2463 / 125) (1970403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360896768 :
    ThetaLowerSegment 360896768 360929536 (36086701363839 / 100000) (36089956479507 / 100000) := by
  exact
    packedTile32768 360896768 360929536 12 1652 18997 28 _ _ (1970409 / 100000) (492603 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360929536 :
    ThetaLowerSegment 360929536 360962304 (36089956479507 / 100000) (7218630105417 / 20000) := by
  exact
    packedTile32768 360929536 360962304 12 1621 18998 28 _ _ (985209 / 50000) (1970421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360962304 :
    ThetaLowerSegment 360962304 360995072 (7218630105417 / 20000) (36096452962737 / 100000) := by
  exact
    packedTile32768 360962304 360995072 12 1676 18999 28 _ _ (1970427 / 100000) (197043 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell360995072 :
    ThetaLowerSegment 360995072 361027840 (36096452962737 / 100000) (36099806644809 / 100000) := by
  exact
    packedTile32768 360995072 361027840 12 1702 18999 28 _ _ (492609 / 25000) (1970439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361027840 :
    ThetaLowerSegment 361027840 361060608 (36099806644809 / 100000) (2256443211039 / 6250) := by
  exact
    packedTile32768 361027840 361060608 12 1667 19000 28 _ _ (394089 / 20000) (123153 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361060608 :
    ThetaLowerSegment 361060608 361093376 (2256443211039 / 6250) (3610636035981 / 10000) := by
  exact
    packedTile32768 361060608 361093376 12 1659 19001 28 _ _ (985227 / 50000) (1970457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361093376 :
    ThetaLowerSegment 361093376 361126144 (3610636035981 / 10000) (36109656944409 / 100000) := by
  exact
    packedTile32768 361093376 361126144 12 1673 19002 28 _ _ (1970463 / 100000) (985233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361126144 :
    ThetaLowerSegment 361126144 361158912 (36109656944409 / 100000) (36112837286217 / 100000) := by
  exact
    packedTile32768 361126144 361158912 12 1614 19003 28 _ _ (246309 / 12500) (78819 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361158912 :
    ThetaLowerSegment 361158912 361191680 (36112837286217 / 100000) (1444644961941 / 4000) := by
  exact
    packedTile32768 361158912 361191680 12 1668 19004 28 _ _ (1970481 / 100000) (492621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361191680 :
    ThetaLowerSegment 361191680 361224448 (1444644961941 / 4000) (7223880588777 / 20000) := by
  exact
    packedTile32768 361191680 361224448 12 1664 19005 28 _ _ (197049 / 10000) (1970493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361224448 :
    ThetaLowerSegment 361224448 361257216 (7223880588777 / 20000) (7224537553477 / 20000) := by
  exact
    packedTile32768 361224448 361257216 12 1667 19005 28 _ _ (3941 / 200) (1970503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361257216 :
    ThetaLowerSegment 361257216 361289984 (7224537553477 / 20000) (36125966694361 / 100000) := by
  exact
    packedTile32768 361257216 361289984 12 1664 19006 28 _ _ (1970509 / 100000) (123157 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361289984 :
    ThetaLowerSegment 361289984 361322752 (36125966694361 / 100000) (7225848733159 / 20000) := by
  exact
    packedTile32768 361289984 361322752 12 1663 19007 28 _ _ (985259 / 50000) (1970521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361322752 :
    ThetaLowerSegment 361322752 361339136 (7225848733159 / 20000) (7226167958533 / 20000) := by
  exact
    packedTile32768 361322752 361339136 11 810 19008 28 _ _ (1970527 / 100000) (197053 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell361339136 :
    ThetaLowerSegment 361339136 361341184 (7226167958533 / 20000) (36131060492137 / 100000) := by
  exact
    packedTile32768 361339136 361341184 8 112 19008 28 _ _ (1970531 / 100000) (985267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_329341184_361341184 :
    ThetaLowerSegment 329341184 361341184 (2058225478409 / 6250) (36131060492137 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell329341184 cell329406720)
                      (ThetaLowerSegment.join cell329472256 cell329537792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell329603328 cell329668864)
                      (ThetaLowerSegment.join cell329734400 cell329799936)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell329865472 cell329931008)
                      (ThetaLowerSegment.join cell329996544 cell330062080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell330127616 cell330193152)
                      (ThetaLowerSegment.join cell330258688 cell330324224))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell330356992 cell330389760)
                      (ThetaLowerSegment.join cell330422528 cell330488064))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell330520832 cell330553600)
                      (ThetaLowerSegment.join cell330619136 cell330651904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell330684672 cell330717440)
                      (ThetaLowerSegment.join cell330750208 cell330782976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell330815744 cell330848512)
                      (ThetaLowerSegment.join cell330881280 cell330914048)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell330946816 cell330979584)
                      (ThetaLowerSegment.join cell331012352 cell331045120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell331077888 cell331110656)
                      (ThetaLowerSegment.join cell331143424 cell331176192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell331208960 cell331241728)
                      (ThetaLowerSegment.join cell331274496 cell331307264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell331340032 cell331372800)
                      (ThetaLowerSegment.join cell331405568 cell331438336))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell331503872 cell331569408)
                      (ThetaLowerSegment.join cell331602176 cell331634944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell331700480 cell331766016)
                      (ThetaLowerSegment.join cell331831552 cell331897088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell331929856 cell331962624)
                      (ThetaLowerSegment.join cell331995392 cell332028160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell332060928 cell332093696)
                      (ThetaLowerSegment.join cell332126464 cell332159232))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell332192000 cell332224768)
                      (ThetaLowerSegment.join cell332257536 cell332290304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell332323072 cell332355840)
                      (ThetaLowerSegment.join cell332388608 cell332421376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell332454144 cell332486912)
                      (ThetaLowerSegment.join cell332519680 cell332552448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell332585216 cell332617984)
                      (ThetaLowerSegment.join cell332650752 cell332683520))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell332716288 cell332781824)
                      (ThetaLowerSegment.join cell332847360 cell332912896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell332978432 cell333043968)
                      (ThetaLowerSegment.join cell333109504 cell333175040)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell333240576 cell333306112)
                      (ThetaLowerSegment.join cell333371648 cell333437184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell333502720 cell333535488)
                      (ThetaLowerSegment.join cell333568256 cell333601024)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell333633792 cell333666560)
                      (ThetaLowerSegment.join cell333699328 cell333732096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell333764864 cell333797632)
                      (ThetaLowerSegment.join cell333830400 cell333895936)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell333928704 cell333994240)
                      (ThetaLowerSegment.join cell334059776 cell334125312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell334190848 cell334223616)
                      (ThetaLowerSegment.join cell334256384 cell334289152))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell334321920 cell334354688)
                      (ThetaLowerSegment.join cell334387456 cell334420224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell334452992 cell334485760)
                      (ThetaLowerSegment.join cell334518528 cell334551296)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell334584064 cell334616832)
                      (ThetaLowerSegment.join cell334682368 cell334715136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell334780672 cell334846208)
                      (ThetaLowerSegment.join cell334911744 cell334977280)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell335042816 cell335108352)
                      (ThetaLowerSegment.join cell335173888 cell335239424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell335304960 cell335370496)
                      (ThetaLowerSegment.join cell335436032 cell335501568)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell335567104 cell335632640)
                      (ThetaLowerSegment.join cell335698176 cell335763712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell335829248 cell335894784)
                      (ThetaLowerSegment.join cell335960320 cell335993088))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell336025856 cell336058624)
                      (ThetaLowerSegment.join cell336091392 cell336156928))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell336222464 cell336288000)
                      (ThetaLowerSegment.join cell336353536 cell336419072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell336451840 cell336517376)
                      (ThetaLowerSegment.join cell336550144 cell336582912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell336615680 cell336681216)
                      (ThetaLowerSegment.join cell336746752 cell336812288)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell336877824 cell336943360)
                      (ThetaLowerSegment.join cell336976128 cell337008896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell337041664 cell337074432)
                      (ThetaLowerSegment.join cell337107200 cell337139968)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell337172736 cell337238272)
                      (ThetaLowerSegment.join cell337303808 cell337369344))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell337402112 cell337434880)
                      (ThetaLowerSegment.join cell337500416 cell337533184))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell337565952 cell337598720)
                      (ThetaLowerSegment.join cell337664256 cell337697024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell337729792 cell337762560)
                      (ThetaLowerSegment.join cell337795328 cell337828096)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell337860864 cell337893632)
                      (ThetaLowerSegment.join cell337926400 cell337959168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell337991936 cell338024704)
                      (ThetaLowerSegment.join cell338057472 cell338090240))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell338123008 cell338155776)
                      (ThetaLowerSegment.join cell338188544 cell338221312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell338254080 cell338286848)
                      (ThetaLowerSegment.join cell338319616 cell338352384)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell338385152 cell338417920)
                      (ThetaLowerSegment.join cell338450688 cell338483456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell338516224 cell338548992)
                      (ThetaLowerSegment.join cell338581760 cell338614528))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell338647296 cell338680064)
                      (ThetaLowerSegment.join cell338712832 cell338745600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell338778368 cell338811136)
                      (ThetaLowerSegment.join cell338843904 cell338876672)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell338909440 cell338974976)
                      (ThetaLowerSegment.join cell339040512 cell339106048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell339138816 cell339204352)
                      (ThetaLowerSegment.join cell339269888 cell339302656)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell339335424 cell339368192)
                      (ThetaLowerSegment.join cell339400960 cell339433728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell339466496 cell339499264)
                      (ThetaLowerSegment.join cell339532032 cell339564800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell339597568 cell339630336)
                      (ThetaLowerSegment.join cell339663104 cell339695872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell339728640 cell339761408)
                      (ThetaLowerSegment.join cell339794176 cell339826944))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell339859712 cell339892480)
                      (ThetaLowerSegment.join cell339925248 cell339958016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell339990784 cell340023552)
                      (ThetaLowerSegment.join cell340056320 cell340089088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell340154624 cell340220160)
                      (ThetaLowerSegment.join cell340285696 cell340351232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell340416768 cell340482304)
                      (ThetaLowerSegment.join cell340547840 cell340613376))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell340678912 cell340744448)
                      (ThetaLowerSegment.join cell340809984 cell340875520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell340941056 cell341006592)
                      (ThetaLowerSegment.join cell341072128 cell341137664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell341203200 cell341268736)
                      (ThetaLowerSegment.join cell341334272 cell341399808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell341465344 cell341530880)
                      (ThetaLowerSegment.join cell341596416 cell341661952))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell341727488 cell341793024)
                      (ThetaLowerSegment.join cell341858560 cell341924096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell341989632 cell342055168)
                      (ThetaLowerSegment.join cell342120704 cell342186240)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell342251776 cell342317312)
                      (ThetaLowerSegment.join cell342382848 cell342448384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell342513920 cell342579456)
                      (ThetaLowerSegment.join cell342644992 cell342710528)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell342776064 cell342841600)
                      (ThetaLowerSegment.join cell342907136 cell342972672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell343038208 cell343103744)
                      (ThetaLowerSegment.join cell343169280 cell343234816)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell343300352 cell343365888)
                      (ThetaLowerSegment.join cell343431424 cell343496960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell343562496 cell343628032)
                      (ThetaLowerSegment.join cell343693568 cell343759104))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell343824640 cell343890176)
                      (ThetaLowerSegment.join cell343955712 cell344021248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell344086784 cell344152320)
                      (ThetaLowerSegment.join cell344217856 cell344283392)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell344348928 cell344414464)
                      (ThetaLowerSegment.join cell344480000 cell344545536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell344611072 cell344676608)
                      (ThetaLowerSegment.join cell344742144 cell344807680))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell344873216 cell344938752)
                      (ThetaLowerSegment.join cell345004288 cell345069824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell345135360 cell345200896)
                      (ThetaLowerSegment.join cell345266432 cell345331968)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell345397504 cell345463040)
                      (ThetaLowerSegment.join cell345528576 cell345594112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell345659648 cell345725184)
                      (ThetaLowerSegment.join cell345790720 cell345856256))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell345921792 cell345987328)
                      (ThetaLowerSegment.join cell346052864 cell346118400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell346183936 cell346249472)
                      (ThetaLowerSegment.join cell346315008 cell346380544)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell346446080 cell346511616)
                      (ThetaLowerSegment.join cell346577152 cell346642688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell346708224 cell346773760)
                      (ThetaLowerSegment.join cell346839296 cell346904832)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell346970368 cell347035904)
                      (ThetaLowerSegment.join cell347101440 cell347166976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell347232512 cell347298048)
                      (ThetaLowerSegment.join cell347363584 cell347429120)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell347494656 cell347560192)
                      (ThetaLowerSegment.join cell347625728 cell347691264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell347756800 cell347822336)
                      (ThetaLowerSegment.join cell347887872 cell347953408))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell348018944 cell348084480)
                      (ThetaLowerSegment.join cell348150016 cell348215552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell348281088 cell348346624)
                      (ThetaLowerSegment.join cell348412160 cell348477696)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell348543232 cell348608768)
                      (ThetaLowerSegment.join cell348674304 cell348707072))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell348772608 cell348838144)
                      (ThetaLowerSegment.join cell348870912 cell348903680)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell348936448 cell348969216)
                      (ThetaLowerSegment.join cell349001984 cell349034752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell349067520 cell349133056)
                      (ThetaLowerSegment.join cell349198592 cell349264128)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell349329664 cell349395200)
                      (ThetaLowerSegment.join cell349460736 cell349526272))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell349591808 cell349657344)
                      (ThetaLowerSegment.join cell349722880 cell349788416))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell349853952 cell349919488)
                      (ThetaLowerSegment.join cell349985024 cell350050560))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell350116096 cell350181632)
                      (ThetaLowerSegment.join cell350247168 cell350312704)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell350378240 cell350443776)
                      (ThetaLowerSegment.join cell350509312 cell350574848))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell350640384 cell350705920)
                      (ThetaLowerSegment.join cell350771456 cell350836992)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell350902528 cell350968064)
                      (ThetaLowerSegment.join cell351033600 cell351099136))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell351164672 cell351230208)
                      (ThetaLowerSegment.join cell351295744 cell351361280)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell351426816 cell351492352)
                      (ThetaLowerSegment.join cell351557888 cell351623424))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell351688960 cell351754496)
                      (ThetaLowerSegment.join cell351820032 cell351885568))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell351951104 cell352016640)
                      (ThetaLowerSegment.join cell352082176 cell352147712))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell352213248 cell352278784)
                      (ThetaLowerSegment.join cell352344320 cell352409856)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell352475392 cell352540928)
                      (ThetaLowerSegment.join cell352606464 cell352672000))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell352737536 cell352803072)
                      (ThetaLowerSegment.join cell352868608 cell352934144))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell352999680 cell353065216)
                      (ThetaLowerSegment.join cell353130752 cell353196288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell353261824 cell353327360)
                      (ThetaLowerSegment.join cell353392896 cell353458432)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell353523968 cell353589504)
                      (ThetaLowerSegment.join cell353655040 cell353720576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell353786112 cell353851648)
                      (ThetaLowerSegment.join cell353917184 cell353982720))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell354048256 cell354113792)
                      (ThetaLowerSegment.join cell354179328 cell354244864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell354310400 cell354375936)
                      (ThetaLowerSegment.join cell354441472 cell354507008)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell354572544 cell354638080)
                      (ThetaLowerSegment.join cell354703616 cell354769152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell354834688 cell354900224)
                      (ThetaLowerSegment.join cell354965760 cell355031296)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell355096832 cell355162368)
                      (ThetaLowerSegment.join cell355227904 cell355293440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell355358976 cell355424512)
                      (ThetaLowerSegment.join cell355490048 cell355555584)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell355621120 cell355686656)
                      (ThetaLowerSegment.join cell355752192 cell355817728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell355883264 cell355948800)
                      (ThetaLowerSegment.join cell356014336 cell356079872))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell356145408 cell356210944)
                      (ThetaLowerSegment.join cell356276480 cell356342016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell356407552 cell356473088)
                      (ThetaLowerSegment.join cell356538624 cell356604160)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell356669696 cell356735232)
                      (ThetaLowerSegment.join cell356800768 cell356866304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell356931840 cell356997376)
                      (ThetaLowerSegment.join cell357062912 cell357128448)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell357193984 cell357259520)
                  (ThetaLowerSegment.join cell357325056 cell357390592))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell357456128 cell357521664)
                  (ThetaLowerSegment.join cell357587200 cell357652736)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell357718272 cell357783808)
                  (ThetaLowerSegment.join cell357849344 cell357914880))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell357980416 cell358045952)
                  (ThetaLowerSegment.join cell358111488 cell358177024))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell358242560 cell358308096)
                  (ThetaLowerSegment.join cell358373632 cell358439168))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell358504704 cell358570240)
                  (ThetaLowerSegment.join cell358635776 cell358701312)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell358766848 cell358832384)
                  (ThetaLowerSegment.join cell358897920 cell358963456))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell359028992 cell359094528)
                  (ThetaLowerSegment.join cell359160064 cell359225600)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell359291136 cell359356672)
                  (ThetaLowerSegment.join cell359422208 cell359487744))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell359553280 cell359618816)
                  (ThetaLowerSegment.join cell359684352 cell359749888)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell359815424 cell359880960)
                  (ThetaLowerSegment.join cell359946496 cell360012032))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell360077568 cell360143104)
                  (ThetaLowerSegment.join cell360175872 cell360208640))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell360241408 cell360274176)
                  (ThetaLowerSegment.join cell360306944 cell360339712))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell360372480 cell360405248)
                  (ThetaLowerSegment.join cell360438016 cell360470784)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell360503552 cell360536320)
                  (ThetaLowerSegment.join cell360569088 cell360601856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell360634624 cell360667392)
                  (ThetaLowerSegment.join cell360700160 cell360732928))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell360765696 cell360798464)
                (ThetaLowerSegment.join cell360831232 cell360864000))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell360896768 cell360929536)
                (ThetaLowerSegment.join cell360962304 cell360995072)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell361027840 cell361060608)
                (ThetaLowerSegment.join cell361093376 cell361126144))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell361158912 cell361191680)
                (ThetaLowerSegment.join cell361224448 cell361257216))))
          (ThetaLowerSegment.join (ThetaLowerSegment.join cell361289984 cell361322752)
            cell361339136))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
