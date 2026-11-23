/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1289341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1257341184 :
    ThetaLowerSegment 1257341184 1257406720 (15716094402221 / 12500) (7858458912823 / 6250) := by
  exact
    packedTile65536 1257341184 1257406720 13 3144 35459 30 _ _ (83809 / 4000) (523807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257406720 :
    ThetaLowerSegment 1257406720 1257472256 (7858458912823 / 6250) (31435473073537 / 25000) := by
  exact
    packedTile65536 1257406720 1257472256 13 3126 35459 30 _ _ (209523 / 10000) (2095233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257472256 :
    ThetaLowerSegment 1257472256 1257537792 (31435473073537 / 25000) (62874254523139 / 50000) := by
  exact
    packedTile65536 1257472256 1257537792 13 3158 35460 30 _ _ (419047 / 20000) (1047619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257537792 :
    ThetaLowerSegment 1257537792 1257603328 (62874254523139 / 50000)
      (125755065055367 / 100000) := by
  exact
    packedTile65536 1257537792 1257603328 13 3129 35461 30 _ _ (2095241 / 100000) (523811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257603328 :
    ThetaLowerSegment 1257603328 1257668864 (125755065055367 / 100000)
      (25152307035003 / 20000) := by
  exact
    packedTile65536 1257603328 1257668864 13 3088 35462 30 _ _ (1047623 / 50000) (2095249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257668864 :
    ThetaLowerSegment 1257668864 1257734400 (25152307035003 / 20000) (31442013375219 / 25000) := by
  exact
    packedTile65536 1257668864 1257734400 13 3111 35463 30 _ _ (2095251 / 100000) (1047627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257734400 :
    ThetaLowerSegment 1257734400 1257799936 (31442013375219 / 25000) (31443669675087 / 25000) := by
  exact
    packedTile65536 1257734400 1257799936 13 3162 35464 30 _ _ (261907 / 12500) (2095259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257799936 :
    ThetaLowerSegment 1257799936 1257865472 (31443669675087 / 25000) (15722646751181 / 12500) := by
  exact
    packedTile65536 1257799936 1257865472 13 3100 35465 30 _ _ (2095261 / 100000) (65477 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257865472 :
    ThetaLowerSegment 1257865472 1257931008 (15722646751181 / 12500) (62893815811171 / 50000) := by
  exact
    packedTile65536 1257865472 1257931008 13 3082 35466 30 _ _ (2095267 / 100000) (209527 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257931008 :
    ThetaLowerSegment 1257931008 1257996544 (62893815811171 / 50000) (62897113769299 / 50000) := by
  exact
    packedTile65536 1257931008 1257996544 13 3148 35467 30 _ _ (261909 / 12500) (83811 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1257996544 :
    ThetaLowerSegment 1257996544 1258062080 (62897113769299 / 50000) (15725089838343 / 12500) := by
  exact
    packedTile65536 1257996544 1258062080 13 3098 35468 30 _ _ (2095277 / 100000) (26191 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258062080 :
    ThetaLowerSegment 1258062080 1258127616 (15725089838343 / 12500) (7862950880059 / 6250) := by
  exact
    packedTile65536 1258062080 1258127616 13 3100 35469 30 _ _ (1047641 / 50000) (419057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258127616 :
    ThetaLowerSegment 1258127616 1258193152 (7862950880059 / 6250) (15726725470213 / 12500) := by
  exact
    packedTile65536 1258127616 1258193152 13 3145 35470 30 _ _ (261911 / 12500) (2095291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258193152 :
    ThetaLowerSegment 1258193152 1258258688 (15726725470213 / 12500) (31455074792501 / 25000) := by
  exact
    packedTile65536 1258193152 1258258688 13 3100 35471 30 _ _ (2095293 / 100000) (65478 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258258688 :
    ThetaLowerSegment 1258258688 1258324224 (31455074792501 / 25000) (62913454917597 / 50000) := by
  exact
    packedTile65536 1258258688 1258324224 13 3155 35471 30 _ _ (1047649 / 50000) (2095301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258324224 :
    ThetaLowerSegment 1258324224 1258389760 (62913454917597 / 50000) (25166679797717 / 20000) := by
  exact
    packedTile65536 1258324224 1258389760 13 3097 35472 30 _ _ (2095303 / 100000) (1047653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258389760 :
    ThetaLowerSegment 1258389760 1258455296 (25166679797717 / 20000)
      (125839980351013 / 100000) := by
  exact
    packedTile65536 1258389760 1258455296 13 3141 35473 30 _ _ (523827 / 25000) (2095311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258455296 :
    ThetaLowerSegment 1258455296 1258520832 (125839980351013 / 100000)
      (125846551255717 / 100000) := by
  exact
    packedTile65536 1258455296 1258520832 13 3136 35474 30 _ _ (1047657 / 50000) (2095317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258520832 :
    ThetaLowerSegment 1258520832 1258586368 (125846551255717 / 100000)
      (125853067697807 / 100000) := by
  exact
    packedTile65536 1258520832 1258586368 13 3110 35475 30 _ _ (2095319 / 100000) (1047661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258586368 :
    ThetaLowerSegment 1258586368 1258651904 (125853067697807 / 100000)
      (125859647015167 / 100000) := by
  exact
    packedTile65536 1258586368 1258651904 13 3140 35476 30 _ _ (523831 / 25000) (2095327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258651904 :
    ThetaLowerSegment 1258651904 1258717440 (125859647015167 / 100000) (2517323982179 / 2000) := by
  exact
    packedTile65536 1258651904 1258717440 13 3127 35477 30 _ _ (2095329 / 100000) (523833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258717440 :
    ThetaLowerSegment 1258717440 1258782976 (2517323982179 / 2000) (6293639446719 / 5000) := by
  exact
    packedTile65536 1258717440 1258782976 13 3145 35478 30 _ _ (1047667 / 50000) (2095337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258782976 :
    ThetaLowerSegment 1258782976 1258848512 (6293639446719 / 5000) (6293964853021 / 5000) := by
  exact
    packedTile65536 1258782976 1258848512 13 3106 35479 30 _ _ (104767 / 5000) (2095343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258848512 :
    ThetaLowerSegment 1258848512 1258914048 (6293964853021 / 5000) (25177190794297 / 20000) := by
  exact
    packedTile65536 1258848512 1258914048 13 3177 35480 30 _ _ (419069 / 20000) (523837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258914048 :
    ThetaLowerSegment 1258914048 1258979584 (25177190794297 / 20000) (25178526789457 / 20000) := by
  exact
    packedTile65536 1258914048 1258979584 13 3188 35481 30 _ _ (41907 / 2000) (2095353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1258979584 :
    ThetaLowerSegment 1258979584 1259045120 (25178526789457 / 20000) (1573740926591 / 1250) := by
  exact
    packedTile65536 1258979584 1259045120 13 3169 35482 30 _ _ (419071 / 20000) (1047679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259045120 :
    ThetaLowerSegment 1259045120 1259110656 (1573740926591 / 1250) (1573825291023 / 1250) := by
  exact
    packedTile65536 1259045120 1259110656 13 3221 35483 30 _ _ (13096 / 625) (2095363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259110656 :
    ThetaLowerSegment 1259110656 1259176192 (1573825291023 / 1250) (6295622802773 / 5000) := by
  exact
    packedTile65536 1259110656 1259176192 13 3070 35483 30 _ _ (1047683 / 50000) (2095369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259176192 :
    ThetaLowerSegment 1259176192 1259241728 (6295622802773 / 5000) (62959469566667 / 50000) := by
  exact
    packedTile65536 1259176192 1259241728 13 3094 35484 30 _ _ (2095371 / 100000) (1047687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259241728 :
    ThetaLowerSegment 1259241728 1259307264 (62959469566667 / 50000) (62962771879243 / 50000) := by
  exact
    packedTile65536 1259241728 1259307264 13 3152 35485 30 _ _ (130961 / 6250) (2095379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259307264 :
    ThetaLowerSegment 1259307264 1259372800 (62962771879243 / 50000) (62966053245889 / 50000) := by
  exact
    packedTile65536 1259307264 1259372800 13 3132 35486 30 _ _ (2095381 / 100000) (261923 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259372800 :
    ThetaLowerSegment 1259372800 1259438336 (62966053245889 / 50000) (31484640594011 / 25000) := by
  exact
    packedTile65536 1259372800 1259438336 13 3081 35487 30 _ _ (1047693 / 50000) (2095389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259438336 :
    ThetaLowerSegment 1259438336 1259503872 (31484640594011 / 25000) (1259450958083 / 1000) := by
  exact
    packedTile65536 1259438336 1259503872 13 3118 35488 30 _ _ (65481 / 3125) (419079 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259503872 :
    ThetaLowerSegment 1259503872 1259569408 (1259450958083 / 1000) (7871981805077 / 6250) := by
  exact
    packedTile65536 1259503872 1259569408 13 3156 35489 30 _ _ (2095397 / 100000) (10477 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259569408 :
    ThetaLowerSegment 1259569408 1259634944 (7871981805077 / 6250) (62979141078653 / 50000) := by
  exact
    packedTile65536 1259569408 1259634944 13 3137 35490 30 _ _ (1047701 / 50000) (419081 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259634944 :
    ThetaLowerSegment 1259634944 1259700480 (62979141078653 / 50000)
      (125964830304181 / 100000) := by
  exact
    packedTile65536 1259634944 1259700480 13 3125 35491 30 _ _ (2095407 / 100000) (209541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259700480 :
    ThetaLowerSegment 1259700480 1259766016 (125964830304181 / 100000)
      (125971347035501 / 100000) := by
  exact
    packedTile65536 1259700480 1259766016 13 3110 35492 30 _ _ (523853 / 25000) (419083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259766016 :
    ThetaLowerSegment 1259766016 1259831552 (125971347035501 / 100000)
      (125977907789259 / 100000) := by
  exact
    packedTile65536 1259766016 1259831552 13 3131 35493 30 _ _ (1047709 / 50000) (2095421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259831552 :
    ThetaLowerSegment 1259831552 1259897088 (125977907789259 / 100000)
      (25196889939973 / 20000) := by
  exact
    packedTile65536 1259831552 1259897088 13 3122 35494 30 _ _ (2095423 / 100000) (1047713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259897088 :
    ThetaLowerSegment 1259897088 1259962624 (25196889939973 / 20000)
      (125990958099233 / 100000) := by
  exact
    packedTile65536 1259897088 1259962624 13 3106 35495 30 _ _ (523857 / 25000) (2095431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1259962624 :
    ThetaLowerSegment 1259962624 1260028160 (125990958099233 / 100000)
      (125997487468461 / 100000) := by
  exact
    packedTile65536 1259962624 1260028160 13 3116 35495 30 _ _ (2095433 / 100000) (523859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260028160 :
    ThetaLowerSegment 1260028160 1260093696 (125997487468461 / 100000)
      (126004039903087 / 100000) := by
  exact
    packedTile65536 1260028160 1260093696 13 3127 35496 30 _ _ (1047719 / 50000) (2095441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260093696 :
    ThetaLowerSegment 1260093696 1260159232 (126004039903087 / 100000)
      (25202122662183 / 20000) := by
  exact
    packedTile65536 1260093696 1260159232 13 3137 35497 30 _ _ (523861 / 25000) (2095447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260159232 :
    ThetaLowerSegment 1260159232 1260224768 (25202122662183 / 20000)
      (126017222357061 / 100000) := by
  exact
    packedTile65536 1260159232 1260224768 13 3154 35498 30 _ _ (2095449 / 100000) (523863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260224768 :
    ThetaLowerSegment 1260224768 1260290304 (126017222357061 / 100000)
      (126023820941707 / 100000) := by
  exact
    packedTile65536 1260224768 1260290304 13 3149 35499 30 _ _ (1047727 / 50000) (2095457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260290304 :
    ThetaLowerSegment 1260290304 1260355840 (126023820941707 / 100000)
      (126030270764509 / 100000) := by
  exact
    packedTile65536 1260290304 1260355840 13 3078 35500 30 _ _ (2095459 / 100000) (1047731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260355840 :
    ThetaLowerSegment 1260355840 1260421376 (126030270764509 / 100000)
      (126036875667037 / 100000) := by
  exact
    packedTile65536 1260355840 1260421376 13 3152 35501 30 _ _ (261933 / 12500) (2095467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260421376 :
    ThetaLowerSegment 1260421376 1260486912 (126036875667037 / 100000)
      (126043344382927 / 100000) := by
  exact
    packedTile65536 1260421376 1260486912 13 3087 35502 30 _ _ (209547 / 10000) (2095473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260486912 :
    ThetaLowerSegment 1260486912 1260552448 (126043344382927 / 100000)
      (63025021808251 / 50000) := by
  exact
    packedTile65536 1260486912 1260552448 13 3197 35503 30 _ _ (83819 / 4000) (1047739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260552448 :
    ThetaLowerSegment 1260552448 1260617984 (63025021808251 / 50000) (63028309616371 / 50000) := by
  exact
    packedTile65536 1260552448 1260617984 13 3138 35504 30 _ _ (52387 / 2500) (2095483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260617984 :
    ThetaLowerSegment 1260617984 1260683520 (63028309616371 / 50000)
      (126063201151127 / 100000) := by
  exact
    packedTile65536 1260617984 1260683520 13 3141 35505 30 _ _ (419097 / 20000) (65484 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260683520 :
    ThetaLowerSegment 1260683520 1260749056 (126063201151127 / 100000)
      (126069617541507 / 100000) := by
  exact
    packedTile65536 1260683520 1260749056 13 3062 35506 30 _ _ (209549 / 10000) (2095493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260749056 :
    ThetaLowerSegment 1260749056 1260814592 (126069617541507 / 100000)
      (126076096815139 / 100000) := by
  exact
    packedTile65536 1260749056 1260814592 13 3092 35507 30 _ _ (261937 / 12500) (2095499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260814592 :
    ThetaLowerSegment 1260814592 1260880128 (126076096815139 / 100000)
      (126082697643289 / 100000) := by
  exact
    packedTile65536 1260814592 1260880128 13 3150 35507 30 _ _ (2095501 / 100000) (130969 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260880128 :
    ThetaLowerSegment 1260880128 1260945664 (126082697643289 / 100000)
      (126089202093913 / 100000) := by
  exact
    packedTile65536 1260880128 1260945664 13 3104 35508 30 _ _ (1047753 / 50000) (2095509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1260945664 :
    ThetaLowerSegment 1260945664 1261011200 (126089202093913 / 100000) (3940494038753 / 3125) := by
  exact
    packedTile65536 1260945664 1261011200 13 3153 35509 30 _ _ (2095511 / 100000) (1047757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261011200 :
    ThetaLowerSegment 1261011200 1261076736 (3940494038753 / 3125) (1261022403787 / 1000) := by
  exact
    packedTile65536 1261011200 1261076736 13 3069 35510 30 _ _ (523879 / 25000) (2095519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261076736 :
    ThetaLowerSegment 1261076736 1261142272 (1261022403787 / 1000) (63054371391733 / 50000) := by
  exact
    packedTile65536 1261076736 1261142272 13 3103 35511 30 _ _ (1047761 / 50000) (83821 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261142272 :
    ThetaLowerSegment 1261142272 1261207808 (63054371391733 / 50000)
      (126115257776909 / 100000) := by
  exact
    packedTile65536 1261142272 1261207808 13 3109 35512 30 _ _ (2095527 / 100000) (209553 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261207808 :
    ThetaLowerSegment 1261207808 1261273344 (126115257776909 / 100000)
      (126121894326753 / 100000) := by
  exact
    packedTile65536 1261207808 1261273344 13 3167 35513 30 _ _ (523883 / 25000) (419107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261273344 :
    ThetaLowerSegment 1261273344 1261338880 (126121894326753 / 100000)
      (31532130627571 / 25000) := by
  exact
    packedTile65536 1261273344 1261338880 13 3163 35514 30 _ _ (2095537 / 100000) (104777 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261338880 :
    ThetaLowerSegment 1261338880 1261404416 (31532130627571 / 25000) (7883454646663 / 6250) := by
  exact
    packedTile65536 1261338880 1261404416 13 3222 35515 30 _ _ (1047771 / 50000) (419109 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261404416 :
    ThetaLowerSegment 1261404416 1261469952 (7883454646663 / 6250) (31535427443629 / 25000) := by
  exact
    packedTile65536 1261404416 1261469952 13 3071 35516 30 _ _ (523887 / 25000) (2095551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261469952 :
    ThetaLowerSegment 1261469952 1261535488 (31535427443629 / 25000)
      (126148241613217 / 100000) := by
  exact
    packedTile65536 1261469952 1261535488 13 3117 35517 30 _ _ (2095553 / 100000) (523889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261535488 :
    ThetaLowerSegment 1261535488 1261601024 (126148241613217 / 100000)
      (126154867767613 / 100000) := by
  exact
    packedTile65536 1261535488 1261601024 13 3162 35518 30 _ _ (1047779 / 50000) (2095561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261601024 :
    ThetaLowerSegment 1261601024 1261666560 (126154867767613 / 100000)
      (126161389159669 / 100000) := by
  exact
    packedTile65536 1261601024 1261666560 13 3112 35519 30 _ _ (2095563 / 100000) (1047783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261666560 :
    ThetaLowerSegment 1261666560 1261732096 (126161389159669 / 100000)
      (126168107550677 / 100000) := by
  exact
    packedTile65536 1261666560 1261732096 13 3206 35519 30 _ _ (130973 / 6250) (2095571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261732096 :
    ThetaLowerSegment 1261732096 1261797632 (126168107550677 / 100000)
      (126174666697297 / 100000) := by
  exact
    packedTile65536 1261732096 1261797632 13 3130 35520 30 _ _ (1047787 / 50000) (2095577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261797632 :
    ThetaLowerSegment 1261797632 1261863168 (126174666697297 / 100000) (3943163504572 / 3125) := by
  exact
    packedTile65536 1261797632 1261863168 13 3133 35521 30 _ _ (2095579 / 100000) (1047791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261863168 :
    ThetaLowerSegment 1261863168 1261928704 (3943163504572 / 3125) (3943363698331 / 3125) := by
  exact
    packedTile65536 1261863168 1261928704 13 3057 35522 30 _ _ (65487 / 3125) (2095587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261928704 :
    ThetaLowerSegment 1261928704 1261994240 (3943363698331 / 3125) (63097123917149 / 50000) := by
  exact
    packedTile65536 1261928704 1261994240 13 3154 35523 30 _ _ (2095589 / 100000) (261949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1261994240 :
    ThetaLowerSegment 1261994240 1262059776 (63097123917149 / 50000) (7887559477469 / 6250) := by
  exact
    packedTile65536 1261994240 1262059776 13 3199 35524 30 _ _ (1047797 / 50000) (2095597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262059776 :
    ThetaLowerSegment 1262059776 1262125312 (7887559477469 / 6250) (7887965238019 / 6250) := by
  exact
    packedTile65536 1262059776 1262125312 13 3098 35525 30 _ _ (5239 / 250) (2095603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262125312 :
    ThetaLowerSegment 1262125312 1262190848 (7887965238019 / 6250) (63106921892987 / 50000) := by
  exact
    packedTile65536 1262125312 1262190848 13 3054 35526 30 _ _ (419121 / 20000) (261951 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262190848 :
    ThetaLowerSegment 1262190848 1262256384 (63106921892987 / 50000) (31555084520341 / 25000) := by
  exact
    packedTile65536 1262190848 1262256384 13 3099 35527 30 _ _ (209561 / 10000) (2095613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262256384 :
    ThetaLowerSegment 1262256384 1262321920 (31555084520341 / 25000)
      (126226891069469 / 100000) := by
  exact
    packedTile65536 1262256384 1262321920 13 3127 35528 30 _ _ (419123 / 20000) (1047809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262321920 :
    ThetaLowerSegment 1262321920 1262387456 (126226891069469 / 100000)
      (126233485985609 / 100000) := by
  exact
    packedTile65536 1262321920 1262387456 13 3147 35529 30 _ _ (104781 / 5000) (2095623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262387456 :
    ThetaLowerSegment 1262387456 1262452992 (126233485985609 / 100000)
      (126240064155623 / 100000) := by
  exact
    packedTile65536 1262387456 1262452992 13 3139 35530 30 _ _ (1047813 / 50000) (2095629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262452992 :
    ThetaLowerSegment 1262452992 1262518528 (126240064155623 / 100000)
      (25249312960597 / 20000) := by
  exact
    packedTile65536 1262452992 1262518528 13 3102 35531 30 _ _ (2095631 / 100000) (1047817 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262518528 :
    ThetaLowerSegment 1262518528 1262584064 (25249312960597 / 20000)
      (126253241499281 / 100000) := by
  exact
    packedTile65536 1262518528 1262584064 13 3186 35531 30 _ _ (523909 / 25000) (2095639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262584064 :
    ThetaLowerSegment 1262584064 1262649600 (126253241499281 / 100000) (3945617532451 / 3125) := by
  exact
    packedTile65536 1262584064 1262649600 13 3111 35532 30 _ _ (2095641 / 100000) (523911 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262649600 :
    ThetaLowerSegment 1262649600 1262715136 (3945617532451 / 3125) (31566569624373 / 25000) := by
  exact
    packedTile65536 1262649600 1262715136 13 3110 35533 30 _ _ (1047823 / 50000) (2095649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262715136 :
    ThetaLowerSegment 1262715136 1262780672 (31566569624373 / 25000) (31568228332931 / 25000) := by
  exact
    packedTile65536 1262715136 1262780672 13 3166 35534 30 _ _ (523913 / 25000) (419131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262780672 :
    ThetaLowerSegment 1262780672 1262846208 (31568228332931 / 25000)
      (126279491599047 / 100000) := by
  exact
    packedTile65536 1262780672 1262846208 13 3139 35535 30 _ _ (2095657 / 100000) (104783 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262846208 :
    ThetaLowerSegment 1262846208 1262911744 (126279491599047 / 100000)
      (126286013299191 / 100000) := by
  exact
    packedTile65536 1262846208 1262911744 13 3112 35536 30 _ _ (1047831 / 50000) (419133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262911744 :
    ThetaLowerSegment 1262911744 1262977280 (126286013299191 / 100000)
      (126292602076239 / 100000) := by
  exact
    packedTile65536 1262911744 1262977280 13 3144 35537 30 _ _ (2095667 / 100000) (209567 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1262977280 :
    ThetaLowerSegment 1262977280 1263042816 (126292602076239 / 100000)
      (126299039980623 / 100000) := by
  exact
    packedTile65536 1262977280 1263042816 13 3072 35538 30 _ _ (261959 / 12500) (83827 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263042816 :
    ThetaLowerSegment 1263042816 1263108352 (126299039980623 / 100000) (3947046511836 / 3125) := by
  exact
    packedTile65536 1263042816 1263108352 13 3077 35539 30 _ _ (2095677 / 100000) (13098 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263108352 :
    ThetaLowerSegment 1263108352 1263173888 (3947046511836 / 3125) (63155994593709 / 50000) := by
  exact
    packedTile65536 1263108352 1263173888 13 3102 35540 30 _ _ (2095683 / 100000) (1047843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263173888 :
    ThetaLowerSegment 1263173888 1263239424 (63155994593709 / 50000) (63159329881161 / 50000) := by
  exact
    packedTile65536 1263173888 1263239424 13 3183 35541 30 _ _ (261961 / 12500) (2095691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263239424 :
    ThetaLowerSegment 1263239424 1263304960 (63159329881161 / 50000)
      (126325183654631 / 100000) := by
  exact
    packedTile65536 1263239424 1263304960 13 3113 35542 30 _ _ (2095693 / 100000) (130981 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263304960 :
    ThetaLowerSegment 1263304960 1263370496 (126325183654631 / 100000)
      (126331845878573 / 100000) := by
  exact
    packedTile65536 1263304960 1263370496 13 3179 35543 30 _ _ (1047849 / 50000) (2095701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263370496 :
    ThetaLowerSegment 1263370496 1263436032 (126331845878573 / 100000)
      (126338451534429 / 100000) := by
  exact
    packedTile65536 1263370496 1263436032 13 3152 35543 30 _ _ (2095703 / 100000) (1047853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263436032 :
    ThetaLowerSegment 1263436032 1263501568 (126338451534429 / 100000)
      (126344864403969 / 100000) := by
  exact
    packedTile65536 1263436032 1263501568 13 3060 35544 30 _ _ (2095709 / 100000) (65491 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263501568 :
    ThetaLowerSegment 1263501568 1263567104 (126344864403969 / 100000)
      (126351438658787 / 100000) := by
  exact
    packedTile65536 1263501568 1263567104 13 3137 35545 30 _ _ (1047857 / 50000) (2095717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263567104 :
    ThetaLowerSegment 1263567104 1263632640 (126351438658787 / 100000)
      (15794752140091 / 12500) := by
  exact
    packedTile65536 1263567104 1263632640 13 3139 35546 30 _ _ (2095719 / 100000) (1047861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263632640 :
    ThetaLowerSegment 1263632640 1263698176 (15794752140091 / 12500) (15795572616037 / 12500) := by
  exact
    packedTile65536 1263632640 1263698176 13 3132 35547 30 _ _ (523931 / 25000) (2095727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263698176 :
    ThetaLowerSegment 1263698176 1263763712 (15795572616037 / 12500) (15796385758889 / 12500) := by
  exact
    packedTile65536 1263698176 1263763712 13 3104 35548 30 _ _ (2095729 / 100000) (523933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263763712 :
    ThetaLowerSegment 1263763712 1263829248 (15796385758889 / 12500)
      (126377656200337 / 100000) := by
  exact
    packedTile65536 1263763712 1263829248 13 3135 35549 30 _ _ (419147 / 20000) (1047869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263829248 :
    ThetaLowerSegment 1263829248 1263894784 (126377656200337 / 100000)
      (126384182334697 / 100000) := by
  exact
    packedTile65536 1263829248 1263894784 13 3114 35550 30 _ _ (104787 / 5000) (2095743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263894784 :
    ThetaLowerSegment 1263894784 1263960320 (126384182334697 / 100000)
      (63195378343381 / 50000) := by
  exact
    packedTile65536 1263894784 1263960320 13 3137 35551 30 _ _ (419149 / 20000) (523937 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1263960320 :
    ThetaLowerSegment 1263960320 1264025856 (63195378343381 / 50000) (7899839478157 / 6250) := by
  exact
    packedTile65536 1263960320 1264025856 13 3185 35552 30 _ _ (8383 / 400) (2095753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264025856 :
    ThetaLowerSegment 1264025856 1264091392 (7899839478157 / 6250) (31601007271813 / 25000) := by
  exact
    packedTile65536 1264025856 1264091392 13 3148 35553 30 _ _ (419151 / 20000) (1047879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264091392 :
    ThetaLowerSegment 1264091392 1264156928 (31601007271813 / 25000) (31602635677333 / 25000) := by
  exact
    packedTile65536 1264091392 1264156928 13 3108 35554 30 _ _ (26197 / 1250) (2095763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264156928 :
    ThetaLowerSegment 1264156928 1264222464 (31602635677333 / 25000) (3950536023603 / 3125) := by
  exact
    packedTile65536 1264156928 1264222464 13 3154 35554 30 _ _ (1047883 / 50000) (2095769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264222464 :
    ThetaLowerSegment 1264222464 1264288000 (3950536023603 / 3125) (126423643358083 / 100000) := by
  exact
    packedTile65536 1264222464 1264288000 13 3097 35555 30 _ _ (2095771 / 100000) (1047887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264288000 :
    ThetaLowerSegment 1264288000 1264353536 (126423643358083 / 100000)
      (126430190562307 / 100000) := by
  exact
    packedTile65536 1264288000 1264353536 13 3124 35556 30 _ _ (65493 / 3125) (2095779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264353536 :
    ThetaLowerSegment 1264353536 1264419072 (126430190562307 / 100000)
      (126436679100283 / 100000) := by
  exact
    packedTile65536 1264353536 1264419072 13 3096 35557 30 _ _ (2095781 / 100000) (261973 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264419072 :
    ThetaLowerSegment 1264419072 1264484608 (126436679100283 / 100000)
      (126443194898957 / 100000) := by
  exact
    packedTile65536 1264419072 1264484608 13 3109 35558 30 _ _ (1047893 / 50000) (2095789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264484608 :
    ThetaLowerSegment 1264484608 1264550144 (126443194898957 / 100000)
      (126449672992029 / 100000) := by
  exact
    packedTile65536 1264484608 1264550144 13 3091 35559 30 _ _ (130987 / 6250) (419159 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264550144 :
    ThetaLowerSegment 1264550144 1264615680 (126449672992029 / 100000)
      (31614029391951 / 25000) := by
  exact
    packedTile65536 1264550144 1264615680 13 3075 35560 30 _ _ (2095797 / 100000) (10479 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264615680 :
    ThetaLowerSegment 1264615680 1264681216 (31614029391951 / 25000) (63231375390567 / 50000) := by
  exact
    packedTile65536 1264615680 1264681216 13 3165 35561 30 _ _ (1047901 / 50000) (419161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264681216 :
    ThetaLowerSegment 1264681216 1264746752 (63231375390567 / 50000)
      (126469425926429 / 100000) := by
  exact
    packedTile65536 1264681216 1264746752 13 3185 35562 30 _ _ (2095807 / 100000) (209581 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264746752 :
    ThetaLowerSegment 1264746752 1264812288 (126469425926429 / 100000)
      (126475910368757 / 100000) := by
  exact
    packedTile65536 1264746752 1264812288 13 3094 35563 30 _ _ (523953 / 25000) (419163 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264812288 :
    ThetaLowerSegment 1264812288 1264877824 (126475910368757 / 100000)
      (126482399018189 / 100000) := by
  exact
    packedTile65536 1264812288 1264877824 13 3096 35564 30 _ _ (2095817 / 100000) (104791 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264877824 :
    ThetaLowerSegment 1264877824 1264943360 (126482399018189 / 100000)
      (63244467945063 / 50000) := by
  exact
    packedTile65536 1264877824 1264943360 13 3119 35565 30 _ _ (2095823 / 100000) (1047913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1264943360 :
    ThetaLowerSegment 1264943360 1265008896 (63244467945063 / 50000) (63247817078207 / 50000) := by
  exact
    packedTile65536 1264943360 1265008896 13 3196 35566 30 _ _ (523957 / 25000) (2095831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265008896 :
    ThetaLowerSegment 1265008896 1265074432 (63247817078207 / 50000) (63251124302681 / 50000) := by
  exact
    packedTile65536 1265008896 1265074432 13 3156 35566 30 _ _ (2095833 / 100000) (523959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265074432 :
    ThetaLowerSegment 1265074432 1265139968 (63251124302681 / 50000) (7906793069721 / 6250) := by
  exact
    packedTile65536 1265074432 1265139968 13 3073 35567 30 _ _ (1047919 / 50000) (2095841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265139968 :
    ThetaLowerSegment 1265139968 1265205504 (7906793069721 / 6250) (31628813323953 / 25000) := by
  exact
    packedTile65536 1265139968 1265205504 13 3132 35568 30 _ _ (2095843 / 100000) (1047923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265205504 :
    ThetaLowerSegment 1265205504 1265271040 (31628813323953 / 25000) (3953808892564 / 3125) := by
  exact
    packedTile65536 1265205504 1265271040 13 3164 35569 30 _ _ (2095849 / 100000) (523963 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265271040 :
    ThetaLowerSegment 1265271040 1265336576 (3953808892564 / 3125) (63264166752403 / 50000) := by
  exact
    packedTile65536 1265271040 1265336576 13 3077 35570 30 _ _ (1047927 / 50000) (2095857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265336576 :
    ThetaLowerSegment 1265336576 1265402112 (63264166752403 / 50000) (3954215685216 / 3125) := by
  exact
    packedTile65536 1265336576 1265402112 13 3134 35571 30 _ _ (2095859 / 100000) (1047931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265402112 :
    ThetaLowerSegment 1265402112 1265467648 (3954215685216 / 3125) (15817694012923 / 12500) := by
  exact
    packedTile65536 1265402112 1265467648 13 3173 35572 30 _ _ (261983 / 12500) (2095867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265467648 :
    ThetaLowerSegment 1265467648 1265533184 (15817694012923 / 12500)
      (126548080735319 / 100000) := by
  exact
    packedTile65536 1265467648 1265533184 13 3115 35573 30 _ _ (2095869 / 100000) (65496 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265533184 :
    ThetaLowerSegment 1265533184 1265598720 (126548080735319 / 100000)
      (25310929840887 / 20000) := by
  exact
    packedTile65536 1265533184 1265598720 13 3134 35574 30 _ _ (1047937 / 50000) (2095877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265598720 :
    ThetaLowerSegment 1265598720 1265664256 (25310929840887 / 20000) (25312233478247 / 20000) := by
  exact
    packedTile65536 1265598720 1265664256 13 3110 35575 30 _ _ (52397 / 2500) (2095883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265664256 :
    ThetaLowerSegment 1265664256 1265729792 (25312233478247 / 20000) (12656767930593 / 10000) := by
  exact
    packedTile65536 1265664256 1265729792 13 3107 35576 30 _ _ (419177 / 20000) (130993 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265729792 :
    ThetaLowerSegment 1265729792 1265795328 (12656767930593 / 10000) (3164353732959 / 2500) := by
  exact
    packedTile65536 1265729792 1265795328 13 3087 35577 30 _ _ (209589 / 10000) (2095893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265795328 :
    ThetaLowerSegment 1265795328 1265860864 (3164353732959 / 2500) (25316138959689 / 20000) := by
  exact
    packedTile65536 1265795328 1265860864 13 3123 35578 30 _ _ (419179 / 20000) (1047949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265860864 :
    ThetaLowerSegment 1265860864 1265926400 (25316138959689 / 20000) (25317436321789 / 20000) := by
  exact
    packedTile65536 1265860864 1265926400 13 3095 35578 30 _ _ (20959 / 1000) (2095903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265926400 :
    ThetaLowerSegment 1265926400 1265991936 (25317436321789 / 20000)
      (126593771137409 / 100000) := by
  exact
    packedTile65536 1265926400 1265991936 13 3144 35579 30 _ _ (1047953 / 50000) (2095909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1265991936 :
    ThetaLowerSegment 1265991936 1266057472 (126593771137409 / 100000)
      (15825034867633 / 12500) := by
  exact
    packedTile65536 1265991936 1266057472 13 3105 35580 30 _ _ (2095911 / 100000) (1047957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266057472 :
    ThetaLowerSegment 1266057472 1266123008 (15825034867633 / 12500) (3165168149467 / 2500) := by
  exact
    packedTile65536 1266057472 1266123008 13 3076 35581 30 _ _ (523979 / 25000) (2095919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266123008 :
    ThetaLowerSegment 1266123008 1266188544 (3165168149467 / 2500) (126613334417593 / 100000) := by
  exact
    packedTile65536 1266123008 1266188544 13 3153 35582 30 _ _ (2095921 / 100000) (523981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266188544 :
    ThetaLowerSegment 1266188544 1266254080 (126613334417593 / 100000)
      (126619928200789 / 100000) := by
  exact
    packedTile65536 1266188544 1266254080 13 3146 35583 30 _ _ (1047963 / 50000) (2095929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266254080 :
    ThetaLowerSegment 1266254080 1266319616 (126619928200789 / 100000)
      (63313236896651 / 50000) := by
  exact
    packedTile65536 1266254080 1266319616 13 3123 35584 30 _ _ (2095931 / 100000) (1047967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266319616 :
    ThetaLowerSegment 1266319616 1266385152 (63313236896651 / 50000) (63316523325867 / 50000) := by
  exact
    packedTile65536 1266319616 1266385152 13 3136 35585 30 _ _ (2095937 / 100000) (104797 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266385152 :
    ThetaLowerSegment 1266385152 1266450688 (63316523325867 / 50000) (31659917981099 / 25000) := by
  exact
    packedTile65536 1266385152 1266450688 13 3161 35586 30 _ _ (1047971 / 50000) (419189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266450688 :
    ThetaLowerSegment 1266450688 1266516224 (31659917981099 / 25000) (63323145462511 / 50000) := by
  exact
    packedTile65536 1266450688 1266516224 13 3158 35587 30 _ _ (2095947 / 100000) (41919 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266516224 :
    ThetaLowerSegment 1266516224 1266581760 (63323145462511 / 50000) (63326428771319 / 50000) := by
  exact
    packedTile65536 1266516224 1266581760 13 3133 35588 30 _ _ (130997 / 6250) (419191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266581760 :
    ThetaLowerSegment 1266581760 1266647296 (63326428771319 / 50000)
      (126659533165683 / 100000) := by
  exact
    packedTile65536 1266581760 1266647296 13 3185 35589 30 _ _ (2095957 / 100000) (52399 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266647296 :
    ThetaLowerSegment 1266647296 1266712832 (126659533165683 / 100000)
      (126666055799427 / 100000) := by
  exact
    packedTile65536 1266647296 1266712832 13 3112 35589 30 _ _ (1047981 / 50000) (419193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266712832 :
    ThetaLowerSegment 1266712832 1266778368 (126666055799427 / 100000)
      (126672641330883 / 100000) := by
  exact
    packedTile65536 1266712832 1266778368 13 3142 35590 30 _ _ (65499 / 3125) (2095971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266778368 :
    ThetaLowerSegment 1266778368 1266843904 (126672641330883 / 100000)
      (63339681558147 / 50000) := by
  exact
    packedTile65536 1266778368 1266843904 13 3207 35591 30 _ _ (2095973 / 100000) (261997 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266843904 :
    ThetaLowerSegment 1266843904 1266909440 (63339681558147 / 50000) (7917875329411 / 6250) := by
  exact
    packedTile65536 1266843904 1266909440 13 3169 35592 30 _ _ (1047989 / 50000) (2095981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266909440 :
    ThetaLowerSegment 1266909440 1266974976 (7917875329411 / 6250) (15836578572107 / 12500) := by
  exact
    packedTile65536 1266909440 1266974976 13 3160 35593 30 _ _ (2095983 / 100000) (1047993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1266974976 :
    ThetaLowerSegment 1266974976 1267040512 (15836578572107 / 12500) (15837406487367 / 12500) := by
  exact
    packedTile65536 1266974976 1267040512 13 3160 35594 30 _ _ (523997 / 25000) (2095991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267040512 :
    ThetaLowerSegment 1267040512 1267106048 (15837406487367 / 12500)
      (126705856372879 / 100000) := by
  exact
    packedTile65536 1267040512 1267106048 13 3151 35595 30 _ _ (2095993 / 100000) (523999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267106048 :
    ThetaLowerSegment 1267106048 1267171584 (126705856372879 / 100000) (5068490302153 / 4000) := by
  exact
    packedTile65536 1267106048 1267171584 13 3054 35596 30 _ _ (2095999 / 100000) (1048001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267171584 :
    ThetaLowerSegment 1267171584 1267237120 (5068490302153 / 4000) (126718832718373 / 100000) := by
  exact
    packedTile65536 1267171584 1267237120 13 3137 35597 30 _ _ (524001 / 25000) (2096007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267237120 :
    ThetaLowerSegment 1267237120 1267302656 (126718832718373 / 100000) (5069015561381 / 4000) := by
  exact
    packedTile65536 1267237120 1267302656 13 3128 35598 30 _ _ (2096009 / 100000) (524003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267302656 :
    ThetaLowerSegment 1267302656 1267368192 (5069015561381 / 4000) (126731758821071 / 100000) := by
  exact
    packedTile65536 1267302656 1267368192 13 3039 35599 30 _ _ (1048007 / 50000) (2096017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267368192 :
    ThetaLowerSegment 1267368192 1267433728 (126731758821071 / 100000)
      (126738273248123 / 100000) := by
  exact
    packedTile65536 1267368192 1267433728 13 3108 35600 30 _ _ (2096019 / 100000) (1048011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267433728 :
    ThetaLowerSegment 1267433728 1267499264 (126738273248123 / 100000)
      (63372485023999 / 50000) := by
  exact
    packedTile65536 1267433728 1267499264 13 3195 35601 30 _ _ (83841 / 4000) (524007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267499264 :
    ThetaLowerSegment 1267499264 1267564800 (63372485023999 / 50000) (63375748542709 / 50000) := by
  exact
    packedTile65536 1267499264 1267564800 13 3114 35601 30 _ _ (209603 / 10000) (2096033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267564800 :
    ThetaLowerSegment 1267564800 1267630336 (63375748542709 / 50000)
      (126757980121673 / 100000) := by
  exact
    packedTile65536 1267564800 1267630336 13 3093 35602 30 _ _ (419207 / 20000) (1048019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267630336 :
    ThetaLowerSegment 1267630336 1267695872 (126757980121673 / 100000)
      (126764637144713 / 100000) := by
  exact
    packedTile65536 1267630336 1267695872 13 3176 35603 30 _ _ (52401 / 2500) (2096043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267695872 :
    ThetaLowerSegment 1267695872 1267761408 (126764637144713 / 100000)
      (15846399982701 / 12500) := by
  exact
    packedTile65536 1267695872 1267761408 13 3131 35604 30 _ _ (419209 / 20000) (131003 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267761408 :
    ThetaLowerSegment 1267761408 1267826944 (15846399982701 / 12500) (3961807242619 / 3125) := by
  exact
    packedTile65536 1267761408 1267826944 13 3164 35605 30 _ _ (41921 / 2000) (2096053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267826944 :
    ThetaLowerSegment 1267826944 1267892480 (3961807242619 / 3125) (3169610177287 / 2500) := by
  exact
    packedTile65536 1267826944 1267892480 13 3137 35606 30 _ _ (262007 / 12500) (2096059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267892480 :
    ThetaLowerSegment 1267892480 1267958016 (3169610177287 / 2500) (63395521610303 / 50000) := by
  exact
    packedTile65536 1267892480 1267958016 13 3166 35607 30 _ _ (2096061 / 100000) (65502 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1267958016 :
    ThetaLowerSegment 1267958016 1268023552 (63395521610303 / 50000) (63398873219837 / 50000) := by
  exact
    packedTile65536 1267958016 1268023552 13 3198 35608 30 _ _ (1048033 / 50000) (2096069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268023552 :
    ThetaLowerSegment 1268023552 1268154624 (63398873219837 / 50000) (3170269914443 / 2500) := by
  exact
    packedTile65536 1268023552 1268154624 14 6226 35609 30 _ _ (2096071 / 100000) (1048037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268154624 :
    ThetaLowerSegment 1268154624 1268285696 (3170269914443 / 2500) (15852971938909 / 12500) := by
  exact
    packedTile65536 1268154624 1268285696 14 6192 35611 30 _ _ (2096081 / 100000) (524021 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268285696 :
    ThetaLowerSegment 1268285696 1268351232 (15852971938909 / 12500) (31707589834061 / 25000) := by
  exact
    packedTile65536 1268285696 1268351232 13 3141 35612 30 _ _ (524023 / 25000) (419219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268351232 :
    ThetaLowerSegment 1268351232 1268416768 (31707589834061 / 25000)
      (126836930600339 / 100000) := by
  exact
    packedTile65536 1268351232 1268416768 13 3135 35613 30 _ _ (2096097 / 100000) (20961 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268416768 :
    ThetaLowerSegment 1268416768 1268482304 (126836930600339 / 100000)
      (126843575243679 / 100000) := by
  exact
    packedTile65536 1268416768 1268482304 13 3170 35614 30 _ _ (1048051 / 50000) (419221 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268482304 :
    ThetaLowerSegment 1268482304 1268613376 (126843575243679 / 100000)
      (126856742987853 / 100000) := by
  exact
    packedTile65536 1268482304 1268613376 14 6282 35615 30 _ _ (2096107 / 100000) (209611 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268613376 :
    ThetaLowerSegment 1268613376 1268744448 (126856742987853 / 100000)
      (126869772457341 / 100000) := by
  exact
    packedTile65536 1268613376 1268744448 14 6216 35617 30 _ _ (1048059 / 50000) (2096121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268744448 :
    ThetaLowerSegment 1268744448 1268875520 (126869772457341 / 100000)
      (126882906795389 / 100000) := by
  exact
    packedTile65536 1268744448 1268875520 14 6266 35619 30 _ _ (65504 / 3125) (2096131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1268875520 :
    ThetaLowerSegment 1268875520 1269006592 (126882906795389 / 100000)
      (126895984600371 / 100000) := by
  exact
    packedTile65536 1268875520 1269006592 14 6239 35621 30 _ _ (1048069 / 50000) (2096141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269006592 :
    ThetaLowerSegment 1269006592 1269137664 (126895984600371 / 100000)
      (126909186146773 / 100000) := by
  exact
    packedTile65536 1269006592 1269137664 14 6298 35623 30 _ _ (2096149 / 100000) (262019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269137664 :
    ThetaLowerSegment 1269137664 1269268736 (126909186146773 / 100000)
      (31730596414999 / 25000) := by
  exact
    packedTile65536 1269137664 1269268736 14 6297 35624 30 _ _ (2096159 / 100000) (1048081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269268736 :
    ThetaLowerSegment 1269268736 1269399808 (31730596414999 / 25000) (15866940555911 / 12500) := by
  exact
    packedTile65536 1269268736 1269399808 14 6268 35626 30 _ _ (2096169 / 100000) (524043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269399808 :
    ThetaLowerSegment 1269399808 1269530880 (15866940555911 / 12500) (15868596538111 / 12500) := by
  exact
    packedTile65536 1269399808 1269530880 14 6320 35628 30 _ _ (104809 / 5000) (2096183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269530880 :
    ThetaLowerSegment 1269530880 1269661952 (15868596538111 / 12500) (63480941986669 / 50000) := by
  exact
    packedTile65536 1269530880 1269661952 14 6255 35630 30 _ _ (209619 / 10000) (2096193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269661952 :
    ThetaLowerSegment 1269661952 1269793024 (63480941986669 / 50000) (63487550257169 / 50000) := by
  exact
    packedTile65536 1269661952 1269793024 14 6305 35632 30 _ _ (10481 / 500) (2096203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269793024 :
    ThetaLowerSegment 1269793024 1269924096 (63487550257169 / 50000) (15873544356271 / 12500) := by
  exact
    packedTile65536 1269793024 1269924096 14 6323 35634 30 _ _ (209621 / 10000) (2096213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1269924096 :
    ThetaLowerSegment 1269924096 1270055168 (15873544356271 / 12500)
      (127001462520081 / 100000) := by
  exact
    packedTile65536 1269924096 1270055168 14 6253 35635 30 _ _ (2096221 / 100000) (65507 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1270055168 :
    ThetaLowerSegment 1270055168 1270186240 (127001462520081 / 100000)
      (63507203373253 / 50000) := by
  exact
    packedTile65536 1270055168 1270186240 14 6175 35637 30 _ _ (2096231 / 100000) (1048117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1270186240 :
    ThetaLowerSegment 1270186240 1270317312 (63507203373253 / 50000) (31756877063189 / 25000) := by
  exact
    packedTile65536 1270186240 1270317312 14 6250 35639 30 _ _ (2096241 / 100000) (524061 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1270317312 :
    ThetaLowerSegment 1270317312 1270448384 (31756877063189 / 25000) (7940035886967 / 6250) := by
  exact
    packedTile65536 1270317312 1270448384 14 6233 35641 30 _ _ (524063 / 25000) (419251 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1270448384 :
    ThetaLowerSegment 1270448384 1270579456 (7940035886967 / 6250) (2541074313159 / 2000) := by
  exact
    packedTile65536 1270448384 1270579456 14 6269 35643 30 _ _ (1048131 / 50000) (419253 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1270579456 :
    ThetaLowerSegment 1270579456 1270710528 (2541074313159 / 2000) (63533338453863 / 50000) := by
  exact
    packedTile65536 1270579456 1270710528 14 6183 35645 30 _ _ (131017 / 6250) (83851 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1270710528 :
    ThetaLowerSegment 1270710528 1270841600 (63533338453863 / 50000) (3971241773463 / 3125) := by
  exact
    packedTile65536 1270710528 1270841600 14 6230 35647 30 _ _ (2096283 / 100000) (1048143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1270841600 :
    ThetaLowerSegment 1270841600 1270972672 (3971241773463 / 3125) (31773252619523 / 25000) := by
  exact
    packedTile65536 1270841600 1270972672 14 6332 35648 30 _ _ (2096293 / 100000) (262037 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1270972672 :
    ThetaLowerSegment 1270972672 1271103744 (31773252619523 / 25000)
      (127106005460389 / 100000) := by
  exact
    packedTile65536 1270972672 1271103744 14 6199 35650 30 _ _ (2096303 / 100000) (1048153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1271103744 :
    ThetaLowerSegment 1271103744 1271234816 (127106005460389 / 100000)
      (127119086459749 / 100000) := by
  exact
    packedTile65536 1271103744 1271234816 14 6240 35652 30 _ _ (1048157 / 50000) (2096317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1271234816 :
    ThetaLowerSegment 1271234816 1271365888 (127119086459749 / 100000)
      (127132402309797 / 100000) := by
  exact
    packedTile65536 1271234816 1271365888 14 6352 35654 30 _ _ (524081 / 25000) (2096327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1271365888 :
    ThetaLowerSegment 1271365888 1271496960 (127132402309797 / 100000)
      (127145479241289 / 100000) := by
  exact
    packedTile65536 1271365888 1271496960 14 6238 35656 30 _ _ (1048167 / 50000) (2096337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1271496960 :
    ThetaLowerSegment 1271496960 1271628032 (127145479241289 / 100000)
      (127158560434089 / 100000) := by
  exact
    packedTile65536 1271496960 1271628032 14 6240 35658 30 _ _ (419269 / 20000) (524087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1271628032 :
    ThetaLowerSegment 1271628032 1271759104 (127158560434089 / 100000)
      (63585798832917 / 50000) := by
  exact
    packedTile65536 1271628032 1271759104 14 6219 35659 30 _ _ (419271 / 20000) (1048179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1271759104 :
    ThetaLowerSegment 1271759104 1271890176 (63585798832917 / 50000) (3974522135392 / 3125) := by
  exact
    packedTile65536 1271759104 1271890176 14 6254 35661 30 _ _ (419273 / 20000) (131023 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1271890176 :
    ThetaLowerSegment 1271890176 1272021248 (3974522135392 / 3125) (127197628291669 / 100000) := by
  exact
    packedTile65536 1271890176 1272021248 14 6163 35663 30 _ _ (16771 / 800) (1048189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272021248 :
    ThetaLowerSegment 1272021248 1272152320 (127197628291669 / 100000)
      (25442146560111 / 20000) := by
  exact
    packedTile65536 1272021248 1272152320 14 6251 35665 30 _ _ (1048193 / 50000) (2096389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272152320 :
    ThetaLowerSegment 1272152320 1272283392 (25442146560111 / 20000)
      (127223843661139 / 100000) := by
  exact
    packedTile65536 1272152320 1272283392 14 6254 35667 30 _ _ (524099 / 25000) (2096399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272283392 :
    ThetaLowerSegment 1272283392 1272414464 (127223843661139 / 100000)
      (127236965066293 / 100000) := by
  exact
    packedTile65536 1272283392 1272414464 14 6259 35669 30 _ _ (1048203 / 50000) (2096409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272414464 :
    ThetaLowerSegment 1272414464 1272545536 (127236965066293 / 100000)
      (63625053752233 / 50000) := by
  exact
    packedTile65536 1272414464 1272545536 14 6269 35670 30 _ _ (2096417 / 100000) (104821 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272545536 :
    ThetaLowerSegment 1272545536 1272676608 (63625053752233 / 50000) (63631636533013 / 50000) := by
  exact
    packedTile65536 1272545536 1272676608 14 6280 35672 30 _ _ (2096427 / 100000) (209643 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272676608 :
    ThetaLowerSegment 1272676608 1272807680 (63631636533013 / 50000)
      (127276281457611 / 100000) := by
  exact
    packedTile65536 1272676608 1272807680 14 6205 35674 30 _ _ (2096437 / 100000) (52411 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272807680 :
    ThetaLowerSegment 1272807680 1272938752 (127276281457611 / 100000) (5091581072643 / 4000) := by
  exact
    packedTile65536 1272807680 1272938752 14 6318 35676 30 _ _ (65514 / 3125) (2096451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1272938752 :
    ThetaLowerSegment 1272938752 1273069824 (5091581072643 / 4000) (127302579363583 / 100000) := by
  exact
    packedTile65536 1272938752 1273069824 14 6226 35678 30 _ _ (1048229 / 50000) (2096461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1273069824 :
    ThetaLowerSegment 1273069824 1273200896 (127302579363583 / 100000)
      (25463110880807 / 20000) := by
  exact
    packedTile65536 1273069824 1273200896 14 6189 35680 30 _ _ (524117 / 25000) (2096471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1273200896 :
    ThetaLowerSegment 1273200896 1273331968 (25463110880807 / 20000)
      (127328705610529 / 100000) := by
  exact
    packedTile65536 1273200896 1273331968 14 6273 35681 30 _ _ (1048239 / 50000) (2096481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1273331968 :
    ThetaLowerSegment 1273331968 1273463040 (127328705610529 / 100000)
      (31835431725927 / 25000) := by
  exact
    packedTile65536 1273331968 1273463040 14 6211 35683 30 _ _ (2096489 / 100000) (524123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1273463040 :
    ThetaLowerSegment 1273463040 1273594112 (31835431725927 / 25000) (25470975648387 / 20000) := by
  exact
    packedTile65536 1273463040 1273594112 14 6273 35685 30 _ _ (2096499 / 100000) (1048251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1273594112 :
    ThetaLowerSegment 1273594112 1273725184 (25470975648387 / 20000) (63683966601739 / 50000) := by
  exact
    packedTile65536 1273594112 1273725184 14 6227 35687 30 _ _ (2096509 / 100000) (65516 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1273725184 :
    ThetaLowerSegment 1273725184 1273856256 (63683966601739 / 50000) (63690548626279 / 50000) := by
  exact
    packedTile65536 1273725184 1273856256 14 6279 35689 30 _ _ (52413 / 2500) (2096523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1273856256 :
    ThetaLowerSegment 1273856256 1273987328 (63690548626279 / 50000) (31848580016817 / 25000) := by
  exact
    packedTile65536 1273856256 1273987328 14 6307 35691 30 _ _ (209653 / 10000) (2096533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1273987328 :
    ThetaLowerSegment 1273987328 1274118400 (31848580016817 / 25000) (3981479296379 / 3125) := by
  exact
    packedTile65536 1273987328 1274118400 14 6209 35692 30 _ _ (104827 / 5000) (2096543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1274118400 :
    ThetaLowerSegment 1274118400 1274249472 (3981479296379 / 3125) (63710178532919 / 50000) := by
  exact
    packedTile65536 1274118400 1274249472 14 6210 35694 30 _ _ (2096551 / 100000) (1048277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1274249472 :
    ThetaLowerSegment 1274249472 1274380544 (63710178532919 / 50000)
      (127433638779773 / 100000) := by
  exact
    packedTile65536 1274249472 1274380544 14 6335 35696 30 _ _ (2096561 / 100000) (524141 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1274380544 :
    ThetaLowerSegment 1274380544 1274511616 (127433638779773 / 100000)
      (25489370274043 / 20000) := by
  exact
    packedTile65536 1274380544 1274511616 14 6302 35698 30 _ _ (2096571 / 100000) (1048287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1274511616 :
    ThetaLowerSegment 1274511616 1274642688 (25489370274043 / 20000) (31865004998869 / 25000) := by
  exact
    packedTile65536 1274511616 1274642688 14 6281 35700 30 _ _ (2096581 / 100000) (262073 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1274642688 :
    ThetaLowerSegment 1274642688 1274773760 (31865004998869 / 25000) (31868248950841 / 25000) := by
  exact
    packedTile65536 1274642688 1274773760 14 6189 35702 30 _ _ (131037 / 6250) (419319 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1274773760 :
    ThetaLowerSegment 1274773760 1274904832 (31868248950841 / 25000) (6374302672031 / 5000) := by
  exact
    packedTile65536 1274773760 1274904832 14 6228 35703 30 _ _ (1048301 / 50000) (419321 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1274904832 :
    ThetaLowerSegment 1274904832 1275035904 (6374302672031 / 5000) (1274989266383 / 1000) := by
  exact
    packedTile65536 1274904832 1275035904 14 6140 35705 30 _ _ (524153 / 25000) (419323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1275035904 :
    ThetaLowerSegment 1275035904 1275166976 (1274989266383 / 1000) (63756011072779 / 50000) := by
  exact
    packedTile65536 1275035904 1275166976 14 6246 35707 30 _ _ (2096623 / 100000) (1048313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1275166976 :
    ThetaLowerSegment 1275166976 1275298048 (63756011072779 / 50000) (63762590307133 / 50000) := by
  exact
    packedTile65536 1275166976 1275298048 14 6276 35709 30 _ _ (2096633 / 100000) (524159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1275298048 :
    ThetaLowerSegment 1275298048 1275429120 (63762590307133 / 50000) (63769136026579 / 50000) := by
  exact
    packedTile65536 1275298048 1275429120 14 6244 35711 30 _ _ (2096643 / 100000) (1048323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1275429120 :
    ThetaLowerSegment 1275429120 1275560192 (63769136026579 / 50000) (6377569226051 / 5000) := by
  exact
    packedTile65536 1275429120 1275560192 14 6254 35713 30 _ _ (2096653 / 100000) (131041 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1275560192 :
    ThetaLowerSegment 1275560192 1275691264 (6377569226051 / 5000) (31891132126909 / 25000) := by
  exact
    packedTile65536 1275560192 1275691264 14 6269 35714 30 _ _ (262083 / 12500) (2096667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1275691264 :
    ThetaLowerSegment 1275691264 1275822336 (31891132126909 / 25000) (31894451161851 / 25000) := by
  exact
    packedTile65536 1275691264 1275822336 14 6332 35716 30 _ _ (1048337 / 50000) (2096677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1275822336 :
    ThetaLowerSegment 1275822336 1275953408 (31894451161851 / 25000) (31897699973709 / 25000) := by
  exact
    packedTile65536 1275822336 1275953408 14 6198 35718 30 _ _ (524171 / 25000) (2096687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1275953408 :
    ThetaLowerSegment 1275953408 1276084480 (31897699973709 / 25000) (31900975009737 / 25000) := by
  exact
    packedTile65536 1275953408 1276084480 14 6248 35720 30 _ _ (1048347 / 50000) (2096697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276084480 :
    ThetaLowerSegment 1276084480 1276215552 (31900975009737 / 25000)
      (127616884933013 / 100000) := by
  exact
    packedTile65536 1276084480 1276215552 14 6193 35722 30 _ _ (419341 / 20000) (524177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276215552 :
    ThetaLowerSegment 1276215552 1276346624 (127616884933013 / 100000)
      (127629930693743 / 100000) := by
  exact
    packedTile65536 1276215552 1276346624 14 6222 35724 30 _ _ (419343 / 20000) (1048359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276346624 :
    ThetaLowerSegment 1276346624 1276477696 (127629930693743 / 100000) (3988845047349 / 3125) := by
  exact
    packedTile65536 1276346624 1276477696 14 6253 35725 30 _ _ (83869 / 4000) (262091 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276477696 :
    ThetaLowerSegment 1276477696 1276608768 (3988845047349 / 3125) (797850153153 / 625) := by
  exact
    packedTile65536 1276477696 1276608768 14 6192 35727 30 _ _ (65523 / 3125) (2096739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276608768 :
    ThetaLowerSegment 1276608768 1276674304 (797850153153 / 625) (63831296804849 / 50000) := by
  exact
    packedTile65536 1276608768 1276674304 13 3133 35729 30 _ _ (1048373 / 50000) (2096749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276674304 :
    ThetaLowerSegment 1276674304 1276739840 (63831296804849 / 50000) (25533834223517 / 20000) := by
  exact
    packedTile65536 1276674304 1276739840 13 3137 35730 30 _ _ (2096751 / 100000) (1048377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276739840 :
    ThetaLowerSegment 1276739840 1276805376 (25533834223517 / 20000)
      (127675683641721 / 100000) := by
  exact
    packedTile65536 1276739840 1276805376 13 3106 35731 30 _ _ (524189 / 25000) (2096759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276805376 :
    ThetaLowerSegment 1276805376 1276870912 (127675683641721 / 100000) (255364530749 / 200) := by
  exact
    packedTile65536 1276805376 1276870912 13 3139 35732 30 _ _ (2096761 / 100000) (524191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276870912 :
    ThetaLowerSegment 1276870912 1276936448 (255364530749 / 200) (6384442460987 / 5000) := by
  exact
    packedTile65536 1276870912 1276936448 13 3140 35733 30 _ _ (1048383 / 50000) (2096769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1276936448 :
    ThetaLowerSegment 1276936448 1277001984 (6384442460987 / 5000) (63847697669401 / 50000) := by
  exact
    packedTile65536 1276936448 1277001984 13 3122 35734 30 _ _ (2096771 / 100000) (1048387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277001984 :
    ThetaLowerSegment 1277001984 1277067520 (63847697669401 / 50000) (25540408005023 / 20000) := by
  exact
    packedTile65536 1277001984 1277067520 13 3169 35735 30 _ _ (2096777 / 100000) (104839 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277067520 :
    ThetaLowerSegment 1277067520 1277198592 (25540408005023 / 20000)
      (127715201525729 / 100000) := by
  exact
    packedTile65536 1277067520 1277198592 14 6277 35736 30 _ _ (1048391 / 50000) (419357 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277198592 :
    ThetaLowerSegment 1277198592 1277329664 (127715201525729 / 100000)
      (127728413412121 / 100000) := by
  exact
    packedTile65536 1277198592 1277329664 14 6301 35737 30 _ _ (262099 / 12500) (419359 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277329664 :
    ThetaLowerSegment 1277329664 1277460736 (127728413412121 / 100000) (5109658807927 / 4000) := by
  exact
    packedTile65536 1277329664 1277460736 14 6227 35739 30 _ _ (1048401 / 50000) (419361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277460736 :
    ThetaLowerSegment 1277460736 1277591808 (5109658807927 / 4000) (63877263526363 / 50000) := by
  exact
    packedTile65536 1277460736 1277591808 14 6227 35741 30 _ _ (2096813 / 100000) (131051 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277591808 :
    ThetaLowerSegment 1277591808 1277722880 (63877263526363 / 50000)
      (127767672036113 / 100000) := by
  exact
    packedTile65536 1277591808 1277722880 14 6269 35743 30 _ _ (2096823 / 100000) (1048413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277722880 :
    ThetaLowerSegment 1277722880 1277853952 (127767672036113 / 100000)
      (31945169672803 / 25000) := by
  exact
    packedTile65536 1277722880 1277853952 14 6203 35745 30 _ _ (2096833 / 100000) (524209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277853952 :
    ThetaLowerSegment 1277853952 1277985024 (31945169672803 / 25000)
      (127793727345201 / 100000) := by
  exact
    packedTile65536 1277853952 1277985024 14 6223 35747 30 _ _ (2096843 / 100000) (1048423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1277985024 :
    ThetaLowerSegment 1277985024 1278050560 (127793727345201 / 100000)
      (127800330338447 / 100000) := by
  exact
    packedTile65536 1277985024 1278050560 13 3149 35748 30 _ _ (1048427 / 50000) (2096857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278050560 :
    ThetaLowerSegment 1278050560 1278181632 (127800330338447 / 100000)
      (25562679592747 / 20000) := by
  exact
    packedTile65536 1278050560 1278181632 14 6232 35749 30 _ _ (2096859 / 100000) (1048431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278181632 :
    ThetaLowerSegment 1278181632 1278312704 (25562679592747 / 20000)
      (127826432101439 / 100000) := by
  exact
    packedTile65536 1278181632 1278312704 14 6216 35751 30 _ _ (2096869 / 100000) (262109 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278312704 :
    ThetaLowerSegment 1278312704 1278378240 (127826432101439 / 100000)
      (127832945007613 / 100000) := by
  exact
    packedTile65536 1278312704 1278378240 13 3106 35753 30 _ _ (2096879 / 100000) (1048441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278378240 :
    ThetaLowerSegment 1278378240 1278443776 (127832945007613 / 100000)
      (127839501963881 / 100000) := by
  exact
    packedTile65536 1278378240 1278443776 13 3127 35754 30 _ _ (524221 / 25000) (2096887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278443776 :
    ThetaLowerSegment 1278443776 1278509312 (127839501963881 / 100000)
      (127846107164231 / 100000) := by
  exact
    packedTile65536 1278443776 1278509312 13 3150 35755 30 _ _ (2096889 / 100000) (524223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278509312 :
    ThetaLowerSegment 1278509312 1278574848 (127846107164231 / 100000)
      (127852804646861 / 100000) := by
  exact
    packedTile65536 1278509312 1278574848 13 3194 35756 30 _ _ (419379 / 20000) (1048449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278574848 :
    ThetaLowerSegment 1278574848 1278705920 (127852804646861 / 100000)
      (127865968985061 / 100000) := by
  exact
    packedTile65536 1278574848 1278705920 14 6278 35757 30 _ _ (20969 / 1000) (2096903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278705920 :
    ThetaLowerSegment 1278705920 1278836992 (127865968985061 / 100000)
      (127879313720301 / 100000) := by
  exact
    packedTile65536 1278705920 1278836992 14 6364 35758 30 _ _ (209691 / 10000) (2096913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278836992 :
    ThetaLowerSegment 1278836992 1278968064 (127879313720301 / 100000)
      (127892442536421 / 100000) := by
  exact
    packedTile65536 1278836992 1278968064 14 6261 35760 30 _ _ (52423 / 2500) (2096923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1278968064 :
    ThetaLowerSegment 1278968064 1279099136 (127892442536421 / 100000)
      (127905334462061 / 100000) := by
  exact
    packedTile65536 1278968064 1279099136 14 6148 35762 30 _ _ (209693 / 10000) (2096933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1279099136 :
    ThetaLowerSegment 1279099136 1279230208 (127905334462061 / 100000)
      (63959252674241 / 50000) := by
  exact
    packedTile65536 1279099136 1279230208 14 6281 35764 30 _ _ (2096941 / 100000) (131059 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1279230208 :
    ThetaLowerSegment 1279230208 1279361280 (63959252674241 / 50000) (63965862263793 / 50000) := by
  exact
    packedTile65536 1279230208 1279361280 14 6304 35766 30 _ _ (2096951 / 100000) (1048477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1279361280 :
    ThetaLowerSegment 1279361280 1279492352 (63965862263793 / 50000)
      (127944841018641 / 100000) := by
  exact
    packedTile65536 1279361280 1279492352 14 6255 35768 30 _ _ (2096961 / 100000) (524241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1279492352 :
    ThetaLowerSegment 1279492352 1279623424 (127944841018641 / 100000)
      (25591574319287 / 20000) := by
  exact
    packedTile65536 1279492352 1279623424 14 6214 35769 30 _ _ (2096971 / 100000) (1048487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1279623424 :
    ThetaLowerSegment 1279623424 1279754496 (25591574319287 / 20000)
      (127971000800737 / 100000) := by
  exact
    packedTile65536 1279623424 1279754496 14 6261 35771 30 _ _ (1048491 / 50000) (419397 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1279754496 :
    ThetaLowerSegment 1279754496 1279885568 (127971000800737 / 100000)
      (127983993763169 / 100000) := by
  exact
    packedTile65536 1279754496 1279885568 14 6196 35773 30 _ _ (65531 / 3125) (419399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1279885568 :
    ThetaLowerSegment 1279885568 1280016640 (127983993763169 / 100000)
      (25599440136353 / 20000) := by
  exact
    packedTile65536 1279885568 1280016640 14 6298 35775 30 _ _ (1048501 / 50000) (419401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280016640 :
    ThetaLowerSegment 1280016640 1280147712 (25599440136353 / 20000)
      (128010332170909 / 100000) := by
  exact
    packedTile65536 1280016640 1280147712 14 6262 35777 30 _ _ (524253 / 25000) (419403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280147712 :
    ThetaLowerSegment 1280147712 1280278784 (128010332170909 / 100000)
      (25604713716017 / 20000) := by
  exact
    packedTile65536 1280147712 1280278784 14 6312 35779 30 _ _ (2097023 / 100000) (1048513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280278784 :
    ThetaLowerSegment 1280278784 1280409856 (25604713716017 / 20000) (25607343395399 / 20000) := by
  exact
    packedTile65536 1280278784 1280409856 14 6270 35780 30 _ _ (2097033 / 100000) (524259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280409856 :
    ThetaLowerSegment 1280409856 1280540928 (25607343395399 / 20000)
      (128049794137143 / 100000) := by
  exact
    packedTile65536 1280409856 1280540928 14 6236 35782 30 _ _ (2097043 / 100000) (1048523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280540928 :
    ThetaLowerSegment 1280540928 1280672000 (128049794137143 / 100000)
      (128062791671637 / 100000) := by
  exact
    packedTile65536 1280540928 1280672000 14 6198 35784 30 _ _ (2097053 / 100000) (65533 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280672000 :
    ThetaLowerSegment 1280672000 1280803072 (128062791671637 / 100000)
      (25615167920769 / 20000) := by
  exact
    packedTile65536 1280672000 1280803072 14 6222 35786 30 _ _ (262133 / 12500) (2097067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280803072 :
    ThetaLowerSegment 1280803072 1280934144 (25615167920769 / 20000)
      (128089002937343 / 100000) := by
  exact
    packedTile65536 1280803072 1280934144 14 6277 35788 30 _ _ (1048537 / 50000) (2097077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1280934144 :
    ThetaLowerSegment 1280934144 1281065216 (128089002937343 / 100000)
      (128102103421091 / 100000) := by
  exact
    packedTile65536 1280934144 1281065216 14 6247 35790 30 _ _ (524271 / 25000) (2097087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1281065216 :
    ThetaLowerSegment 1281065216 1281196288 (128102103421091 / 100000)
      (128115145248677 / 100000) := by
  exact
    packedTile65536 1281065216 1281196288 14 6219 35791 30 _ _ (1048547 / 50000) (2097097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1281196288 :
    ThetaLowerSegment 1281196288 1281327360 (128115145248677 / 100000)
      (128128172464937 / 100000) := by
  exact
    packedTile65536 1281196288 1281327360 14 6212 35793 30 _ _ (419421 / 20000) (524277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1281327360 :
    ThetaLowerSegment 1281327360 1281458432 (128128172464937 / 100000)
      (64070695290391 / 50000) := by
  exact
    packedTile65536 1281327360 1281458432 14 6303 35795 30 _ _ (419423 / 20000) (1048559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1281458432 :
    ThetaLowerSegment 1281458432 1281589504 (64070695290391 / 50000)
      (128154478737907 / 100000) := by
  exact
    packedTile65536 1281458432 1281589504 14 6241 35797 30 _ _ (16777 / 800) (262141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1281589504 :
    ThetaLowerSegment 1281589504 1281720576 (128154478737907 / 100000)
      (64083812838611 / 50000) := by
  exact
    packedTile65536 1281589504 1281720576 14 6269 35799 30 _ _ (419427 / 20000) (1048569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1281720576 :
    ThetaLowerSegment 1281720576 1281851648 (64083812838611 / 50000) (8011289510657 / 6250) := by
  exact
    packedTile65536 1281720576 1281851648 14 6202 35801 30 _ _ (419429 / 20000) (524287 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1281851648 :
    ThetaLowerSegment 1281851648 1281982720 (8011289510657 / 6250) (801211107152 / 625) := by
  exact
    packedTile65536 1281851648 1281982720 14 6268 35802 30 _ _ (524289 / 25000) (2097159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1281982720 :
    ThetaLowerSegment 1281982720 1282113792 (801211107152 / 625) (64103413904169 / 50000) := by
  exact
    packedTile65536 1281982720 1282113792 14 6223 35804 30 _ _ (1048583 / 50000) (2097169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282113792 :
    ThetaLowerSegment 1282113792 1282244864 (64103413904169 / 50000) (12821968769157 / 10000) := by
  exact
    packedTile65536 1282113792 1282244864 14 6132 35806 30 _ _ (262147 / 12500) (2097179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282244864 :
    ThetaLowerSegment 1282244864 1282310400 (12821968769157 / 10000) (801414664107 / 625) := by
  exact
    packedTile65536 1282244864 1282310400 13 3175 35808 30 _ _ (1048593 / 50000) (2097189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282310400 :
    ThetaLowerSegment 1282310400 1282441472 (801414664107 / 625) (12823957953233 / 10000) := by
  exact
    packedTile65536 1282310400 1282441472 14 6310 35809 30 _ _ (2097191 / 100000) (1048597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282441472 :
    ThetaLowerSegment 1282441472 1282572544 (12823957953233 / 10000) (16031589288557 / 12500) := by
  exact
    packedTile65536 1282441472 1282572544 14 6263 35811 30 _ _ (1048601 / 50000) (419441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282572544 :
    ThetaLowerSegment 1282572544 1282703616 (16031589288557 / 12500) (6413287633773 / 5000) := by
  exact
    packedTile65536 1282572544 1282703616 14 6217 35813 30 _ _ (524303 / 25000) (419443 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282703616 :
    ThetaLowerSegment 1282703616 1282834688 (6413287633773 / 5000) (64139357802321 / 50000) := by
  exact
    packedTile65536 1282703616 1282834688 14 6181 35814 30 _ _ (1048611 / 50000) (83889 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282834688 :
    ThetaLowerSegment 1282834688 1282965760 (64139357802321 / 50000) (2565834117193 / 2000) := by
  exact
    packedTile65536 1282834688 1282965760 14 6194 35816 30 _ _ (131077 / 6250) (419447 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1282965760 :
    ThetaLowerSegment 1282965760 1283031296 (2565834117193 / 2000) (12829829120267 / 10000) := by
  exact
    packedTile65536 1282965760 1283031296 13 3140 35818 30 _ _ (2097243 / 100000) (1048623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1283031296 :
    ThetaLowerSegment 1283031296 1283096832 (12829829120267 / 10000) (64152441426567 / 50000) := by
  exact
    packedTile65536 1283031296 1283096832 13 3143 35819 30 _ _ (65539 / 3125) (2097251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1283096832 :
    ThetaLowerSegment 1283096832 1283227904 (64152441426567 / 50000)
      (128318076671757 / 100000) := by
  exact
    packedTile65536 1283096832 1283227904 14 6291 35820 30 _ _ (2097253 / 100000) (262157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1283227904 :
    ThetaLowerSegment 1283227904 1283358976 (128318076671757 / 100000)
      (128331138425721 / 100000) := by
  exact
    packedTile65536 1283227904 1283358976 14 6228 35822 30 _ _ (2097263 / 100000) (1048633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1283358976 :
    ThetaLowerSegment 1283358976 1283490048 (128331138425721 / 100000)
      (25668877799307 / 20000) := by
  exact
    packedTile65536 1283358976 1283490048 14 6318 35824 30 _ _ (2097273 / 100000) (524319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1283490048 :
    ThetaLowerSegment 1283490048 1283621120 (25668877799307 / 20000) (64178730680737 / 50000) := by
  exact
    packedTile65536 1283490048 1283621120 14 6233 35825 30 _ _ (2097283 / 100000) (1048643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1283621120 :
    ThetaLowerSegment 1283621120 1283752192 (64178730680737 / 50000) (32092628205509 / 25000) := by
  exact
    packedTile65536 1283621120 1283752192 14 6223 35827 30 _ _ (1048647 / 50000) (2097297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1283752192 :
    ThetaLowerSegment 1283752192 1283883264 (32092628205509 / 25000) (32095909437617 / 25000) := by
  exact
    packedTile65536 1283752192 1283883264 14 6258 35829 30 _ _ (262163 / 12500) (2097307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1283883264 :
    ThetaLowerSegment 1283883264 1284014336 (32095909437617 / 25000) (12839675225491 / 10000) := by
  exact
    packedTile65536 1283883264 1284014336 14 6253 35831 30 _ _ (1048657 / 50000) (2097317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284014336 :
    ThetaLowerSegment 1284014336 1284145408 (12839675225491 / 10000) (64204927118969 / 50000) := by
  exact
    packedTile65536 1284014336 1284145408 14 6247 35833 30 _ _ (524331 / 25000) (2097327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284145408 :
    ThetaLowerSegment 1284145408 1284276480 (64204927118969 / 50000) (8026439748883 / 6250) := by
  exact
    packedTile65536 1284145408 1284276480 14 6285 35834 30 _ _ (1048667 / 50000) (2097337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284276480 :
    ThetaLowerSegment 1284276480 1284407552 (8026439748883 / 6250) (32109020367007 / 25000) := by
  exact
    packedTile65536 1284276480 1284407552 14 6220 35836 30 _ _ (419469 / 20000) (524337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284407552 :
    ThetaLowerSegment 1284407552 1284538624 (32109020367007 / 25000) (64224586578969 / 50000) := by
  exact
    packedTile65536 1284407552 1284538624 14 6242 35838 30 _ _ (419471 / 20000) (1048679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284538624 :
    ThetaLowerSegment 1284538624 1284669696 (64224586578969 / 50000)
      (128462409628453 / 100000) := by
  exact
    packedTile65536 1284538624 1284669696 14 6311 35840 30 _ _ (419473 / 20000) (262171 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284669696 :
    ThetaLowerSegment 1284669696 1284800768 (128462409628453 / 100000)
      (128475363016453 / 100000) := by
  exact
    packedTile65536 1284669696 1284800768 14 6176 35842 30 _ _ (16779 / 800) (1048689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284800768 :
    ThetaLowerSegment 1284800768 1284931840 (128475363016453 / 100000)
      (32122078592207 / 25000) := by
  exact
    packedTile65536 1284800768 1284931840 14 6175 35844 30 _ _ (419477 / 20000) (524347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284931840 :
    ThetaLowerSegment 1284931840 1284997376 (32122078592207 / 25000) (32123704074107 / 25000) := by
  exact
    packedTile65536 1284931840 1284997376 13 3100 35845 30 _ _ (524349 / 25000) (2097399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1284997376 :
    ThetaLowerSegment 1284997376 1285062912 (32123704074107 / 25000) (5140052477893 / 4000) := by
  exact
    packedTile65536 1284997376 1285062912 13 3097 35846 30 _ _ (2097401 / 100000) (524351 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285062912 :
    ThetaLowerSegment 1285062912 1285128448 (5140052477893 / 4000) (128507864243669 / 100000) := by
  exact
    packedTile65536 1285062912 1285128448 13 3124 35847 30 _ _ (1048703 / 50000) (2097409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285128448 :
    ThetaLowerSegment 1285128448 1285193984 (128507864243669 / 100000)
      (128514513036539 / 100000) := by
  exact
    packedTile65536 1285128448 1285193984 13 3170 35848 30 _ _ (2097411 / 100000) (1048707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285193984 :
    ThetaLowerSegment 1285193984 1285259520 (128514513036539 / 100000)
      (25704213911791 / 20000) := by
  exact
    packedTile65536 1285193984 1285259520 13 3126 35849 30 _ _ (262177 / 12500) (2097419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285259520 :
    ThetaLowerSegment 1285259520 1285325056 (25704213911791 / 20000) (3213189551279 / 2500) := by
  exact
    packedTile65536 1285259520 1285325056 13 3105 35850 30 _ _ (2097421 / 100000) (131089 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285325056 :
    ThetaLowerSegment 1285325056 1285390592 (3213189551279 / 2500) (8033384449337 / 6250) := by
  exact
    packedTile65536 1285325056 1285390592 13 3132 35851 30 _ _ (1048713 / 50000) (2097429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285390592 :
    ThetaLowerSegment 1285390592 1285456128 (8033384449337 / 6250) (128540735025301 / 100000) := by
  exact
    packedTile65536 1285390592 1285456128 13 3139 35852 30 _ _ (2097431 / 100000) (1048717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285456128 :
    ThetaLowerSegment 1285456128 1285521664 (128540735025301 / 100000)
      (128547232882029 / 100000) := by
  exact
    packedTile65536 1285456128 1285521664 13 3098 35853 30 _ _ (524359 / 25000) (2097439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285521664 :
    ThetaLowerSegment 1285521664 1285587200 (128547232882029 / 100000)
      (128553753829207 / 100000) := by
  exact
    packedTile65536 1285521664 1285587200 13 3109 35854 30 _ _ (1048721 / 50000) (419489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285587200 :
    ThetaLowerSegment 1285587200 1285652736 (128553753829207 / 100000)
      (64280091252131 / 50000) := by
  exact
    packedTile65536 1285587200 1285652736 13 3065 35855 30 _ _ (2097447 / 100000) (41949 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285652736 :
    ThetaLowerSegment 1285652736 1285718272 (64280091252131 / 50000) (64283379008141 / 50000) := by
  exact
    packedTile65536 1285652736 1285718272 13 3135 35856 30 _ _ (524363 / 25000) (419491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285718272 :
    ThetaLowerSegment 1285718272 1285783808 (64283379008141 / 50000) (25714676776589 / 20000) := by
  exact
    packedTile65536 1285718272 1285783808 13 3159 35856 30 _ _ (2097457 / 100000) (104873 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285783808 :
    ThetaLowerSegment 1285783808 1285849344 (25714676776589 / 20000) (25715981397953 / 20000) := by
  exact
    packedTile65536 1285783808 1285849344 13 3110 35857 30 _ _ (1048731 / 50000) (419493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285849344 :
    ThetaLowerSegment 1285849344 1285914880 (25715981397953 / 20000) (16073321330303 / 12500) := by
  exact
    packedTile65536 1285849344 1285914880 13 3177 35858 30 _ _ (2097467 / 100000) (209747 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285914880 :
    ThetaLowerSegment 1285914880 1285980416 (16073321330303 / 12500) (16074156386343 / 12500) := by
  exact
    packedTile65536 1285914880 1285980416 13 3185 35859 30 _ _ (65546 / 3125) (83899 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1285980416 :
    ThetaLowerSegment 1285980416 1286111488 (16074156386343 / 12500) (25721281712793 / 20000) := by
  exact
    packedTile65536 1285980416 1286111488 14 6273 35860 30 _ _ (2097477 / 100000) (52437 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1286111488 :
    ThetaLowerSegment 1286111488 1286242560 (25721281712793 / 20000) (8038722356873 / 6250) := by
  exact
    packedTile65536 1286111488 1286242560 14 6269 35862 30 _ _ (2097487 / 100000) (209749 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1286242560 :
    ThetaLowerSegment 1286242560 1286373632 (8038722356873 / 6250) (64316277952537 / 50000) := by
  exact
    packedTile65536 1286242560 1286373632 14 6197 35864 30 _ _ (1048749 / 50000) (2097501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1286373632 :
    ThetaLowerSegment 1286373632 1286504704 (64316277952537 / 50000) (64322928101651 / 50000) := by
  exact
    packedTile65536 1286373632 1286504704 14 6341 35866 30 _ _ (524377 / 25000) (2097511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1286504704 :
    ThetaLowerSegment 1286504704 1286635776 (64322928101651 / 50000) (64329535283351 / 50000) := by
  exact
    packedTile65536 1286504704 1286635776 14 6300 35867 30 _ _ (1048759 / 50000) (2097521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1286635776 :
    ThetaLowerSegment 1286635776 1286766848 (64329535283351 / 50000) (64336026083747 / 50000) := by
  exact
    packedTile65536 1286635776 1286766848 14 6189 35869 30 _ _ (262191 / 12500) (2097531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1286766848 :
    ThetaLowerSegment 1286766848 1286897920 (64336026083747 / 50000) (64342637523523 / 50000) := by
  exact
    packedTile65536 1286766848 1286897920 14 6304 35871 30 _ _ (1048769 / 50000) (2097541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1286897920 :
    ThetaLowerSegment 1286897920 1287028992 (64342637523523 / 50000)
      (128698420386629 / 100000) := by
  exact
    packedTile65536 1286897920 1287028992 14 6267 35873 30 _ _ (2097549 / 100000) (131097 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1287028992 :
    ThetaLowerSegment 1287028992 1287160064 (128698420386629 / 100000)
      (128711555301087 / 100000) := by
  exact
    packedTile65536 1287028992 1287160064 14 6262 35875 30 _ _ (2097559 / 100000) (1048781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1287160064 :
    ThetaLowerSegment 1287160064 1287291136 (128711555301087 / 100000)
      (16090578681083 / 12500) := by
  exact
    packedTile65536 1287160064 1287291136 14 6233 35877 30 _ _ (2097569 / 100000) (524393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1287291136 :
    ThetaLowerSegment 1287291136 1287422208 (16090578681083 / 12500)
      (128737846293943 / 100000) := by
  exact
    packedTile65536 1287291136 1287422208 14 6301 35878 30 _ _ (2097579 / 100000) (1048791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1287422208 :
    ThetaLowerSegment 1287422208 1287553280 (128737846293943 / 100000)
      (64375441404789 / 50000) := by
  exact
    packedTile65536 1287422208 1287553280 14 6215 35880 30 _ _ (2097589 / 100000) (262199 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1287553280 :
    ThetaLowerSegment 1287553280 1287684352 (64375441404789 / 50000) (64381893619313 / 50000) := by
  exact
    packedTile65536 1287553280 1287684352 14 6152 35882 30 _ _ (2097599 / 100000) (1048801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1287684352 :
    ThetaLowerSegment 1287684352 1287815424 (64381893619313 / 50000) (64388392015093 / 50000) := by
  exact
    packedTile65536 1287684352 1287815424 14 6196 35884 30 _ _ (209761 / 10000) (2097613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1287815424 :
    ThetaLowerSegment 1287815424 1287946496 (64388392015093 / 50000) (64394961760933 / 50000) := by
  exact
    packedTile65536 1287815424 1287946496 14 6264 35886 30 _ _ (104881 / 5000) (2097623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1287946496 :
    ThetaLowerSegment 1287946496 1288077568 (64394961760933 / 50000) (64401485390233 / 50000) := by
  exact
    packedTile65536 1287946496 1288077568 14 6220 35887 30 _ _ (209763 / 10000) (2097633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288077568 :
    ThetaLowerSegment 1288077568 1288208640 (64401485390233 / 50000) (64408040515233 / 50000) := by
  exact
    packedTile65536 1288077568 1288208640 14 6250 35889 30 _ _ (52441 / 2500) (2097643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288208640 :
    ThetaLowerSegment 1288208640 1288339712 (64408040515233 / 50000) (16103642887127 / 12500) := by
  exact
    packedTile65536 1288208640 1288339712 14 6227 35891 30 _ _ (41953 / 2000) (2097653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288339712 :
    ThetaLowerSegment 1288339712 1288470784 (16103642887127 / 12500)
      (128842268161893 / 100000) := by
  exact
    packedTile65536 1288339712 1288470784 14 6257 35893 30 _ _ (2097661 / 100000) (65552 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288470784 :
    ThetaLowerSegment 1288470784 1288601856 (128842268161893 / 100000) (8053467849179 / 6250) := by
  exact
    packedTile65536 1288470784 1288601856 14 6301 35895 30 _ _ (2097671 / 100000) (1048837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288601856 :
    ThetaLowerSegment 1288601856 1288732928 (8053467849179 / 6250) (64434239311489 / 50000) := by
  exact
    packedTile65536 1288601856 1288732928 14 6194 35897 30 _ _ (2097681 / 100000) (524421 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288732928 :
    ThetaLowerSegment 1288732928 1288864000 (64434239311489 / 50000)
      (128881616461711 / 100000) := by
  exact
    packedTile65536 1288732928 1288864000 14 6263 35898 30 _ _ (2097691 / 100000) (1048847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288864000 :
    ThetaLowerSegment 1288864000 1288995072 (128881616461711 / 100000)
      (64447385572341 / 50000) := by
  exact
    packedTile65536 1288864000 1288995072 14 6271 35900 30 _ _ (2097701 / 100000) (262213 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1288995072 :
    ThetaLowerSegment 1288995072 1289126144 (64447385572341 / 50000) (32226968361897 / 25000) := by
  exact
    packedTile65536 1288995072 1289126144 14 6246 35902 30 _ _ (2097711 / 100000) (1048857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289126144 :
    ThetaLowerSegment 1289126144 1289257216 (32226968361897 / 25000) (6446051937543 / 5000) := by
  exact
    packedTile65536 1289126144 1289257216 14 6276 35904 30 _ _ (1048861 / 50000) (83909 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289257216 :
    ThetaLowerSegment 1289257216 1289322752 (6446051937543 / 5000) (805796939088 / 625) := by
  exact
    packedTile65536 1289257216 1289322752 13 3085 35906 30 _ _ (524433 / 25000) (419547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289322752 :
    ThetaLowerSegment 1289322752 1289339136 (805796939088 / 625) (6446457324447 / 5000) := by
  exact
    packedTile65536 1289322752 1289339136 11 780 35907 30 _ _ (2097737 / 100000) (104887 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1289339136 :
    ThetaLowerSegment 1289339136 1289341184 (6446457324447 / 5000) (1611616691067 / 1250) := by
  exact
    packedTile65536 1289339136 1289341184 8 90 35907 30 _ _ (1048869 / 50000) (2097741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1257341184_1289341184 :
    ThetaLowerSegment 1257341184 1289341184 (15716094402221 / 12500) (1611616691067 / 1250) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1257341184 cell1257406720)
                    (ThetaLowerSegment.join cell1257472256 cell1257537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1257603328 cell1257668864)
                    (ThetaLowerSegment.join cell1257734400 cell1257799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1257865472 cell1257931008)
                    (ThetaLowerSegment.join cell1257996544 cell1258062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1258127616 cell1258193152)
                    (ThetaLowerSegment.join cell1258258688 cell1258324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1258389760 cell1258455296)
                    (ThetaLowerSegment.join cell1258520832 cell1258586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1258651904 cell1258717440)
                    (ThetaLowerSegment.join cell1258782976 cell1258848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1258914048 cell1258979584)
                    (ThetaLowerSegment.join cell1259045120 cell1259110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1259176192 cell1259241728)
                    (ThetaLowerSegment.join cell1259307264 cell1259372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1259438336 cell1259503872)
                    (ThetaLowerSegment.join cell1259569408 cell1259634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1259700480 cell1259766016)
                    (ThetaLowerSegment.join cell1259831552 cell1259897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1259962624 cell1260028160)
                    (ThetaLowerSegment.join cell1260093696 cell1260159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1260224768 cell1260290304)
                    (ThetaLowerSegment.join cell1260355840 cell1260421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1260486912 cell1260552448)
                    (ThetaLowerSegment.join cell1260617984 cell1260683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1260749056 cell1260814592)
                    (ThetaLowerSegment.join cell1260880128 cell1260945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1261011200 cell1261076736)
                    (ThetaLowerSegment.join cell1261142272 cell1261207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1261273344 cell1261338880)
                    (ThetaLowerSegment.join cell1261404416 cell1261469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1261535488 cell1261601024)
                    (ThetaLowerSegment.join cell1261666560 cell1261732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1261797632 cell1261863168)
                    (ThetaLowerSegment.join cell1261928704 cell1261994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1262059776 cell1262125312)
                    (ThetaLowerSegment.join cell1262190848 cell1262256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1262321920 cell1262387456)
                    (ThetaLowerSegment.join cell1262452992 cell1262518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1262584064 cell1262649600)
                    (ThetaLowerSegment.join cell1262715136 cell1262780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1262846208 cell1262911744)
                    (ThetaLowerSegment.join cell1262977280 cell1263042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1263108352 cell1263173888)
                    (ThetaLowerSegment.join cell1263239424 cell1263304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1263370496 cell1263436032)
                    (ThetaLowerSegment.join cell1263501568 cell1263567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1263632640 cell1263698176)
                    (ThetaLowerSegment.join cell1263763712 cell1263829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1263894784 cell1263960320)
                    (ThetaLowerSegment.join cell1264025856 cell1264091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1264156928 cell1264222464)
                    (ThetaLowerSegment.join cell1264288000 cell1264353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1264419072 cell1264484608)
                    (ThetaLowerSegment.join cell1264550144 cell1264615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1264681216 cell1264746752)
                    (ThetaLowerSegment.join cell1264812288 cell1264877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1264943360 cell1265008896)
                    (ThetaLowerSegment.join cell1265074432 cell1265139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1265205504 cell1265271040)
                    (ThetaLowerSegment.join cell1265336576 cell1265402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1265467648 cell1265533184)
                    (ThetaLowerSegment.join cell1265598720 cell1265664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1265729792 cell1265795328)
                    (ThetaLowerSegment.join cell1265860864 cell1265926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1265991936 cell1266057472)
                    (ThetaLowerSegment.join cell1266123008 cell1266188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1266254080 cell1266319616)
                    (ThetaLowerSegment.join cell1266385152 cell1266450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1266516224 cell1266581760)
                    (ThetaLowerSegment.join cell1266647296 cell1266712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1266778368 cell1266843904)
                    (ThetaLowerSegment.join cell1266909440 cell1266974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1267040512 cell1267106048)
                    (ThetaLowerSegment.join cell1267171584 cell1267237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1267302656 cell1267368192)
                    (ThetaLowerSegment.join cell1267433728 cell1267499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1267564800 cell1267630336)
                    (ThetaLowerSegment.join cell1267695872 cell1267761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1267826944 cell1267892480)
                    (ThetaLowerSegment.join cell1267958016 cell1268023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1268154624 cell1268285696)
                    (ThetaLowerSegment.join cell1268351232 cell1268416768)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1268482304 cell1268613376)
                    (ThetaLowerSegment.join cell1268744448 cell1268875520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1269006592 cell1269137664)
                    (ThetaLowerSegment.join cell1269268736 cell1269399808))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1269530880 cell1269661952)
                    (ThetaLowerSegment.join cell1269793024 cell1269924096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1270055168 cell1270186240)
                    (ThetaLowerSegment.join cell1270317312 cell1270448384)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1270579456 cell1270710528)
                    (ThetaLowerSegment.join cell1270841600 cell1270972672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1271103744 cell1271234816)
                    (ThetaLowerSegment.join cell1271365888 cell1271496960))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1271628032 cell1271759104)
                    (ThetaLowerSegment.join cell1271890176 cell1272021248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1272152320 cell1272283392)
                    (ThetaLowerSegment.join cell1272414464 cell1272545536)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1272676608 cell1272807680)
                    (ThetaLowerSegment.join cell1272938752 cell1273069824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1273200896 cell1273331968)
                    (ThetaLowerSegment.join cell1273463040 cell1273594112))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1273725184 cell1273856256)
                    (ThetaLowerSegment.join cell1273987328 cell1274118400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1274249472 cell1274380544)
                    (ThetaLowerSegment.join cell1274511616 cell1274642688)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1274773760 cell1274904832)
                    (ThetaLowerSegment.join cell1275035904 cell1275166976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1275298048 cell1275429120)
                    (ThetaLowerSegment.join cell1275560192 cell1275691264)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1275822336 cell1275953408)
                    (ThetaLowerSegment.join cell1276084480 cell1276215552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1276346624 cell1276477696)
                    (ThetaLowerSegment.join cell1276608768 cell1276674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1276739840 cell1276805376)
                    (ThetaLowerSegment.join cell1276870912 cell1276936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1277001984 cell1277067520)
                    (ThetaLowerSegment.join cell1277198592 cell1277329664))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1277460736 cell1277591808)
                    (ThetaLowerSegment.join cell1277722880 cell1277853952))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1277985024 cell1278050560)
                    (ThetaLowerSegment.join cell1278181632 cell1278312704)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1278378240 cell1278443776)
                    (ThetaLowerSegment.join cell1278509312 cell1278574848))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1278705920 cell1278836992)
                    (ThetaLowerSegment.join cell1278968064 cell1279099136))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1279230208 cell1279361280)
                  (ThetaLowerSegment.join cell1279492352 cell1279623424))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1279754496 cell1279885568)
                  (ThetaLowerSegment.join cell1280016640 cell1280147712)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1280278784 cell1280409856)
                  (ThetaLowerSegment.join cell1280540928 cell1280672000))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1280803072 cell1280934144)
                  (ThetaLowerSegment.join cell1281065216 cell1281196288))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1281327360 cell1281458432)
                  (ThetaLowerSegment.join cell1281589504 cell1281720576))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1281851648 cell1281982720)
                  (ThetaLowerSegment.join cell1282113792 cell1282244864)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1282310400 cell1282441472)
                  (ThetaLowerSegment.join cell1282572544 cell1282703616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1282834688 cell1282965760)
                  (ThetaLowerSegment.join cell1283031296 cell1283096832)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1283227904 cell1283358976)
                  (ThetaLowerSegment.join cell1283490048 cell1283621120))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1283752192 cell1283883264)
                  (ThetaLowerSegment.join cell1284014336 cell1284145408)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1284276480 cell1284407552)
                  (ThetaLowerSegment.join cell1284538624 cell1284669696))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1284800768 cell1284931840)
                  (ThetaLowerSegment.join cell1284997376 cell1285062912))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1285128448 cell1285193984)
                  (ThetaLowerSegment.join cell1285259520 cell1285325056))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1285390592 cell1285456128)
                  (ThetaLowerSegment.join cell1285521664 cell1285587200)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1285652736 cell1285718272)
                  (ThetaLowerSegment.join cell1285783808 cell1285849344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1285914880 cell1285980416)
                  (ThetaLowerSegment.join cell1286111488 cell1286242560))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1286373632 cell1286504704)
                (ThetaLowerSegment.join cell1286635776 cell1286766848))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1286897920 cell1287028992)
                (ThetaLowerSegment.join cell1287160064 cell1287291136)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1287422208 cell1287553280)
                (ThetaLowerSegment.join cell1287684352 cell1287815424))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1287946496 cell1288077568)
                (ThetaLowerSegment.join cell1288208640 cell1288339712))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1288470784 cell1288601856)
                (ThetaLowerSegment.join cell1288732928 cell1288864000))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1288995072 cell1289126144)
                (ThetaLowerSegment.join cell1289257216 cell1289322752)))
            cell1289339136))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
