/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 1001341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell969341184 :
    ThetaLowerSegment 969341184 969406720 (12116309513907 / 12500) (6058565495337 / 6250) := by
  exact
    packedTile32768 969341184 969406720 13 3176 31134 30 _ _ (2069211 / 100000) (1034607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969406720 :
    ThetaLowerSegment 969406720 969472256 (6058565495337 / 6250) (48471790223309 / 50000) := by
  exact
    packedTile32768 969406720 969472256 13 3157 31135 30 _ _ (1034609 / 50000) (2069221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969472256 :
    ThetaLowerSegment 969472256 969537792 (48471790223309 / 50000) (96950117128393 / 100000) := by
  exact
    packedTile32768 969472256 969537792 13 3159 31136 30 _ _ (82769 / 4000) (517307 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969537792 :
    ThetaLowerSegment 969537792 969603328 (96950117128393 / 100000) (96956693147689 / 100000) := by
  exact
    packedTile32768 969537792 969603328 13 3178 31137 30 _ _ (129327 / 6250) (413847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969603328 :
    ThetaLowerSegment 969603328 969668864 (96956693147689 / 100000) (96963304363099 / 100000) := by
  exact
    packedTile32768 969603328 969668864 13 3195 31138 30 _ _ (1034619 / 50000) (2069241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969668864 :
    ThetaLowerSegment 969668864 969734400 (96963304363099 / 100000) (3030306629332 / 3125) := by
  exact
    packedTile32768 969668864 969734400 13 3145 31139 30 _ _ (413849 / 20000) (64664 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969734400 :
    ThetaLowerSegment 969734400 969799936 (3030306629332 / 3125) (12122041285303 / 12500) := by
  exact
    packedTile32768 969734400 969799936 13 3150 31140 30 _ _ (517313 / 25000) (413851 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969799936 :
    ThetaLowerSegment 969799936 969865472 (12122041285303 / 12500) (96982912595303 / 100000) := by
  exact
    packedTile32768 969799936 969865472 13 3181 31141 30 _ _ (2069259 / 100000) (1034631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969865472 :
    ThetaLowerSegment 969865472 969931008 (96982912595303 / 100000) (6061844984903 / 6250) := by
  exact
    packedTile32768 969865472 969931008 13 3193 31142 30 _ _ (413853 / 20000) (517317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969931008 :
    ThetaLowerSegment 969931008 969996544 (6061844984903 / 6250) (606224926892 / 625) := by
  exact
    packedTile32768 969931008 969996544 13 3126 31143 30 _ _ (258659 / 12500) (82771 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969996544 :
    ThetaLowerSegment 969996544 970062080 (606224926892 / 625) (19400503375593 / 20000) := by
  exact
    packedTile32768 969996544 970062080 13 3155 31144 30 _ _ (2069279 / 100000) (1034641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970062080 :
    ThetaLowerSegment 970062080 970127616 (19400503375593 / 20000) (97009057891011 / 100000) := by
  exact
    packedTile32768 970062080 970127616 13 3161 31145 30 _ _ (1034643 / 50000) (2069289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970127616 :
    ThetaLowerSegment 970127616 970193152 (97009057891011 / 100000) (97015739634879 / 100000) := by
  exact
    packedTile32768 970127616 970193152 13 3229 31146 30 _ _ (517323 / 25000) (413859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970193152 :
    ThetaLowerSegment 970193152 970258688 (97015739634879 / 100000) (3880890648157 / 4000) := by
  exact
    packedTile32768 970193152 970258688 13 3154 31147 30 _ _ (2069299 / 100000) (1034651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970258688 :
    ThetaLowerSegment 970258688 970324224 (3880890648157 / 4000) (19405769319401 / 20000) := by
  exact
    packedTile32768 970258688 970324224 13 3180 31148 30 _ _ (1034653 / 50000) (2069309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970324224 :
    ThetaLowerSegment 970324224 970389760 (19405769319401 / 20000) (97035418735093 / 100000) := by
  exact
    packedTile32768 970324224 970389760 13 3176 31150 30 _ _ (2069313 / 100000) (517329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970389760 :
    ThetaLowerSegment 970389760 970455296 (97035418735093 / 100000) (48521006827373 / 50000) := by
  exact
    packedTile32768 970389760 970455296 13 3187 31151 30 _ _ (2069319 / 100000) (1034661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970455296 :
    ThetaLowerSegment 970455296 970520832 (48521006827373 / 50000) (48524354996841 / 50000) := by
  exact
    packedTile32768 970455296 970520832 13 3236 31152 30 _ _ (1034663 / 50000) (2069329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970520832 :
    ThetaLowerSegment 970520832 970586368 (48524354996841 / 50000) (19411050231059 / 20000) := by
  exact
    packedTile32768 970520832 970586368 13 3161 31153 30 _ _ (2069333 / 100000) (258667 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970586368 :
    ThetaLowerSegment 970586368 970651904 (19411050231059 / 20000) (19412330324783 / 20000) := by
  exact
    packedTile32768 970586368 970651904 13 3093 31154 30 _ _ (103467 / 5000) (2069343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970651904 :
    ThetaLowerSegment 970651904 970717440 (19412330324783 / 20000) (97068176271853 / 100000) := by
  exact
    packedTile32768 970651904 970717440 13 3153 31155 30 _ _ (1034673 / 50000) (2069349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970717440 :
    ThetaLowerSegment 970717440 970782976 (97068176271853 / 100000) (19414973711891 / 20000) := by
  exact
    packedTile32768 970717440 970782976 13 3234 31156 30 _ _ (2069353 / 100000) (517339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970782976 :
    ThetaLowerSegment 970782976 970848512 (19414973711891 / 20000) (19416284030643 / 20000) := by
  exact
    packedTile32768 970782976 970848512 13 3166 31157 30 _ _ (25867 / 1250) (2069363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970848512 :
    ThetaLowerSegment 970848512 970914048 (19416284030643 / 20000) (97088009017743 / 100000) := by
  exact
    packedTile32768 970848512 970914048 13 3184 31158 30 _ _ (2069367 / 100000) (206937 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970914048 :
    ThetaLowerSegment 970914048 970979584 (97088009017743 / 100000) (48547268944779 / 50000) := by
  exact
    packedTile32768 970914048 970979584 13 3155 31159 30 _ _ (2069373 / 100000) (64668 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell970979584 :
    ThetaLowerSegment 970979584 971045120 (48547268944779 / 50000) (48550552016149 / 50000) := by
  exact
    packedTile32768 970979584 971045120 13 3173 31160 30 _ _ (103469 / 5000) (2069383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971045120 :
    ThetaLowerSegment 971045120 971110656 (48550552016149 / 50000) (48553771982321 / 50000) := by
  exact
    packedTile32768 971045120 971110656 13 3112 31161 30 _ _ (2069387 / 100000) (206939 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971110656 :
    ThetaLowerSegment 971110656 971176192 (48553771982321 / 50000) (12139269459809 / 12500) := by
  exact
    packedTile32768 971110656 971176192 13 3195 31162 30 _ _ (1034697 / 50000) (2069397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971176192 :
    ThetaLowerSegment 971176192 971241728 (12139269459809 / 12500) (6070034512117 / 6250) := by
  exact
    packedTile32768 971176192 971241728 13 3091 31163 30 _ _ (10347 / 500) (2069403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971241728 :
    ThetaLowerSegment 971241728 971307264 (6070034512117 / 6250) (97127122561097 / 100000) := by
  exact
    packedTile32768 971241728 971307264 13 3175 31164 30 _ _ (2069407 / 100000) (206941 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971307264 :
    ThetaLowerSegment 971307264 971372800 (97127122561097 / 100000) (97133630868127 / 100000) := by
  exact
    packedTile32768 971307264 971372800 13 3145 31165 30 _ _ (1034707 / 50000) (2069417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971372800 :
    ThetaLowerSegment 971372800 971438336 (97133630868127 / 100000) (12142518434357 / 12500) := by
  exact
    packedTile32768 971372800 971438336 13 3149 31166 30 _ _ (2069421 / 100000) (129339 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971438336 :
    ThetaLowerSegment 971438336 971503872 (12142518434357 / 12500) (97146730322143 / 100000) := by
  exact
    packedTile32768 971438336 971503872 13 3181 31167 30 _ _ (2069427 / 100000) (206943 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971503872 :
    ThetaLowerSegment 971503872 971569408 (97146730322143 / 100000) (97153280080753 / 100000) := by
  exact
    packedTile32768 971503872 971569408 13 3165 31168 30 _ _ (1034717 / 50000) (2069437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971569408 :
    ThetaLowerSegment 971569408 971634944 (97153280080753 / 100000) (19431964730639 / 20000) := by
  exact
    packedTile32768 971569408 971634944 13 3162 31170 30 _ _ (2069441 / 100000) (517361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971634944 :
    ThetaLowerSegment 971634944 971700480 (19431964730639 / 20000) (19433295385703 / 20000) := by
  exact
    packedTile32768 971634944 971700480 13 3215 31171 30 _ _ (258681 / 12500) (2069451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971700480 :
    ThetaLowerSegment 971700480 971766016 (19433295385703 / 20000) (97173032958787 / 100000) := by
  exact
    packedTile32768 971700480 971766016 13 3168 31172 30 _ _ (1034727 / 50000) (2069457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971766016 :
    ThetaLowerSegment 971766016 971831552 (97173032958787 / 100000) (97179539344171 / 100000) := by
  exact
    packedTile32768 971766016 971831552 13 3144 31173 30 _ _ (2069461 / 100000) (258683 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971831552 :
    ThetaLowerSegment 971831552 971897088 (97179539344171 / 100000) (97186056098903 / 100000) := by
  exact
    packedTile32768 971831552 971897088 13 3149 31174 30 _ _ (517367 / 25000) (2069471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971897088 :
    ThetaLowerSegment 971897088 971962624 (97186056098903 / 100000) (97192632890453 / 100000) := by
  exact
    packedTile32768 971897088 971962624 13 3178 31175 30 _ _ (82779 / 4000) (1034739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell971962624 :
    ThetaLowerSegment 971962624 972028160 (97192632890453 / 100000) (9719920763159 / 10000) := by
  exact
    packedTile32768 971962624 972028160 13 3177 31176 30 _ _ (2069481 / 100000) (517371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972028160 :
    ThetaLowerSegment 972028160 972093696 (9719920763159 / 10000) (48602913961851 / 50000) := by
  exact
    packedTile32768 972028160 972093696 13 3199 31177 30 _ _ (129343 / 6250) (2069491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972093696 :
    ThetaLowerSegment 972093696 972159232 (48602913961851 / 50000) (48606171346981 / 50000) := by
  exact
    packedTile32768 972093696 972159232 13 3148 31178 30 _ _ (413899 / 20000) (1034749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972159232 :
    ThetaLowerSegment 972159232 972224768 (48606171346981 / 50000) (1215235744447 / 1250) := by
  exact
    packedTile32768 972159232 972224768 13 3149 31179 30 _ _ (1034751 / 50000) (413901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972224768 :
    ThetaLowerSegment 972224768 972290304 (1215235744447 / 1250) (1215316455259 / 1250) := by
  exact
    packedTile32768 972224768 972290304 13 3120 31180 30 _ _ (517377 / 25000) (2069511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972290304 :
    ThetaLowerSegment 972290304 972355840 (1215316455259 / 1250) (19446360870049 / 20000) := by
  exact
    packedTile32768 972290304 972355840 13 3135 31181 30 _ _ (413903 / 20000) (1034759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972355840 :
    ThetaLowerSegment 972355840 972421376 (19446360870049 / 20000) (3889538314539 / 4000) := by
  exact
    packedTile32768 972355840 972421376 13 3215 31182 30 _ _ (1034761 / 50000) (82781 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972421376 :
    ThetaLowerSegment 972421376 972486912 (3889538314539 / 4000) (97245088631187 / 100000) := by
  exact
    packedTile32768 972421376 972486912 13 3204 31183 30 _ _ (258691 / 12500) (2069531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972486912 :
    ThetaLowerSegment 972486912 972552448 (97245088631187 / 100000) (97251665613417 / 100000) := by
  exact
    packedTile32768 972486912 972552448 13 3178 31184 30 _ _ (413907 / 20000) (1034769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972552448 :
    ThetaLowerSegment 972552448 972617984 (97251665613417 / 100000) (97258145349419 / 100000) := by
  exact
    packedTile32768 972552448 972617984 13 3131 31185 30 _ _ (1034771 / 50000) (413909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972617984 :
    ThetaLowerSegment 972617984 972683520 (97258145349419 / 100000) (97264685124259 / 100000) := by
  exact
    packedTile32768 972617984 972683520 13 3160 31186 30 _ _ (2069549 / 100000) (129347 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972683520 :
    ThetaLowerSegment 972683520 972749056 (97264685124259 / 100000) (24317787086131 / 25000) := by
  exact
    packedTile32768 972683520 972749056 13 3123 31187 30 _ _ (413911 / 20000) (1034779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972749056 :
    ThetaLowerSegment 972749056 972814592 (24317787086131 / 25000) (24319434457483 / 25000) := by
  exact
    packedTile32768 972749056 972814592 13 3184 31188 30 _ _ (1034781 / 50000) (413913 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972814592 :
    ThetaLowerSegment 972814592 972880128 (24319434457483 / 25000) (48642107790451 / 50000) := by
  exact
    packedTile32768 972814592 972880128 13 3130 31189 30 _ _ (2069569 / 100000) (517393 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972880128 :
    ThetaLowerSegment 972880128 972945664 (48642107790451 / 50000) (48645399451079 / 50000) := by
  exact
    packedTile32768 972880128 972945664 13 3181 31191 30 _ _ (258697 / 12500) (2069579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell972945664 :
    ThetaLowerSegment 972945664 973011200 (48645399451079 / 50000) (24324312447313 / 25000) := by
  exact
    packedTile32768 972945664 973011200 13 3117 31192 30 _ _ (1034791 / 50000) (413917 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973011200 :
    ThetaLowerSegment 973011200 973076736 (24324312447313 / 25000) (97303837291039 / 100000) := by
  exact
    packedTile32768 973011200 973076736 13 3183 31193 30 _ _ (2069589 / 100000) (258699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973076736 :
    ThetaLowerSegment 973076736 973142272 (97303837291039 / 100000) (97310232342679 / 100000) := by
  exact
    packedTile32768 973076736 973142272 13 3090 31194 30 _ _ (517399 / 25000) (2069599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973142272 :
    ThetaLowerSegment 973142272 973207808 (97310232342679 / 100000) (3041147775828 / 3125) := by
  exact
    packedTile32768 973142272 973207808 13 3139 31195 30 _ _ (2069603 / 100000) (1034803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973207808 :
    ThetaLowerSegment 973207808 973273344 (3041147775828 / 3125) (24330831684997 / 25000) := by
  exact
    packedTile32768 973207808 973273344 13 3188 31196 30 _ _ (2069609 / 100000) (517403 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973273344 :
    ThetaLowerSegment 973273344 973338880 (24330831684997 / 25000) (24332452711729 / 25000) := by
  exact
    packedTile32768 973273344 973338880 13 3133 31197 30 _ _ (129351 / 6250) (2069619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973338880 :
    ThetaLowerSegment 973338880 973404416 (24332452711729 / 25000) (97336456406369 / 100000) := by
  exact
    packedTile32768 973338880 973404416 13 3211 31198 30 _ _ (2069623 / 100000) (1034813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973404416 :
    ThetaLowerSegment 973404416 973469952 (97336456406369 / 100000) (97342973671239 / 100000) := by
  exact
    packedTile32768 973404416 973469952 13 3149 31199 30 _ _ (206963 / 10000) (2069633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973469952 :
    ThetaLowerSegment 973469952 973535488 (97342973671239 / 100000) (3893986012679 / 4000) := by
  exact
    packedTile32768 973469952 973535488 13 3226 31200 30 _ _ (517409 / 25000) (2069639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973535488 :
    ThetaLowerSegment 973535488 973601024 (3893986012679 / 4000) (9735624212993 / 10000) := by
  exact
    packedTile32768 973535488 973601024 13 3185 31201 30 _ _ (2069643 / 100000) (1034823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973601024 :
    ThetaLowerSegment 973601024 973666560 (9735624212993 / 10000) (9736283603483 / 10000) := by
  exact
    packedTile32768 973601024 973666560 13 3186 31202 30 _ _ (41393 / 2000) (2069653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973666560 :
    ThetaLowerSegment 973666560 973732096 (9736283603483 / 10000) (48684683934583 / 50000) := by
  exact
    packedTile32768 973666560 973732096 13 3156 31203 30 _ _ (258707 / 12500) (2069659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973732096 :
    ThetaLowerSegment 973732096 973797632 (48684683934583 / 50000) (48687987116731 / 50000) := by
  exact
    packedTile32768 973732096 973797632 13 3192 31204 30 _ _ (2069663 / 100000) (1034833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973797632 :
    ThetaLowerSegment 973797632 973863168 (48687987116731 / 50000) (48691238568301 / 50000) := by
  exact
    packedTile32768 973797632 973863168 13 3142 31205 30 _ _ (206967 / 10000) (2069673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973863168 :
    ThetaLowerSegment 973863168 973928704 (48691238568301 / 50000) (97389048361077 / 100000) := by
  exact
    packedTile32768 973863168 973928704 13 3175 31206 30 _ _ (2069677 / 100000) (25871 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973928704 :
    ThetaLowerSegment 973928704 973994240 (97389048361077 / 100000) (6087220274949 / 6250) := by
  exact
    packedTile32768 973928704 973994240 13 3129 31207 30 _ _ (2069683 / 100000) (1034843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell973994240 :
    ThetaLowerSegment 973994240 974059776 (6087220274949 / 6250) (48701035414327 / 50000) := by
  exact
    packedTile32768 973994240 974059776 13 3163 31208 30 _ _ (206969 / 10000) (2069693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974059776 :
    ThetaLowerSegment 974059776 974125312 (48701035414327 / 50000) (2435216208143 / 2500) := by
  exact
    packedTile32768 974059776 974125312 13 3178 31209 30 _ _ (2069697 / 100000) (20697 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974125312 :
    ThetaLowerSegment 974125312 974190848 (2435216208143 / 2500) (12176904782907 / 12500) := by
  exact
    packedTile32768 974125312 974190848 13 3184 31210 30 _ _ (258713 / 12500) (2069707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974190848 :
    ThetaLowerSegment 974190848 974256384 (12176904782907 / 12500) (24355420835049 / 25000) := by
  exact
    packedTile32768 974190848 974256384 13 3114 31212 30 _ _ (206971 / 10000) (2069713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974256384 :
    ThetaLowerSegment 974256384 974321920 (24355420835049 / 25000) (48714138729279 / 50000) := by
  exact
    packedTile32768 974256384 974321920 13 3186 31213 30 _ _ (2069717 / 100000) (51743 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974321920 :
    ThetaLowerSegment 974321920 974387456 (48714138729279 / 50000) (48717397509717 / 50000) := by
  exact
    packedTile32768 974321920 974387456 13 3149 31214 30 _ _ (517431 / 25000) (2069727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974387456 :
    ThetaLowerSegment 974387456 974452992 (48717397509717 / 50000) (24360334358991 / 25000) := by
  exact
    packedTile32768 974387456 974452992 13 3161 31215 30 _ _ (206973 / 10000) (2069733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974452992 :
    ThetaLowerSegment 974452992 974518528 (24360334358991 / 25000) (48723920274809 / 50000) := by
  exact
    packedTile32768 974452992 974518528 13 3142 31216 30 _ _ (2069737 / 100000) (103487 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974518528 :
    ThetaLowerSegment 974518528 974584064 (48723920274809 / 50000) (9745443889349 / 10000) := by
  exact
    packedTile32768 974518528 974584064 13 3188 31217 30 _ _ (129359 / 6250) (2069747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974584064 :
    ThetaLowerSegment 974584064 974649600 (9745443889349 / 10000) (48730439979301 / 50000) := by
  exact
    packedTile32768 974584064 974649600 13 3112 31218 30 _ _ (2069751 / 100000) (1034877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974649600 :
    ThetaLowerSegment 974649600 974715136 (48730439979301 / 50000) (48733747450987 / 50000) := by
  exact
    packedTile32768 974649600 974715136 13 3196 31219 30 _ _ (2069757 / 100000) (12936 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974715136 :
    ThetaLowerSegment 974715136 974780672 (48733747450987 / 50000) (9747412642583 / 10000) := by
  exact
    packedTile32768 974715136 974780672 13 3204 31220 30 _ _ (517441 / 25000) (2069767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974780672 :
    ThetaLowerSegment 974780672 974846208 (9747412642583 / 10000) (97480611018373 / 100000) := by
  exact
    packedTile32768 974780672 974846208 13 3133 31221 30 _ _ (2069771 / 100000) (1034887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974846208 :
    ThetaLowerSegment 974846208 974911744 (97480611018373 / 100000) (3899492187217 / 4000) := by
  exact
    packedTile32768 974846208 974911744 13 3234 31222 30 _ _ (1034889 / 50000) (2069781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974911744 :
    ThetaLowerSegment 974911744 974977280 (3899492187217 / 4000) (97493870035273 / 100000) := by
  exact
    packedTile32768 974911744 974977280 13 3172 31223 30 _ _ (258723 / 12500) (2069787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell974977280 :
    ThetaLowerSegment 974977280 975042816 (97493870035273 / 100000) (97500344341521 / 100000) := by
  exact
    packedTile32768 974977280 975042816 13 3128 31224 30 _ _ (2069791 / 100000) (1034897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975042816 :
    ThetaLowerSegment 975042816 975108352 (97500344341521 / 100000) (97506928368959 / 100000) := by
  exact
    packedTile32768 975042816 975108352 13 3181 31225 30 _ _ (1034899 / 50000) (2069801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975108352 :
    ThetaLowerSegment 975108352 975173888 (97506928368959 / 100000) (97513553811563 / 100000) := by
  exact
    packedTile32768 975108352 975173888 13 3201 31226 30 _ _ (517451 / 25000) (2069807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975173888 :
    ThetaLowerSegment 975173888 975239424 (97513553811563 / 100000) (19503999012679 / 20000) := by
  exact
    packedTile32768 975173888 975239424 13 3112 31227 30 _ _ (2069811 / 100000) (1034907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975239424 :
    ThetaLowerSegment 975239424 975304960 (19503999012679 / 20000) (19505288509293 / 20000) := by
  exact
    packedTile32768 975239424 975304960 13 3115 31228 30 _ _ (1034909 / 50000) (2069821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975304960 :
    ThetaLowerSegment 975304960 975370496 (19505288509293 / 20000) (19506603262133 / 20000) := by
  exact
    packedTile32768 975304960 975370496 13 3176 31229 30 _ _ (82793 / 4000) (517457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975370496 :
    ThetaLowerSegment 975370496 975436032 (19506603262133 / 20000) (24384879412459 / 25000) := by
  exact
    packedTile32768 975370496 975436032 13 3141 31230 30 _ _ (2069831 / 100000) (1034917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975436032 :
    ThetaLowerSegment 975436032 975501568 (24384879412459 / 25000) (9754608524581 / 10000) := by
  exact
    packedTile32768 975436032 975501568 13 3173 31231 30 _ _ (1034919 / 50000) (2069841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975501568 :
    ThetaLowerSegment 975501568 975567104 (9754608524581 / 10000) (243881471747 / 250) := by
  exact
    packedTile32768 975501568 975567104 13 3142 31233 30 _ _ (413969 / 20000) (258731 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975567104 :
    ThetaLowerSegment 975567104 975632640 (243881471747 / 250) (48779529526513 / 50000) := by
  exact
    packedTile32768 975567104 975632640 13 3126 31234 30 _ _ (2069851 / 100000) (1034927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975632640 :
    ThetaLowerSegment 975632640 975698176 (48779529526513 / 50000) (48782820600733 / 50000) := by
  exact
    packedTile32768 975632640 975698176 13 3180 31235 30 _ _ (1034929 / 50000) (2069861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975698176 :
    ThetaLowerSegment 975698176 975763712 (48782820600733 / 50000) (97572188184461 / 100000) := by
  exact
    packedTile32768 975698176 975763712 13 3163 31236 30 _ _ (413973 / 20000) (517467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975763712 :
    ThetaLowerSegment 975763712 975829248 (97572188184461 / 100000) (97578755888317 / 100000) := by
  exact
    packedTile32768 975763712 975829248 13 3173 31237 30 _ _ (129367 / 6250) (16559 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975829248 :
    ThetaLowerSegment 975829248 975894784 (97578755888317 / 100000) (97585321541333 / 100000) := by
  exact
    packedTile32768 975829248 975894784 13 3172 31238 30 _ _ (1034939 / 50000) (2069881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975894784 :
    ThetaLowerSegment 975894784 975960320 (97585321541333 / 100000) (24397929888967 / 25000) := by
  exact
    packedTile32768 975894784 975960320 13 3091 31239 30 _ _ (413977 / 20000) (64684 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell975960320 :
    ThetaLowerSegment 975960320 976025856 (24397929888967 / 25000) (12199778153303 / 12500) := by
  exact
    packedTile32768 975960320 976025856 13 3143 31240 30 _ _ (517473 / 25000) (413979 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976025856 :
    ThetaLowerSegment 976025856 976091392 (12199778153303 / 12500) (24401194630873 / 25000) := by
  exact
    packedTile32768 976025856 976091392 13 3166 31241 30 _ _ (1034949 / 50000) (2069901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976091392 :
    ThetaLowerSegment 976091392 976156928 (24401194630873 / 25000) (48805690760221 / 50000) := by
  exact
    packedTile32768 976091392 976156928 13 3190 31242 30 _ _ (413981 / 20000) (517477 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976156928 :
    ThetaLowerSegment 976156928 976222464 (48805690760221 / 50000) (48808946731797 / 50000) := by
  exact
    packedTile32768 976156928 976222464 13 3146 31243 30 _ _ (258739 / 12500) (413983 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976222464 :
    ThetaLowerSegment 976222464 976288000 (48808946731797 / 50000) (48812217203817 / 50000) := by
  exact
    packedTile32768 976222464 976288000 13 3160 31244 30 _ _ (2069919 / 100000) (1034961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976288000 :
    ThetaLowerSegment 976288000 976353536 (48812217203817 / 50000) (48815541503367 / 50000) := by
  exact
    packedTile32768 976288000 976353536 13 3212 31245 30 _ _ (82797 / 4000) (258741 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976353536 :
    ThetaLowerSegment 976353536 976419072 (48815541503367 / 50000) (48818770597287 / 50000) := by
  exact
    packedTile32768 976353536 976419072 13 3120 31246 30 _ _ (517483 / 25000) (413987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976419072 :
    ThetaLowerSegment 976419072 976484608 (48818770597287 / 50000) (48822041100907 / 50000) := by
  exact
    packedTile32768 976419072 976484608 13 3160 31247 30 _ _ (2069939 / 100000) (1034971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976484608 :
    ThetaLowerSegment 976484608 976550144 (48822041100907 / 50000) (48825357152797 / 50000) := by
  exact
    packedTile32768 976484608 976550144 13 3204 31248 30 _ _ (413989 / 20000) (517487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976550144 :
    ThetaLowerSegment 976550144 976615680 (48825357152797 / 50000) (48828644236573 / 50000) := by
  exact
    packedTile32768 976550144 976615680 13 3176 31249 30 _ _ (64686 / 3125) (413991 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976615680 :
    ThetaLowerSegment 976615680 976681216 (48828644236573 / 50000) (24415964630753 / 25000) := by
  exact
    packedTile32768 976615680 976681216 13 3174 31250 30 _ _ (2069959 / 100000) (1034981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976681216 :
    ThetaLowerSegment 976681216 976746752 (24415964630753 / 25000) (3052201669834 / 3125) := by
  exact
    packedTile32768 976681216 976746752 13 3186 31251 30 _ _ (1034983 / 50000) (2069969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976746752 :
    ThetaLowerSegment 976746752 976812288 (3052201669834 / 3125) (24419258468919 / 25000) := by
  exact
    packedTile32768 976746752 976812288 13 3179 31252 30 _ _ (517493 / 25000) (82799 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976812288 :
    ThetaLowerSegment 976812288 976877824 (24419258468919 / 25000) (19536715415859 / 20000) := by
  exact
    packedTile32768 976812288 976877824 13 3161 31253 30 _ _ (2069979 / 100000) (1034991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976877824 :
    ThetaLowerSegment 976877824 976943360 (19536715415859 / 20000) (97690192754551 / 100000) := by
  exact
    packedTile32768 976877824 976943360 13 3196 31255 30 _ _ (1034993 / 50000) (2069989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell976943360 :
    ThetaLowerSegment 976943360 977008896 (97690192754551 / 100000) (97696694599423 / 100000) := by
  exact
    packedTile32768 976943360 977008896 13 3141 31256 30 _ _ (258749 / 12500) (413999 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977008896 :
    ThetaLowerSegment 977008896 977074432 (97696694599423 / 100000) (48851656193113 / 50000) := by
  exact
    packedTile32768 977008896 977074432 13 3197 31257 30 _ _ (2069999 / 100000) (1035001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977074432 :
    ThetaLowerSegment 977074432 977139968 (48851656193113 / 50000) (3053432731099 / 3125) := by
  exact
    packedTile32768 977074432 977139968 13 3157 31258 30 _ _ (1035003 / 50000) (2070009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977139968 :
    ThetaLowerSegment 977139968 977205504 (3053432731099 / 3125) (9771645901669 / 10000) := by
  exact
    packedTile32768 977139968 977205504 13 3194 31259 30 _ _ (2070013 / 100000) (64688 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977205504 :
    ThetaLowerSegment 977205504 977271040 (9771645901669 / 10000) (48861537398707 / 50000) := by
  exact
    packedTile32768 977205504 977271040 13 3196 31260 30 _ _ (2070019 / 100000) (1035011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977271040 :
    ThetaLowerSegment 977271040 977336576 (48861537398707 / 50000) (48864774919371 / 50000) := by
  exact
    packedTile32768 977271040 977336576 13 3128 31261 30 _ _ (1035013 / 50000) (2070029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977336576 :
    ThetaLowerSegment 977336576 977402112 (48864774919371 / 50000) (97736076652791 / 100000) := by
  exact
    packedTile32768 977336576 977402112 13 3153 31262 30 _ _ (2070033 / 100000) (517509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977402112 :
    ThetaLowerSegment 977402112 977467648 (97736076652791 / 100000) (48871272762333 / 50000) := by
  exact
    packedTile32768 977402112 977467648 13 3125 31263 30 _ _ (2070039 / 100000) (1035021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977467648 :
    ThetaLowerSegment 977467648 977533184 (48871272762333 / 50000) (48874603466347 / 50000) := by
  exact
    packedTile32768 977467648 977533184 13 3218 31264 30 _ _ (1035023 / 50000) (2070049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977533184 :
    ThetaLowerSegment 977533184 977598720 (48874603466347 / 50000) (48877911411041 / 50000) := by
  exact
    packedTile32768 977533184 977598720 13 3196 31265 30 _ _ (2070053 / 100000) (258757 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977598720 :
    ThetaLowerSegment 977598720 977664256 (48877911411041 / 50000) (48881190384497 / 50000) := by
  exact
    packedTile32768 977598720 977664256 13 3168 31266 30 _ _ (2070059 / 100000) (1035031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977664256 :
    ThetaLowerSegment 977664256 977729792 (48881190384497 / 50000) (24442222781641 / 25000) := by
  exact
    packedTile32768 977664256 977729792 13 3145 31267 30 _ _ (1035033 / 50000) (2070069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977729792 :
    ThetaLowerSegment 977729792 977795328 (24442222781641 / 25000) (24443845718873 / 25000) := by
  exact
    packedTile32768 977729792 977795328 13 3136 31268 30 _ _ (2070073 / 100000) (517519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977795328 :
    ThetaLowerSegment 977795328 977860864 (24443845718873 / 25000) (24445483669673 / 25000) := by
  exact
    packedTile32768 977795328 977860864 13 3165 31269 30 _ _ (12938 / 625) (2070083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977860864 :
    ThetaLowerSegment 977860864 977926400 (24445483669673 / 25000) (48894259811129 / 50000) := by
  exact
    packedTile32768 977860864 977926400 13 3181 31270 30 _ _ (1035043 / 50000) (2070089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977926400 :
    ThetaLowerSegment 977926400 977991936 (48894259811129 / 50000) (3911803189879 / 4000) := by
  exact
    packedTile32768 977926400 977991936 13 3169 31271 30 _ _ (2070093 / 100000) (129381 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell977991936 :
    ThetaLowerSegment 977991936 978057472 (3911803189879 / 4000) (3912063774067 / 4000) := by
  exact
    packedTile32768 977991936 978057472 13 3147 31272 30 _ _ (20701 / 1000) (2070103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978057472 :
    ThetaLowerSegment 978057472 978123008 (3912063774067 / 4000) (97808183499073 / 100000) := by
  exact
    packedTile32768 978057472 978123008 13 3183 31273 30 _ _ (1035053 / 50000) (2070109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978123008 :
    ThetaLowerSegment 978123008 978188544 (97808183499073 / 100000) (24453653835041 / 25000) := by
  exact
    packedTile32768 978123008 978188544 13 3107 31274 30 _ _ (2070113 / 100000) (517529 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978188544 :
    ThetaLowerSegment 978188544 978254080 (24453653835041 / 25000) (24455282501951 / 25000) := by
  exact
    packedTile32768 978188544 978254080 13 3147 31276 30 _ _ (51753 / 2500) (2070123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978254080 :
    ThetaLowerSegment 978254080 978319616 (24455282501951 / 25000) (24456919971617 / 25000) := by
  exact
    packedTile32768 978254080 978319616 13 3164 31277 30 _ _ (1035063 / 50000) (2070129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978319616 :
    ThetaLowerSegment 978319616 978385152 (24456919971617 / 25000) (97834256699009 / 100000) := by
  exact
    packedTile32768 978319616 978385152 13 3177 31278 30 _ _ (2070133 / 100000) (258767 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978385152 :
    ThetaLowerSegment 978385152 978450688 (97834256699009 / 100000) (97840918409529 / 100000) := by
  exact
    packedTile32768 978385152 978450688 13 3218 31279 30 _ _ (103507 / 5000) (2070143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978450688 :
    ThetaLowerSegment 978450688 978516224 (97840918409529 / 100000) (48923741422833 / 50000) := by
  exact
    packedTile32768 978450688 978516224 13 3171 31280 30 _ _ (2070147 / 100000) (41403 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978516224 :
    ThetaLowerSegment 978516224 978581760 (48923741422833 / 50000) (3914164541829 / 4000) := by
  exact
    packedTile32768 978516224 978581760 13 3203 31281 30 _ _ (2070153 / 100000) (517539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978581760 :
    ThetaLowerSegment 978581760 978647296 (3914164541829 / 4000) (19572129394137 / 20000) := by
  exact
    packedTile32768 978581760 978647296 13 3156 31282 30 _ _ (25877 / 1250) (2070163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978647296 :
    ThetaLowerSegment 978647296 978712832 (19572129394137 / 20000) (9786697133087 / 10000) := by
  exact
    packedTile32768 978647296 978712832 13 3055 31283 30 _ _ (2070167 / 100000) (207017 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978712832 :
    ThetaLowerSegment 978712832 978778368 (9786697133087 / 10000) (9787338886717 / 10000) := by
  exact
    packedTile32768 978712832 978778368 13 3100 31284 30 _ _ (2070173 / 100000) (64693 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978778368 :
    ThetaLowerSegment 978778368 978843904 (9787338886717 / 10000) (9787998239047 / 10000) := by
  exact
    packedTile32768 978778368 978843904 13 3185 31285 30 _ _ (103509 / 5000) (2070183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978843904 :
    ThetaLowerSegment 978843904 978909440 (9787998239047 / 10000) (97886530391951 / 100000) := by
  exact
    packedTile32768 978843904 978909440 13 3163 31286 30 _ _ (2070187 / 100000) (207019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978909440 :
    ThetaLowerSegment 978909440 978974976 (97886530391951 / 100000) (3059159088549 / 3125) := by
  exact
    packedTile32768 978909440 978974976 13 3169 31287 30 _ _ (2070193 / 100000) (517549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell978974976 :
    ThetaLowerSegment 978974976 979040512 (3059159088549 / 3125) (12237435192621 / 12500) := by
  exact
    packedTile32768 978974976 979040512 13 3087 31288 30 _ _ (10351 / 500) (2070203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979040512 :
    ThetaLowerSegment 979040512 979106048 (12237435192621 / 12500) (97906166239371 / 100000) := by
  exact
    packedTile32768 979040512 979106048 13 3229 31289 30 _ _ (2070207 / 100000) (207021 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979106048 :
    ThetaLowerSegment 979106048 979171584 (97906166239371 / 100000) (97912815766739 / 100000) := by
  exact
    packedTile32768 979106048 979171584 13 3212 31290 30 _ _ (1035107 / 50000) (2070217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979171584 :
    ThetaLowerSegment 979171584 979237120 (97912815766739 / 100000) (97919463243159 / 100000) := by
  exact
    packedTile32768 979171584 979237120 13 3211 31291 30 _ _ (103511 / 5000) (2070223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979237120 :
    ThetaLowerSegment 979237120 979302656 (97919463243159 / 100000) (97925972036847 / 100000) := by
  exact
    packedTile32768 979237120 979302656 13 3144 31292 30 _ _ (2070227 / 100000) (207023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979302656 :
    ThetaLowerSegment 979302656 979368192 (97925972036847 / 100000) (19586513974521 / 20000) := by
  exact
    packedTile32768 979302656 979368192 13 3187 31293 30 _ _ (1035117 / 50000) (2070237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979368192 :
    ThetaLowerSegment 979368192 979433728 (19586513974521 / 20000) (19587804148089 / 20000) := by
  exact
    packedTile32768 979368192 979433728 13 3116 31294 30 _ _ (12939 / 625) (2070243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979433728 :
    ThetaLowerSegment 979433728 979499264 (19587804148089 / 20000) (97945657952327 / 100000) := by
  exact
    packedTile32768 979433728 979499264 13 3206 31295 30 _ _ (2070247 / 100000) (8281 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979499264 :
    ThetaLowerSegment 979499264 979564800 (97945657952327 / 100000) (97952228938523 / 100000) := by
  exact
    packedTile32768 979499264 979564800 13 3174 31296 30 _ _ (1035127 / 50000) (2070257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979564800 :
    ThetaLowerSegment 979564800 979630336 (97952228938523 / 100000) (97958611550103 / 100000) := by
  exact
    packedTile32768 979564800 979630336 13 3083 31297 30 _ _ (103513 / 5000) (2070263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979630336 :
    ThetaLowerSegment 979630336 979695872 (97958611550103 / 100000) (97965016956201 / 100000) := by
  exact
    packedTile32768 979630336 979695872 13 3094 31299 30 _ _ (2070267 / 100000) (207027 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979695872 :
    ThetaLowerSegment 979695872 979761408 (97965016956201 / 100000) (97971672887111 / 100000) := by
  exact
    packedTile32768 979695872 979761408 13 3215 31300 30 _ _ (1035137 / 50000) (2070277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979761408 :
    ThetaLowerSegment 979761408 979826944 (97971672887111 / 100000) (97978246026111 / 100000) := by
  exact
    packedTile32768 979761408 979826944 13 3175 31301 30 _ _ (51757 / 2500) (2070283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979826944 :
    ThetaLowerSegment 979826944 979892480 (97978246026111 / 100000) (4899242201539 / 5000) := by
  exact
    packedTile32768 979826944 979892480 13 3187 31302 30 _ _ (2070287 / 100000) (207029 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979892480 :
    ThetaLowerSegment 979892480 979958016 (4899242201539 / 5000) (48995632006237 / 50000) := by
  exact
    packedTile32768 979892480 979958016 13 3101 31303 30 _ _ (1035147 / 50000) (2070297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell979958016 :
    ThetaLowerSegment 979958016 980023552 (48995632006237 / 50000) (3062435971397 / 3125) := by
  exact
    packedTile32768 979958016 980023552 13 3230 31304 30 _ _ (2070301 / 100000) (64697 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980023552 :
    ThetaLowerSegment 980023552 980089088 (3062435971397 / 3125) (24501129524627 / 25000) := by
  exact
    packedTile32768 980023552 980089088 13 3172 31305 30 _ _ (2070307 / 100000) (207031 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980089088 :
    ThetaLowerSegment 980089088 980154624 (24501129524627 / 25000) (49005535321159 / 50000) := by
  exact
    packedTile32768 980089088 980154624 13 3165 31306 30 _ _ (1035157 / 50000) (2070317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980154624 :
    ThetaLowerSegment 980154624 980220160 (49005535321159 / 50000) (49008773303203 / 50000) := by
  exact
    packedTile32768 980154624 980220160 13 3128 31307 30 _ _ (2070321 / 100000) (517581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980220160 :
    ThetaLowerSegment 980220160 980285696 (49008773303203 / 50000) (12253008517057 / 12500) := by
  exact
    packedTile32768 980220160 980285696 13 3150 31308 30 _ _ (2070327 / 100000) (207033 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980285696 :
    ThetaLowerSegment 980285696 980351232 (12253008517057 / 12500) (49015335215791 / 50000) := by
  exact
    packedTile32768 980285696 980351232 13 3189 31309 30 _ _ (1035167 / 50000) (2070337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980351232 :
    ThetaLowerSegment 980351232 980416768 (49015335215791 / 50000) (24509335267571 / 25000) := by
  exact
    packedTile32768 980351232 980416768 13 3222 31310 30 _ _ (2070341 / 100000) (258793 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980416768 :
    ThetaLowerSegment 980416768 980482304 (24509335267571 / 25000) (98043831608129 / 100000) := by
  exact
    packedTile32768 980416768 980482304 13 3135 31311 30 _ _ (2070347 / 100000) (41407 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980482304 :
    ThetaLowerSegment 980482304 980547840 (98043831608129 / 100000) (98050400841371 / 100000) := by
  exact
    packedTile32768 980482304 980547840 13 3173 31312 30 _ _ (1035177 / 50000) (2070357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980547840 :
    ThetaLowerSegment 980547840 980613376 (98050400841371 / 100000) (98056881071301 / 100000) := by
  exact
    packedTile32768 980547840 980613376 13 3130 31313 30 _ _ (2070361 / 100000) (517591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980613376 :
    ThetaLowerSegment 980613376 980678912 (98056881071301 / 100000) (49031689976657 / 50000) := by
  exact
    packedTile32768 980613376 980678912 13 3139 31314 30 _ _ (2070367 / 100000) (207037 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980678912 :
    ThetaLowerSegment 980678912 980744448 (49031689976657 / 50000) (6129366652191 / 6250) := by
  exact
    packedTile32768 980678912 980744448 13 3133 31315 30 _ _ (1035187 / 50000) (2070377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980744448 :
    ThetaLowerSegment 980744448 980809984 (6129366652191 / 6250) (6129776587629 / 6250) := by
  exact
    packedTile32768 980744448 980809984 13 3168 31316 30 _ _ (2070381 / 100000) (129399 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980809984 :
    ThetaLowerSegment 980809984 980875520 (6129776587629 / 6250) (49041485982879 / 50000) := by
  exact
    packedTile32768 980809984 980875520 13 3162 31317 30 _ _ (2070387 / 100000) (207039 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980875520 :
    ThetaLowerSegment 980875520 980941056 (49041485982879 / 50000) (2452237497951 / 2500) := by
  exact
    packedTile32768 980875520 980941056 13 3153 31318 30 _ _ (1035197 / 50000) (2070397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell980941056 :
    ThetaLowerSegment 980941056 981006592 (2452237497951 / 2500) (4904804189661 / 5000) := by
  exact
    packedTile32768 980941056 981006592 13 3180 31319 30 _ _ (2070401 / 100000) (517601 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981006592 :
    ThetaLowerSegment 981006592 981072128 (4904804189661 / 5000) (12262829320121 / 12500) := by
  exact
    packedTile32768 981006592 981072128 13 3164 31321 30 _ _ (2070407 / 100000) (207041 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981072128 :
    ThetaLowerSegment 981072128 981137664 (12262829320121 / 12500) (122636543801 / 125) := by
  exact
    packedTile32768 981072128 981137664 13 3188 31322 30 _ _ (1035207 / 50000) (2070417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981137664 :
    ThetaLowerSegment 981137664 981203200 (122636543801 / 125) (3924632345099 / 4000) := by
  exact
    packedTile32768 981137664 981203200 13 3175 31323 30 _ _ (2070421 / 100000) (258803 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981203200 :
    ThetaLowerSegment 981203200 981268736 (3924632345099 / 4000) (98122373954663 / 100000) := by
  exact
    packedTile32768 981203200 981268736 13 3171 31324 30 _ _ (517607 / 25000) (2070431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981268736 :
    ThetaLowerSegment 981268736 981334272 (98122373954663 / 100000) (98128978639123 / 100000) := by
  exact
    packedTile32768 981268736 981334272 13 3190 31325 30 _ _ (1035217 / 50000) (2070437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981334272 :
    ThetaLowerSegment 981334272 981399808 (98128978639123 / 100000) (98135500528273 / 100000) := by
  exact
    packedTile32768 981334272 981399808 13 3150 31326 30 _ _ (2070441 / 100000) (517611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981399808 :
    ThetaLowerSegment 981399808 981465344 (98135500528273 / 100000) (98142125961873 / 100000) := by
  exact
    packedTile32768 981399808 981465344 13 3200 31327 30 _ _ (129403 / 6250) (2070451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981465344 :
    ThetaLowerSegment 981465344 981530880 (98142125961873 / 100000) (98148730710133 / 100000) := by
  exact
    packedTile32768 981465344 981530880 13 3190 31328 30 _ _ (1035227 / 50000) (2070457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981530880 :
    ThetaLowerSegment 981530880 981596416 (98148730710133 / 100000) (98155368608099 / 100000) := by
  exact
    packedTile32768 981530880 981596416 13 3206 31329 30 _ _ (2070461 / 100000) (64702 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981596416 :
    ThetaLowerSegment 981596416 981661952 (98155368608099 / 100000) (98161878159491 / 100000) := by
  exact
    packedTile32768 981596416 981661952 13 3144 31330 30 _ _ (517617 / 25000) (2070471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981661952 :
    ThetaLowerSegment 981661952 981727488 (98161878159491 / 100000) (98168300769839 / 100000) := by
  exact
    packedTile32768 981661952 981727488 13 3102 31331 30 _ _ (1035237 / 50000) (2070477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981727488 :
    ThetaLowerSegment 981727488 981793024 (98168300769839 / 100000) (98174785516331 / 100000) := by
  exact
    packedTile32768 981727488 981793024 13 3132 31332 30 _ _ (2070481 / 100000) (517621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981793024 :
    ThetaLowerSegment 981793024 981858560 (98174785516331 / 100000) (98181338610851 / 100000) := by
  exact
    packedTile32768 981793024 981858560 13 3165 31333 30 _ _ (258811 / 12500) (2070491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981858560 :
    ThetaLowerSegment 981858560 981924096 (98181338610851 / 100000) (98187860666951 / 100000) := by
  exact
    packedTile32768 981858560 981924096 13 3150 31334 30 _ _ (1035247 / 50000) (2070497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981924096 :
    ThetaLowerSegment 981924096 981989632 (98187860666951 / 100000) (98194395168107 / 100000) := by
  exact
    packedTile32768 981924096 981989632 13 3156 31335 30 _ _ (2070501 / 100000) (258813 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell981989632 :
    ThetaLowerSegment 981989632 982055168 (98194395168107 / 100000) (98200871717131 / 100000) := by
  exact
    packedTile32768 981989632 982055168 13 3128 31336 30 _ _ (517627 / 25000) (2070511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982055168 :
    ThetaLowerSegment 982055168 982120704 (98200871717131 / 100000) (98207455951651 / 100000) := by
  exact
    packedTile32768 982055168 982120704 13 3180 31337 30 _ _ (1035257 / 50000) (2070517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982120704 :
    ThetaLowerSegment 982120704 982186240 (98207455951651 / 100000) (98213920118213 / 100000) := by
  exact
    packedTile32768 982120704 982186240 13 3122 31338 30 _ _ (2070521 / 100000) (517631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982186240 :
    ThetaLowerSegment 982186240 982251776 (98213920118213 / 100000) (98220483691973 / 100000) := by
  exact
    packedTile32768 982186240 982251776 13 3170 31339 30 _ _ (64704 / 3125) (2070531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982251776 :
    ThetaLowerSegment 982251776 982317312 (98220483691973 / 100000) (98227134247181 / 100000) := by
  exact
    packedTile32768 982251776 982317312 13 3212 31340 30 _ _ (1035267 / 50000) (2070537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982317312 :
    ThetaLowerSegment 982317312 982382848 (98227134247181 / 100000) (98233693721069 / 100000) := by
  exact
    packedTile32768 982317312 982382848 13 3168 31341 30 _ _ (2070541 / 100000) (129409 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982382848 :
    ThetaLowerSegment 982382848 982448384 (98233693721069 / 100000) (98240360885629 / 100000) := by
  exact
    packedTile32768 982382848 982448384 13 3220 31342 30 _ _ (517637 / 25000) (2070551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982448384 :
    ThetaLowerSegment 982448384 982513920 (98240360885629 / 100000) (98246926612363 / 100000) := by
  exact
    packedTile32768 982448384 982513920 13 3171 31344 30 _ _ (1035277 / 50000) (2070557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982513920 :
    ThetaLowerSegment 982513920 982579456 (98246926612363 / 100000) (1965069681581 / 2000) := by
  exact
    packedTile32768 982513920 982579456 13 3167 31345 30 _ _ (2070561 / 100000) (517641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982579456 :
    ThetaLowerSegment 982579456 982644992 (1965069681581 / 2000) (49130004219409 / 50000) := by
  exact
    packedTile32768 982579456 982644992 13 3151 31346 30 _ _ (258821 / 12500) (2070571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982644992 :
    ThetaLowerSegment 982644992 982710528 (49130004219409 / 50000) (24566633204373 / 25000) := by
  exact
    packedTile32768 982644992 982710528 13 3151 31347 30 _ _ (1035287 / 50000) (2070577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982710528 :
    ThetaLowerSegment 982710528 982776064 (24566633204373 / 25000) (98273053077061 / 100000) := by
  exact
    packedTile32768 982710528 982776064 13 3149 31348 30 _ _ (2070581 / 100000) (258823 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982776064 :
    ThetaLowerSegment 982776064 982841600 (98273053077061 / 100000) (98279707946893 / 100000) := by
  exact
    packedTile32768 982776064 982841600 13 3214 31349 30 _ _ (517647 / 25000) (2070591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982841600 :
    ThetaLowerSegment 982841600 982907136 (98279707946893 / 100000) (98286364906603 / 100000) := by
  exact
    packedTile32768 982841600 982907136 13 3215 31350 30 _ _ (1035297 / 50000) (2070597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982907136 :
    ThetaLowerSegment 982907136 982972672 (98286364906603 / 100000) (24573248225101 / 25000) := by
  exact
    packedTile32768 982907136 982972672 13 3201 31351 30 _ _ (2070601 / 100000) (517651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell982972672 :
    ThetaLowerSegment 982972672 983038208 (24573248225101 / 25000) (24574888146637 / 25000) := by
  exact
    packedTile32768 982972672 983038208 13 3168 31352 30 _ _ (129413 / 6250) (2070611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983038208 :
    ThetaLowerSegment 983038208 983103744 (24574888146637 / 25000) (24576523931697 / 25000) := by
  exact
    packedTile32768 983038208 983103744 13 3160 31353 30 _ _ (1035307 / 50000) (2070617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983103744 :
    ThetaLowerSegment 983103744 983169280 (24576523931697 / 25000) (24578180428497 / 25000) := by
  exact
    packedTile32768 983103744 983169280 13 3200 31354 30 _ _ (2070621 / 100000) (64707 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983169280 :
    ThetaLowerSegment 983169280 983234816 (24578180428497 / 25000) (24579791377081 / 25000) := by
  exact
    packedTile32768 983169280 983234816 13 3112 31355 30 _ _ (517657 / 25000) (2070631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983234816 :
    ThetaLowerSegment 983234816 983300352 (24579791377081 / 25000) (49162878168173 / 50000) := by
  exact
    packedTile32768 983234816 983300352 13 3183 31356 30 _ _ (1035317 / 50000) (2070637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983300352 :
    ThetaLowerSegment 983300352 983365888 (49162878168173 / 50000) (98332334762803 / 100000) := by
  exact
    packedTile32768 983300352 983365888 13 3177 31357 30 _ _ (2070641 / 100000) (517661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983365888 :
    ThetaLowerSegment 983365888 983431424 (98332334762803 / 100000) (19667773117319 / 20000) := by
  exact
    packedTile32768 983365888 983431424 13 3154 31358 30 _ _ (258831 / 12500) (2070651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983431424 :
    ThetaLowerSegment 983431424 983496960 (19667773117319 / 20000) (98345437842391 / 100000) := by
  exact
    packedTile32768 983431424 983496960 13 3174 31359 30 _ _ (1035327 / 50000) (2070657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983496960 :
    ThetaLowerSegment 983496960 983562496 (98345437842391 / 100000) (98351935576609 / 100000) := by
  exact
    packedTile32768 983496960 983562496 13 3138 31360 30 _ _ (2070661 / 100000) (258833 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983562496 :
    ThetaLowerSegment 983562496 983628032 (98351935576609 / 100000) (98358460251477 / 100000) := by
  exact
    packedTile32768 983562496 983628032 13 3151 31361 30 _ _ (517667 / 25000) (2070671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983628032 :
    ThetaLowerSegment 983628032 983693568 (98358460251477 / 100000) (98365051206819 / 100000) := by
  exact
    packedTile32768 983628032 983693568 13 3183 31362 30 _ _ (1035337 / 50000) (2070677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983693568 :
    ThetaLowerSegment 983693568 983759104 (98365051206819 / 100000) (24592886733279 / 25000) := by
  exact
    packedTile32768 983693568 983759104 13 3137 31363 30 _ _ (2070681 / 100000) (517671 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983759104 :
    ThetaLowerSegment 983759104 983824640 (24592886733279 / 25000) (983782104071 / 1000) := by
  exact
    packedTile32768 983759104 983824640 13 3218 31364 30 _ _ (64709 / 3125) (2070691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983824640 :
    ThetaLowerSegment 983824640 983890176 (983782104071 / 1000) (1967695697211 / 2000) := by
  exact
    packedTile32768 983824640 983890176 13 3175 31365 30 _ _ (1035347 / 50000) (2070697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983890176 :
    ThetaLowerSegment 983890176 983955712 (1967695697211 / 2000) (2459785795269 / 2500) := by
  exact
    packedTile32768 983890176 983955712 13 3210 31367 30 _ _ (2070701 / 100000) (129419 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell983955712 :
    ThetaLowerSegment 983955712 984021248 (2459785795269 / 2500) (6149886136089 / 6250) := by
  exact
    packedTile32768 983955712 984021248 13 3258 31368 30 _ _ (517677 / 25000) (2070711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984021248 :
    ThetaLowerSegment 984021248 984086784 (6149886136089 / 6250) (24601214575197 / 25000) := by
  exact
    packedTile32768 984021248 984086784 13 3226 31369 30 _ _ (1035357 / 50000) (2070717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984086784 :
    ThetaLowerSegment 984086784 984152320 (24601214575197 / 25000) (3075355529078 / 3125) := by
  exact
    packedTile32768 984086784 984152320 13 3148 31370 30 _ _ (2070721 / 100000) (517681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984152320 :
    ThetaLowerSegment 984152320 984217856 (3075355529078 / 3125) (6151115108957 / 6250) := by
  exact
    packedTile32768 984152320 984217856 13 3122 31371 30 _ _ (258841 / 12500) (2070731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984217856 :
    ThetaLowerSegment 984217856 984283392 (6151115108957 / 6250) (24606084926651 / 25000) := by
  exact
    packedTile32768 984217856 984283392 13 3138 31372 30 _ _ (1035367 / 50000) (2070737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984283392 :
    ThetaLowerSegment 984283392 984348928 (24606084926651 / 25000) (98430980572991 / 100000) := by
  exact
    packedTile32768 984283392 984348928 13 3207 31373 30 _ _ (2070741 / 100000) (258843 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984348928 :
    ThetaLowerSegment 984348928 984414464 (98430980572991 / 100000) (98437435094507 / 100000) := by
  exact
    packedTile32768 984348928 984414464 13 3117 31374 30 _ _ (517687 / 25000) (2070751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984414464 :
    ThetaLowerSegment 984414464 984480000 (98437435094507 / 100000) (98444113276157 / 100000) := by
  exact
    packedTile32768 984414464 984480000 13 3225 31375 30 _ _ (1035377 / 50000) (2070757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984480000 :
    ThetaLowerSegment 984480000 984545536 (98444113276157 / 100000) (3076582186282 / 3125) := by
  exact
    packedTile32768 984480000 984545536 13 3147 31376 30 _ _ (2070761 / 100000) (517691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984545536 :
    ThetaLowerSegment 984545536 984611072 (3076582186282 / 3125) (6153573996359 / 6250) := by
  exact
    packedTile32768 984545536 984611072 13 3165 31377 30 _ _ (129423 / 6250) (2070771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984611072 :
    ThetaLowerSegment 984611072 984676608 (6153573996359 / 6250) (4923187828921 / 5000) := by
  exact
    packedTile32768 984611072 984676608 13 3174 31378 30 _ _ (1035387 / 50000) (2070777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984676608 :
    ThetaLowerSegment 984676608 984742144 (4923187828921 / 5000) (2461756470769 / 2500) := by
  exact
    packedTile32768 984676608 984742144 13 3140 31379 30 _ _ (2070781 / 100000) (64712 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984742144 :
    ThetaLowerSegment 984742144 984807680 (2461756470769 / 2500) (24619202183301 / 25000) := by
  exact
    packedTile32768 984742144 984807680 13 3163 31380 30 _ _ (517697 / 25000) (2070791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984807680 :
    ThetaLowerSegment 984807680 984873216 (24619202183301 / 25000) (49241733167957 / 50000) := by
  exact
    packedTile32768 984807680 984873216 13 3215 31381 30 _ _ (1035397 / 50000) (2070797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984873216 :
    ThetaLowerSegment 984873216 984938752 (49241733167957 / 50000) (98489983146661 / 100000) := by
  exact
    packedTile32768 984873216 984938752 13 3147 31382 30 _ _ (2070801 / 100000) (517701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell984938752 :
    ThetaLowerSegment 984938752 985004288 (98489983146661 / 100000) (19699308693281 / 20000) := by
  exact
    packedTile32768 984938752 985004288 13 3168 31383 30 _ _ (258851 / 12500) (2070811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985004288 :
    ThetaLowerSegment 985004288 985069824 (19699308693281 / 20000) (98503012689341 / 100000) := by
  exact
    packedTile32768 985004288 985069824 13 3124 31384 30 _ _ (1035407 / 50000) (2070817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985069824 :
    ThetaLowerSegment 985069824 985135360 (98503012689341 / 100000) (98509473650861 / 100000) := by
  exact
    packedTile32768 985069824 985135360 13 3120 31385 30 _ _ (2070821 / 100000) (258853 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985135360 :
    ThetaLowerSegment 985135360 985200896 (98509473650861 / 100000) (98516096155607 / 100000) := by
  exact
    packedTile32768 985135360 985200896 13 3198 31386 30 _ _ (2070827 / 100000) (207083 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985200896 :
    ThetaLowerSegment 985200896 985266432 (98516096155607 / 100000) (157636197479 / 160) := by
  exact
    packedTile32768 985200896 985266432 13 3152 31387 30 _ _ (1035417 / 50000) (2070837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985266432 :
    ThetaLowerSegment 985266432 985331968 (157636197479 / 160) (98529258398939 / 100000) := by
  exact
    packedTile32768 985266432 985331968 13 3204 31388 30 _ _ (2070841 / 100000) (517711 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985331968 :
    ThetaLowerSegment 985331968 985397504 (98529258398939 / 100000) (24633958334541 / 25000) := by
  exact
    packedTile32768 985331968 985397504 13 3175 31389 30 _ _ (2070847 / 100000) (41417 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985397504 :
    ThetaLowerSegment 985397504 985463040 (24633958334541 / 25000) (985424269373 / 1000) := by
  exact
    packedTile32768 985397504 985463040 13 3184 31391 30 _ _ (1035427 / 50000) (2070857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985463040 :
    ThetaLowerSegment 985463040 985528576 (985424269373 / 1000) (24637250997959 / 25000) := by
  exact
    packedTile32768 985463040 985528576 13 3176 31392 30 _ _ (2070861 / 100000) (129429 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985528576 :
    ThetaLowerSegment 985528576 985594112 (24637250997959 / 25000) (9855559349063 / 10000) := by
  exact
    packedTile32768 985528576 985594112 13 3182 31393 30 _ _ (2070867 / 100000) (207087 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985594112 :
    ThetaLowerSegment 985594112 985659648 (9855559349063 / 10000) (492811153209 / 500) := by
  exact
    packedTile32768 985594112 985659648 13 3205 31394 30 _ _ (1035437 / 50000) (2070877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985659648 :
    ThetaLowerSegment 985659648 985725184 (492811153209 / 500) (49284343824379 / 50000) := by
  exact
    packedTile32768 985659648 985725184 13 3118 31395 30 _ _ (2070881 / 100000) (517721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985725184 :
    ThetaLowerSegment 985725184 985790720 (49284343824379 / 50000) (3080472753354 / 3125) := by
  exact
    packedTile32768 985725184 985790720 13 3110 31396 30 _ _ (2070887 / 100000) (207089 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985790720 :
    ThetaLowerSegment 985790720 985856256 (3080472753354 / 3125) (985816265727 / 1000) := by
  exact
    packedTile32768 985790720 985856256 13 3138 31397 30 _ _ (1035447 / 50000) (2070897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985856256 :
    ThetaLowerSegment 985856256 985921792 (985816265727 / 1000) (49294091522633 / 50000) := by
  exact
    packedTile32768 985856256 985921792 13 3166 31398 30 _ _ (2070901 / 100000) (258863 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985921792 :
    ThetaLowerSegment 985921792 985987328 (49294091522633 / 50000) (24648705593277 / 25000) := by
  exact
    packedTile32768 985921792 985987328 13 3206 31399 30 _ _ (2070907 / 100000) (207091 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell985987328 :
    ThetaLowerSegment 985987328 986052864 (24648705593277 / 25000) (9860139338323 / 10000) := by
  exact
    packedTile32768 985987328 986052864 13 3173 31400 30 _ _ (1035457 / 50000) (2070917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986052864 :
    ThetaLowerSegment 986052864 986118400 (9860139338323 / 10000) (9860793749359 / 10000) := by
  exact
    packedTile32768 986052864 986118400 13 3160 31401 30 _ _ (2070921 / 100000) (517731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986118400 :
    ThetaLowerSegment 986118400 986183936 (9860793749359 / 10000) (98614363580071 / 100000) := by
  exact
    packedTile32768 986118400 986183936 13 3103 31402 30 _ _ (2070927 / 100000) (207093 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986183936 :
    ThetaLowerSegment 986183936 986249472 (98614363580071 / 100000) (98621027845683 / 100000) := by
  exact
    packedTile32768 986183936 986249472 13 3218 31403 30 _ _ (1035467 / 50000) (2070937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986249472 :
    ThetaLowerSegment 986249472 986315008 (98621027845683 / 100000) (98627607222063 / 100000) := by
  exact
    packedTile32768 986249472 986315008 13 3177 31404 30 _ _ (103547 / 5000) (2070943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986315008 :
    ThetaLowerSegment 986315008 986380544 (98627607222063 / 100000) (616463070982 / 625) := by
  exact
    packedTile32768 986315008 986380544 13 3131 31405 30 _ _ (2070947 / 100000) (41419 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986380544 :
    ThetaLowerSegment 986380544 986446080 (616463070982 / 625) (24660155786509 / 25000) := by
  exact
    packedTile32768 986380544 986446080 13 3154 31406 30 _ _ (1035477 / 50000) (2070957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986446080 :
    ThetaLowerSegment 986446080 986511616 (24660155786509 / 25000) (24661806341629 / 25000) := by
  exact
    packedTile32768 986446080 986511616 13 3188 31407 30 _ _ (25887 / 1250) (2070963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986511616 :
    ThetaLowerSegment 986511616 986577152 (24661806341629 / 25000) (98653821396411 / 100000) := by
  exact
    packedTile32768 986511616 986577152 13 3185 31408 30 _ _ (2070967 / 100000) (207097 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986577152 :
    ThetaLowerSegment 986577152 986642688 (98653821396411 / 100000) (98660423661523 / 100000) := by
  exact
    packedTile32768 986577152 986642688 13 3188 31409 30 _ _ (1035487 / 50000) (2070977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986642688 :
    ThetaLowerSegment 986642688 986708224 (98660423661523 / 100000) (98667038371643 / 100000) := by
  exact
    packedTile32768 986642688 986708224 13 3194 31410 30 _ _ (103549 / 5000) (2070983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986708224 :
    ThetaLowerSegment 986708224 986773760 (98667038371643 / 100000) (98673640678199 / 100000) := by
  exact
    packedTile32768 986708224 986773760 13 3188 31411 30 _ _ (2070987 / 100000) (207099 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986773760 :
    ThetaLowerSegment 986773760 986839296 (98673640678199 / 100000) (98680205729179 / 100000) := by
  exact
    packedTile32768 986773760 986839296 13 3170 31412 30 _ _ (1035497 / 50000) (2070997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986839296 :
    ThetaLowerSegment 986839296 986904832 (98680205729179 / 100000) (98686675533179 / 100000) := by
  exact
    packedTile32768 986839296 986904832 13 3124 31413 30 _ _ (2071 / 100) (2071003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986904832 :
    ThetaLowerSegment 986904832 986970368 (98686675533179 / 100000) (98693124648977 / 100000) := by
  exact
    packedTile32768 986904832 986970368 13 3114 31415 30 _ _ (2071007 / 100000) (207101 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell986970368 :
    ThetaLowerSegment 986970368 987035904 (98693124648977 / 100000) (98699785030001 / 100000) := by
  exact
    packedTile32768 986970368 987035904 13 3216 31416 30 _ _ (1035507 / 50000) (2071017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987035904 :
    ThetaLowerSegment 987035904 987101440 (98699785030001 / 100000) (98706385370741 / 100000) := by
  exact
    packedTile32768 987035904 987101440 13 3187 31417 30 _ _ (103551 / 5000) (2071023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987101440 :
    ThetaLowerSegment 987101440 987166976 (98706385370741 / 100000) (98712971236601 / 100000) := by
  exact
    packedTile32768 987101440 987166976 13 3180 31418 30 _ _ (2071027 / 100000) (207103 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987166976 :
    ThetaLowerSegment 987166976 987232512 (98712971236601 / 100000) (98719528127079 / 100000) := by
  exact
    packedTile32768 987166976 987232512 13 3166 31419 30 _ _ (2071033 / 100000) (517759 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987232512 :
    ThetaLowerSegment 987232512 987298048 (98719528127079 / 100000) (98726047760999 / 100000) := by
  exact
    packedTile32768 987232512 987298048 13 3148 31420 30 _ _ (12944 / 625) (2071043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987298048 :
    ThetaLowerSegment 987298048 987363584 (98726047760999 / 100000) (49366264033531 / 50000) := by
  exact
    packedTile32768 987298048 987363584 13 3129 31421 30 _ _ (2071047 / 100000) (41421 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987363584 :
    ThetaLowerSegment 987363584 987429120 (49366264033531 / 50000) (493695217999 / 500) := by
  exact
    packedTile32768 987363584 987429120 13 3146 31422 30 _ _ (2071053 / 100000) (129441 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987429120 :
    ThetaLowerSegment 987429120 987494656 (493695217999 / 500) (2468639496629 / 2500) := by
  exact
    packedTile32768 987429120 987494656 13 3156 31423 30 _ _ (103553 / 5000) (2071063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987494656 :
    ThetaLowerSegment 987494656 987560192 (2468639496629 / 2500) (98752188639957 / 100000) := by
  exact
    packedTile32768 987494656 987560192 13 3191 31424 30 _ _ (2071067 / 100000) (207107 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987560192 :
    ThetaLowerSegment 987560192 987625728 (98752188639957 / 100000) (19751724278539 / 20000) := by
  exact
    packedTile32768 987560192 987625728 13 3106 31425 30 _ _ (2071073 / 100000) (517769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987625728 :
    ThetaLowerSegment 987625728 987691264 (19751724278539 / 20000) (19753038585907 / 20000) := by
  exact
    packedTile32768 987625728 987691264 13 3173 31426 30 _ _ (51777 / 2500) (2071083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987691264 :
    ThetaLowerSegment 987691264 987756800 (19753038585907 / 20000) (19754368223761 / 20000) := by
  exact
    packedTile32768 987691264 987756800 13 3210 31427 30 _ _ (2071087 / 100000) (207109 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987756800 :
    ThetaLowerSegment 987756800 987822336 (19754368223761 / 20000) (98778472758591 / 100000) := by
  exact
    packedTile32768 987756800 987822336 13 3202 31428 30 _ _ (2071093 / 100000) (258887 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987822336 :
    ThetaLowerSegment 987822336 987887872 (98778472758591 / 100000) (98785073354291 / 100000) := by
  exact
    packedTile32768 987822336 987887872 13 3187 31429 30 _ _ (20711 / 1000) (2071103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987887872 :
    ThetaLowerSegment 987887872 987953408 (98785073354291 / 100000) (98791427507499 / 100000) := by
  exact
    packedTile32768 987887872 987953408 13 3068 31430 30 _ _ (1035553 / 50000) (2071109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell987953408 :
    ThetaLowerSegment 987953408 988018944 (98791427507499 / 100000) (98798084064681 / 100000) := by
  exact
    packedTile32768 987953408 988018944 13 3214 31431 30 _ _ (2071113 / 100000) (517779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988018944 :
    ThetaLowerSegment 988018944 988084480 (98798084064681 / 100000) (98804695079721 / 100000) := by
  exact
    packedTile32768 988018944 988084480 13 3192 31432 30 _ _ (25889 / 1250) (2071123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988084480 :
    ThetaLowerSegment 988084480 988150016 (98804695079721 / 100000) (98811235695629 / 100000) := by
  exact
    packedTile32768 988084480 988150016 13 3158 31433 30 _ _ (1035563 / 50000) (2071129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988150016 :
    ThetaLowerSegment 988150016 988215552 (98811235695629 / 100000) (98817693488323 / 100000) := by
  exact
    packedTile32768 988150016 988215552 13 3118 31434 30 _ _ (2071133 / 100000) (64723 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988215552 :
    ThetaLowerSegment 988215552 988281088 (98817693488323 / 100000) (98824215508183 / 100000) := by
  exact
    packedTile32768 988215552 988281088 13 3149 31435 30 _ _ (103557 / 5000) (2071143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988281088 :
    ThetaLowerSegment 988281088 988346624 (98824215508183 / 100000) (19766152894367 / 20000) := by
  exact
    packedTile32768 988281088 988346624 13 3162 31436 30 _ _ (1035573 / 50000) (2071149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988346624 :
    ThetaLowerSegment 988346624 988412160 (19766152894367 / 20000) (49418695045141 / 50000) := by
  exact
    packedTile32768 988346624 988412160 13 3199 31437 30 _ _ (2071153 / 100000) (517789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988412160 :
    ThetaLowerSegment 988412160 988477696 (49418695045141 / 50000) (49421974727001 / 50000) := by
  exact
    packedTile32768 988412160 988477696 13 3167 31439 30 _ _ (51779 / 2500) (2071163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988477696 :
    ThetaLowerSegment 988477696 988543232 (49421974727001 / 50000) (3089075941638 / 3125) := by
  exact
    packedTile32768 988477696 988543232 13 3129 31440 30 _ _ (1035583 / 50000) (2071169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988543232 :
    ThetaLowerSegment 988543232 988608768 (3089075941638 / 3125) (49428456451953 / 50000) := by
  exact
    packedTile32768 988543232 988608768 13 3130 31441 30 _ _ (2071173 / 100000) (258897 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988608768 :
    ThetaLowerSegment 988608768 988674304 (49428456451953 / 50000) (24715859279439 / 25000) := by
  exact
    packedTile32768 988608768 988674304 13 3150 31442 30 _ _ (2071179 / 100000) (1035591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988674304 :
    ThetaLowerSegment 988674304 988739840 (24715859279439 / 25000) (2471748205367 / 2500) := by
  exact
    packedTile32768 988674304 988739840 13 3134 31443 30 _ _ (1035593 / 50000) (2071189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988739840 :
    ThetaLowerSegment 988739840 988805376 (2471748205367 / 2500) (9887657674421 / 10000) := by
  exact
    packedTile32768 988739840 988805376 13 3210 31444 30 _ _ (2071193 / 100000) (517799 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988805376 :
    ThetaLowerSegment 988805376 988870912 (9887657674421 / 10000) (98883156943433 / 100000) := by
  exact
    packedTile32768 988805376 988870912 13 3177 31445 30 _ _ (2071199 / 100000) (1035601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988870912 :
    ThetaLowerSegment 988870912 988936448 (98883156943433 / 100000) (98889724737659 / 100000) := by
  exact
    packedTile32768 988870912 988936448 13 3171 31446 30 _ _ (1035603 / 50000) (2071209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell988936448 :
    ThetaLowerSegment 988936448 989001984 (98889724737659 / 100000) (2472405553321 / 2500) := by
  exact
    packedTile32768 988936448 989001984 13 3137 31447 30 _ _ (2071213 / 100000) (129451 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989001984 :
    ThetaLowerSegment 989001984 989067520 (2472405553321 / 2500) (49451410518287 / 50000) := by
  exact
    packedTile32768 989001984 989067520 13 3186 31448 30 _ _ (2071219 / 100000) (1035611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989067520 :
    ThetaLowerSegment 989067520 989133056 (49451410518287 / 50000) (49454670628011 / 50000) := by
  exact
    packedTile32768 989067520 989133056 13 3148 31449 30 _ _ (1035613 / 50000) (2071229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989133056 :
    ThetaLowerSegment 989133056 989198592 (49454670628011 / 50000) (49457987706059 / 50000) := by
  exact
    packedTile32768 989133056 989198592 13 3203 31450 30 _ _ (64726 / 3125) (414247 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989198592 :
    ThetaLowerSegment 989198592 989264128 (49457987706059 / 50000) (98922601305679 / 100000) := by
  exact
    packedTile32768 989198592 989264128 13 3199 31451 30 _ _ (2071239 / 100000) (1035621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989264128 :
    ThetaLowerSegment 989264128 989329664 (98922601305679 / 100000) (19785819346627 / 20000) := by
  exact
    packedTile32768 989264128 989329664 13 3136 31452 30 _ _ (1035623 / 50000) (2071249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989329664 :
    ThetaLowerSegment 989329664 989395200 (19785819346627 / 20000) (98935606678171 / 100000) := by
  exact
    packedTile32768 989329664 989395200 13 3143 31453 30 _ _ (517813 / 25000) (414251 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989395200 :
    ThetaLowerSegment 989395200 989460736 (98935606678171 / 100000) (98942106288913 / 100000) := by
  exact
    packedTile32768 989395200 989460736 13 3138 31454 30 _ _ (2071259 / 100000) (1035631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989460736 :
    ThetaLowerSegment 989460736 989526272 (98942106288913 / 100000) (19789720770071 / 20000) := by
  exact
    packedTile32768 989460736 989526272 13 3137 31455 30 _ _ (1035633 / 50000) (2071269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989526272 :
    ThetaLowerSegment 989526272 989591808 (19789720770071 / 20000) (98955198780403 / 100000) := by
  exact
    packedTile32768 989526272 989591808 13 3184 31456 30 _ _ (258909 / 12500) (82851 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989591808 :
    ThetaLowerSegment 989591808 989657344 (98955198780403 / 100000) (98961955292501 / 100000) := by
  exact
    packedTile32768 989591808 989657344 13 3262 31457 30 _ _ (2071279 / 100000) (1035641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989657344 :
    ThetaLowerSegment 989657344 989722880 (98961955292501 / 100000) (98968442557121 / 100000) := by
  exact
    packedTile32768 989657344 989722880 13 3132 31458 30 _ _ (414257 / 20000) (258911 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989722880 :
    ThetaLowerSegment 989722880 989788416 (98968442557121 / 100000) (98974975412089 / 100000) := by
  exact
    packedTile32768 989722880 989788416 13 3154 31459 30 _ _ (517823 / 25000) (414259 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989788416 :
    ThetaLowerSegment 989788416 989853952 (98974975412089 / 100000) (98981553857713 / 100000) := by
  exact
    packedTile32768 989788416 989853952 13 3176 31460 30 _ _ (2071299 / 100000) (1035651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989853952 :
    ThetaLowerSegment 989853952 989919488 (98981553857713 / 100000) (98988020471923 / 100000) := by
  exact
    packedTile32768 989853952 989919488 13 3122 31461 30 _ _ (414261 / 20000) (517827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989919488 :
    ThetaLowerSegment 989919488 989985024 (98988020471923 / 100000) (19798901149959 / 20000) := by
  exact
    packedTile32768 989919488 989985024 13 3131 31462 30 _ _ (129457 / 6250) (414263 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell989985024 :
    ThetaLowerSegment 989985024 990050560 (19798901149959 / 20000) (24750278832181 / 25000) := by
  exact
    packedTile32768 989985024 990050560 13 3191 31464 30 _ _ (2071319 / 100000) (1035661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990050560 :
    ThetaLowerSegment 990050560 990116096 (24750278832181 / 25000) (6187981383889 / 6250) := by
  exact
    packedTile32768 990050560 990116096 13 3180 31465 30 _ _ (82853 / 4000) (64729 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990116096 :
    ThetaLowerSegment 990116096 990181632 (6187981383889 / 6250) (6188395650289 / 6250) := by
  exact
    packedTile32768 990116096 990181632 13 3200 31466 30 _ _ (517833 / 25000) (414267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990181632 :
    ThetaLowerSegment 990181632 990247168 (6188395650289 / 6250) (6188799561199 / 6250) := by
  exact
    packedTile32768 990181632 990247168 13 3120 31467 30 _ _ (1035669 / 50000) (2071341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990247168 :
    ThetaLowerSegment 990247168 990312704 (6188799561199 / 6250) (49513708570247 / 50000) := by
  exact
    packedTile32768 990247168 990312704 13 3198 31468 30 _ _ (414269 / 20000) (517837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990312704 :
    ThetaLowerSegment 990312704 990378240 (49513708570247 / 50000) (49516945057747 / 50000) := by
  exact
    packedTile32768 990312704 990378240 13 3125 31469 30 _ _ (258919 / 12500) (414271 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990378240 :
    ThetaLowerSegment 990378240 990443776 (49516945057747 / 50000) (9904035689517 / 10000) := by
  exact
    packedTile32768 990378240 990443776 13 3122 31470 30 _ _ (1035679 / 50000) (2071361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990443776 :
    ThetaLowerSegment 990443776 990509312 (9904035689517 / 10000) (19809390009993 / 20000) := by
  exact
    packedTile32768 990443776 990509312 13 3183 31471 30 _ _ (414273 / 20000) (258921 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990509312 :
    ThetaLowerSegment 990509312 990574848 (19809390009993 / 20000) (99053487296841 / 100000) := by
  exact
    packedTile32768 990509312 990574848 13 3156 31472 30 _ _ (2071371 / 100000) (1035687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990574848 :
    ThetaLowerSegment 990574848 990640384 (99053487296841 / 100000) (99060045279589 / 100000) := by
  exact
    packedTile32768 990574848 990640384 13 3166 31473 30 _ _ (1035689 / 50000) (2071381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990640384 :
    ThetaLowerSegment 990640384 990705920 (99060045279589 / 100000) (49533317177637 / 50000) := by
  exact
    packedTile32768 990640384 990705920 13 3181 31474 30 _ _ (414277 / 20000) (517847 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990705920 :
    ThetaLowerSegment 990705920 990771456 (49533317177637 / 50000) (99073273163429 / 100000) := by
  exact
    packedTile32768 990705920 990771456 13 3205 31475 30 _ _ (2071391 / 100000) (1035697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990771456 :
    ThetaLowerSegment 990771456 990836992 (99073273163429 / 100000) (99079785638741 / 100000) := by
  exact
    packedTile32768 990771456 990836992 13 3144 31476 30 _ _ (1035699 / 50000) (2071401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990836992 :
    ThetaLowerSegment 990836992 990902528 (99079785638741 / 100000) (99086389277881 / 100000) := by
  exact
    packedTile32768 990836992 990902528 13 3188 31477 30 _ _ (414281 / 20000) (129463 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990902528 :
    ThetaLowerSegment 990902528 990968064 (99086389277881 / 100000) (24773225966369 / 25000) := by
  exact
    packedTile32768 990902528 990968064 13 3145 31478 30 _ _ (2071411 / 100000) (1035707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell990968064 :
    ThetaLowerSegment 990968064 991033600 (24773225966369 / 25000) (49549744451649 / 50000) := by
  exact
    packedTile32768 990968064 991033600 13 3179 31479 30 _ _ (1035709 / 50000) (2071421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991033600 :
    ThetaLowerSegment 991033600 991099136 (49549744451649 / 50000) (49553053551489 / 50000) := by
  exact
    packedTile32768 991033600 991099136 13 3195 31480 30 _ _ (64732 / 3125) (2071427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991099136 :
    ThetaLowerSegment 991099136 991164672 (49553053551489 / 50000) (19822537607853 / 20000) := by
  exact
    packedTile32768 991099136 991164672 13 3177 31481 30 _ _ (2071431 / 100000) (1035717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991164672 :
    ThetaLowerSegment 991164672 991230208 (19822537607853 / 20000) (99119302140799 / 100000) := by
  exact
    packedTile32768 991164672 991230208 13 3193 31482 30 _ _ (1035719 / 50000) (2071441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991230208 :
    ThetaLowerSegment 991230208 991295744 (99119302140799 / 100000) (19825185738031 / 20000) := by
  exact
    packedTile32768 991230208 991295744 13 3199 31483 30 _ _ (517861 / 25000) (2071447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991295744 :
    ThetaLowerSegment 991295744 991361280 (19825185738031 / 20000) (24783132601123 / 25000) := by
  exact
    packedTile32768 991295744 991361280 13 3187 31484 30 _ _ (2071451 / 100000) (1035727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991361280 :
    ThetaLowerSegment 991361280 991426816 (24783132601123 / 25000) (99139078280069 / 100000) := by
  exact
    packedTile32768 991361280 991426816 13 3161 31485 30 _ _ (2071457 / 100000) (103573 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991426816 :
    ThetaLowerSegment 991426816 991492352 (99139078280069 / 100000) (19829169979177 / 20000) := by
  exact
    packedTile32768 991426816 991492352 13 3269 31486 30 _ _ (258933 / 12500) (2071467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991492352 :
    ThetaLowerSegment 991492352 991557888 (19829169979177 / 20000) (24788062167451 / 25000) := by
  exact
    packedTile32768 991492352 991557888 13 3089 31487 30 _ _ (2071471 / 100000) (1035737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991557888 :
    ThetaLowerSegment 991557888 991623424 (24788062167451 / 25000) (99158751036107 / 100000) := by
  exact
    packedTile32768 991557888 991623424 13 3139 31489 30 _ _ (2071477 / 100000) (51787 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991623424 :
    ThetaLowerSegment 991623424 991688960 (99158751036107 / 100000) (99165257567351 / 100000) := by
  exact
    packedTile32768 991623424 991688960 13 3141 31490 30 _ _ (517871 / 25000) (2071487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991688960 :
    ThetaLowerSegment 991688960 991754496 (99165257567351 / 100000) (99171712333307 / 100000) := by
  exact
    packedTile32768 991688960 991754496 13 3116 31491 30 _ _ (2071491 / 100000) (1035747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991754496 :
    ThetaLowerSegment 991754496 991820032 (99171712333307 / 100000) (12397281506167 / 12500) := by
  exact
    packedTile32768 991754496 991820032 13 3157 31492 30 _ _ (2071497 / 100000) (4143 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991820032 :
    ThetaLowerSegment 991820032 991885568 (12397281506167 / 12500) (12398093017859 / 12500) := by
  exact
    packedTile32768 991820032 991885568 13 3134 31493 30 _ _ (129469 / 6250) (2071507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991885568 :
    ThetaLowerSegment 991885568 991951104 (12398093017859 / 12500) (12398907121289 / 12500) := by
  exact
    packedTile32768 991885568 991951104 13 3144 31494 30 _ _ (207151 / 10000) (2071513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell991951104 :
    ThetaLowerSegment 991951104 992016640 (12398907121289 / 12500) (4959886419471 / 5000) := by
  exact
    packedTile32768 991951104 992016640 13 3124 31495 30 _ _ (2071517 / 100000) (12947 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992016640 :
    ThetaLowerSegment 992016640 992082176 (4959886419471 / 5000) (6200266244037 / 6250) := by
  exact
    packedTile32768 992016640 992082176 13 3153 31496 30 _ _ (517881 / 25000) (2071527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992082176 :
    ThetaLowerSegment 992082176 992147712 (6200266244037 / 6250) (49605426792291 / 50000) := by
  exact
    packedTile32768 992082176 992147712 13 3183 31497 30 _ _ (207153 / 10000) (2071533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992147712 :
    ThetaLowerSegment 992147712 992213248 (49605426792291 / 50000) (99217434857631 / 100000) := by
  exact
    packedTile32768 992147712 992213248 13 3177 31498 30 _ _ (2071537 / 100000) (103577 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992213248 :
    ThetaLowerSegment 992213248 992278784 (99217434857631 / 100000) (49612012217957 / 50000) := by
  exact
    packedTile32768 992213248 992278784 13 3181 31499 30 _ _ (2071543 / 100000) (1035773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992278784 :
    ThetaLowerSegment 992278784 992344320 (49612012217957 / 50000) (3100955134977 / 3125) := by
  exact
    packedTile32768 992278784 992344320 13 3157 31500 30 _ _ (41431 / 2000) (2071553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992344320 :
    ThetaLowerSegment 992344320 992409856 (3100955134977 / 3125) (99237050364231 / 100000) := by
  exact
    packedTile32768 992344320 992409856 13 3131 31501 30 _ _ (2071557 / 100000) (51789 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992409856 :
    ThetaLowerSegment 992409856 992475392 (99237050364231 / 100000) (2481092139513 / 2500) := by
  exact
    packedTile32768 992409856 992475392 13 3203 31502 30 _ _ (2071563 / 100000) (1035783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992475392 :
    ThetaLowerSegment 992475392 992540928 (2481092139513 / 2500) (2481253307659 / 2500) := by
  exact
    packedTile32768 992475392 992540928 13 3112 31503 30 _ _ (207157 / 10000) (2071573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992540928 :
    ThetaLowerSegment 992540928 992606464 (2481253307659 / 2500) (6203543570669 / 6250) := by
  exact
    packedTile32768 992540928 992606464 13 3169 31504 30 _ _ (258947 / 12500) (2071579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992606464 :
    ThetaLowerSegment 992606464 992672000 (6203543570669 / 6250) (99263232975069 / 100000) := by
  exact
    packedTile32768 992606464 992672000 13 3155 31505 30 _ _ (2071583 / 100000) (1035793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992672000 :
    ThetaLowerSegment 992672000 992737536 (99263232975069 / 100000) (99269799915369 / 100000) := by
  exact
    packedTile32768 992672000 992737536 13 3170 31506 30 _ _ (207159 / 10000) (2071593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992737536 :
    ThetaLowerSegment 992737536 992803072 (99269799915369 / 100000) (99276387590649 / 100000) := by
  exact
    packedTile32768 992737536 992803072 13 3180 31507 30 _ _ (517899 / 25000) (2071599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992803072 :
    ThetaLowerSegment 992803072 992868608 (99276387590649 / 100000) (99282987717807 / 100000) := by
  exact
    packedTile32768 992803072 992868608 13 3186 31508 30 _ _ (2071603 / 100000) (1035803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992868608 :
    ThetaLowerSegment 992868608 992934144 (99282987717807 / 100000) (9928963136787 / 10000) := by
  exact
    packedTile32768 992868608 992934144 13 3207 31509 30 _ _ (2071609 / 100000) (517903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992934144 :
    ThetaLowerSegment 992934144 992999680 (9928963136787 / 10000) (9929612588403 / 10000) := by
  exact
    packedTile32768 992934144 992999680 13 3135 31510 30 _ _ (64738 / 3125) (2071619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell992999680 :
    ThetaLowerSegment 992999680 993065216 (9929612588403 / 10000) (99302636995119 / 100000) := by
  exact
    packedTile32768 992999680 993065216 13 3143 31511 30 _ _ (2071623 / 100000) (1035813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993065216 :
    ThetaLowerSegment 993065216 993130752 (99302636995119 / 100000) (6206829785379 / 6250) := by
  exact
    packedTile32768 993065216 993130752 13 3205 31512 30 _ _ (2071629 / 100000) (129477 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993130752 :
    ThetaLowerSegment 993130752 993196288 (6206829785379 / 6250) (24828983183133 / 25000) := by
  exact
    packedTile32768 993130752 993196288 13 3213 31513 30 _ _ (517909 / 25000) (2071639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993196288 :
    ThetaLowerSegment 993196288 993261824 (24828983183133 / 25000) (49661230238237 / 50000) := by
  exact
    packedTile32768 993196288 993261824 13 3151 31515 30 _ _ (1035821 / 50000) (414329 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993261824 :
    ThetaLowerSegment 993261824 993327360 (49661230238237 / 50000) (24832252757653 / 25000) := by
  exact
    packedTile32768 993261824 993327360 13 3162 31516 30 _ _ (2071649 / 100000) (517913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993327360 :
    ThetaLowerSegment 993327360 993392896 (24832252757653 / 25000) (993355326037 / 1000) := by
  exact
    packedTile32768 993327360 993392896 13 3148 31517 30 _ _ (258957 / 12500) (2071659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993392896 :
    ThetaLowerSegment 993392896 993458432 (993355326037 / 1000) (12417755220713 / 12500) := by
  exact
    packedTile32768 993392896 993458432 13 3142 31518 30 _ _ (1035831 / 50000) (414333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993458432 :
    ThetaLowerSegment 993458432 993523968 (12417755220713 / 12500) (24837136701591 / 25000) := by
  exact
    packedTile32768 993458432 993523968 13 3140 31519 30 _ _ (2071669 / 100000) (258959 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993523968 :
    ThetaLowerSegment 993523968 993589504 (24837136701591 / 25000) (99355078797639 / 100000) := by
  exact
    packedTile32768 993523968 993589504 13 3153 31520 30 _ _ (82867 / 4000) (1035839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993589504 :
    ThetaLowerSegment 993589504 993655040 (99355078797639 / 100000) (99361627384441 / 100000) := by
  exact
    packedTile32768 993589504 993655040 13 3161 31521 30 _ _ (1035841 / 50000) (414337 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993655040 :
    ThetaLowerSegment 993655040 993720576 (99361627384441 / 100000) (49684112856953 / 50000) := by
  exact
    packedTile32768 993655040 993720576 13 3185 31522 30 _ _ (2071689 / 100000) (517923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993720576 :
    ThetaLowerSegment 993720576 993786112 (49684112856953 / 50000) (99374774341801 / 100000) := by
  exact
    packedTile32768 993720576 993786112 13 3161 31523 30 _ _ (414339 / 20000) (1035849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993786112 :
    ThetaLowerSegment 993786112 993851648 (99374774341801 / 100000) (99381196618001 / 100000) := by
  exact
    packedTile32768 993786112 993851648 13 3100 31524 30 _ _ (1035851 / 50000) (414341 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993851648 :
    ThetaLowerSegment 993851648 993917184 (99381196618001 / 100000) (99387699709413 / 100000) := by
  exact
    packedTile32768 993851648 993917184 13 3139 31525 30 _ _ (517927 / 25000) (2071711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993917184 :
    ThetaLowerSegment 993917184 993982720 (99387699709413 / 100000) (24848597319287 / 25000) := by
  exact
    packedTile32768 993917184 993982720 13 3229 31526 30 _ _ (414343 / 20000) (1035859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell993982720 :
    ThetaLowerSegment 993982720 994048256 (24848597319287 / 25000) (9940085512151 / 10000) := by
  exact
    packedTile32768 993982720 994048256 13 3121 31527 30 _ _ (1035861 / 50000) (82869 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994048256 :
    ThetaLowerSegment 994048256 994113792 (9940085512151 / 10000) (49703717464819 / 50000) := by
  exact
    packedTile32768 994048256 994113792 13 3176 31528 30 _ _ (129483 / 6250) (2071731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994113792 :
    ThetaLowerSegment 994113792 994179328 (49703717464819 / 50000) (99413962966623 / 100000) := by
  exact
    packedTile32768 994113792 994179328 13 3151 31529 30 _ _ (414347 / 20000) (1035869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994179328 :
    ThetaLowerSegment 994179328 994244864 (99413962966623 / 100000) (99420497237737 / 100000) := by
  exact
    packedTile32768 994179328 994244864 13 3154 31530 30 _ _ (2071741 / 100000) (64742 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994244864 :
    ThetaLowerSegment 994244864 994310400 (99420497237737 / 100000) (99427166194549 / 100000) := by
  exact
    packedTile32768 994244864 994310400 13 3219 31531 30 _ _ (517937 / 25000) (2071751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994310400 :
    ThetaLowerSegment 994310400 994375936 (99427166194549 / 100000) (99433764731039 / 100000) := by
  exact
    packedTile32768 994310400 994375936 13 3185 31532 30 _ _ (1035877 / 50000) (2071757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994375936 :
    ThetaLowerSegment 994375936 994441472 (99433764731039 / 100000) (24860059746041 / 25000) := by
  exact
    packedTile32768 994375936 994441472 13 3125 31533 30 _ _ (2071761 / 100000) (517941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994441472 :
    ThetaLowerSegment 994441472 994507008 (24860059746041 / 25000) (24861695924819 / 25000) := by
  exact
    packedTile32768 994441472 994507008 13 3159 31534 30 _ _ (258971 / 12500) (2071771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994507008 :
    ThetaLowerSegment 994507008 994572544 (24861695924819 / 25000) (6215842220581 / 6250) := by
  exact
    packedTile32768 994507008 994572544 13 3230 31535 30 _ _ (1035887 / 50000) (2071777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994572544 :
    ThetaLowerSegment 994572544 994638080 (6215842220581 / 6250) (19891991626409 / 20000) := by
  exact
    packedTile32768 994572544 994638080 13 3129 31536 30 _ _ (2071781 / 100000) (258973 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994638080 :
    ThetaLowerSegment 994638080 994703616 (19891991626409 / 20000) (49733255597163 / 50000) := by
  exact
    packedTile32768 994638080 994703616 13 3163 31537 30 _ _ (2071787 / 100000) (207179 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994703616 :
    ThetaLowerSegment 994703616 994769152 (49733255597163 / 50000) (24868263997893 / 25000) := by
  exact
    packedTile32768 994703616 994769152 13 3159 31538 30 _ _ (1035897 / 50000) (2071797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994769152 :
    ThetaLowerSegment 994769152 994834688 (24868263997893 / 25000) (99479559374911 / 100000) := by
  exact
    packedTile32768 994769152 994834688 13 3139 31539 30 _ _ (2071801 / 100000) (517951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994834688 :
    ThetaLowerSegment 994834688 994900224 (99479559374911 / 100000) (99486160152013 / 100000) := by
  exact
    packedTile32768 994834688 994900224 13 3186 31541 30 _ _ (2071807 / 100000) (207181 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994900224 :
    ThetaLowerSegment 994900224 994965760 (99486160152013 / 100000) (19898532300869 / 20000) := by
  exact
    packedTile32768 994900224 994965760 13 3138 31542 30 _ _ (1035907 / 50000) (2071817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell994965760 :
    ThetaLowerSegment 994965760 995031296 (19898532300869 / 20000) (19899839619289 / 20000) := by
  exact
    packedTile32768 994965760 995031296 13 3155 31543 30 _ _ (103591 / 5000) (2071823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995031296 :
    ThetaLowerSegment 995031296 995096832 (19899839619289 / 20000) (99505939821503 / 100000) := by
  exact
    packedTile32768 995031296 995096832 13 3254 31544 30 _ _ (2071827 / 100000) (207183 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995096832 :
    ThetaLowerSegment 995096832 995162368 (99505939821503 / 100000) (99512592480477 / 100000) := by
  exact
    packedTile32768 995096832 995162368 13 3211 31545 30 _ _ (1035917 / 50000) (2071837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995162368 :
    ThetaLowerSegment 995162368 995227904 (99512592480477 / 100000) (99519093914397 / 100000) := by
  exact
    packedTile32768 995162368 995227904 13 3138 31546 30 _ _ (12949 / 625) (2071843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995227904 :
    ThetaLowerSegment 995227904 995293440 (99519093914397 / 100000) (3110175049557 / 3125) := by
  exact
    packedTile32768 995227904 995293440 13 3141 31547 30 _ _ (2071847 / 100000) (41437 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995293440 :
    ThetaLowerSegment 995293440 995358976 (3110175049557 / 3125) (99532113419803 / 100000) := by
  exact
    packedTile32768 995293440 995358976 13 3143 31548 30 _ _ (2071853 / 100000) (129491 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995358976 :
    ThetaLowerSegment 995358976 995424512 (99532113419803 / 100000) (99538621132063 / 100000) := by
  exact
    packedTile32768 995358976 995424512 13 3141 31549 30 _ _ (103593 / 5000) (2071863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995424512 :
    ThetaLowerSegment 995424512 995490048 (99538621132063 / 100000) (99545180659819 / 100000) := by
  exact
    packedTile32768 995424512 995490048 13 3166 31550 30 _ _ (1035933 / 50000) (2071869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995490048 :
    ThetaLowerSegment 995490048 995555584 (99545180659819 / 100000) (99551756784721 / 100000) := by
  exact
    packedTile32768 995490048 995555584 13 3174 31551 30 _ _ (2071873 / 100000) (517969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995555584 :
    ThetaLowerSegment 995555584 995621120 (99551756784721 / 100000) (99558233481601 / 100000) := by
  exact
    packedTile32768 995555584 995621120 13 3126 31552 30 _ _ (51797 / 2500) (2071883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995621120 :
    ThetaLowerSegment 995621120 995686656 (99558233481601 / 100000) (99564749563071 / 100000) := by
  exact
    packedTile32768 995621120 995686656 13 3145 31553 30 _ _ (1035943 / 50000) (2071889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995686656 :
    ThetaLowerSegment 995686656 995752192 (99564749563071 / 100000) (99571305032523 / 100000) := by
  exact
    packedTile32768 995686656 995752192 13 3164 31554 30 _ _ (2071893 / 100000) (258987 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995752192 :
    ThetaLowerSegment 995752192 995817728 (99571305032523 / 100000) (6223624958637 / 6250) := by
  exact
    packedTile32768 995752192 995817728 13 3231 31555 30 _ _ (2071899 / 100000) (1035951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995817728 :
    ThetaLowerSegment 995817728 995883264 (6223624958637 / 6250) (12448063140379 / 12500) := by
  exact
    packedTile32768 995817728 995883264 13 3140 31556 30 _ _ (1035953 / 50000) (2071909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995883264 :
    ThetaLowerSegment 995883264 995948800 (12448063140379 / 12500) (19918194312701 / 20000) := by
  exact
    packedTile32768 995883264 995948800 13 3121 31557 30 _ _ (2071913 / 100000) (517979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell995948800 :
    ThetaLowerSegment 995948800 996014336 (19918194312701 / 20000) (49798770809327 / 50000) := by
  exact
    packedTile32768 995948800 996014336 13 3171 31558 30 _ _ (2071919 / 100000) (1035961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996014336 :
    ThetaLowerSegment 996014336 996079872 (49798770809327 / 50000) (24901055895001 / 25000) := by
  exact
    packedTile32768 996014336 996079872 13 3225 31559 30 _ _ (1035963 / 50000) (2071929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996079872 :
    ThetaLowerSegment 996079872 996145408 (24901055895001 / 25000) (24902701009009 / 25000) := by
  exact
    packedTile32768 996079872 996145408 13 3176 31560 30 _ _ (517983 / 25000) (414387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996145408 :
    ThetaLowerSegment 996145408 996210944 (24902701009009 / 25000) (99617295420923 / 100000) := by
  exact
    packedTile32768 996145408 996210944 13 3133 31561 30 _ _ (2071939 / 100000) (1035971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996210944 :
    ThetaLowerSegment 996210944 996276480 (99617295420923 / 100000) (99623871774353 / 100000) := by
  exact
    packedTile32768 996210944 996276480 13 3174 31562 30 _ _ (414389 / 20000) (517987 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996276480 :
    ThetaLowerSegment 996276480 996342016 (99623871774353 / 100000) (19926092530733 / 20000) := by
  exact
    packedTile32768 996276480 996342016 13 3181 31563 30 _ _ (129497 / 6250) (414391 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996342016 :
    ThetaLowerSegment 996342016 996407552 (19926092530733 / 20000) (49818557857007 / 50000) := by
  exact
    packedTile32768 996342016 996407552 13 3211 31564 30 _ _ (2071959 / 100000) (1035981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996407552 :
    ThetaLowerSegment 996407552 996473088 (49818557857007 / 50000) (49821810842057 / 50000) := by
  exact
    packedTile32768 996407552 996473088 13 3140 31565 30 _ _ (414393 / 20000) (64749 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996473088 :
    ThetaLowerSegment 996473088 996538624 (49821810842057 / 50000) (9965018569141 / 10000) := by
  exact
    packedTile32768 996473088 996538624 13 3168 31566 30 _ _ (517993 / 25000) (82879 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996538624 :
    ThetaLowerSegment 996538624 996604160 (9965018569141 / 10000) (9965673314189 / 10000) := by
  exact
    packedTile32768 996538624 996604160 13 3160 31568 30 _ _ (1035989 / 50000) (2071981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996604160 :
    ThetaLowerSegment 996604160 996669696 (9965673314189 / 10000) (2491581082969 / 2500) := by
  exact
    packedTile32768 996604160 996669696 13 3142 31569 30 _ _ (414397 / 20000) (517997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996669696 :
    ThetaLowerSegment 996669696 996735232 (2491581082969 / 2500) (99669921345753 / 100000) := by
  exact
    packedTile32768 996669696 996735232 13 3223 31570 30 _ _ (2071991 / 100000) (1035997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996735232 :
    ThetaLowerSegment 996735232 996800768 (99669921345753 / 100000) (19935289213491 / 20000) := by
  exact
    packedTile32768 996735232 996800768 13 3149 31571 30 _ _ (1035999 / 50000) (2072001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996800768 :
    ThetaLowerSegment 996800768 996866304 (19935289213491 / 20000) (623018981971 / 625) := by
  exact
    packedTile32768 996800768 996866304 13 3181 31572 30 _ _ (414401 / 20000) (259001 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996866304 :
    ThetaLowerSegment 996866304 996931840 (623018981971 / 625) (99689478997559 / 100000) := by
  exact
    packedTile32768 996866304 996931840 13 3109 31573 30 _ _ (2072011 / 100000) (1036007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996931840 :
    ThetaLowerSegment 996931840 996997376 (99689478997559 / 100000) (99696070086817 / 100000) := by
  exact
    packedTile32768 996931840 996997376 13 3181 31574 30 _ _ (1036009 / 50000) (2072021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell996997376 :
    ThetaLowerSegment 996997376 997062912 (99696070086817 / 100000) (99702644618969 / 100000) := by
  exact
    packedTile32768 996997376 997062912 13 3173 31575 30 _ _ (259003 / 12500) (2072027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997062912 :
    ThetaLowerSegment 997062912 997128448 (99702644618969 / 100000) (99709130075999 / 100000) := by
  exact
    packedTile32768 997062912 997128448 13 3130 31576 30 _ _ (2072031 / 100000) (1036017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997128448 :
    ThetaLowerSegment 997128448 997193984 (99709130075999 / 100000) (99715696364421 / 100000) := by
  exact
    packedTile32768 997128448 997193984 13 3169 31577 30 _ _ (1036019 / 50000) (2072041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997193984 :
    ThetaLowerSegment 997193984 997259520 (99715696364421 / 100000) (19944449219101 / 20000) := by
  exact
    packedTile32768 997193984 997259520 13 3161 31578 30 _ _ (518011 / 25000) (2072047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997259520 :
    ThetaLowerSegment 997259520 997325056 (19944449219101 / 20000) (24932207250383 / 25000) := by
  exact
    packedTile32768 997259520 997325056 13 3177 31579 30 _ _ (2072051 / 100000) (1036027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997325056 :
    ThetaLowerSegment 997325056 997390592 (24932207250383 / 25000) (12466910691393 / 12500) := by
  exact
    packedTile32768 997325056 997390592 13 3116 31580 30 _ _ (2072057 / 100000) (103603 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997390592 :
    ThetaLowerSegment 997390592 997456128 (12466910691393 / 12500) (12467736926913 / 12500) := by
  exact
    packedTile32768 997390592 997456128 13 3190 31581 30 _ _ (64752 / 3125) (2072067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997456128 :
    ThetaLowerSegment 997456128 997521664 (12467736926913 / 12500) (49874206037727 / 50000) := by
  exact
    packedTile32768 997456128 997521664 13 3145 31582 30 _ _ (207207 / 10000) (2072073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997521664 :
    ThetaLowerSegment 997521664 997587200 (49874206037727 / 50000) (99755061370547 / 100000) := by
  exact
    packedTile32768 997521664 997587200 13 3209 31583 30 _ _ (2072077 / 100000) (25901 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997587200 :
    ThetaLowerSegment 997587200 997652736 (99755061370547 / 100000) (99761584290979 / 100000) := by
  exact
    packedTile32768 997587200 997652736 13 3148 31584 30 _ _ (518021 / 25000) (2072087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997652736 :
    ThetaLowerSegment 997652736 997718272 (99761584290979 / 100000) (99768136239559 / 100000) := by
  exact
    packedTile32768 997652736 997718272 13 3162 31585 30 _ _ (207209 / 10000) (2072093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997718272 :
    ThetaLowerSegment 997718272 997783808 (99768136239559 / 100000) (24943690183417 / 25000) := by
  exact
    packedTile32768 997718272 997783808 13 3197 31586 30 _ _ (2072097 / 100000) (20721 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997783808 :
    ThetaLowerSegment 997783808 997849344 (24943690183417 / 25000) (49890660505883 / 50000) := by
  exact
    packedTile32768 997783808 997849344 13 3166 31587 30 _ _ (2072103 / 100000) (1036053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997849344 :
    ThetaLowerSegment 997849344 997914880 (49890660505883 / 50000) (24946998819519 / 25000) := by
  exact
    packedTile32768 997849344 997914880 13 3221 31588 30 _ _ (207211 / 10000) (2072113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997914880 :
    ThetaLowerSegment 997914880 997980416 (24946998819519 / 25000) (1247432022671 / 1250) := by
  exact
    packedTile32768 997914880 997980416 13 3169 31589 30 _ _ (518029 / 25000) (2072119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell997980416 :
    ThetaLowerSegment 997980416 998045952 (1247432022671 / 1250) (19960215728103 / 20000) := by
  exact
    packedTile32768 997980416 998045952 13 3145 31590 30 _ _ (2072123 / 100000) (1036063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998045952 :
    ThetaLowerSegment 998045952 998111488 (19960215728103 / 20000) (99807622423897 / 100000) := by
  exact
    packedTile32768 998045952 998111488 13 3158 31591 30 _ _ (2072129 / 100000) (518033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998111488 :
    ThetaLowerSegment 998111488 998177024 (99807622423897 / 100000) (99814133075209 / 100000) := by
  exact
    packedTile32768 998111488 998177024 13 3142 31592 30 _ _ (259017 / 12500) (2072139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998177024 :
    ThetaLowerSegment 998177024 998242560 (99814133075209 / 100000) (9982069555209 / 10000) := by
  exact
    packedTile32768 998177024 998242560 13 3167 31593 30 _ _ (2072143 / 100000) (1036073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998242560 :
    ThetaLowerSegment 998242560 998308096 (9982069555209 / 10000) (24956840931893 / 25000) := by
  exact
    packedTile32768 998242560 998308096 13 3218 31594 30 _ _ (2072149 / 100000) (259019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998308096 :
    ThetaLowerSegment 998308096 998373632 (24956840931893 / 25000) (24958493476303 / 25000) := by
  exact
    packedTile32768 998308096 998373632 13 3190 31596 30 _ _ (518039 / 25000) (2072159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998373632 :
    ThetaLowerSegment 998373632 998439168 (24958493476303 / 25000) (24960147061579 / 25000) := by
  exact
    packedTile32768 998373632 998439168 13 3192 31597 30 _ _ (1036081 / 50000) (414433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998439168 :
    ThetaLowerSegment 998439168 998504704 (24960147061579 / 25000) (6240447572899 / 6250) := by
  exact
    packedTile32768 998439168 998504704 13 3172 31598 30 _ _ (2072169 / 100000) (518043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998504704 :
    ThetaLowerSegment 998504704 998570240 (6240447572899 / 6250) (99853781765509 / 100000) := by
  exact
    packedTile32768 998504704 998570240 13 3195 31599 30 _ _ (82887 / 4000) (1036089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998570240 :
    ThetaLowerSegment 998570240 998635776 (99853781765509 / 100000) (99860344365903 / 100000) := by
  exact
    packedTile32768 998570240 998635776 13 3167 31600 30 _ _ (1036091 / 50000) (414437 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998635776 :
    ThetaLowerSegment 998635776 998701312 (99860344365903 / 100000) (49933503226769 / 50000) := by
  exact
    packedTile32768 998635776 998701312 13 3215 31601 30 _ _ (2072189 / 100000) (64756 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998701312 :
    ThetaLowerSegment 998701312 998766848 (49933503226769 / 50000) (49936785583649 / 50000) := by
  exact
    packedTile32768 998701312 998766848 13 3168 31602 30 _ _ (414439 / 20000) (1036099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998766848 :
    ThetaLowerSegment 998766848 998832384 (49936785583649 / 50000) (49940043085193 / 50000) := by
  exact
    packedTile32768 998766848 998832384 13 3144 31603 30 _ _ (1036101 / 50000) (414441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998832384 :
    ThetaLowerSegment 998832384 998897920 (49940043085193 / 50000) (9988670273053 / 10000) := by
  exact
    packedTile32768 998832384 998897920 13 3193 31604 30 _ _ (129513 / 6250) (2072211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998897920 :
    ThetaLowerSegment 998897920 998963456 (9988670273053 / 10000) (4994661510389 / 5000) := by
  exact
    packedTile32768 998897920 998963456 13 3150 31605 30 _ _ (414443 / 20000) (1036109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell998963456 :
    ThetaLowerSegment 998963456 999028992 (4994661510389 / 5000) (99899755631709 / 100000) := by
  exact
    packedTile32768 998963456 999028992 13 3149 31606 30 _ _ (2072221 / 100000) (64757 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999028992 :
    ThetaLowerSegment 999028992 999094528 (99899755631709 / 100000) (99906254138717 / 100000) := by
  exact
    packedTile32768 999028992 999094528 13 3136 31607 30 _ _ (518057 / 25000) (2072231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999094528 :
    ThetaLowerSegment 999094528 999160064 (99906254138717 / 100000) (99912756809009 / 100000) := by
  exact
    packedTile32768 999094528 999160064 13 3138 31608 30 _ _ (1036117 / 50000) (2072237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999160064 :
    ThetaLowerSegment 999160064 999225600 (99912756809009 / 100000) (49959666014851 / 50000) := by
  exact
    packedTile32768 999160064 999225600 13 3173 31609 30 _ _ (2072241 / 100000) (518061 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999225600 :
    ThetaLowerSegment 999225600 999291136 (49959666014851 / 50000) (1998517233663 / 2000) := by
  exact
    packedTile32768 999225600 999291136 13 3151 31610 30 _ _ (259031 / 12500) (2072251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999291136 :
    ThetaLowerSegment 999291136 999356672 (1998517233663 / 2000) (6245774459719 / 6250) := by
  exact
    packedTile32768 999291136 999356672 13 3151 31611 30 _ _ (1036127 / 50000) (2072257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999356672 :
    ThetaLowerSegment 999356672 999422208 (6245774459719 / 6250) (99938991506789 / 100000) := by
  exact
    packedTile32768 999356672 999422208 13 3185 31612 30 _ _ (2072261 / 100000) (259033 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999422208 :
    ThetaLowerSegment 999422208 999487744 (99938991506789 / 100000) (99945564737713 / 100000) := by
  exact
    packedTile32768 999422208 999487744 13 3172 31613 30 _ _ (2072267 / 100000) (207227 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999487744 :
    ThetaLowerSegment 999487744 999553280 (99945564737713 / 100000) (99951980498017 / 100000) := by
  exact
    packedTile32768 999487744 999553280 13 3096 31614 30 _ _ (1036137 / 50000) (2072277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999553280 :
    ThetaLowerSegment 999553280 999618816 (99951980498017 / 100000) (99958468806697 / 100000) := by
  exact
    packedTile32768 999553280 999618816 13 3131 31615 30 _ _ (51807 / 2500) (2072283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999618816 :
    ThetaLowerSegment 999618816 999684352 (99958468806697 / 100000) (9996497371559 / 10000) := by
  exact
    packedTile32768 999618816 999684352 13 3139 31616 30 _ _ (2072287 / 100000) (207229 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999684352 :
    ThetaLowerSegment 999684352 999749888 (9996497371559 / 10000) (499857144557 / 500) := by
  exact
    packedTile32768 999684352 999749888 13 3115 31617 30 _ _ (1036147 / 50000) (2072297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999749888 :
    ThetaLowerSegment 999749888 999815424 (499857144557 / 500) (999778343907 / 1000) := by
  exact
    packedTile32768 999749888 999815424 13 3091 31618 30 _ _ (20723 / 1000) (2072303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999815424 :
    ThetaLowerSegment 999815424 999880960 (999778343907 / 1000) (9998444505003 / 10000) := by
  exact
    packedTile32768 999815424 999880960 13 3190 31619 30 _ _ (2072307 / 100000) (207231 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999880960 :
    ThetaLowerSegment 999880960 999946496 (9998444505003 / 10000) (624943839264 / 625) := by
  exact
    packedTile32768 999880960 999946496 13 3170 31620 30 _ _ (2072313 / 100000) (518079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell999946496 :
    ThetaLowerSegment 999946496 1000012032 (624943839264 / 625) (624984651016 / 625) := by
  exact
    packedTile32768 999946496 1000012032 13 3151 31621 30 _ _ (12952 / 625) (2072323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000012032 :
    ThetaLowerSegment 1000012032 1000077568 (624984651016 / 625) (12500514697579 / 12500) := by
  exact
    packedTile32768 1000012032 1000077568 13 3172 31622 30 _ _ (1036163 / 50000) (2072329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000077568 :
    ThetaLowerSegment 1000077568 1000143104 (12500514697579 / 12500) (6250666634557 / 6250) := by
  exact
    packedTile32768 1000077568 1000143104 13 3160 31624 30 _ _ (2072333 / 100000) (129521 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000143104 :
    ThetaLowerSegment 1000143104 1000208640 (6250666634557 / 6250) (20003420982037 / 20000) := by
  exact
    packedTile32768 1000143104 1000208640 13 3107 31625 30 _ _ (2072339 / 100000) (1036171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000208640 :
    ThetaLowerSegment 1000208640 1000274176 (20003420982037 / 20000)
      (100023738489731 / 100000) := by
  exact
    packedTile32768 1000208640 1000274176 13 3201 31626 30 _ _ (1036173 / 50000) (2072349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000274176 :
    ThetaLowerSegment 1000274176 1000339712 (100023738489731 / 100000)
      (100030191793859 / 100000) := by
  exact
    packedTile32768 1000274176 1000339712 13 3114 31627 30 _ _ (64761 / 3125) (414471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000339712 :
    ThetaLowerSegment 1000339712 1000405248 (100030191793859 / 100000)
      (20007349747547 / 20000) := by
  exact
    packedTile32768 1000339712 1000405248 13 3164 31628 30 _ _ (2072359 / 100000) (1036181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000405248 :
    ThetaLowerSegment 1000405248 1000470784 (20007349747547 / 20000)
      (100043260111707 / 100000) := by
  exact
    packedTile32768 1000405248 1000470784 13 3142 31629 30 _ _ (1036183 / 50000) (2072369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000470784 :
    ThetaLowerSegment 1000470784 1000536320 (100043260111707 / 100000)
      (100049688609651 / 100000) := by
  exact
    packedTile32768 1000470784 1000536320 13 3102 31630 30 _ _ (518093 / 25000) (16579 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000536320 :
    ThetaLowerSegment 1000536320 1000601856 (100049688609651 / 100000)
      (50028103120803 / 50000) := by
  exact
    packedTile32768 1000536320 1000601856 13 3145 31631 30 _ _ (2072379 / 100000) (1036191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000601856 :
    ThetaLowerSegment 1000601856 1000667392 (50028103120803 / 50000) (12507855252297 / 12500) := by
  exact
    packedTile32768 1000601856 1000667392 13 3202 31632 30 _ _ (414477 / 20000) (518097 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000667392 :
    ThetaLowerSegment 1000667392 1000732928 (12507855252297 / 12500) (12508660376589 / 12500) := by
  exact
    packedTile32768 1000667392 1000732928 13 3108 31633 30 _ _ (259049 / 12500) (414479 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000732928 :
    ThetaLowerSegment 1000732928 1000798464 (12508660376589 / 12500) (10007595820667 / 10000) := by
  exact
    packedTile32768 1000732928 1000798464 13 3221 31634 30 _ _ (1036199 / 50000) (2072401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000798464 :
    ThetaLowerSegment 1000798464 1000864000 (10007595820667 / 10000) (10008250700647 / 10000) := by
  exact
    packedTile32768 1000798464 1000864000 13 3160 31635 30 _ _ (414481 / 20000) (259051 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000864000 :
    ThetaLowerSegment 1000864000 1000929536 (10008250700647 / 10000)
      (100088970856379 / 100000) := by
  exact
    packedTile32768 1000864000 1000929536 13 3119 31636 30 _ _ (2072411 / 100000) (1036207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000929536 :
    ThetaLowerSegment 1000929536 1000995072 (100088970856379 / 100000)
      (100095631607831 / 100000) := by
  exact
    packedTile32768 1000929536 1000995072 13 3214 31637 30 _ _ (1036209 / 50000) (2072421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1000995072 :
    ThetaLowerSegment 1000995072 1001060608 (100095631607831 / 100000)
      (100102246788431 / 100000) := by
  exact
    packedTile32768 1000995072 1001060608 13 3192 31638 30 _ _ (82897 / 4000) (518107 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001060608 :
    ThetaLowerSegment 1001060608 1001126144 (100102246788431 / 100000)
      (100108745932047 / 100000) := by
  exact
    packedTile32768 1001060608 1001126144 13 3136 31639 30 _ _ (2072431 / 100000) (1036217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001126144 :
    ThetaLowerSegment 1001126144 1001191680 (100108745932047 / 100000)
      (100115487572861 / 100000) := by
  exact
    packedTile32768 1001126144 1001191680 13 3253 31640 30 _ _ (1036219 / 50000) (2072441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001191680 :
    ThetaLowerSegment 1001191680 1001257216 (100115487572861 / 100000)
      (100122036495901 / 100000) := by
  exact
    packedTile32768 1001191680 1001257216 13 3160 31641 30 _ _ (518111 / 25000) (2072447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001257216 :
    ThetaLowerSegment 1001257216 1001322752 (100122036495901 / 100000)
      (100128432079687 / 100000) := by
  exact
    packedTile32768 1001257216 1001322752 13 3086 31642 30 _ _ (2072451 / 100000) (1036227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001322752 :
    ThetaLowerSegment 1001322752 1001339136 (100128432079687 / 100000)
      (50065035696587 / 50000) := by
  exact
    packedTile32768 1001322752 1001339136 11 791 31643 30 _ _ (2072457 / 100000) (103623 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1001339136 :
    ThetaLowerSegment 1001339136 1001341184 (50065035696587 / 50000)
      (100130293146287 / 100000) := by
  exact
    packedTile32768 1001339136 1001341184 8 107 31643 30 _ _ (2072459 / 100000) (1036231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_969341184_1001341184 :
    ThetaLowerSegment 969341184 1001341184 (12116309513907 / 12500) (100130293146287 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell969341184 cell969406720)
                    (ThetaLowerSegment.join cell969472256 cell969537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell969603328 cell969668864)
                    (ThetaLowerSegment.join cell969734400 cell969799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell969865472 cell969931008)
                    (ThetaLowerSegment.join cell969996544 cell970062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell970127616 cell970193152)
                    (ThetaLowerSegment.join cell970258688 cell970324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell970389760 cell970455296)
                    (ThetaLowerSegment.join cell970520832 cell970586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell970651904 cell970717440)
                    (ThetaLowerSegment.join cell970782976 cell970848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell970914048 cell970979584)
                    (ThetaLowerSegment.join cell971045120 cell971110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell971176192 cell971241728)
                    (ThetaLowerSegment.join cell971307264 cell971372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell971438336 cell971503872)
                    (ThetaLowerSegment.join cell971569408 cell971634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell971700480 cell971766016)
                    (ThetaLowerSegment.join cell971831552 cell971897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell971962624 cell972028160)
                    (ThetaLowerSegment.join cell972093696 cell972159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell972224768 cell972290304)
                    (ThetaLowerSegment.join cell972355840 cell972421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell972486912 cell972552448)
                    (ThetaLowerSegment.join cell972617984 cell972683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell972749056 cell972814592)
                    (ThetaLowerSegment.join cell972880128 cell972945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell973011200 cell973076736)
                    (ThetaLowerSegment.join cell973142272 cell973207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell973273344 cell973338880)
                    (ThetaLowerSegment.join cell973404416 cell973469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell973535488 cell973601024)
                    (ThetaLowerSegment.join cell973666560 cell973732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell973797632 cell973863168)
                    (ThetaLowerSegment.join cell973928704 cell973994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell974059776 cell974125312)
                    (ThetaLowerSegment.join cell974190848 cell974256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell974321920 cell974387456)
                    (ThetaLowerSegment.join cell974452992 cell974518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell974584064 cell974649600)
                    (ThetaLowerSegment.join cell974715136 cell974780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell974846208 cell974911744)
                    (ThetaLowerSegment.join cell974977280 cell975042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell975108352 cell975173888)
                    (ThetaLowerSegment.join cell975239424 cell975304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell975370496 cell975436032)
                    (ThetaLowerSegment.join cell975501568 cell975567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell975632640 cell975698176)
                    (ThetaLowerSegment.join cell975763712 cell975829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell975894784 cell975960320)
                    (ThetaLowerSegment.join cell976025856 cell976091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell976156928 cell976222464)
                    (ThetaLowerSegment.join cell976288000 cell976353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell976419072 cell976484608)
                    (ThetaLowerSegment.join cell976550144 cell976615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell976681216 cell976746752)
                    (ThetaLowerSegment.join cell976812288 cell976877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell976943360 cell977008896)
                    (ThetaLowerSegment.join cell977074432 cell977139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell977205504 cell977271040)
                    (ThetaLowerSegment.join cell977336576 cell977402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell977467648 cell977533184)
                    (ThetaLowerSegment.join cell977598720 cell977664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell977729792 cell977795328)
                    (ThetaLowerSegment.join cell977860864 cell977926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell977991936 cell978057472)
                    (ThetaLowerSegment.join cell978123008 cell978188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell978254080 cell978319616)
                    (ThetaLowerSegment.join cell978385152 cell978450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell978516224 cell978581760)
                    (ThetaLowerSegment.join cell978647296 cell978712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell978778368 cell978843904)
                    (ThetaLowerSegment.join cell978909440 cell978974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell979040512 cell979106048)
                    (ThetaLowerSegment.join cell979171584 cell979237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell979302656 cell979368192)
                    (ThetaLowerSegment.join cell979433728 cell979499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell979564800 cell979630336)
                    (ThetaLowerSegment.join cell979695872 cell979761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell979826944 cell979892480)
                    (ThetaLowerSegment.join cell979958016 cell980023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell980089088 cell980154624)
                    (ThetaLowerSegment.join cell980220160 cell980285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell980351232 cell980416768)
                    (ThetaLowerSegment.join cell980482304 cell980547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell980613376 cell980678912)
                    (ThetaLowerSegment.join cell980744448 cell980809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell980875520 cell980941056)
                    (ThetaLowerSegment.join cell981006592 cell981072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell981137664 cell981203200)
                    (ThetaLowerSegment.join cell981268736 cell981334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell981399808 cell981465344)
                    (ThetaLowerSegment.join cell981530880 cell981596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell981661952 cell981727488)
                    (ThetaLowerSegment.join cell981793024 cell981858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell981924096 cell981989632)
                    (ThetaLowerSegment.join cell982055168 cell982120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell982186240 cell982251776)
                    (ThetaLowerSegment.join cell982317312 cell982382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell982448384 cell982513920)
                    (ThetaLowerSegment.join cell982579456 cell982644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell982710528 cell982776064)
                    (ThetaLowerSegment.join cell982841600 cell982907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell982972672 cell983038208)
                    (ThetaLowerSegment.join cell983103744 cell983169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell983234816 cell983300352)
                    (ThetaLowerSegment.join cell983365888 cell983431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell983496960 cell983562496)
                    (ThetaLowerSegment.join cell983628032 cell983693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell983759104 cell983824640)
                    (ThetaLowerSegment.join cell983890176 cell983955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell984021248 cell984086784)
                    (ThetaLowerSegment.join cell984152320 cell984217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell984283392 cell984348928)
                    (ThetaLowerSegment.join cell984414464 cell984480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell984545536 cell984611072)
                    (ThetaLowerSegment.join cell984676608 cell984742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell984807680 cell984873216)
                    (ThetaLowerSegment.join cell984938752 cell985004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell985069824 cell985135360)
                    (ThetaLowerSegment.join cell985200896 cell985266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell985331968 cell985397504)
                    (ThetaLowerSegment.join cell985463040 cell985528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell985594112 cell985659648)
                    (ThetaLowerSegment.join cell985725184 cell985790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell985856256 cell985921792)
                    (ThetaLowerSegment.join cell985987328 cell986052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell986118400 cell986183936)
                    (ThetaLowerSegment.join cell986249472 cell986315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell986380544 cell986446080)
                    (ThetaLowerSegment.join cell986511616 cell986577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell986642688 cell986708224)
                    (ThetaLowerSegment.join cell986773760 cell986839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell986904832 cell986970368)
                    (ThetaLowerSegment.join cell987035904 cell987101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell987166976 cell987232512)
                    (ThetaLowerSegment.join cell987298048 cell987363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell987429120 cell987494656)
                    (ThetaLowerSegment.join cell987560192 cell987625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell987691264 cell987756800)
                    (ThetaLowerSegment.join cell987822336 cell987887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell987953408 cell988018944)
                    (ThetaLowerSegment.join cell988084480 cell988150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell988215552 cell988281088)
                    (ThetaLowerSegment.join cell988346624 cell988412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell988477696 cell988543232)
                    (ThetaLowerSegment.join cell988608768 cell988674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell988739840 cell988805376)
                    (ThetaLowerSegment.join cell988870912 cell988936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell989001984 cell989067520)
                    (ThetaLowerSegment.join cell989133056 cell989198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell989264128 cell989329664)
                    (ThetaLowerSegment.join cell989395200 cell989460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell989526272 cell989591808)
                    (ThetaLowerSegment.join cell989657344 cell989722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell989788416 cell989853952)
                    (ThetaLowerSegment.join cell989919488 cell989985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell990050560 cell990116096)
                    (ThetaLowerSegment.join cell990181632 cell990247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell990312704 cell990378240)
                    (ThetaLowerSegment.join cell990443776 cell990509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell990574848 cell990640384)
                    (ThetaLowerSegment.join cell990705920 cell990771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell990836992 cell990902528)
                    (ThetaLowerSegment.join cell990968064 cell991033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell991099136 cell991164672)
                    (ThetaLowerSegment.join cell991230208 cell991295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell991361280 cell991426816)
                    (ThetaLowerSegment.join cell991492352 cell991557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell991623424 cell991688960)
                    (ThetaLowerSegment.join cell991754496 cell991820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell991885568 cell991951104)
                    (ThetaLowerSegment.join cell992016640 cell992082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell992147712 cell992213248)
                    (ThetaLowerSegment.join cell992278784 cell992344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell992409856 cell992475392)
                    (ThetaLowerSegment.join cell992540928 cell992606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell992672000 cell992737536)
                    (ThetaLowerSegment.join cell992803072 cell992868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell992934144 cell992999680)
                    (ThetaLowerSegment.join cell993065216 cell993130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell993196288 cell993261824)
                    (ThetaLowerSegment.join cell993327360 cell993392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell993458432 cell993523968)
                    (ThetaLowerSegment.join cell993589504 cell993655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell993720576 cell993786112)
                    (ThetaLowerSegment.join cell993851648 cell993917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell993982720 cell994048256)
                    (ThetaLowerSegment.join cell994113792 cell994179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell994244864 cell994310400)
                    (ThetaLowerSegment.join cell994375936 cell994441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell994507008 cell994572544)
                    (ThetaLowerSegment.join cell994638080 cell994703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell994769152 cell994834688)
                    (ThetaLowerSegment.join cell994900224 cell994965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell995031296 cell995096832)
                    (ThetaLowerSegment.join cell995162368 cell995227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell995293440 cell995358976)
                    (ThetaLowerSegment.join cell995424512 cell995490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell995555584 cell995621120)
                    (ThetaLowerSegment.join cell995686656 cell995752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell995817728 cell995883264)
                    (ThetaLowerSegment.join cell995948800 cell996014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell996079872 cell996145408)
                    (ThetaLowerSegment.join cell996210944 cell996276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell996342016 cell996407552)
                    (ThetaLowerSegment.join cell996473088 cell996538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell996604160 cell996669696)
                    (ThetaLowerSegment.join cell996735232 cell996800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell996866304 cell996931840)
                    (ThetaLowerSegment.join cell996997376 cell997062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell997128448 cell997193984)
                    (ThetaLowerSegment.join cell997259520 cell997325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell997390592 cell997456128)
                    (ThetaLowerSegment.join cell997521664 cell997587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell997652736 cell997718272)
                    (ThetaLowerSegment.join cell997783808 cell997849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell997914880 cell997980416)
                    (ThetaLowerSegment.join cell998045952 cell998111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell998177024 cell998242560)
                    (ThetaLowerSegment.join cell998308096 cell998373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell998439168 cell998504704)
                    (ThetaLowerSegment.join cell998570240 cell998635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell998701312 cell998766848)
                    (ThetaLowerSegment.join cell998832384 cell998897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell998963456 cell999028992)
                    (ThetaLowerSegment.join cell999094528 cell999160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell999225600 cell999291136)
                    (ThetaLowerSegment.join cell999356672 cell999422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell999487744 cell999553280)
                    (ThetaLowerSegment.join cell999618816 cell999684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell999749888 cell999815424)
                    (ThetaLowerSegment.join cell999880960 cell999946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1000012032 cell1000077568)
                    (ThetaLowerSegment.join cell1000143104 cell1000208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1000274176 cell1000339712)
                    (ThetaLowerSegment.join cell1000405248 cell1000470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1000536320 cell1000601856)
                    (ThetaLowerSegment.join cell1000667392 cell1000732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1000798464 cell1000864000)
                  (ThetaLowerSegment.join cell1000929536 cell1000995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1001060608 cell1001126144)
                  (ThetaLowerSegment.join cell1001191680 cell1001257216)))
              (ThetaLowerSegment.join cell1001322752 cell1001339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
