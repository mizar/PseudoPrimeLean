/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 713341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell681341184 :
    ThetaLowerSegment 681341184 681406720 (68130641690641 / 100000) (68137160519621 / 100000) := by
  exact
    packedTile32768 681341184 681406720 13 3205 26102 29 _ _ (508489 / 25000) (2033959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681406720 :
    ThetaLowerSegment 681406720 681472256 (68137160519621 / 100000) (68143685479341 / 100000) := by
  exact
    packedTile32768 681406720 681472256 13 3208 26103 29 _ _ (406793 / 20000) (127123 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681472256 :
    ThetaLowerSegment 681472256 681537792 (68143685479341 / 100000) (34075193713483 / 50000) := by
  exact
    packedTile32768 681472256 681537792 13 3295 26105 29 _ _ (81359 / 4000) (1016989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681537792 :
    ThetaLowerSegment 681537792 681603328 (34075193713483 / 50000) (34078521312943 / 50000) := by
  exact
    packedTile32768 681537792 681603328 13 3272 26106 29 _ _ (406797 / 20000) (508497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681603328 :
    ThetaLowerSegment 681603328 681668864 (34078521312943 / 50000) (34081773669349 / 50000) := by
  exact
    packedTile32768 681603328 681668864 13 3198 26107 29 _ _ (1016997 / 50000) (2033997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681668864 :
    ThetaLowerSegment 681668864 681734400 (34081773669349 / 50000) (6816996055331 / 10000) := by
  exact
    packedTile32768 681668864 681734400 13 3153 26108 29 _ _ (508501 / 25000) (2034007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681734400 :
    ThetaLowerSegment 681734400 681799936 (6816996055331 / 10000) (8522063505547 / 12500) := by
  exact
    packedTile32768 681734400 681799936 13 3219 26110 29 _ _ (1017007 / 50000) (2034017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681799936 :
    ThetaLowerSegment 681799936 681865472 (8522063505547 / 12500) (68183100312919 / 100000) := by
  exact
    packedTile32768 681799936 681865472 13 3241 26111 29 _ _ (2034023 / 100000) (1017013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681865472 :
    ThetaLowerSegment 681865472 681931008 (68183100312919 / 100000) (34094860545167 / 50000) := by
  exact
    packedTile32768 681865472 681931008 13 3255 26112 29 _ _ (2034033 / 100000) (508509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681931008 :
    ThetaLowerSegment 681931008 681996544 (34094860545167 / 50000) (1363924519133 / 2000) := by
  exact
    packedTile32768 681931008 681996544 13 3198 26113 29 _ _ (1017021 / 50000) (406809 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell681996544 :
    ThetaLowerSegment 681996544 682062080 (1363924519133 / 2000) (34101375597733 / 50000) := by
  exact
    packedTile32768 681996544 682062080 13 3208 26115 29 _ _ (508513 / 25000) (406811 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682062080 :
    ThetaLowerSegment 682062080 682127616 (34101375597733 / 50000) (34104660607863 / 50000) := by
  exact
    packedTile32768 682062080 682127616 13 3230 26116 29 _ _ (1017031 / 50000) (406813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682127616 :
    ThetaLowerSegment 682127616 682193152 (34104660607863 / 50000) (17053946373341 / 25000) := by
  exact
    packedTile32768 682127616 682193152 13 3178 26117 29 _ _ (2034071 / 100000) (1017037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682193152 :
    ThetaLowerSegment 682193152 682258688 (17053946373341 / 25000) (17055557365493 / 25000) := by
  exact
    packedTile32768 682193152 682258688 13 3168 26118 29 _ _ (2034081 / 100000) (508521 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682258688 :
    ThetaLowerSegment 682258688 682324224 (17055557365493 / 25000) (34114351985221 / 50000) := by
  exact
    packedTile32768 682258688 682324224 13 3183 26120 29 _ _ (203409 / 10000) (2034093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682324224 :
    ThetaLowerSegment 682324224 682389760 (34114351985221 / 50000) (34117647227221 / 50000) := by
  exact
    packedTile32768 682324224 682389760 13 3240 26121 29 _ _ (20341 / 1000) (2034103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682389760 :
    ThetaLowerSegment 682389760 682455296 (34117647227221 / 50000) (2132556680531 / 3125) := by
  exact
    packedTile32768 682389760 682455296 13 3205 26122 29 _ _ (203411 / 10000) (2034113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682455296 :
    ThetaLowerSegment 682455296 682520832 (2132556680531 / 3125) (17062135660661 / 25000) := by
  exact
    packedTile32768 682455296 682520832 13 3308 26123 29 _ _ (2034119 / 100000) (1017061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682520832 :
    ThetaLowerSegment 682520832 682586368 (17062135660661 / 25000) (2730201179201 / 4000) := by
  exact
    packedTile32768 682520832 682586368 13 3189 26125 29 _ _ (2034129 / 100000) (508533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682586368 :
    ThetaLowerSegment 682586368 682651904 (2730201179201 / 4000) (68261554994729 / 100000) := by
  exact
    packedTile32768 682586368 682651904 13 3208 26126 29 _ _ (1017069 / 50000) (2034141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682651904 :
    ThetaLowerSegment 682651904 682717440 (68261554994729 / 100000) (68268184283061 / 100000) := by
  exact
    packedTile32768 682651904 682717440 13 3259 26127 29 _ _ (508537 / 25000) (2034151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682717440 :
    ThetaLowerSegment 682717440 682782976 (68268184283061 / 100000) (68274626461447 / 100000) := by
  exact
    packedTile32768 682717440 682782976 13 3167 26128 29 _ _ (1017079 / 50000) (2034161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682782976 :
    ThetaLowerSegment 682782976 682848512 (68274626461447 / 100000) (17070277337919 / 25000) := by
  exact
    packedTile32768 682782976 682848512 13 3187 26130 29 _ _ (2034167 / 100000) (203417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682848512 :
    ThetaLowerSegment 682848512 682914048 (17070277337919 / 25000) (68287588205421 / 100000) := by
  exact
    packedTile32768 682848512 682914048 13 3185 26131 29 _ _ (2034177 / 100000) (101709 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682914048 :
    ThetaLowerSegment 682914048 682979584 (68287588205421 / 100000) (68294079292947 / 100000) := by
  exact
    packedTile32768 682914048 682979584 13 3191 26132 29 _ _ (1017093 / 50000) (2034189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell682979584 :
    ThetaLowerSegment 682979584 683045120 (68294079292947 / 100000) (68300779934571 / 100000) := by
  exact
    packedTile32768 682979584 683045120 13 3294 26133 29 _ _ (508549 / 25000) (2034199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683045120 :
    ThetaLowerSegment 683045120 683110656 (68300779934571 / 100000) (13661453403501 / 20000) := by
  exact
    packedTile32768 683045120 683110656 13 3189 26135 29 _ _ (1017103 / 50000) (2034209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683110656 :
    ThetaLowerSegment 683110656 683176192 (13661453403501 / 20000) (13662744723183 / 20000) := by
  exact
    packedTile32768 683110656 683176192 13 3174 26136 29 _ _ (406843 / 20000) (1017109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683176192 :
    ThetaLowerSegment 683176192 683241728 (13662744723183 / 20000) (3416014199577 / 5000) := by
  exact
    packedTile32768 683176192 683241728 13 3225 26137 29 _ _ (81369 / 4000) (508557 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683241728 :
    ThetaLowerSegment 683241728 683307264 (3416014199577 / 5000) (34163458814307 / 50000) := by
  exact
    packedTile32768 683241728 683307264 13 3261 26138 29 _ _ (1017117 / 50000) (2034237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683307264 :
    ThetaLowerSegment 683307264 683372800 (34163458814307 / 50000) (1366667282957 / 2000) := by
  exact
    packedTile32768 683307264 683372800 13 3169 26140 29 _ _ (508561 / 25000) (2034247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683372800 :
    ThetaLowerSegment 683372800 683438336 (1366667282957 / 2000) (17084998445409 / 25000) := by
  exact
    packedTile32768 683372800 683438336 13 3259 26141 29 _ _ (1017127 / 50000) (2034257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683438336 :
    ThetaLowerSegment 683438336 683503872 (17084998445409 / 25000) (68346586828019 / 100000) := by
  exact
    packedTile32768 683438336 683503872 13 3241 26142 29 _ _ (2034263 / 100000) (1017133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683503872 :
    ThetaLowerSegment 683503872 683569408 (68346586828019 / 100000) (34176587919133 / 50000) := by
  exact
    packedTile32768 683503872 683569408 13 3239 26143 29 _ _ (2034273 / 100000) (508569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683569408 :
    ThetaLowerSegment 683569408 683634944 (34176587919133 / 50000) (34179861078871 / 50000) := by
  exact
    packedTile32768 683569408 683634944 13 3218 26145 29 _ _ (1017141 / 50000) (406857 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683634944 :
    ThetaLowerSegment 683634944 683700480 (34179861078871 / 50000) (6836627054369 / 10000) := by
  exact
    packedTile32768 683634944 683700480 13 3219 26146 29 _ _ (508573 / 25000) (406859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683700480 :
    ThetaLowerSegment 683700480 683766016 (6836627054369 / 10000) (854660898171 / 1250) := by
  exact
    packedTile32768 683700480 683766016 13 3245 26147 29 _ _ (1017151 / 50000) (406861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683766016 :
    ThetaLowerSegment 683766016 683831552 (854660898171 / 1250) (8547416603177 / 12500) := by
  exact
    packedTile32768 683766016 683831552 13 3176 26148 29 _ _ (2034311 / 100000) (1017157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683831552 :
    ThetaLowerSegment 683831552 683897088 (8547416603177 / 12500) (13677184398227 / 20000) := by
  exact
    packedTile32768 683831552 683897088 13 3239 26150 29 _ _ (2034321 / 100000) (508581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683897088 :
    ThetaLowerSegment 683897088 683962624 (13677184398227 / 20000) (13678508340191 / 20000) := by
  exact
    packedTile32768 683897088 683962624 13 3254 26151 29 _ _ (203433 / 10000) (2034333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell683962624 :
    ThetaLowerSegment 683962624 684028160 (13678508340191 / 20000) (2735968817567 / 4000) := by
  exact
    packedTile32768 683962624 684028160 13 3283 26152 29 _ _ (101717 / 5000) (2034343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684028160 :
    ThetaLowerSegment 684028160 684093696 (2735968817567 / 4000) (17101449372373 / 25000) := by
  exact
    packedTile32768 684028160 684093696 13 3233 26153 29 _ _ (2034349 / 100000) (127147 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684093696 :
    ThetaLowerSegment 684093696 684159232 (17101449372373 / 25000) (68412276922907 / 100000) := by
  exact
    packedTile32768 684093696 684159232 13 3185 26155 29 _ _ (2034359 / 100000) (1017181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684159232 :
    ThetaLowerSegment 684159232 684224768 (68412276922907 / 100000) (17104713509471 / 25000) := by
  exact
    packedTile32768 684159232 684224768 13 3233 26156 29 _ _ (2034369 / 100000) (508593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684224768 :
    ThetaLowerSegment 684224768 684290304 (17104713509471 / 25000) (17106351183761 / 25000) := by
  exact
    packedTile32768 684224768 684290304 13 3220 26157 29 _ _ (1017189 / 50000) (2034381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684290304 :
    ThetaLowerSegment 684290304 684355840 (17106351183761 / 25000) (3421594925077 / 5000) := by
  exact
    packedTile32768 684290304 684355840 13 3192 26158 29 _ _ (508597 / 25000) (2034391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684355840 :
    ThetaLowerSegment 684355840 684421376 (3421594925077 / 5000) (68438475707041 / 100000) := by
  exact
    packedTile32768 684355840 684421376 13 3233 26160 29 _ _ (2034397 / 100000) (2543 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684421376 :
    ThetaLowerSegment 684421376 684486912 (68438475707041 / 100000) (34222524438029 / 50000) := by
  exact
    packedTile32768 684421376 684486912 13 3231 26161 29 _ _ (2034407 / 100000) (203441 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684486912 :
    ThetaLowerSegment 684486912 684552448 (34222524438029 / 50000) (13690324415477 / 20000) := by
  exact
    packedTile32768 684486912 684552448 13 3231 26162 29 _ _ (2034417 / 100000) (101721 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684552448 :
    ThetaLowerSegment 684552448 684617984 (13690324415477 / 20000) (68458231927459 / 100000) := by
  exact
    packedTile32768 684552448 684617984 13 3249 26163 29 _ _ (1017213 / 50000) (2034429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684617984 :
    ThetaLowerSegment 684617984 684683520 (68458231927459 / 100000) (68464776708071 / 100000) := by
  exact
    packedTile32768 684617984 684683520 13 3217 26165 29 _ _ (508609 / 25000) (2034439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684683520 :
    ThetaLowerSegment 684683520 684749056 (68464776708071 / 100000) (34235638379923 / 50000) := by
  exact
    packedTile32768 684683520 684749056 13 3195 26166 29 _ _ (406889 / 20000) (127153 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684749056 :
    ThetaLowerSegment 684749056 684814592 (34235638379923 / 50000) (68477882635231 / 100000) := by
  exact
    packedTile32768 684749056 684814592 13 3247 26167 29 _ _ (406891 / 20000) (1017229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684814592 :
    ThetaLowerSegment 684814592 684880128 (68477882635231 / 100000) (68484482436447 / 100000) := by
  exact
    packedTile32768 684814592 684880128 13 3244 26168 29 _ _ (63577 / 3125) (2034467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684880128 :
    ThetaLowerSegment 684880128 684945664 (68484482436447 / 100000) (68490992753247 / 100000) := by
  exact
    packedTile32768 684880128 684945664 13 3200 26170 29 _ _ (1017237 / 50000) (2034477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell684945664 :
    ThetaLowerSegment 684945664 685011200 (68490992753247 / 100000) (68497728929771 / 100000) := by
  exact
    packedTile32768 684945664 685011200 13 3311 26171 29 _ _ (508621 / 25000) (2034487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685011200 :
    ThetaLowerSegment 685011200 685076736 (68497728929771 / 100000) (68504279997231 / 100000) := by
  exact
    packedTile32768 685011200 685076736 13 3220 26172 29 _ _ (2034493 / 100000) (63578 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685076736 :
    ThetaLowerSegment 685076736 685142272 (68504279997231 / 100000) (13702185750607 / 20000) := by
  exact
    packedTile32768 685076736 685142272 13 3268 26173 29 _ _ (2034503 / 100000) (1017253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685142272 :
    ThetaLowerSegment 685142272 685207808 (13702185750607 / 20000) (68517400535707 / 100000) := by
  exact
    packedTile32768 685142272 685207808 13 3181 26175 29 _ _ (127157 / 6250) (406903 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685207808 :
    ThetaLowerSegment 685207808 685273344 (68517400535707 / 100000) (68523917109673 / 100000) := by
  exact
    packedTile32768 685207808 685273344 13 3203 26176 29 _ _ (1017261 / 50000) (81381 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685273344 :
    ThetaLowerSegment 685273344 685338880 (68523917109673 / 100000) (68530382849191 / 100000) := by
  exact
    packedTile32768 685273344 685338880 13 3178 26177 29 _ _ (2034531 / 100000) (1017267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685338880 :
    ThetaLowerSegment 685338880 685404416 (68530382849191 / 100000) (34268502640073 / 50000) := by
  exact
    packedTile32768 685338880 685404416 13 3255 26178 29 _ _ (2034541 / 100000) (127159 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685404416 :
    ThetaLowerSegment 685404416 685469952 (34268502640073 / 50000) (34271774196473 / 50000) := by
  exact
    packedTile32768 685404416 685469952 13 3216 26180 29 _ _ (40691 / 2000) (2034553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685469952 :
    ThetaLowerSegment 685469952 685535488 (34271774196473 / 50000) (34275069166393 / 50000) := by
  exact
    packedTile32768 685469952 685535488 13 3239 26181 29 _ _ (12716 / 625) (2034563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685535488 :
    ThetaLowerSegment 685535488 685601024 (34275069166393 / 50000) (17139187162679 / 25000) := by
  exact
    packedTile32768 685535488 685601024 13 3249 26182 29 _ _ (203457 / 10000) (2034573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685601024 :
    ThetaLowerSegment 685601024 685666560 (17139187162679 / 25000) (2142602616202 / 3125) := by
  exact
    packedTile32768 685601024 685666560 13 3212 26183 29 _ _ (2034579 / 100000) (1017291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685666560 :
    ThetaLowerSegment 685666560 685732096 (2142602616202 / 3125) (68569885959769 / 100000) := by
  exact
    packedTile32768 685666560 685732096 13 3245 26185 29 _ _ (2034589 / 100000) (63581 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685732096 :
    ThetaLowerSegment 685732096 685797632 (68569885959769 / 100000) (68576402777163 / 100000) := by
  exact
    packedTile32768 685732096 685797632 13 3203 26186 29 _ _ (1017299 / 50000) (2034601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685797632 :
    ThetaLowerSegment 685797632 685863168 (68576402777163 / 100000) (13716612816751 / 20000) := by
  exact
    packedTile32768 685797632 685863168 13 3274 26187 29 _ _ (127163 / 6250) (2034611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685863168 :
    ThetaLowerSegment 685863168 685928704 (13716612816751 / 20000) (34294814896407 / 50000) := by
  exact
    packedTile32768 685863168 685928704 13 3227 26188 29 _ _ (2034617 / 100000) (101731 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685928704 :
    ThetaLowerSegment 685928704 685994240 (34294814896407 / 50000) (68596154841603 / 100000) := by
  exact
    packedTile32768 685928704 685994240 13 3207 26190 29 _ _ (2034627 / 100000) (203463 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell685994240 :
    ThetaLowerSegment 685994240 686059776 (68596154841603 / 100000) (13720546157031 / 20000) := by
  exact
    packedTile32768 685994240 686059776 13 3232 26191 29 _ _ (508659 / 25000) (2034639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686059776 :
    ThetaLowerSegment 686059776 686125312 (13720546157031 / 20000) (13721848330471 / 20000) := by
  exact
    packedTile32768 686059776 686125312 13 3200 26192 29 _ _ (1017323 / 50000) (2034649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686125312 :
    ThetaLowerSegment 686125312 686190848 (13721848330471 / 20000) (68615795279331 / 100000) := by
  exact
    packedTile32768 686125312 686190848 13 3221 26193 29 _ _ (63583 / 3125) (2034659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686190848 :
    ThetaLowerSegment 686190848 686256384 (68615795279331 / 100000) (34311266027573 / 50000) := by
  exact
    packedTile32768 686190848 686256384 13 3311 26195 29 _ _ (406933 / 20000) (508667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686256384 :
    ThetaLowerSegment 686256384 686321920 (34311266027573 / 50000) (68629085743321 / 100000) := by
  exact
    packedTile32768 686256384 686321920 13 3221 26196 29 _ _ (81387 / 4000) (1017339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686321920 :
    ThetaLowerSegment 686321920 686387456 (68629085743321 / 100000) (68635505171341 / 100000) := by
  exact
    packedTile32768 686321920 686387456 13 3155 26197 29 _ _ (508671 / 25000) (2034687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686387456 :
    ThetaLowerSegment 686387456 686452992 (68635505171341 / 100000) (68642042643163 / 100000) := by
  exact
    packedTile32768 686387456 686452992 13 3213 26198 29 _ _ (1017347 / 50000) (2034697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686452992 :
    ThetaLowerSegment 686452992 686518528 (68642042643163 / 100000) (68648594386823 / 100000) := by
  exact
    packedTile32768 686452992 686518528 13 3220 26200 29 _ _ (2034703 / 100000) (1017353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686518528 :
    ThetaLowerSegment 686518528 686584064 (68648594386823 / 100000) (34327629035949 / 50000) := by
  exact
    packedTile32768 686518528 686584064 13 3275 26201 29 _ _ (2034713 / 100000) (508679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686584064 :
    ThetaLowerSegment 686584064 686649600 (34327629035949 / 50000) (2145681495063 / 3125) := by
  exact
    packedTile32768 686584064 686649600 13 3219 26202 29 _ _ (1017361 / 50000) (81389 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686649600 :
    ThetaLowerSegment 686649600 686715136 (2145681495063 / 3125) (429176891916 / 625) := by
  exact
    packedTile32768 686649600 686715136 13 3192 26203 29 _ _ (508683 / 25000) (406947 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686715136 :
    ThetaLowerSegment 686715136 686780672 (429176891916 / 625) (6867498683403 / 10000) := by
  exact
    packedTile32768 686715136 686780672 13 3285 26205 29 _ _ (1017371 / 50000) (406949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686780672 :
    ThetaLowerSegment 686780672 686846208 (6867498683403 / 10000) (34340785644133 / 50000) := by
  exact
    packedTile32768 686780672 686846208 13 3236 26206 29 _ _ (2034751 / 100000) (1017377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686846208 :
    ThetaLowerSegment 686846208 686911744 (34340785644133 / 50000) (17172025717769 / 25000) := by
  exact
    packedTile32768 686846208 686911744 13 3210 26207 29 _ _ (2034761 / 100000) (508691 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686911744 :
    ThetaLowerSegment 686911744 686977280 (17172025717769 / 25000) (2146710634088 / 3125) := by
  exact
    packedTile32768 686911744 686977280 13 3262 26209 29 _ _ (203477 / 10000) (2034773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell686977280 :
    ThetaLowerSegment 686977280 687042816 (2146710634088 / 3125) (17175313405399 / 25000) := by
  exact
    packedTile32768 686977280 687042816 13 3201 26210 29 _ _ (101739 / 5000) (2034783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687042816 :
    ThetaLowerSegment 687042816 687108352 (17175313405399 / 25000) (2147120961107 / 3125) := by
  exact
    packedTile32768 687042816 687108352 13 3252 26211 29 _ _ (2034789 / 100000) (254349 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687108352 :
    ThetaLowerSegment 687108352 687173888 (2147120961107 / 3125) (1374286584149 / 2000) := by
  exact
    packedTile32768 687108352 687173888 13 3174 26212 29 _ _ (2034799 / 100000) (1017401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687173888 :
    ThetaLowerSegment 687173888 687239424 (1374286584149 / 2000) (34360478288553 / 50000) := by
  exact
    packedTile32768 687173888 687239424 13 3257 26214 29 _ _ (254351 / 12500) (2034811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687239424 :
    ThetaLowerSegment 687239424 687304960 (34360478288553 / 50000) (34363770624077 / 50000) := by
  exact
    packedTile32768 687239424 687304960 13 3236 26215 29 _ _ (1017409 / 50000) (2034821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687304960 :
    ThetaLowerSegment 687304960 687370496 (34363770624077 / 50000) (68734071007997 / 100000) := by
  exact
    packedTile32768 687304960 687370496 13 3209 26216 29 _ _ (2034827 / 100000) (203483 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687370496 :
    ThetaLowerSegment 687370496 687436032 (68734071007997 / 100000) (8592576626119 / 12500) := by
  exact
    packedTile32768 687370496 687436032 13 3215 26217 29 _ _ (2034837 / 100000) (50871 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687436032 :
    ThetaLowerSegment 687436032 687501568 (8592576626119 / 12500) (34373591763343 / 50000) := by
  exact
    packedTile32768 687436032 687501568 13 3229 26219 29 _ _ (1017423 / 50000) (2034849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687501568 :
    ThetaLowerSegment 687501568 687567104 (34373591763343 / 50000) (34376857707223 / 50000) := by
  exact
    packedTile32768 687501568 687567104 13 3210 26220 29 _ _ (254357 / 12500) (2034859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687567104 :
    ThetaLowerSegment 687567104 687632640 (34376857707223 / 50000) (68760351109211 / 100000) := by
  exact
    packedTile32768 687567104 687632640 13 3261 26221 29 _ _ (406973 / 20000) (508717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687632640 :
    ThetaLowerSegment 687632640 687698176 (68760351109211 / 100000) (34383444581293 / 50000) := by
  exact
    packedTile32768 687632640 687698176 13 3213 26222 29 _ _ (16279 / 800) (1017439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687698176 :
    ThetaLowerSegment 687698176 687763712 (34383444581293 / 50000) (34386684118213 / 50000) := by
  exact
    packedTile32768 687698176 687763712 13 3184 26224 29 _ _ (406977 / 20000) (254361 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687763712 :
    ThetaLowerSegment 687763712 687829248 (34386684118213 / 50000) (8597483206621 / 12500) := by
  exact
    packedTile32768 687763712 687829248 13 3193 26225 29 _ _ (1017447 / 50000) (2034897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687829248 :
    ThetaLowerSegment 687829248 687894784 (8597483206621 / 12500) (429915023747 / 625) := by
  exact
    packedTile32768 687829248 687894784 13 3213 26226 29 _ _ (254363 / 12500) (2034907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687894784 :
    ThetaLowerSegment 687894784 687960320 (429915023747 / 625) (68792832089687 / 100000) := by
  exact
    packedTile32768 687894784 687960320 13 3159 26227 29 _ _ (2034913 / 100000) (508729 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell687960320 :
    ThetaLowerSegment 687960320 688025856 (68792832089687 / 100000) (34399717707411 / 50000) := by
  exact
    packedTile32768 687960320 688025856 13 3245 26228 29 _ _ (2034923 / 100000) (1017463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688025856 :
    ThetaLowerSegment 688025856 688091392 (34399717707411 / 50000) (34403056013357 / 50000) := by
  exact
    packedTile32768 688025856 688091392 13 3281 26230 29 _ _ (508733 / 25000) (406987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688091392 :
    ThetaLowerSegment 688091392 688156928 (34403056013357 / 50000) (1376252802413 / 2000) := by
  exact
    packedTile32768 688091392 688156928 13 3208 26231 29 _ _ (1017471 / 50000) (406989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688156928 :
    ThetaLowerSegment 688156928 688222464 (1376252802413 / 2000) (13763869056839 / 20000) := by
  exact
    packedTile32768 688156928 688222464 13 3295 26232 29 _ _ (2034951 / 100000) (1017477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688222464 :
    ThetaLowerSegment 688222464 688288000 (13763869056839 / 20000) (34412972331359 / 50000) := by
  exact
    packedTile32768 688222464 688288000 13 3243 26233 29 _ _ (2034961 / 100000) (508741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688288000 :
    ThetaLowerSegment 688288000 688353536 (34412972331359 / 50000) (34416228283359 / 50000) := by
  exact
    packedTile32768 688288000 688353536 13 3200 26235 29 _ _ (203497 / 10000) (2034973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688353536 :
    ThetaLowerSegment 688353536 688419072 (34416228283359 / 50000) (34419497478729 / 50000) := by
  exact
    packedTile32768 688353536 688419072 13 3213 26236 29 _ _ (101749 / 5000) (2034983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688419072 :
    ThetaLowerSegment 688419072 688484608 (34419497478729 / 50000) (17211357398169 / 25000) := by
  exact
    packedTile32768 688419072 688484608 13 3162 26237 29 _ _ (2034989 / 100000) (127187 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688484608 :
    ThetaLowerSegment 688484608 688550144 (17211357398169 / 25000) (2151627499044 / 3125) := by
  exact
    packedTile32768 688484608 688550144 13 3268 26238 29 _ _ (2034999 / 100000) (1017501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688550144 :
    ThetaLowerSegment 688550144 688615680 (2151627499044 / 3125) (2151833289228 / 3125) := by
  exact
    packedTile32768 688550144 688615680 13 3236 26240 29 _ _ (63594 / 3125) (2035011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688615680 :
    ThetaLowerSegment 688615680 688681216 (2151833289228 / 3125) (1377303668359 / 2000) := by
  exact
    packedTile32768 688615680 688681216 13 3203 26241 29 _ _ (1017509 / 50000) (2035021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688681216 :
    ThetaLowerSegment 688681216 688746752 (1377303668359 / 2000) (17217924893601 / 25000) := by
  exact
    packedTile32768 688681216 688746752 13 3202 26242 29 _ _ (2035027 / 100000) (203503 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688746752 :
    ThetaLowerSegment 688746752 688812288 (17217924893601 / 25000) (34439087531069 / 50000) := by
  exact
    packedTile32768 688746752 688812288 13 3182 26243 29 _ _ (2035037 / 100000) (12719 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688812288 :
    ThetaLowerSegment 688812288 688877824 (34439087531069 / 50000) (17221177398711 / 25000) := by
  exact
    packedTile32768 688812288 688877824 13 3211 26245 29 _ _ (1017523 / 50000) (2035049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688877824 :
    ThetaLowerSegment 688877824 688943360 (17221177398711 / 25000) (17222809004859 / 25000) := by
  exact
    packedTile32768 688877824 688943360 13 3207 26246 29 _ _ (127191 / 6250) (2035059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell688943360 :
    ThetaLowerSegment 688943360 689008896 (17222809004859 / 25000) (34448965691643 / 50000) := by
  exact
    packedTile32768 688943360 689008896 13 3290 26247 29 _ _ (407013 / 20000) (508767 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689008896 :
    ThetaLowerSegment 689008896 689074432 (34448965691643 / 50000) (17226115993509 / 25000) := by
  exact
    packedTile32768 689008896 689074432 13 3210 26248 29 _ _ (81403 / 4000) (1017539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689074432 :
    ThetaLowerSegment 689074432 689139968 (17226115993509 / 25000) (17227753218587 / 25000) := by
  exact
    packedTile32768 689074432 689139968 13 3218 26250 29 _ _ (508771 / 25000) (2035087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689139968 :
    ThetaLowerSegment 689139968 689205504 (17227753218587 / 25000) (17229393504351 / 25000) := by
  exact
    packedTile32768 689139968 689205504 13 3224 26251 29 _ _ (1017547 / 50000) (2035097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689205504 :
    ThetaLowerSegment 689205504 689271040 (17229393504351 / 25000) (3446210829843 / 5000) := by
  exact
    packedTile32768 689205504 689271040 13 3264 26252 29 _ _ (63597 / 3125) (2035107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689271040 :
    ThetaLowerSegment 689271040 689336576 (3446210829843 / 5000) (68930844959901 / 100000) := by
  exact
    packedTile32768 689271040 689336576 13 3257 26253 29 _ _ (2035113 / 100000) (508779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689336576 :
    ThetaLowerSegment 689336576 689402112 (68930844959901 / 100000) (68937337002271 / 100000) := by
  exact
    packedTile32768 689336576 689402112 13 3190 26255 29 _ _ (2035123 / 100000) (1017563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689402112 :
    ThetaLowerSegment 689402112 689467648 (68937337002271 / 100000) (68943922689423 / 100000) := by
  exact
    packedTile32768 689402112 689467648 13 3236 26256 29 _ _ (508783 / 25000) (407027 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689467648 :
    ThetaLowerSegment 689467648 689533184 (68943922689423 / 100000) (68950490092657 / 100000) := by
  exact
    packedTile32768 689467648 689533184 13 3227 26257 29 _ _ (1017571 / 50000) (407029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689533184 :
    ThetaLowerSegment 689533184 689598720 (68950490092657 / 100000) (68957006646159 / 100000) := by
  exact
    packedTile32768 689533184 689598720 13 3202 26258 29 _ _ (2035151 / 100000) (1017577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689598720 :
    ThetaLowerSegment 689598720 689664256 (68957006646159 / 100000) (34481746352133 / 50000) := by
  exact
    packedTile32768 689598720 689664256 13 3187 26260 29 _ _ (2035161 / 100000) (508791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689664256 :
    ThetaLowerSegment 689664256 689729792 (34481746352133 / 50000) (34485061644063 / 50000) := by
  exact
    packedTile32768 689664256 689729792 13 3258 26261 29 _ _ (203517 / 10000) (2035173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689729792 :
    ThetaLowerSegment 689729792 689795328 (34485061644063 / 50000) (34488381022643 / 50000) := by
  exact
    packedTile32768 689729792 689795328 13 3262 26262 29 _ _ (101759 / 5000) (2035183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689795328 :
    ThetaLowerSegment 689795328 689860864 (34488381022643 / 50000) (68983349952079 / 100000) := by
  exact
    packedTile32768 689795328 689860864 13 3237 26263 29 _ _ (2035189 / 100000) (254399 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689860864 :
    ThetaLowerSegment 689860864 689926400 (68983349952079 / 100000) (68989907363257 / 100000) := by
  exact
    packedTile32768 689860864 689926400 13 3222 26265 29 _ _ (2035199 / 100000) (1017601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689926400 :
    ThetaLowerSegment 689926400 689991936 (68989907363257 / 100000) (68996365078241 / 100000) := by
  exact
    packedTile32768 689926400 689991936 13 3173 26266 29 _ _ (254401 / 12500) (2035211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell689991936 :
    ThetaLowerSegment 689991936 690057472 (68996365078241 / 100000) (69002997853703 / 100000) := by
  exact
    packedTile32768 689991936 690057472 13 3259 26267 29 _ _ (1017609 / 50000) (2035221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690057472 :
    ThetaLowerSegment 690057472 690123008 (69002997853703 / 100000) (17252405629397 / 25000) := by
  exact
    packedTile32768 690057472 690123008 13 3255 26268 29 _ _ (2035227 / 100000) (203523 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690123008 :
    ThetaLowerSegment 690123008 690188544 (17252405629397 / 25000) (1725405213613 / 2500) := by
  exact
    packedTile32768 690123008 690188544 13 3236 26270 29 _ _ (2035237 / 100000) (50881 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690188544 :
    ThetaLowerSegment 690188544 690254080 (1725405213613 / 2500) (17255667103831 / 25000) := by
  exact
    packedTile32768 690188544 690254080 13 3174 26271 29 _ _ (1017623 / 50000) (2035249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690254080 :
    ThetaLowerSegment 690254080 690319616 (17255667103831 / 25000) (17257302432027 / 25000) := by
  exact
    packedTile32768 690254080 690319616 13 3214 26272 29 _ _ (254407 / 12500) (2035259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690319616 :
    ThetaLowerSegment 690319616 690385152 (17257302432027 / 25000) (34517940663389 / 50000) := by
  exact
    packedTile32768 690319616 690385152 13 3278 26273 29 _ _ (407053 / 20000) (508817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690385152 :
    ThetaLowerSegment 690385152 690450688 (34517940663389 / 50000) (69042518358553 / 100000) := by
  exact
    packedTile32768 690385152 690450688 13 3261 26275 29 _ _ (81411 / 4000) (1017639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690450688 :
    ThetaLowerSegment 690450688 690516224 (69042518358553 / 100000) (69049031267353 / 100000) := by
  exact
    packedTile32768 690450688 690516224 13 3200 26276 29 _ _ (508821 / 25000) (2035287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690516224 :
    ThetaLowerSegment 690516224 690581760 (69049031267353 / 100000) (69055572702269 / 100000) := by
  exact
    packedTile32768 690516224 690581760 13 3214 26277 29 _ _ (1017647 / 50000) (2035297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690581760 :
    ThetaLowerSegment 690581760 690647296 (69055572702269 / 100000) (6906218133111 / 10000) := by
  exact
    packedTile32768 690581760 690647296 13 3247 26278 29 _ _ (2035303 / 100000) (1017653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690647296 :
    ThetaLowerSegment 690647296 690712832 (6906218133111 / 10000) (6906872485919 / 10000) := by
  exact
    packedTile32768 690647296 690712832 13 3215 26280 29 _ _ (127207 / 6250) (407063 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690712832 :
    ThetaLowerSegment 690712832 690778368 (6906872485919 / 10000) (34537651509947 / 50000) := by
  exact
    packedTile32768 690712832 690778368 13 3232 26281 29 _ _ (1017661 / 50000) (81413 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690778368 :
    ThetaLowerSegment 690778368 690843904 (34537651509947 / 50000) (13816367693547 / 20000) := by
  exact
    packedTile32768 690778368 690843904 13 3211 26282 29 _ _ (2035331 / 100000) (1017667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690843904 :
    ThetaLowerSegment 690843904 690909440 (13816367693547 / 20000) (69088461467349 / 100000) := by
  exact
    packedTile32768 690843904 690909440 13 3254 26283 29 _ _ (2035341 / 100000) (127209 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690909440 :
    ThetaLowerSegment 690909440 690974976 (69088461467349 / 100000) (69094990870149 / 100000) := by
  exact
    packedTile32768 690909440 690974976 13 3208 26285 29 _ _ (40707 / 2000) (2035353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell690974976 :
    ThetaLowerSegment 690974976 691040512 (69094990870149 / 100000) (69101491809989 / 100000) := by
  exact
    packedTile32768 690974976 691040512 13 3194 26286 29 _ _ (12721 / 625) (2035363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691040512 :
    ThetaLowerSegment 691040512 691106048 (69101491809989 / 100000) (69108163749571 / 100000) := by
  exact
    packedTile32768 691040512 691106048 13 3278 26287 29 _ _ (2035369 / 100000) (508843 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691106048 :
    ThetaLowerSegment 691106048 691171584 (69108163749571 / 100000) (69114615901001 / 100000) := by
  exact
    packedTile32768 691106048 691171584 13 3170 26288 29 _ _ (2035379 / 100000) (1017691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691171584 :
    ThetaLowerSegment 691171584 691237120 (69114615901001 / 100000) (69121302150581 / 100000) := by
  exact
    packedTile32768 691171584 691237120 13 3285 26290 29 _ _ (508847 / 25000) (2035391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691237120 :
    ThetaLowerSegment 691237120 691302656 (69121302150581 / 100000) (69127856132141 / 100000) := by
  exact
    packedTile32768 691237120 691302656 13 3220 26291 29 _ _ (1017699 / 50000) (2035401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691302656 :
    ThetaLowerSegment 691302656 691368192 (69127856132141 / 100000) (17283613221557 / 25000) := by
  exact
    packedTile32768 691302656 691368192 13 3241 26292 29 _ _ (2035407 / 100000) (203541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691368192 :
    ThetaLowerSegment 691368192 691433728 (17283613221557 / 25000) (34570497358233 / 50000) := by
  exact
    packedTile32768 691368192 691433728 13 3214 26293 29 _ _ (2035417 / 100000) (101771 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691433728 :
    ThetaLowerSegment 691433728 691499264 (34570497358233 / 50000) (6914759763841 / 10000) := by
  exact
    packedTile32768 691433728 691499264 13 3244 26295 29 _ _ (1017713 / 50000) (2035429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691499264 :
    ThetaLowerSegment 691499264 691564800 (6914759763841 / 10000) (34577081977473 / 50000) := by
  exact
    packedTile32768 691499264 691564800 13 3226 26296 29 _ _ (508859 / 25000) (2035439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691564800 :
    ThetaLowerSegment 691564800 691630336 (34577081977473 / 50000) (69160728265071 / 100000) := by
  exact
    packedTile32768 691564800 691630336 13 3225 26297 29 _ _ (407089 / 20000) (254431 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691630336 :
    ThetaLowerSegment 691630336 691695872 (69160728265071 / 100000) (69167294642901 / 100000) := by
  exact
    packedTile32768 691630336 691695872 13 3226 26298 29 _ _ (407091 / 20000) (1017729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691695872 :
    ThetaLowerSegment 691695872 691761408 (69167294642901 / 100000) (69173745028317 / 100000) := by
  exact
    packedTile32768 691695872 691761408 13 3169 26300 29 _ _ (254433 / 12500) (2035467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691761408 :
    ThetaLowerSegment 691761408 691826944 (69173745028317 / 100000) (69180207658267 / 100000) := by
  exact
    packedTile32768 691761408 691826944 13 3175 26301 29 _ _ (1017737 / 50000) (2035477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691826944 :
    ThetaLowerSegment 691826944 691892480 (69180207658267 / 100000) (1729667572113 / 2500) := by
  exact
    packedTile32768 691826944 691892480 13 3191 26302 29 _ _ (2035483 / 100000) (1017743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691892480 :
    ThetaLowerSegment 691892480 691958016 (1729667572113 / 2500) (4324572975643 / 6250) := by
  exact
    packedTile32768 691892480 691958016 13 3176 26303 29 _ _ (2035493 / 100000) (254437 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell691958016 :
    ThetaLowerSegment 691958016 692023552 (4324572975643 / 6250) (8649963205339 / 12500) := by
  exact
    packedTile32768 691958016 692023552 13 3212 26305 29 _ _ (1017751 / 50000) (407101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692023552 :
    ThetaLowerSegment 692023552 692089088 (8649963205339 / 12500) (4325393921069 / 6250) := by
  exact
    packedTile32768 692023552 692089088 13 3241 26306 29 _ _ (254439 / 12500) (407103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692089088 :
    ThetaLowerSegment 692089088 692154624 (4325393921069 / 6250) (34606483516429 / 50000) := by
  exact
    packedTile32768 692089088 692154624 13 3274 26307 29 _ _ (2035521 / 100000) (508881 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692154624 :
    ThetaLowerSegment 692154624 692220160 (34606483516429 / 50000) (17304880868747 / 25000) := by
  exact
    packedTile32768 692154624 692220160 13 3221 26308 29 _ _ (203553 / 10000) (2035533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692220160 :
    ThetaLowerSegment 692220160 692285696 (17304880868747 / 25000) (4326628979063 / 6250) := by
  exact
    packedTile32768 692220160 692285696 13 3213 26310 29 _ _ (101777 / 5000) (2035543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692285696 :
    ThetaLowerSegment 692285696 692351232 (4326628979063 / 6250) (17308150462099 / 25000) := by
  exact
    packedTile32768 692285696 692351232 13 3212 26311 29 _ _ (2035549 / 100000) (63611 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692351232 :
    ThetaLowerSegment 692351232 692416768 (17308150462099 / 25000) (69239174668407 / 100000) := by
  exact
    packedTile32768 692351232 692416768 13 3229 26312 29 _ _ (2035559 / 100000) (1017781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692416768 :
    ThetaLowerSegment 692416768 692482304 (69239174668407 / 100000) (69245682379303 / 100000) := by
  exact
    packedTile32768 692416768 692482304 13 3197 26313 29 _ _ (127223 / 6250) (2035571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692482304 :
    ThetaLowerSegment 692482304 692547840 (69245682379303 / 100000) (69252190122169 / 100000) := by
  exact
    packedTile32768 692482304 692547840 13 3197 26315 29 _ _ (1017789 / 50000) (2035581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692547840 :
    ThetaLowerSegment 692547840 692613376 (69252190122169 / 100000) (69258655146481 / 100000) := by
  exact
    packedTile32768 692547840 692613376 13 3176 26316 29 _ _ (2035587 / 100000) (203559 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692613376 :
    ThetaLowerSegment 692613376 692678912 (69258655146481 / 100000) (69265242338373 / 100000) := by
  exact
    packedTile32768 692613376 692678912 13 3236 26317 29 _ _ (2035597 / 100000) (5089 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692678912 :
    ThetaLowerSegment 692678912 692744448 (69265242338373 / 100000) (69271823452571 / 100000) := by
  exact
    packedTile32768 692678912 692744448 13 3233 26318 29 _ _ (1017803 / 50000) (2035609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692744448 :
    ThetaLowerSegment 692744448 692809984 (69271823452571 / 100000) (69278363886779 / 100000) := by
  exact
    packedTile32768 692744448 692809984 13 3213 26320 29 _ _ (63613 / 3125) (2035619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692809984 :
    ThetaLowerSegment 692809984 692875520 (69278363886779 / 100000) (69284845316779 / 100000) := by
  exact
    packedTile32768 692809984 692875520 13 3184 26321 29 _ _ (3257 / 160) (508907 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692875520 :
    ThetaLowerSegment 692875520 692941056 (69284845316779 / 100000) (17322837292651 / 25000) := by
  exact
    packedTile32768 692875520 692941056 13 3195 26322 29 _ _ (407127 / 20000) (1017819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell692941056 :
    ThetaLowerSegment 692941056 693006592 (17322837292651 / 25000) (4331110217803 / 6250) := by
  exact
    packedTile32768 692941056 693006592 13 3151 26323 29 _ _ (508911 / 25000) (2035647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693006592 :
    ThetaLowerSegment 693006592 693072128 (4331110217803 / 6250) (34652139806651 / 50000) := by
  exact
    packedTile32768 693006592 693072128 13 3201 26325 29 _ _ (1017827 / 50000) (2035657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693072128 :
    ThetaLowerSegment 693072128 693137664 (34652139806651 / 50000) (34655400938777 / 50000) := by
  exact
    packedTile32768 693072128 693137664 13 3204 26326 29 _ _ (2035663 / 100000) (1017833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693137664 :
    ThetaLowerSegment 693137664 693203200 (34655400938777 / 50000) (34658668192337 / 50000) := by
  exact
    packedTile32768 693137664 693203200 13 3210 26327 29 _ _ (254459 / 12500) (81427 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693203200 :
    ThetaLowerSegment 693203200 693268736 (34658668192337 / 50000) (34661951747403 / 50000) := by
  exact
    packedTile32768 693203200 693268736 13 3226 26328 29 _ _ (1017841 / 50000) (407137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693268736 :
    ThetaLowerSegment 693268736 693334272 (34661951747403 / 50000) (17332585087437 / 25000) := by
  exact
    packedTile32768 693268736 693334272 13 3162 26329 29 _ _ (2035691 / 100000) (1017847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693334272 :
    ThetaLowerSegment 693334272 693399808 (17332585087437 / 25000) (13867369697169 / 20000) := by
  exact
    packedTile32768 693334272 693399808 13 3197 26331 29 _ _ (2035701 / 100000) (254463 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693399808 :
    ThetaLowerSegment 693399808 693465344 (13867369697169 / 20000) (13868684765829 / 20000) := by
  exact
    packedTile32768 693399808 693465344 13 3230 26332 29 _ _ (203571 / 10000) (2035713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693465344 :
    ThetaLowerSegment 693465344 693530880 (13868684765829 / 20000) (13869992919501 / 20000) := by
  exact
    packedTile32768 693465344 693530880 13 3213 26333 29 _ _ (50893 / 2500) (2035723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693530880 :
    ThetaLowerSegment 693530880 693596416 (13869992919501 / 20000) (17339141616663 / 25000) := by
  exact
    packedTile32768 693530880 693596416 13 3243 26334 29 _ _ (2035729 / 100000) (508933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693596416 :
    ThetaLowerSegment 693596416 693661952 (17339141616663 / 25000) (34681550594421 / 50000) := by
  exact
    packedTile32768 693596416 693661952 13 3210 26336 29 _ _ (2035739 / 100000) (1017871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693661952 :
    ThetaLowerSegment 693661952 693727488 (34681550594421 / 50000) (34684899399881 / 50000) := by
  exact
    packedTile32768 693661952 693727488 13 3290 26337 29 _ _ (508937 / 25000) (2035751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693727488 :
    ThetaLowerSegment 693727488 693793024 (34684899399881 / 50000) (13875250022739 / 20000) := by
  exact
    packedTile32768 693727488 693793024 13 3169 26338 29 _ _ (2035757 / 100000) (25447 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693793024 :
    ThetaLowerSegment 693793024 693858560 (13875250022739 / 20000) (69382748281959 / 100000) := by
  exact
    packedTile32768 693793024 693858560 13 3192 26339 29 _ _ (2035767 / 100000) (203577 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693858560 :
    ThetaLowerSegment 693858560 693924096 (69382748281959 / 100000) (69389329945767 / 100000) := by
  exact
    packedTile32768 693858560 693924096 13 3233 26341 29 _ _ (63618 / 3125) (2035779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693924096 :
    ThetaLowerSegment 693924096 693989632 (69389329945767 / 100000) (69395999180703 / 100000) := by
  exact
    packedTile32768 693924096 693989632 13 3276 26342 29 _ _ (1017893 / 50000) (2035789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell693989632 :
    ThetaLowerSegment 693989632 694055168 (69395999180703 / 100000) (8675319050601 / 12500) := by
  exact
    packedTile32768 693989632 694055168 13 3219 26343 29 _ _ (407159 / 20000) (1017899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694055168 :
    ThetaLowerSegment 694055168 694120704 (8675319050601 / 12500) (34704592528749 / 50000) := by
  exact
    packedTile32768 694055168 694120704 13 3258 26344 29 _ _ (407161 / 20000) (63619 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694120704 :
    ThetaLowerSegment 694120704 694186240 (34704592528749 / 50000) (694157872023 / 1000) := by
  exact
    packedTile32768 694120704 694186240 13 3243 26346 29 _ _ (1017907 / 50000) (2035817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694186240 :
    ThetaLowerSegment 694186240 694251776 (694157872023 / 1000) (17355562226919 / 25000) := by
  exact
    packedTile32768 694186240 694251776 13 3174 26347 29 _ _ (127239 / 6250) (2035827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694251776 :
    ThetaLowerSegment 694251776 694317312 (17355562226919 / 25000) (69428704534119 / 100000) := by
  exact
    packedTile32768 694251776 694317312 13 3171 26348 29 _ _ (2035833 / 100000) (508959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694317312 :
    ThetaLowerSegment 694317312 694382848 (69428704534119 / 100000) (69435312877251 / 100000) := by
  exact
    packedTile32768 694317312 694382848 13 3246 26349 29 _ _ (1017921 / 50000) (407169 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694382848 :
    ThetaLowerSegment 694382848 694448384 (69435312877251 / 100000) (69441904966027 / 100000) := by
  exact
    packedTile32768 694382848 694448384 13 3238 26351 29 _ _ (508963 / 25000) (407171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694448384 :
    ThetaLowerSegment 694448384 694513920 (69441904966027 / 100000) (34724261775069 / 50000) := by
  exact
    packedTile32768 694448384 694513920 13 3251 26352 29 _ _ (2035861 / 100000) (254483 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694513920 :
    ThetaLowerSegment 694513920 694579456 (34724261775069 / 50000) (69455121808049 / 100000) := by
  exact
    packedTile32768 694513920 694579456 13 3241 26353 29 _ _ (2035871 / 100000) (1017937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694579456 :
    ThetaLowerSegment 694579456 694644992 (69455121808049 / 100000) (69461683449289 / 100000) := by
  exact
    packedTile32768 694579456 694644992 13 3223 26354 29 _ _ (50897 / 2500) (2035883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694644992 :
    ThetaLowerSegment 694644992 694710528 (69461683449289 / 100000) (69468302127679 / 100000) := by
  exact
    packedTile32768 694644992 694710528 13 3251 26356 29 _ _ (203589 / 10000) (2035893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694710528 :
    ThetaLowerSegment 694710528 694776064 (69468302127679 / 100000) (34737454309967 / 50000) := by
  exact
    packedTile32768 694710528 694776064 13 3245 26357 29 _ _ (2035899 / 100000) (1017951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694776064 :
    ThetaLowerSegment 694776064 694841600 (34737454309967 / 50000) (69481559934637 / 100000) := by
  exact
    packedTile32768 694776064 694841600 13 3267 26358 29 _ _ (2035909 / 100000) (254489 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694841600 :
    ThetaLowerSegment 694841600 694907136 (69481559934637 / 100000) (69488140021613 / 100000) := by
  exact
    packedTile32768 694841600 694907136 13 3232 26359 29 _ _ (1017959 / 50000) (2035921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694907136 :
    ThetaLowerSegment 694907136 694972672 (69488140021613 / 100000) (13898929368861 / 20000) := by
  exact
    packedTile32768 694907136 694972672 13 3196 26361 29 _ _ (2035927 / 100000) (203593 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell694972672 :
    ThetaLowerSegment 694972672 695038208 (13898929368861 / 20000) (34750581939321 / 50000) := by
  exact
    packedTile32768 694972672 695038208 13 3201 26362 29 _ _ (2035937 / 100000) (101797 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695038208 :
    ThetaLowerSegment 695038208 695103744 (34750581939321 / 50000) (34753890351571 / 50000) := by
  exact
    packedTile32768 695038208 695103744 13 3250 26363 29 _ _ (1017973 / 50000) (2035949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695103744 :
    ThetaLowerSegment 695103744 695169280 (34753890351571 / 50000) (34757153989039 / 50000) := by
  exact
    packedTile32768 695103744 695169280 13 3206 26364 29 _ _ (508989 / 25000) (2035959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695169280 :
    ThetaLowerSegment 695169280 695234816 (34757153989039 / 50000) (34760403389179 / 50000) := by
  exact
    packedTile32768 695169280 695234816 13 3192 26366 29 _ _ (407193 / 20000) (63624 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695234816 :
    ThetaLowerSegment 695234816 695300352 (34760403389179 / 50000) (69527454236733 / 100000) := by
  exact
    packedTile32768 695234816 695300352 13 3265 26367 29 _ _ (81439 / 4000) (1017989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695300352 :
    ThetaLowerSegment 695300352 695365888 (69527454236733 / 100000) (69534065076781 / 100000) := by
  exact
    packedTile32768 695300352 695365888 13 3247 26368 29 _ _ (127249 / 6250) (2035987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695365888 :
    ThetaLowerSegment 695365888 695431424 (69534065076781 / 100000) (69540710557933 / 100000) := by
  exact
    packedTile32768 695365888 695431424 13 3264 26369 29 _ _ (2035993 / 100000) (508999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695431424 :
    ThetaLowerSegment 695431424 695496960 (69540710557933 / 100000) (13909438638297 / 20000) := by
  exact
    packedTile32768 695431424 695496960 13 3184 26371 29 _ _ (2036003 / 100000) (1018003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695496960 :
    ThetaLowerSegment 695496960 695562496 (13909438638297 / 20000) (69553838734653 / 100000) := by
  exact
    packedTile32768 695496960 695562496 13 3264 26372 29 _ _ (509003 / 25000) (407203 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695562496 :
    ThetaLowerSegment 695562496 695628032 (69553838734653 / 100000) (69560347896987 / 100000) := by
  exact
    packedTile32768 695562496 695628032 13 3197 26373 29 _ _ (1018011 / 50000) (81441 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695628032 :
    ThetaLowerSegment 695628032 695693568 (69560347896987 / 100000) (13913388113073 / 20000) := by
  exact
    packedTile32768 695628032 695693568 13 3238 26374 29 _ _ (2036031 / 100000) (1018017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695693568 :
    ThetaLowerSegment 695693568 695759104 (13913388113073 / 20000) (13914710724657 / 20000) := by
  exact
    packedTile32768 695693568 695759104 13 3248 26376 29 _ _ (50901 / 2500) (2036043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695759104 :
    ThetaLowerSegment 695759104 695824640 (13914710724657 / 20000) (13916023569697 / 20000) := by
  exact
    packedTile32768 695759104 695824640 13 3224 26377 29 _ _ (40721 / 2000) (2036053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695824640 :
    ThetaLowerSegment 695824640 695890176 (13916023569697 / 20000) (69586743184471 / 100000) := by
  exact
    packedTile32768 695824640 695890176 13 3254 26378 29 _ _ (2036059 / 100000) (1018031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695890176 :
    ThetaLowerSegment 695890176 695955712 (69586743184471 / 100000) (1391864805613 / 2000) := by
  exact
    packedTile32768 695890176 695955712 13 3191 26379 29 _ _ (2036069 / 100000) (254509 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell695955712 :
    ThetaLowerSegment 695955712 696021248 (1391864805613 / 2000) (34799930803153 / 50000) := by
  exact
    packedTile32768 695955712 696021248 13 3252 26380 29 _ _ (1018039 / 50000) (2036081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696021248 :
    ThetaLowerSegment 696021248 696086784 (34799930803153 / 50000) (34803187525909 / 50000) := by
  exact
    packedTile32768 696021248 696086784 13 3199 26382 29 _ _ (254511 / 12500) (2036091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696086784 :
    ThetaLowerSegment 696086784 696152320 (34803187525909 / 50000) (4350814568063 / 6250) := by
  exact
    packedTile32768 696086784 696152320 13 3270 26383 29 _ _ (2036097 / 100000) (20361 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696152320 :
    ThetaLowerSegment 696152320 696217856 (4350814568063 / 6250) (17404892247317 / 25000) := by
  exact
    packedTile32768 696152320 696217856 13 3210 26384 29 _ _ (1018053 / 50000) (2036109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696217856 :
    ThetaLowerSegment 696217856 696283392 (17404892247317 / 25000) (17406541501277 / 25000) := by
  exact
    packedTile32768 696217856 696283392 13 3240 26385 29 _ _ (509029 / 25000) (2036119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696283392 :
    ThetaLowerSegment 696283392 696348928 (17406541501277 / 25000) (69632585907233 / 100000) := by
  exact
    packedTile32768 696283392 696348928 13 3153 26387 29 _ _ (16289 / 800) (63629 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696348928 :
    ThetaLowerSegment 696348928 696414464 (69632585907233 / 100000) (69639174840093 / 100000) := by
  exact
    packedTile32768 696348928 696414464 13 3236 26388 29 _ _ (407227 / 20000) (1018069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696414464 :
    ThetaLowerSegment 696414464 696480000 (69639174840093 / 100000) (69645670139453 / 100000) := by
  exact
    packedTile32768 696414464 696480000 13 3190 26389 29 _ _ (127259 / 6250) (2036147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696480000 :
    ThetaLowerSegment 696480000 696545536 (69645670139453 / 100000) (34826069498767 / 50000) := by
  exact
    packedTile32768 696480000 696545536 13 3177 26390 29 _ _ (2036153 / 100000) (509039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696545536 :
    ThetaLowerSegment 696545536 696611072 (34826069498767 / 50000) (4353662611181 / 6250) := by
  exact
    packedTile32768 696545536 696611072 13 3174 26392 29 _ _ (2036163 / 100000) (1018083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696611072 :
    ThetaLowerSegment 696611072 696676608 (4353662611181 / 6250) (1741629058127 / 2500) := by
  exact
    packedTile32768 696611072 696676608 13 3222 26393 29 _ _ (509043 / 25000) (81447 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696676608 :
    ThetaLowerSegment 696676608 696742144 (1741629058127 / 2500) (34835911338201 / 50000) := by
  exact
    packedTile32768 696676608 696742144 13 3271 26394 29 _ _ (1018091 / 50000) (407237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696742144 :
    ThetaLowerSegment 696742144 696807680 (34835911338201 / 50000) (13935697425909 / 20000) := by
  exact
    packedTile32768 696742144 696807680 13 3273 26395 29 _ _ (2036191 / 100000) (1018097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696807680 :
    ThetaLowerSegment 696807680 696873216 (13935697425909 / 20000) (69684884873087 / 100000) := by
  exact
    packedTile32768 696807680 696873216 13 3142 26397 29 _ _ (2036201 / 100000) (509051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696873216 :
    ThetaLowerSegment 696873216 696938752 (69684884873087 / 100000) (69691522917687 / 100000) := by
  exact
    packedTile32768 696873216 696938752 13 3260 26398 29 _ _ (203621 / 10000) (2036213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell696938752 :
    ThetaLowerSegment 696938752 697004288 (69691522917687 / 100000) (69698075470429 / 100000) := by
  exact
    packedTile32768 696938752 697004288 13 3218 26399 29 _ _ (2036219 / 100000) (1018111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697004288 :
    ThetaLowerSegment 697004288 697069824 (69698075470429 / 100000) (69704583258313 / 100000) := by
  exact
    packedTile32768 697004288 697069824 13 3196 26400 29 _ _ (2036229 / 100000) (254529 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697069824 :
    ThetaLowerSegment 697069824 697135360 (69704583258313 / 100000) (69711141980911 / 100000) := by
  exact
    packedTile32768 697069824 697135360 13 3221 26402 29 _ _ (1018119 / 50000) (2036241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697135360 :
    ThetaLowerSegment 697135360 697200896 (69711141980911 / 100000) (69717698699471 / 100000) := by
  exact
    packedTile32768 697135360 697200896 13 3220 26403 29 _ _ (254531 / 12500) (2036251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697200896 :
    ThetaLowerSegment 697200896 697266432 (69717698699471 / 100000) (69724141416619 / 100000) := by
  exact
    packedTile32768 697200896 697266432 13 3164 26404 29 _ _ (2036257 / 100000) (101813 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697266432 :
    ThetaLowerSegment 697266432 697331968 (69724141416619 / 100000) (13946144118413 / 20000) := by
  exact
    packedTile32768 697266432 697331968 13 3231 26405 29 _ _ (1018133 / 50000) (2036269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697331968 :
    ThetaLowerSegment 697331968 697397504 (13946144118413 / 20000) (69737157260501 / 100000) := by
  exact
    packedTile32768 697331968 697397504 13 3161 26407 29 _ _ (509069 / 25000) (2036279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697397504 :
    ThetaLowerSegment 697397504 697463040 (69737157260501 / 100000) (34871841776963 / 50000) := by
  exact
    packedTile32768 697397504 697463040 13 3205 26408 29 _ _ (407257 / 20000) (63634 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697463040 :
    ThetaLowerSegment 697463040 697528576 (34871841776963 / 50000) (69750148790551 / 100000) := by
  exact
    packedTile32768 697463040 697528576 13 3175 26409 29 _ _ (407259 / 20000) (1018149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697528576 :
    ThetaLowerSegment 697528576 697594112 (69750148790551 / 100000) (13951359871883 / 20000) := by
  exact
    packedTile32768 697528576 697594112 13 3266 26410 29 _ _ (127269 / 6250) (2036307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697594112 :
    ThetaLowerSegment 697594112 697659648 (13951359871883 / 20000) (34881668980229 / 50000) := by
  exact
    packedTile32768 697594112 697659648 13 3211 26412 29 _ _ (2036313 / 100000) (509079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697659648 :
    ThetaLowerSegment 697659648 697725184 (34881668980229 / 50000) (69769819576567 / 100000) := by
  exact
    packedTile32768 697659648 697725184 13 3183 26413 29 _ _ (2036323 / 100000) (1018163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697725184 :
    ThetaLowerSegment 697725184 697790720 (69769819576567 / 100000) (69776409146919 / 100000) := by
  exact
    packedTile32768 697725184 697790720 13 3236 26414 29 _ _ (509083 / 25000) (407267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697790720 :
    ThetaLowerSegment 697790720 697856256 (69776409146919 / 100000) (4361429403557 / 6250) := by
  exact
    packedTile32768 697790720 697856256 13 3173 26415 29 _ _ (2036341 / 100000) (254543 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697856256 :
    ThetaLowerSegment 697856256 697921792 (4361429403557 / 6250) (69789523215629 / 100000) := by
  exact
    packedTile32768 697856256 697921792 13 3267 26416 29 _ _ (2036351 / 100000) (1018177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697921792 :
    ThetaLowerSegment 697921792 697987328 (69789523215629 / 100000) (69796092512989 / 100000) := by
  exact
    packedTile32768 697921792 697987328 13 3226 26418 29 _ _ (50909 / 2500) (2036363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell697987328 :
    ThetaLowerSegment 697987328 698052864 (69796092512989 / 100000) (69802672024459 / 100000) := by
  exact
    packedTile32768 697987328 698052864 13 3231 26419 29 _ _ (203637 / 10000) (2036373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698052864 :
    ThetaLowerSegment 698052864 698118400 (69802672024459 / 100000) (872614830011 / 1250) := by
  exact
    packedTile32768 698052864 698118400 13 3199 26420 29 _ _ (2036379 / 100000) (1018191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698118400 :
    ThetaLowerSegment 698118400 698183936 (872614830011 / 1250) (8726952164273 / 12500) := by
  exact
    packedTile32768 698118400 698183936 13 3158 26421 29 _ _ (509097 / 25000) (2036391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698183936 :
    ThetaLowerSegment 698183936 698249472 (8726952164273 / 12500) (17455567047513 / 25000) := by
  exact
    packedTile32768 698183936 698249472 13 3266 26423 29 _ _ (1018199 / 50000) (2036401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698249472 :
    ThetaLowerSegment 698249472 698315008 (17455567047513 / 25000) (69828668617253 / 100000) := by
  exact
    packedTile32768 698249472 698315008 13 3143 26424 29 _ _ (2036407 / 100000) (203641 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698315008 :
    ThetaLowerSegment 698315008 698380544 (69828668617253 / 100000) (17458787633141 / 25000) := by
  exact
    packedTile32768 698315008 698380544 13 3183 26425 29 _ _ (2036417 / 100000) (101821 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698380544 :
    ThetaLowerSegment 698380544 698446080 (17458787633141 / 25000) (17460433065349 / 25000) := by
  exact
    packedTile32768 698380544 698446080 13 3232 26426 29 _ _ (1018213 / 50000) (2036429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698446080 :
    ThetaLowerSegment 698446080 698511616 (17460433065349 / 25000) (69848254962701 / 100000) := by
  exact
    packedTile32768 698446080 698511616 13 3203 26428 29 _ _ (407287 / 20000) (1018219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698511616 :
    ThetaLowerSegment 698511616 698577152 (69848254962701 / 100000) (69854800096931 / 100000) := by
  exact
    packedTile32768 698511616 698577152 13 3214 26429 29 _ _ (407289 / 20000) (63639 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698577152 :
    ThetaLowerSegment 698577152 698642688 (69854800096931 / 100000) (69861424681793 / 100000) := by
  exact
    packedTile32768 698577152 698642688 13 3253 26430 29 _ _ (1018227 / 50000) (2036457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698642688 :
    ThetaLowerSegment 698642688 698708224 (69861424681793 / 100000) (69868096134581 / 100000) := by
  exact
    packedTile32768 698642688 698708224 13 3276 26431 29 _ _ (2036463 / 100000) (1018233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698708224 :
    ThetaLowerSegment 698708224 698773760 (69868096134581 / 100000) (69874747255399 / 100000) := by
  exact
    packedTile32768 698708224 698773760 13 3266 26433 29 _ _ (2036473 / 100000) (509119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698773760 :
    ThetaLowerSegment 698773760 698839296 (69874747255399 / 100000) (69881213085749 / 100000) := by
  exact
    packedTile32768 698773760 698839296 13 3175 26434 29 _ _ (1018241 / 50000) (407297 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698839296 :
    ThetaLowerSegment 698839296 698904832 (69881213085749 / 100000) (69887625999057 / 100000) := by
  exact
    packedTile32768 698839296 698904832 13 3149 26435 29 _ _ (509123 / 25000) (407299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698904832 :
    ThetaLowerSegment 698904832 698970368 (69887625999057 / 100000) (13978823672849 / 20000) := by
  exact
    packedTile32768 698904832 698970368 13 3188 26436 29 _ _ (2036501 / 100000) (254563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell698970368 :
    ThetaLowerSegment 698970368 699035904 (13978823672849 / 20000) (13980165325637 / 20000) := by
  exact
    packedTile32768 698970368 699035904 13 3294 26438 29 _ _ (203651 / 10000) (2036513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699035904 :
    ThetaLowerSegment 699035904 699101440 (13980165325637 / 20000) (13981478881037 / 20000) := by
  exact
    packedTile32768 699035904 699101440 13 3225 26439 29 _ _ (50913 / 2500) (2036523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699101440 :
    ThetaLowerSegment 699101440 699166976 (13981478881037 / 20000) (4369623401899 / 6250) := by
  exact
    packedTile32768 699101440 699166976 13 3231 26440 29 _ _ (2036529 / 100000) (509133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699166976 :
    ThetaLowerSegment 699166976 699232512 (4369623401899 / 6250) (34960243641053 / 50000) := by
  exact
    packedTile32768 699166976 699232512 13 3198 26441 29 _ _ (2036539 / 100000) (1018271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699232512 :
    ThetaLowerSegment 699232512 699298048 (34960243641053 / 50000) (34963526556429 / 50000) := by
  exact
    packedTile32768 699232512 699298048 13 3224 26443 29 _ _ (509137 / 25000) (2036551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699298048 :
    ThetaLowerSegment 699298048 699363584 (34963526556429 / 50000) (2797345329141 / 4000) := by
  exact
    packedTile32768 699298048 699363584 13 3231 26444 29 _ _ (2036557 / 100000) (25457 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699363584 :
    ThetaLowerSegment 699363584 699429120 (2797345329141 / 4000) (13988042267987 / 20000) := by
  exact
    packedTile32768 699363584 699429120 13 3230 26445 29 _ _ (2036567 / 100000) (203657 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699429120 :
    ThetaLowerSegment 699429120 699494656 (13988042267987 / 20000) (69946589895967 / 100000) := by
  exact
    packedTile32768 699429120 699494656 13 3132 26446 29 _ _ (63643 / 3125) (2036579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699494656 :
    ThetaLowerSegment 699494656 699560192 (69946589895967 / 100000) (69953212870387 / 100000) := by
  exact
    packedTile32768 699494656 699560192 13 3252 26447 29 _ _ (407317 / 20000) (509147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699560192 :
    ThetaLowerSegment 699560192 699625728 (69953212870387 / 100000) (17489925874663 / 25000) := by
  exact
    packedTile32768 699560192 699625728 13 3187 26449 29 _ _ (407319 / 20000) (1018299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699625728 :
    ThetaLowerSegment 699625728 699691264 (17489925874663 / 25000) (2186446367693 / 3125) := by
  exact
    packedTile32768 699625728 699691264 13 3231 26450 29 _ _ (509151 / 25000) (2036607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699691264 :
    ThetaLowerSegment 699691264 699756800 (2186446367693 / 3125) (69972778525033 / 100000) := by
  exact
    packedTile32768 699691264 699756800 13 3189 26451 29 _ _ (2036613 / 100000) (254577 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699756800 :
    ThetaLowerSegment 699756800 699822336 (69972778525033 / 100000) (34989724232679 / 50000) := by
  exact
    packedTile32768 699756800 699822336 13 3275 26452 29 _ _ (2036623 / 100000) (1018313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699822336 :
    ThetaLowerSegment 699822336 699887872 (34989724232679 / 50000) (34992984880511 / 50000) := by
  exact
    packedTile32768 699822336 699887872 13 3202 26454 29 _ _ (254579 / 12500) (407327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699887872 :
    ThetaLowerSegment 699887872 699953408 (34992984880511 / 50000) (34996261837489 / 50000) := by
  exact
    packedTile32768 699887872 699953408 13 3218 26455 29 _ _ (1018321 / 50000) (407329 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell699953408 :
    ThetaLowerSegment 699953408 700018944 (34996261837489 / 50000) (69999067434641 / 100000) := by
  exact
    packedTile32768 699953408 700018944 13 3213 26456 29 _ _ (2036651 / 100000) (1018327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700018944 :
    ThetaLowerSegment 700018944 700084480 (69999067434641 / 100000) (70005590856621 / 100000) := by
  exact
    packedTile32768 700018944 700084480 13 3203 26457 29 _ _ (101833 / 5000) (2036663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700084480 :
    ThetaLowerSegment 700084480 700150016 (70005590856621 / 100000) (70012191704091 / 100000) := by
  exact
    packedTile32768 700084480 700150016 13 3241 26459 29 _ _ (203667 / 10000) (2036673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700150016 :
    ThetaLowerSegment 700150016 700215552 (70012191704091 / 100000) (4376169699183 / 6250) := by
  exact
    packedTile32768 700150016 700215552 13 3203 26460 29 _ _ (2036679 / 100000) (1018341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700215552 :
    ThetaLowerSegment 700215552 700281088 (4376169699183 / 6250) (4376585692707 / 6250) := by
  exact
    packedTile32768 700215552 700281088 13 3268 26461 29 _ _ (127293 / 6250) (2036691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700281088 :
    ThetaLowerSegment 700281088 700346624 (4376585692707 / 6250) (35015947313503 / 50000) := by
  exact
    packedTile32768 700281088 700346624 13 3203 26462 29 _ _ (1018349 / 50000) (2036701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700346624 :
    ThetaLowerSegment 700346624 700412160 (35015947313503 / 50000) (2801537868537 / 4000) := by
  exact
    packedTile32768 700346624 700412160 13 3217 26464 29 _ _ (2036707 / 100000) (203671 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700412160 :
    ThetaLowerSegment 700412160 700477696 (2801537868537 / 4000) (70044945874181 / 100000) := by
  exact
    packedTile32768 700412160 700477696 13 3191 26465 29 _ _ (509179 / 25000) (2036719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700477696 :
    ThetaLowerSegment 700477696 700543232 (70044945874181 / 100000) (70051550976599 / 100000) := by
  exact
    packedTile32768 700477696 700543232 13 3243 26466 29 _ _ (1018363 / 50000) (2036729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700543232 :
    ThetaLowerSegment 700543232 700608768 (70051550976599 / 100000) (70058084822479 / 100000) := by
  exact
    packedTile32768 700543232 700608768 13 3208 26467 29 _ _ (407347 / 20000) (1018369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700608768 :
    ThetaLowerSegment 700608768 700674304 (70058084822479 / 100000) (17516140927081 / 25000) := by
  exact
    packedTile32768 700608768 700674304 13 3181 26469 29 _ _ (407349 / 20000) (509187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700674304 :
    ThetaLowerSegment 700674304 700739840 (17516140927081 / 25000) (350355345503 / 500) := by
  exact
    packedTile32768 700674304 700739840 13 3194 26470 29 _ _ (1018377 / 50000) (2036757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700739840 :
    ThetaLowerSegment 700739840 700805376 (350355345503 / 500) (17519390575261 / 25000) := by
  exact
    packedTile32768 700739840 700805376 13 3188 26471 29 _ _ (2036763 / 100000) (1018383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700805376 :
    ThetaLowerSegment 700805376 700870912 (17519390575261 / 25000) (70084183850067 / 100000) := by
  exact
    packedTile32768 700805376 700870912 13 3251 26472 29 _ _ (2036773 / 100000) (254597 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700870912 :
    ThetaLowerSegment 700870912 700936448 (70084183850067 / 100000) (14018139903137 / 20000) := by
  exact
    packedTile32768 700870912 700936448 13 3199 26473 29 _ _ (1018391 / 50000) (407357 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell700936448 :
    ThetaLowerSegment 700936448 701001984 (14018139903137 / 20000) (35048676855941 / 50000) := by
  exact
    packedTile32768 700936448 701001984 13 3267 26475 29 _ _ (2036791 / 100000) (1018397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701001984 :
    ThetaLowerSegment 701001984 701067520 (35048676855941 / 50000) (35052000915173 / 50000) := by
  exact
    packedTile32768 701001984 701067520 13 3264 26476 29 _ _ (2036801 / 100000) (509201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701067520 :
    ThetaLowerSegment 701067520 701133056 (35052000915173 / 50000) (8763805532547 / 12500) := by
  exact
    packedTile32768 701067520 701133056 13 3163 26477 29 _ _ (203681 / 10000) (2036813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701133056 :
    ThetaLowerSegment 701133056 701198592 (8763805532547 / 12500) (35058515666511 / 50000) := by
  exact
    packedTile32768 701133056 701198592 13 3234 26478 29 _ _ (2036819 / 100000) (1018411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701198592 :
    ThetaLowerSegment 701198592 701264128 (35058515666511 / 50000) (35061843845097 / 50000) := by
  exact
    packedTile32768 701198592 701264128 13 3268 26480 29 _ _ (2036829 / 100000) (63651 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701264128 :
    ThetaLowerSegment 701264128 701329664 (35061843845097 / 50000) (35065143522657 / 50000) := by
  exact
    packedTile32768 701264128 701329664 13 3240 26481 29 _ _ (1018419 / 50000) (2036841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701329664 :
    ThetaLowerSegment 701329664 701395200 (35065143522657 / 50000) (17534216515281 / 25000) := by
  exact
    packedTile32768 701329664 701395200 13 3230 26482 29 _ _ (2036847 / 100000) (40737 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701395200 :
    ThetaLowerSegment 701395200 701460736 (17534216515281 / 25000) (35071706259761 / 50000) := by
  exact
    packedTile32768 701395200 701460736 13 3214 26483 29 _ _ (2036857 / 100000) (101843 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701460736 :
    ThetaLowerSegment 701460736 701526272 (35071706259761 / 50000) (17537485168763 / 25000) := by
  exact
    packedTile32768 701460736 701526272 13 3205 26485 29 _ _ (1018433 / 50000) (2036869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701526272 :
    ThetaLowerSegment 701526272 701591808 (17537485168763 / 25000) (35078251743151 / 50000) := by
  exact
    packedTile32768 701526272 701591808 13 3222 26486 29 _ _ (3259 / 160) (1018439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701591808 :
    ThetaLowerSegment 701591808 701657344 (35078251743151 / 50000) (35081539275541 / 50000) := by
  exact
    packedTile32768 701591808 701657344 13 3228 26487 29 _ _ (407377 / 20000) (254611 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701657344 :
    ThetaLowerSegment 701657344 701722880 (35081539275541 / 50000) (17542429197157 / 25000) := by
  exact
    packedTile32768 701657344 701722880 13 3259 26488 29 _ _ (1018447 / 50000) (2036897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701722880 :
    ThetaLowerSegment 701722880 701788416 (17542429197157 / 25000) (35088078737957 / 50000) := by
  exact
    packedTile32768 701722880 701788416 13 3162 26490 29 _ _ (2036903 / 100000) (1018453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701788416 :
    ThetaLowerSegment 701788416 701853952 (35088078737957 / 50000) (2193212049713 / 3125) := by
  exact
    packedTile32768 701788416 701853952 13 3254 26491 29 _ _ (2036913 / 100000) (509229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701853952 :
    ThetaLowerSegment 701853952 701919488 (2193212049713 / 3125) (2193414723452 / 3125) := by
  exact
    packedTile32768 701853952 701919488 13 3184 26492 29 _ _ (1018461 / 50000) (81477 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701919488 :
    ThetaLowerSegment 701919488 701985024 (2193414723452 / 3125) (7019576081263 / 10000) := by
  exact
    packedTile32768 701919488 701985024 13 3186 26493 29 _ _ (2036931 / 100000) (1018467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell701985024 :
    ThetaLowerSegment 701985024 702050560 (7019576081263 / 10000) (2808098901329 / 4000) := by
  exact
    packedTile32768 701985024 702050560 13 3295 26494 29 _ _ (2036941 / 100000) (127309 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702050560 :
    ThetaLowerSegment 702050560 702116096 (2808098901329 / 4000) (2808358897627 / 4000) := by
  exact
    packedTile32768 702050560 702116096 13 3191 26496 29 _ _ (40739 / 2000) (2036953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702116096 :
    ThetaLowerSegment 702116096 702181632 (2808358897627 / 4000) (17553884389883 / 25000) := by
  exact
    packedTile32768 702116096 702181632 13 3223 26497 29 _ _ (2036959 / 100000) (1018481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702181632 :
    ThetaLowerSegment 702181632 702247168 (17553884389883 / 25000) (35111034041073 / 50000) := by
  exact
    packedTile32768 702181632 702247168 13 3206 26498 29 _ _ (2036969 / 100000) (509243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702247168 :
    ThetaLowerSegment 702247168 702312704 (35111034041073 / 50000) (35114348204279 / 50000) := by
  exact
    packedTile32768 702247168 702312704 13 3254 26499 29 _ _ (1018489 / 50000) (2036981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702312704 :
    ThetaLowerSegment 702312704 702378240 (35114348204279 / 50000) (3511763386431 / 5000) := by
  exact
    packedTile32768 702312704 702378240 13 3226 26501 29 _ _ (2036987 / 100000) (203699 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702378240 :
    ThetaLowerSegment 702378240 702443776 (3511763386431 / 5000) (561933718593 / 800) := by
  exact
    packedTile32768 702378240 702443776 13 3165 26502 29 _ _ (2036997 / 100000) (2037 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702443776 :
    ThetaLowerSegment 702443776 702509312 (561933718593 / 800) (70248428795901 / 100000) := by
  exact
    packedTile32768 702443776 702509312 13 3296 26503 29 _ _ (1018503 / 50000) (2037009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702509312 :
    ThetaLowerSegment 702509312 702574848 (70248428795901 / 100000) (35127513343743 / 50000) := by
  exact
    packedTile32768 702509312 702574848 13 3239 26504 29 _ _ (407403 / 20000) (1018509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702574848 :
    ThetaLowerSegment 702574848 702640384 (35127513343743 / 50000) (70261534982361 / 100000) := by
  exact
    packedTile32768 702574848 702640384 13 3195 26506 29 _ _ (81481 / 4000) (509257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702640384 :
    ThetaLowerSegment 702640384 702705920 (70261534982361 / 100000) (70268008676413 / 100000) := by
  exact
    packedTile32768 702640384 702705920 13 3178 26507 29 _ _ (1018517 / 50000) (2037037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702705920 :
    ThetaLowerSegment 702705920 702771456 (70268008676413 / 100000) (70274563880787 / 100000) := by
  exact
    packedTile32768 702705920 702771456 13 3218 26508 29 _ _ (2037043 / 100000) (1018523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702771456 :
    ThetaLowerSegment 702771456 702836992 (70274563880787 / 100000) (35140564651303 / 50000) := by
  exact
    packedTile32768 702771456 702836992 13 3223 26509 29 _ _ (2037053 / 100000) (63658 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702836992 :
    ThetaLowerSegment 702836992 702902528 (35140564651303 / 50000) (17571916558641 / 25000) := by
  exact
    packedTile32768 702836992 702902528 13 3209 26511 29 _ _ (1018531 / 50000) (407413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702902528 :
    ThetaLowerSegment 702902528 702968064 (17571916558641 / 25000) (70294133934989 / 100000) := by
  exact
    packedTile32768 702902528 702968064 13 3175 26512 29 _ _ (2037071 / 100000) (1018537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell702968064 :
    ThetaLowerSegment 702968064 703033600 (70294133934989 / 100000) (70300721854943 / 100000) := by
  exact
    packedTile32768 702968064 703033600 13 3234 26513 29 _ _ (2037081 / 100000) (509271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703033600 :
    ThetaLowerSegment 703033600 703099136 (70300721854943 / 100000) (70307248691303 / 100000) := by
  exact
    packedTile32768 703033600 703099136 13 3204 26514 29 _ _ (203709 / 10000) (2037093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703099136 :
    ThetaLowerSegment 703099136 703164672 (70307248691303 / 100000) (70313836669469 / 100000) := by
  exact
    packedTile32768 703099136 703164672 13 3234 26516 29 _ _ (2037099 / 100000) (1018551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703164672 :
    ThetaLowerSegment 703164672 703230208 (70313836669469 / 100000) (70320457273719 / 100000) := by
  exact
    packedTile32768 703164672 703230208 13 3250 26517 29 _ _ (2037109 / 100000) (254639 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703230208 :
    ThetaLowerSegment 703230208 703295744 (70320457273719 / 100000) (70326931234723 / 100000) := by
  exact
    packedTile32768 703230208 703295744 13 3178 26518 29 _ _ (1018559 / 50000) (2037121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703295744 :
    ThetaLowerSegment 703295744 703361280 (70326931234723 / 100000) (4395837953841 / 6250) := by
  exact
    packedTile32768 703295744 703361280 13 3179 26519 29 _ _ (2037127 / 100000) (203713 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703361280 :
    ThetaLowerSegment 703361280 703426816 (4395837953841 / 6250) (17584995784923 / 25000) := by
  exact
    packedTile32768 703361280 703426816 13 3228 26520 29 _ _ (2037137 / 100000) (101857 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703426816 :
    ThetaLowerSegment 703426816 703492352 (17584995784923 / 25000) (35173280542063 / 50000) := by
  exact
    packedTile32768 703426816 703492352 13 3229 26522 29 _ _ (1018573 / 50000) (2037149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703492352 :
    ThetaLowerSegment 703492352 703557888 (35173280542063 / 50000) (70353204246581 / 100000) := by
  exact
    packedTile32768 703492352 703557888 13 3261 26523 29 _ _ (407431 / 20000) (1018579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703557888 :
    ThetaLowerSegment 703557888 703623424 (70353204246581 / 100000) (70359629464991 / 100000) := by
  exact
    packedTile32768 703557888 703623424 13 3154 26524 29 _ _ (407433 / 20000) (127323 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703623424 :
    ThetaLowerSegment 703623424 703688960 (70359629464991 / 100000) (70366185090923 / 100000) := by
  exact
    packedTile32768 703623424 703688960 13 3218 26525 29 _ _ (1018587 / 50000) (2037177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703688960 :
    ThetaLowerSegment 703688960 703754496 (70366185090923 / 100000) (2814907674137 / 4000) := by
  exact
    packedTile32768 703688960 703754496 13 3194 26527 29 _ _ (2037183 / 100000) (1018593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703754496 :
    ThetaLowerSegment 703754496 703820032 (2814907674137 / 4000) (17594783873721 / 25000) := by
  exact
    packedTile32768 703754496 703820032 13 3163 26528 29 _ _ (2037193 / 100000) (509299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703820032 :
    ThetaLowerSegment 703820032 703885568 (17594783873721 / 25000) (35192909777323 / 50000) := by
  exact
    packedTile32768 703820032 703885568 13 3281 26529 29 _ _ (1018601 / 50000) (407441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703885568 :
    ThetaLowerSegment 703885568 703951104 (35192909777323 / 50000) (563140159533 / 800) := by
  exact
    packedTile32768 703885568 703951104 13 3289 26530 29 _ _ (2037211 / 100000) (1018607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell703951104 :
    ThetaLowerSegment 703951104 704016640 (563140159533 / 800) (14079802919797 / 20000) := by
  exact
    packedTile32768 703951104 704016640 13 3188 26532 29 _ _ (101861 / 5000) (2037223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704016640 :
    ThetaLowerSegment 704016640 704082176 (14079802919797 / 20000) (14081098190631 / 20000) := by
  exact
    packedTile32768 704016640 704082176 13 3179 26533 29 _ _ (203723 / 10000) (2037233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704082176 :
    ThetaLowerSegment 704082176 704147712 (14081098190631 / 20000) (70412063086169 / 100000) := by
  exact
    packedTile32768 704082176 704147712 13 3226 26534 29 _ _ (2037239 / 100000) (1018621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704147712 :
    ThetaLowerSegment 704147712 704213248 (70412063086169 / 100000) (70418730998873 / 100000) := by
  exact
    packedTile32768 704147712 704213248 13 3273 26535 29 _ _ (63664 / 3125) (2037251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704213248 :
    ThetaLowerSegment 704213248 704278784 (70418730998873 / 100000) (70425274671569 / 100000) := by
  exact
    packedTile32768 704213248 704278784 13 3212 26537 29 _ _ (1018629 / 50000) (2037261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704278784 :
    ThetaLowerSegment 704278784 704344320 (70425274671569 / 100000) (70431834671309 / 100000) := by
  exact
    packedTile32768 704278784 704344320 13 3220 26538 29 _ _ (2037267 / 100000) (203727 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704344320 :
    ThetaLowerSegment 704344320 704409856 (70431834671309 / 100000) (14087650825597 / 20000) := by
  exact
    packedTile32768 704344320 704409856 13 3151 26539 29 _ _ (509319 / 25000) (2037279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704409856 :
    ThetaLowerSegment 704409856 704475392 (14087650825597 / 20000) (14089019881789 / 20000) := by
  exact
    packedTile32768 704409856 704475392 13 3360 26540 29 _ _ (1018643 / 50000) (2037289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704475392 :
    ThetaLowerSegment 704475392 704540928 (14089019881789 / 20000) (440323444857 / 625) := by
  exact
    packedTile32768 704475392 704540928 13 3265 26541 29 _ _ (407459 / 20000) (1018649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704540928 :
    ThetaLowerSegment 704540928 704606464 (440323444857 / 625) (8807292222619 / 12500) := by
  exact
    packedTile32768 704540928 704606464 13 3233 26543 29 _ _ (254663 / 12500) (2037307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704606464 :
    ThetaLowerSegment 704606464 704672000 (8807292222619 / 12500) (70464745130337 / 100000) := by
  exact
    packedTile32768 704606464 704672000 13 3145 26544 29 _ _ (2037313 / 100000) (509329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704672000 :
    ThetaLowerSegment 704672000 704737536 (70464745130337 / 100000) (70471284937167 / 100000) := by
  exact
    packedTile32768 704672000 704737536 13 3210 26545 29 _ _ (2037323 / 100000) (1018663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704737536 :
    ThetaLowerSegment 704737536 704803072 (70471284937167 / 100000) (70477747354271 / 100000) := by
  exact
    packedTile32768 704737536 704803072 13 3172 26546 29 _ _ (509333 / 25000) (407467 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704803072 :
    ThetaLowerSegment 704803072 704868608 (70477747354271 / 100000) (14096822401511 / 20000) := by
  exact
    packedTile32768 704803072 704868608 13 3124 26548 29 _ _ (2037341 / 100000) (63667 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704868608 :
    ThetaLowerSegment 704868608 704934144 (14096822401511 / 20000) (14098118156747 / 20000) := by
  exact
    packedTile32768 704868608 704934144 13 3180 26549 29 _ _ (2037351 / 100000) (1018677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704934144 :
    ThetaLowerSegment 704934144 704999680 (14098118156747 / 20000) (14099448960299 / 20000) := by
  exact
    packedTile32768 704934144 704999680 13 3266 26550 29 _ _ (25467 / 1250) (2037363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell704999680 :
    ThetaLowerSegment 704999680 705065216 (14099448960299 / 20000) (35251934144057 / 50000) := by
  exact
    packedTile32768 704999680 705065216 13 3251 26551 29 _ _ (2037369 / 100000) (509343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705065216 :
    ThetaLowerSegment 705065216 705130752 (35251934144057 / 50000) (14102089396981 / 20000) := by
  exact
    packedTile32768 705065216 705130752 13 3229 26553 29 _ _ (2037379 / 100000) (1018691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705130752 :
    ThetaLowerSegment 705130752 705196288 (14102089396981 / 20000) (70517021635981 / 100000) := by
  exact
    packedTile32768 705130752 705196288 13 3227 26554 29 _ _ (509347 / 25000) (2037391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705196288 :
    ThetaLowerSegment 705196288 705261824 (70517021635981 / 100000) (2820941815247 / 4000) := by
  exact
    packedTile32768 705196288 705261824 13 3202 26555 29 _ _ (2037397 / 100000) (10187 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705261824 :
    ThetaLowerSegment 705261824 705327360 (2820941815247 / 4000) (70529928574173 / 100000) := by
  exact
    packedTile32768 705261824 705327360 13 3133 26556 29 _ _ (1018703 / 50000) (2037409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705327360 :
    ThetaLowerSegment 705327360 705392896 (70529928574173 / 100000) (70536454417621 / 100000) := by
  exact
    packedTile32768 705327360 705392896 13 3203 26557 29 _ _ (254677 / 12500) (2037419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705392896 :
    ThetaLowerSegment 705392896 705458432 (70536454417621 / 100000) (70543047524921 / 100000) := by
  exact
    packedTile32768 705392896 705458432 13 3236 26559 29 _ _ (81497 / 4000) (509357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705458432 :
    ThetaLowerSegment 705458432 705523968 (70543047524921 / 100000) (70549699746931 / 100000) := by
  exact
    packedTile32768 705458432 705523968 13 3265 26560 29 _ _ (1018717 / 50000) (2037437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705523968 :
    ThetaLowerSegment 705523968 705589504 (70549699746931 / 100000) (70556368301143 / 100000) := by
  exact
    packedTile32768 705523968 705589504 13 3273 26561 29 _ _ (509361 / 25000) (2037447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705589504 :
    ThetaLowerSegment 705589504 705655040 (70556368301143 / 100000) (7056296761141 / 10000) := by
  exact
    packedTile32768 705589504 705655040 13 3239 26562 29 _ _ (2037453 / 100000) (127341 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705655040 :
    ThetaLowerSegment 705655040 705720576 (7056296761141 / 10000) (2205299858603 / 3125) := by
  exact
    packedTile32768 705655040 705720576 13 3253 26564 29 _ _ (1018731 / 50000) (407493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705720576 :
    ThetaLowerSegment 705720576 705786112 (2205299858603 / 3125) (14115194144411 / 20000) := by
  exact
    packedTile32768 705720576 705786112 13 3129 26565 29 _ _ (2037471 / 100000) (1018737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705786112 :
    ThetaLowerSegment 705786112 705851648 (14115194144411 / 20000) (70582474361407 / 100000) := by
  exact
    packedTile32768 705786112 705851648 13 3192 26566 29 _ _ (2037481 / 100000) (509371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705851648 :
    ThetaLowerSegment 705851648 705917184 (70582474361407 / 100000) (70588939317177 / 100000) := by
  exact
    packedTile32768 705851648 705917184 13 3173 26567 29 _ _ (203749 / 10000) (2037493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705917184 :
    ThetaLowerSegment 705917184 705982720 (70588939317177 / 100000) (7059555507643 / 10000) := by
  exact
    packedTile32768 705917184 705982720 13 3247 26569 29 _ _ (2037499 / 100000) (1018751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell705982720 :
    ThetaLowerSegment 705982720 706048256 (7059555507643 / 10000) (70602113817901 / 100000) := by
  exact
    packedTile32768 705982720 706048256 13 3219 26570 29 _ _ (2037509 / 100000) (254689 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706048256 :
    ThetaLowerSegment 706048256 706113792 (70602113817901 / 100000) (70608552374781 / 100000) := by
  exact
    packedTile32768 706048256 706113792 13 3160 26571 29 _ _ (1018759 / 50000) (2037521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706113792 :
    ThetaLowerSegment 706113792 706179328 (70608552374781 / 100000) (70615125436883 / 100000) := by
  exact
    packedTile32768 706113792 706179328 13 3226 26572 29 _ _ (2037527 / 100000) (203753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706179328 :
    ThetaLowerSegment 706179328 706244864 (70615125436883 / 100000) (70621647589619 / 100000) := by
  exact
    packedTile32768 706179328 706244864 13 3201 26574 29 _ _ (63673 / 3125) (2037539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706244864 :
    ThetaLowerSegment 706244864 706310400 (70621647589619 / 100000) (565026336217 / 800) := by
  exact
    packedTile32768 706244864 706310400 13 3261 26575 29 _ _ (1018773 / 50000) (2037549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706310400 :
    ThetaLowerSegment 706310400 706375936 (565026336217 / 800) (14126967330757 / 20000) := by
  exact
    packedTile32768 706310400 706375936 13 3212 26576 29 _ _ (407511 / 20000) (1018779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706375936 :
    ThetaLowerSegment 706375936 706441472 (14126967330757 / 20000) (70641385384481 / 100000) := by
  exact
    packedTile32768 706375936 706441472 13 3214 26577 29 _ _ (509391 / 25000) (2037567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706441472 :
    ThetaLowerSegment 706441472 706507008 (70641385384481 / 100000) (70647942297613 / 100000) := by
  exact
    packedTile32768 706441472 706507008 13 3218 26578 29 _ _ (1018787 / 50000) (2037577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706507008 :
    ThetaLowerSegment 706507008 706572544 (70647942297613 / 100000) (17663644676361 / 25000) := by
  exact
    packedTile32768 706507008 706572544 13 3257 26580 29 _ _ (2037583 / 100000) (1018793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706572544 :
    ThetaLowerSegment 706572544 706638080 (17663644676361 / 25000) (17665282390931 / 25000) := by
  exact
    packedTile32768 706572544 706638080 13 3215 26581 29 _ _ (254699 / 12500) (407519 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706638080 :
    ThetaLowerSegment 706638080 706703616 (17665282390931 / 25000) (2826706076981 / 4000) := by
  exact
    packedTile32768 706638080 706703616 13 3201 26582 29 _ _ (2037601 / 100000) (509401 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706703616 :
    ThetaLowerSegment 706703616 706769152 (2826706076981 / 4000) (7067424359611 / 10000) := by
  exact
    packedTile32768 706703616 706769152 13 3235 26583 29 _ _ (2037611 / 100000) (1018807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706769152 :
    ThetaLowerSegment 706769152 706834688 (7067424359611 / 10000) (7068078028107 / 10000) := by
  exact
    packedTile32768 706769152 706834688 13 3208 26585 29 _ _ (101881 / 5000) (2037623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706834688 :
    ThetaLowerSegment 706834688 706900224 (7068078028107 / 10000) (2208977764628 / 3125) := by
  exact
    packedTile32768 706834688 706900224 13 3194 26586 29 _ _ (2037629 / 100000) (63676 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706900224 :
    ThetaLowerSegment 706900224 706965760 (2208977764628 / 3125) (35346894268253 / 50000) := by
  exact
    packedTile32768 706900224 706965760 13 3190 26587 29 _ _ (2037639 / 100000) (1018821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell706965760 :
    ThetaLowerSegment 706965760 707031296 (35346894268253 / 50000) (35350219709789 / 50000) := by
  exact
    packedTile32768 706965760 707031296 13 3264 26588 29 _ _ (127353 / 6250) (2037651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707031296 :
    ThetaLowerSegment 707031296 707096832 (35350219709789 / 50000) (2209593898451 / 3125) := by
  exact
    packedTile32768 707031296 707096832 13 3222 26590 29 _ _ (2037657 / 100000) (101883 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707096832 :
    ThetaLowerSegment 707096832 707162368 (2209593898451 / 3125) (35356794224639 / 50000) := by
  exact
    packedTile32768 707096832 707162368 13 3231 26591 29 _ _ (1018833 / 50000) (2037669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707162368 :
    ThetaLowerSegment 707162368 707227904 (35356794224639 / 50000) (35360074882999 / 50000) := by
  exact
    packedTile32768 707162368 707227904 13 3220 26592 29 _ _ (509419 / 25000) (2037679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707227904 :
    ThetaLowerSegment 707227904 707293440 (35360074882999 / 50000) (70726684621793 / 100000) := by
  exact
    packedTile32768 707227904 707293440 13 3207 26593 29 _ _ (407537 / 20000) (254711 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707293440 :
    ThetaLowerSegment 707293440 707358976 (70726684621793 / 100000) (70733215431063 / 100000) := by
  exact
    packedTile32768 707293440 707358976 13 3205 26594 29 _ _ (1018847 / 50000) (2037697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707358976 :
    ThetaLowerSegment 707358976 707424512 (70733215431063 / 100000) (1414795903481 / 2000) := by
  exact
    packedTile32768 707358976 707424512 13 3229 26596 29 _ _ (2037703 / 100000) (1018853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707424512 :
    ThetaLowerSegment 707424512 707490048 (1414795903481 / 2000) (8843291010241 / 12500) := by
  exact
    packedTile32768 707424512 707490048 13 3206 26597 29 _ _ (2037713 / 100000) (509429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707490048 :
    ThetaLowerSegment 707490048 707555584 (8843291010241 / 12500) (7075289158449 / 10000) := by
  exact
    packedTile32768 707490048 707555584 13 3221 26598 29 _ _ (1018861 / 50000) (81509 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707555584 :
    ThetaLowerSegment 707555584 707621120 (7075289158449 / 10000) (35379718388231 / 50000) := by
  exact
    packedTile32768 707555584 707621120 13 3212 26599 29 _ _ (2037731 / 100000) (1018867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707621120 :
    ThetaLowerSegment 707621120 707686656 (35379718388231 / 50000) (35383055187481 / 50000) := by
  exact
    packedTile32768 707621120 707686656 13 3275 26601 29 _ _ (101887 / 5000) (2037743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707686656 :
    ThetaLowerSegment 707686656 707752192 (35383055187481 / 50000) (17693134869053 / 25000) := by
  exact
    packedTile32768 707686656 707752192 13 3155 26602 29 _ _ (8151 / 400) (2037753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707752192 :
    ThetaLowerSegment 707752192 707817728 (17693134869053 / 25000) (70779090871397 / 100000) := by
  exact
    packedTile32768 707752192 707817728 13 3215 26603 29 _ _ (2037759 / 100000) (1018881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707817728 :
    ThetaLowerSegment 707817728 707883264 (70779090871397 / 100000) (70785678975341 / 100000) := by
  exact
    packedTile32768 707817728 707883264 13 3233 26604 29 _ _ (254721 / 12500) (2037771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707883264 :
    ThetaLowerSegment 707883264 707948800 (70785678975341 / 100000) (1415844690079 / 2000) := by
  exact
    packedTile32768 707883264 707948800 13 3217 26606 29 _ _ (2037777 / 100000) (101889 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell707948800 :
    ThetaLowerSegment 707948800 708014336 (1415844690079 / 2000) (4424922978067 / 6250) := by
  exact
    packedTile32768 707948800 708014336 13 3206 26607 29 _ _ (2037787 / 100000) (203779 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708014336 :
    ThetaLowerSegment 708014336 708079872 (4424922978067 / 6250) (3540265754381 / 5000) := by
  exact
    packedTile32768 708014336 708079872 13 3213 26608 29 _ _ (509449 / 25000) (2037799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708079872 :
    ThetaLowerSegment 708079872 708145408 (3540265754381 / 5000) (14162386368091 / 20000) := by
  exact
    packedTile32768 708079872 708145408 13 3247 26609 29 _ _ (407561 / 20000) (127363 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708145408 :
    ThetaLowerSegment 708145408 708210944 (14162386368091 / 20000) (14163709317589 / 20000) := by
  exact
    packedTile32768 708145408 708210944 13 3246 26611 29 _ _ (407563 / 20000) (1018909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708210944 :
    ThetaLowerSegment 708210944 708276480 (14163709317589 / 20000) (70825063549097 / 100000) := by
  exact
    packedTile32768 708210944 708276480 13 3198 26612 29 _ _ (63682 / 3125) (2037827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708276480 :
    ThetaLowerSegment 708276480 708342016 (70825063549097 / 100000) (35415842234257 / 50000) := by
  exact
    packedTile32768 708276480 708342016 13 3249 26613 29 _ _ (2037833 / 100000) (509459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708342016 :
    ThetaLowerSegment 708342016 708407552 (35415842234257 / 50000) (35419123159877 / 50000) := by
  exact
    packedTile32768 708342016 708407552 13 3220 26614 29 _ _ (1018921 / 50000) (407569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708407552 :
    ThetaLowerSegment 708407552 708473088 (35419123159877 / 50000) (35422441801859 / 50000) := by
  exact
    packedTile32768 708407552 708473088 13 3257 26615 29 _ _ (509463 / 25000) (407571 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708473088 :
    ThetaLowerSegment 708473088 708538624 (35422441801859 / 50000) (17712854246521 / 25000) := by
  exact
    packedTile32768 708473088 708538624 13 3206 26617 29 _ _ (2037861 / 100000) (254733 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708538624 :
    ThetaLowerSegment 708538624 708604160 (17712854246521 / 25000) (17714480466781 / 25000) := by
  exact
    packedTile32768 708538624 708604160 13 3192 26618 29 _ _ (203787 / 10000) (2037873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708604160 :
    ThetaLowerSegment 708604160 708669696 (17714480466781 / 25000) (3543224599451 / 5000) := by
  exact
    packedTile32768 708604160 708669696 13 3224 26619 29 _ _ (2037879 / 100000) (1018941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708669696 :
    ThetaLowerSegment 708669696 708735232 (3543224599451 / 5000) (7087099285493 / 10000) := by
  exact
    packedTile32768 708669696 708735232 13 3190 26620 29 _ _ (2037889 / 100000) (509473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708735232 :
    ThetaLowerSegment 708735232 708800768 (7087099285493 / 10000) (2214923017044 / 3125) := by
  exact
    packedTile32768 708735232 708800768 13 3211 26622 29 _ _ (1018949 / 50000) (2037901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708800768 :
    ThetaLowerSegment 708800768 708866304 (2214923017044 / 3125) (8860497041441 / 12500) := by
  exact
    packedTile32768 708800768 708866304 13 3160 26623 29 _ _ (2037907 / 100000) (203791 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708866304 :
    ThetaLowerSegment 708866304 708931840 (8860497041441 / 12500) (17722626963077 / 25000) := by
  exact
    packedTile32768 708866304 708931840 13 3205 26624 29 _ _ (509479 / 25000) (2037919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708931840 :
    ThetaLowerSegment 708931840 708997376 (17722626963077 / 25000) (35448569630129 / 50000) := by
  exact
    packedTile32768 708931840 708997376 13 3254 26625 29 _ _ (81517 / 4000) (254741 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell708997376 :
    ThetaLowerSegment 708997376 709062912 (35448569630129 / 50000) (35451871084829 / 50000) := by
  exact
    packedTile32768 708997376 709062912 13 3240 26627 29 _ _ (407587 / 20000) (1018969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709062912 :
    ThetaLowerSegment 709062912 709128448 (35451871084829 / 50000) (35455149117753 / 50000) := by
  exact
    packedTile32768 709062912 709128448 13 3217 26628 29 _ _ (254743 / 12500) (2037947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709128448 :
    ThetaLowerSegment 709128448 709193984 (35455149117753 / 50000) (70916838026683 / 100000) := by
  exact
    packedTile32768 709128448 709193984 13 3209 26629 29 _ _ (2037953 / 100000) (509489 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709193984 :
    ThetaLowerSegment 709193984 709259520 (70916838026683 / 100000) (567388359677 / 800) := by
  exact
    packedTile32768 709193984 709259520 13 3291 26630 29 _ _ (1018981 / 50000) (407593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709259520 :
    ThetaLowerSegment 709259520 709325056 (567388359677 / 800) (70930113343381 / 100000) := by
  exact
    packedTile32768 709259520 709325056 13 3223 26631 29 _ _ (509493 / 25000) (81519 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709325056 :
    ThetaLowerSegment 709325056 709390592 (70930113343381 / 100000) (70936671566239 / 100000) := by
  exact
    packedTile32768 709325056 709390592 13 3218 26633 29 _ _ (2037981 / 100000) (63687 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709390592 :
    ThetaLowerSegment 709390592 709456128 (70936671566239 / 100000) (70943113652629 / 100000) := by
  exact
    packedTile32768 709390592 709456128 13 3161 26634 29 _ _ (203799 / 10000) (2037993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709456128 :
    ThetaLowerSegment 709456128 709521664 (70943113652629 / 100000) (17737437853843 / 25000) := by
  exact
    packedTile32768 709456128 709521664 13 3257 26635 29 _ _ (2037999 / 100000) (1019001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709521664 :
    ThetaLowerSegment 709521664 709587200 (17737437853843 / 25000) (4434771650781 / 6250) := by
  exact
    packedTile32768 709521664 709587200 13 3236 26636 29 _ _ (2038009 / 100000) (509503 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709587200 :
    ThetaLowerSegment 709587200 709652736 (4434771650781 / 6250) (17740724150587 / 25000) := by
  exact
    packedTile32768 709587200 709652736 13 3214 26638 29 _ _ (1019009 / 50000) (2038021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709652736 :
    ThetaLowerSegment 709652736 709718272 (17740724150587 / 25000) (14193871837193 / 20000) := by
  exact
    packedTile32768 709652736 709718272 13 3171 26639 29 _ _ (2038027 / 100000) (203803 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709718272 :
    ThetaLowerSegment 709718272 709783808 (14193871837193 / 20000) (70975856444733 / 100000) := by
  exact
    packedTile32768 709718272 709783808 13 3188 26640 29 _ _ (509509 / 25000) (2038039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709783808 :
    ThetaLowerSegment 709783808 709849344 (70975856444733 / 100000) (70982339469059 / 100000) := by
  exact
    packedTile32768 709783808 709849344 13 3181 26641 29 _ _ (1019023 / 50000) (2038049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709849344 :
    ThetaLowerSegment 709849344 709914880 (70982339469059 / 100000) (70988926462819 / 100000) := by
  exact
    packedTile32768 709849344 709914880 13 3232 26642 29 _ _ (407611 / 20000) (1019029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709914880 :
    ThetaLowerSegment 709914880 709980416 (70988926462819 / 100000) (70995529790179 / 100000) := by
  exact
    packedTile32768 709914880 709980416 13 3240 26644 29 _ _ (127379 / 6250) (2038067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell709980416 :
    ThetaLowerSegment 709980416 710045952 (70995529790179 / 100000) (7100198436737 / 10000) := by
  exact
    packedTile32768 709980416 710045952 13 3167 26645 29 _ _ (2038073 / 100000) (509519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710045952 :
    ThetaLowerSegment 710045952 710111488 (7100198436737 / 10000) (71008528651883 / 100000) := by
  exact
    packedTile32768 710045952 710111488 13 3211 26646 29 _ _ (2038083 / 100000) (1019043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710111488 :
    ThetaLowerSegment 710111488 710177024 (71008528651883 / 100000) (71015028127271 / 100000) := by
  exact
    packedTile32768 710111488 710177024 13 3189 26647 29 _ _ (509523 / 25000) (407619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710177024 :
    ThetaLowerSegment 710177024 710242560 (71015028127271 / 100000) (17755396174547 / 25000) := by
  exact
    packedTile32768 710177024 710242560 13 3217 26649 29 _ _ (2038101 / 100000) (254763 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710242560 :
    ThetaLowerSegment 710242560 710308096 (17755396174547 / 25000) (35514070649029 / 50000) := by
  exact
    packedTile32768 710242560 710308096 13 3217 26650 29 _ _ (203811 / 10000) (2038113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710308096 :
    ThetaLowerSegment 710308096 710373632 (35514070649029 / 50000) (3551732960131 / 5000) := by
  exact
    packedTile32768 710308096 710373632 13 3198 26651 29 _ _ (2038119 / 100000) (1019061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710373632 :
    ThetaLowerSegment 710373632 710439168 (3551732960131 / 5000) (17760319761403 / 25000) := by
  exact
    packedTile32768 710373632 710439168 13 3248 26652 29 _ _ (2038129 / 100000) (509533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710439168 :
    ThetaLowerSegment 710439168 710504704 (17760319761403 / 25000) (17761960462493 / 25000) := by
  exact
    packedTile32768 710439168 710504704 13 3220 26654 29 _ _ (1019069 / 50000) (2038141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710504704 :
    ThetaLowerSegment 710504704 710570240 (17761960462493 / 25000) (35527126930217 / 50000) := by
  exact
    packedTile32768 710504704 710570240 13 3146 26655 29 _ _ (2038147 / 100000) (40763 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710570240 :
    ThetaLowerSegment 710570240 710635776 (35527126930217 / 50000) (35530444029107 / 50000) := by
  exact
    packedTile32768 710570240 710635776 13 3255 26656 29 _ _ (509539 / 25000) (2038159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710635776 :
    ThetaLowerSegment 710635776 710701312 (35530444029107 / 50000) (35533684713047 / 50000) := by
  exact
    packedTile32768 710635776 710701312 13 3180 26657 29 _ _ (1019083 / 50000) (2038169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710701312 :
    ThetaLowerSegment 710701312 710766848 (35533684713047 / 50000) (17768469839261 / 25000) := by
  exact
    packedTile32768 710701312 710766848 13 3194 26658 29 _ _ (81527 / 4000) (1019089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710766848 :
    ThetaLowerSegment 710766848 710832384 (17768469839261 / 25000) (17770110577381 / 25000) := by
  exact
    packedTile32768 710766848 710832384 13 3220 26660 29 _ _ (254773 / 12500) (2038187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710832384 :
    ThetaLowerSegment 710832384 710897920 (17770110577381 / 25000) (35543512836457 / 50000) := by
  exact
    packedTile32768 710832384 710897920 13 3230 26661 29 _ _ (2038193 / 100000) (509549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710897920 :
    ThetaLowerSegment 710897920 710963456 (35543512836457 / 50000) (17773387489379 / 25000) := by
  exact
    packedTile32768 710897920 710963456 13 3201 26662 29 _ _ (1019101 / 50000) (407641 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell710963456 :
    ThetaLowerSegment 710963456 711028992 (17773387489379 / 25000) (4443758718557 / 6250) := by
  exact
    packedTile32768 710963456 711028992 13 3233 26663 29 _ _ (509553 / 25000) (407643 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711028992 :
    ThetaLowerSegment 711028992 711094528 (4443758718557 / 6250) (17776691947901 / 25000) := by
  exact
    packedTile32768 711028992 711094528 13 3252 26665 29 _ _ (2038221 / 100000) (127389 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711094528 :
    ThetaLowerSegment 711094528 711160064 (17776691947901 / 25000) (8889152603473 / 12500) := by
  exact
    packedTile32768 711094528 711160064 13 3166 26666 29 _ _ (203823 / 10000) (2038233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711160064 :
    ThetaLowerSegment 711160064 711225600 (8889152603473 / 12500) (71119830836861 / 100000) := by
  exact
    packedTile32768 711160064 711225600 13 3243 26667 29 _ _ (2038239 / 100000) (1019121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711225600 :
    ThetaLowerSegment 711225600 711291136 (71119830836861 / 100000) (71126381769147 / 100000) := by
  exact
    packedTile32768 711225600 711291136 13 3214 26668 29 _ _ (2038249 / 100000) (509563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711291136 :
    ThetaLowerSegment 711291136 711356672 (71126381769147 / 100000) (71133006107647 / 100000) := by
  exact
    packedTile32768 711291136 711356672 13 3250 26670 29 _ _ (1019129 / 50000) (2038261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711356672 :
    ThetaLowerSegment 711356672 711422208 (71133006107647 / 100000) (14227903266489 / 20000) := by
  exact
    packedTile32768 711356672 711422208 13 3194 26671 29 _ _ (2038267 / 100000) (203827 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711422208 :
    ThetaLowerSegment 711422208 711487744 (14227903266489 / 20000) (14229217954509 / 20000) := by
  exact
    packedTile32768 711422208 711487744 13 3225 26672 29 _ _ (509569 / 25000) (2038279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711487744 :
    ThetaLowerSegment 711487744 711553280 (14229217954509 / 20000) (14230531425363 / 20000) := by
  exact
    packedTile32768 711487744 711553280 13 3222 26673 29 _ _ (407657 / 20000) (127393 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711553280 :
    ThetaLowerSegment 711553280 711618816 (14230531425363 / 20000) (7115919801547 / 10000) := by
  exact
    packedTile32768 711553280 711618816 13 3209 26674 29 _ _ (407659 / 20000) (1019149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711618816 :
    ThetaLowerSegment 711618816 711684352 (7115919801547 / 10000) (35582930615623 / 50000) := by
  exact
    packedTile32768 711618816 711684352 13 3269 26676 29 _ _ (63697 / 3125) (2038307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711684352 :
    ThetaLowerSegment 711684352 711749888 (35582930615623 / 50000) (711722982237 / 1000) := by
  exact
    packedTile32768 711684352 711749888 13 3158 26677 29 _ _ (2038313 / 100000) (509579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711749888 :
    ThetaLowerSegment 711749888 711815424 (711722982237 / 1000) (35589391062991 / 50000) := by
  exact
    packedTile32768 711749888 711815424 13 3181 26678 29 _ _ (1019161 / 50000) (81533 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711815424 :
    ThetaLowerSegment 711815424 711880960 (35589391062991 / 50000) (17796319062137 / 25000) := by
  exact
    packedTile32768 711815424 711880960 13 3186 26679 29 _ _ (2038331 / 100000) (1019167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711880960 :
    ThetaLowerSegment 711880960 711946496 (17796319062137 / 25000) (71191817284817 / 100000) := by
  exact
    packedTile32768 711880960 711946496 13 3209 26681 29 _ _ (2038341 / 100000) (254793 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell711946496 :
    ThetaLowerSegment 711946496 712012032 (71191817284817 / 100000) (71198486766017 / 100000) := by
  exact
    packedTile32768 711946496 712012032 13 3272 26682 29 _ _ (40767 / 2000) (2038353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712012032 :
    ThetaLowerSegment 712012032 712077568 (71198486766017 / 100000) (4450314241253 / 6250) := by
  exact
    packedTile32768 712012032 712077568 13 3209 26683 29 _ _ (2038359 / 100000) (1019181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712077568 :
    ThetaLowerSegment 712077568 712143104 (4450314241253 / 6250) (178029202733 / 250) := by
  exact
    packedTile32768 712077568 712143104 13 3264 26684 29 _ _ (63699 / 3125) (2038371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712143104 :
    ThetaLowerSegment 712143104 712208640 (178029202733 / 250) (17804577473801 / 25000) := by
  exact
    packedTile32768 712143104 712208640 13 3252 26686 29 _ _ (2038377 / 100000) (101919 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712208640 :
    ThetaLowerSegment 712208640 712274176 (17804577473801 / 25000) (71224867386183 / 100000) := by
  exact
    packedTile32768 712208640 712274176 13 3217 26687 29 _ _ (2038387 / 100000) (203839 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712274176 :
    ThetaLowerSegment 712274176 712339712 (71224867386183 / 100000) (14246284981223 / 20000) := by
  exact
    packedTile32768 712274176 712339712 13 3217 26688 29 _ _ (509599 / 25000) (2038399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712339712 :
    ThetaLowerSegment 712339712 712405248 (14246284981223 / 20000) (89047579989 / 125) := by
  exact
    packedTile32768 712339712 712405248 13 3257 26689 29 _ _ (407681 / 20000) (254801 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712405248 :
    ThetaLowerSegment 712405248 712470784 (89047579989 / 125) (35622333207073 / 50000) := by
  exact
    packedTile32768 712405248 712470784 13 3239 26690 29 _ _ (1019207 / 50000) (2038417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712470784 :
    ThetaLowerSegment 712470784 712536320 (35622333207073 / 50000) (71251162868247 / 100000) := by
  exact
    packedTile32768 712470784 712536320 13 3187 26692 29 _ _ (2038423 / 100000) (1019213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712536320 :
    ThetaLowerSegment 712536320 712601856 (71251162868247 / 100000) (4453608550917 / 6250) := by
  exact
    packedTile32768 712536320 712601856 13 3225 26693 29 _ _ (2038433 / 100000) (509609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712601856 :
    ThetaLowerSegment 712601856 712667392 (4453608550917 / 6250) (3563214418363 / 5000) := by
  exact
    packedTile32768 712601856 712667392 13 3214 26694 29 _ _ (1019221 / 50000) (407689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712667392 :
    ThetaLowerSegment 712667392 712732928 (3563214418363 / 5000) (17817690621909 / 25000) := by
  exact
    packedTile32768 712667392 712732928 13 3176 26695 29 _ _ (2038451 / 100000) (1019227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712732928 :
    ThetaLowerSegment 712732928 712798464 (17817690621909 / 25000) (4454832513341 / 6250) := by
  exact
    packedTile32768 712732928 712798464 13 3217 26697 29 _ _ (101923 / 5000) (2038463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712798464 :
    ThetaLowerSegment 712798464 712864000 (4454832513341 / 6250) (71283731198461 / 100000) := by
  exact
    packedTile32768 712798464 712864000 13 3145 26698 29 _ _ (2038469 / 100000) (254809 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712864000 :
    ThetaLowerSegment 712864000 712929536 (71283731198461 / 100000) (71290335870421 / 100000) := by
  exact
    packedTile32768 712864000 712929536 13 3240 26699 29 _ _ (2038479 / 100000) (1019241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712929536 :
    ThetaLowerSegment 712929536 712995072 (71290335870421 / 100000) (71296995610717 / 100000) := by
  exact
    packedTile32768 712929536 712995072 13 3267 26700 29 _ _ (254811 / 12500) (2038491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell712995072 :
    ThetaLowerSegment 712995072 713060608 (71296995610717 / 100000) (14260701314027 / 20000) := by
  exact
    packedTile32768 712995072 713060608 13 3194 26701 29 _ _ (2038497 / 100000) (4077 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713060608 :
    ThetaLowerSegment 713060608 713126144 (14260701314027 / 20000) (71310145984177 / 100000) := by
  exact
    packedTile32768 713060608 713126144 13 3257 26703 29 _ _ (1019253 / 50000) (2038509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713126144 :
    ThetaLowerSegment 713126144 713191680 (71310145984177 / 100000) (71316710002477 / 100000) := by
  exact
    packedTile32768 713126144 713191680 13 3220 26704 29 _ _ (407703 / 20000) (1019259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713191680 :
    ThetaLowerSegment 713191680 713257216 (71316710002477 / 100000) (35661642122801 / 50000) := by
  exact
    packedTile32768 713191680 713257216 13 3225 26705 29 _ _ (81541 / 4000) (63704 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713257216 :
    ThetaLowerSegment 713257216 713322752 (35661642122801 / 50000) (17832420800957 / 25000) := by
  exact
    packedTile32768 713257216 713322752 13 3139 26706 29 _ _ (1019267 / 50000) (2038537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713322752 :
    ThetaLowerSegment 713322752 713339136 (17832420800957 / 25000) (71331303845513 / 100000) := by
  exact
    packedTile32768 713322752 713339136 11 795 26708 29 _ _ (2038543 / 100000) (1019273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713339136 :
    ThetaLowerSegment 713339136 713341184 (71331303845513 / 100000) (35665746715099 / 50000) := by
  exact
    packedTile32768 713339136 713341184 8 93 26708 29 _ _ (407709 / 20000) (509637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_681341184_713341184 :
    ThetaLowerSegment 681341184 713341184 (68130641690641 / 100000) (35665746715099 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell681341184 cell681406720)
                    (ThetaLowerSegment.join cell681472256 cell681537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell681603328 cell681668864)
                    (ThetaLowerSegment.join cell681734400 cell681799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell681865472 cell681931008)
                    (ThetaLowerSegment.join cell681996544 cell682062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell682127616 cell682193152)
                    (ThetaLowerSegment.join cell682258688 cell682324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell682389760 cell682455296)
                    (ThetaLowerSegment.join cell682520832 cell682586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell682651904 cell682717440)
                    (ThetaLowerSegment.join cell682782976 cell682848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell682914048 cell682979584)
                    (ThetaLowerSegment.join cell683045120 cell683110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell683176192 cell683241728)
                    (ThetaLowerSegment.join cell683307264 cell683372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell683438336 cell683503872)
                    (ThetaLowerSegment.join cell683569408 cell683634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell683700480 cell683766016)
                    (ThetaLowerSegment.join cell683831552 cell683897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell683962624 cell684028160)
                    (ThetaLowerSegment.join cell684093696 cell684159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell684224768 cell684290304)
                    (ThetaLowerSegment.join cell684355840 cell684421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell684486912 cell684552448)
                    (ThetaLowerSegment.join cell684617984 cell684683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell684749056 cell684814592)
                    (ThetaLowerSegment.join cell684880128 cell684945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell685011200 cell685076736)
                    (ThetaLowerSegment.join cell685142272 cell685207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell685273344 cell685338880)
                    (ThetaLowerSegment.join cell685404416 cell685469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell685535488 cell685601024)
                    (ThetaLowerSegment.join cell685666560 cell685732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell685797632 cell685863168)
                    (ThetaLowerSegment.join cell685928704 cell685994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell686059776 cell686125312)
                    (ThetaLowerSegment.join cell686190848 cell686256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell686321920 cell686387456)
                    (ThetaLowerSegment.join cell686452992 cell686518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell686584064 cell686649600)
                    (ThetaLowerSegment.join cell686715136 cell686780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell686846208 cell686911744)
                    (ThetaLowerSegment.join cell686977280 cell687042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell687108352 cell687173888)
                    (ThetaLowerSegment.join cell687239424 cell687304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell687370496 cell687436032)
                    (ThetaLowerSegment.join cell687501568 cell687567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell687632640 cell687698176)
                    (ThetaLowerSegment.join cell687763712 cell687829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell687894784 cell687960320)
                    (ThetaLowerSegment.join cell688025856 cell688091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell688156928 cell688222464)
                    (ThetaLowerSegment.join cell688288000 cell688353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell688419072 cell688484608)
                    (ThetaLowerSegment.join cell688550144 cell688615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell688681216 cell688746752)
                    (ThetaLowerSegment.join cell688812288 cell688877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell688943360 cell689008896)
                    (ThetaLowerSegment.join cell689074432 cell689139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell689205504 cell689271040)
                    (ThetaLowerSegment.join cell689336576 cell689402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell689467648 cell689533184)
                    (ThetaLowerSegment.join cell689598720 cell689664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell689729792 cell689795328)
                    (ThetaLowerSegment.join cell689860864 cell689926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell689991936 cell690057472)
                    (ThetaLowerSegment.join cell690123008 cell690188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell690254080 cell690319616)
                    (ThetaLowerSegment.join cell690385152 cell690450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell690516224 cell690581760)
                    (ThetaLowerSegment.join cell690647296 cell690712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell690778368 cell690843904)
                    (ThetaLowerSegment.join cell690909440 cell690974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell691040512 cell691106048)
                    (ThetaLowerSegment.join cell691171584 cell691237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell691302656 cell691368192)
                    (ThetaLowerSegment.join cell691433728 cell691499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell691564800 cell691630336)
                    (ThetaLowerSegment.join cell691695872 cell691761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell691826944 cell691892480)
                    (ThetaLowerSegment.join cell691958016 cell692023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell692089088 cell692154624)
                    (ThetaLowerSegment.join cell692220160 cell692285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell692351232 cell692416768)
                    (ThetaLowerSegment.join cell692482304 cell692547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell692613376 cell692678912)
                    (ThetaLowerSegment.join cell692744448 cell692809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell692875520 cell692941056)
                    (ThetaLowerSegment.join cell693006592 cell693072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell693137664 cell693203200)
                    (ThetaLowerSegment.join cell693268736 cell693334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell693399808 cell693465344)
                    (ThetaLowerSegment.join cell693530880 cell693596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell693661952 cell693727488)
                    (ThetaLowerSegment.join cell693793024 cell693858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell693924096 cell693989632)
                    (ThetaLowerSegment.join cell694055168 cell694120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell694186240 cell694251776)
                    (ThetaLowerSegment.join cell694317312 cell694382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell694448384 cell694513920)
                    (ThetaLowerSegment.join cell694579456 cell694644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell694710528 cell694776064)
                    (ThetaLowerSegment.join cell694841600 cell694907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell694972672 cell695038208)
                    (ThetaLowerSegment.join cell695103744 cell695169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell695234816 cell695300352)
                    (ThetaLowerSegment.join cell695365888 cell695431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell695496960 cell695562496)
                    (ThetaLowerSegment.join cell695628032 cell695693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell695759104 cell695824640)
                    (ThetaLowerSegment.join cell695890176 cell695955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell696021248 cell696086784)
                    (ThetaLowerSegment.join cell696152320 cell696217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell696283392 cell696348928)
                    (ThetaLowerSegment.join cell696414464 cell696480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell696545536 cell696611072)
                    (ThetaLowerSegment.join cell696676608 cell696742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell696807680 cell696873216)
                    (ThetaLowerSegment.join cell696938752 cell697004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell697069824 cell697135360)
                    (ThetaLowerSegment.join cell697200896 cell697266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell697331968 cell697397504)
                    (ThetaLowerSegment.join cell697463040 cell697528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell697594112 cell697659648)
                    (ThetaLowerSegment.join cell697725184 cell697790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell697856256 cell697921792)
                    (ThetaLowerSegment.join cell697987328 cell698052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell698118400 cell698183936)
                    (ThetaLowerSegment.join cell698249472 cell698315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell698380544 cell698446080)
                    (ThetaLowerSegment.join cell698511616 cell698577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell698642688 cell698708224)
                    (ThetaLowerSegment.join cell698773760 cell698839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell698904832 cell698970368)
                    (ThetaLowerSegment.join cell699035904 cell699101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell699166976 cell699232512)
                    (ThetaLowerSegment.join cell699298048 cell699363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell699429120 cell699494656)
                    (ThetaLowerSegment.join cell699560192 cell699625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell699691264 cell699756800)
                    (ThetaLowerSegment.join cell699822336 cell699887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell699953408 cell700018944)
                    (ThetaLowerSegment.join cell700084480 cell700150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell700215552 cell700281088)
                    (ThetaLowerSegment.join cell700346624 cell700412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell700477696 cell700543232)
                    (ThetaLowerSegment.join cell700608768 cell700674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell700739840 cell700805376)
                    (ThetaLowerSegment.join cell700870912 cell700936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell701001984 cell701067520)
                    (ThetaLowerSegment.join cell701133056 cell701198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell701264128 cell701329664)
                    (ThetaLowerSegment.join cell701395200 cell701460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell701526272 cell701591808)
                    (ThetaLowerSegment.join cell701657344 cell701722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell701788416 cell701853952)
                    (ThetaLowerSegment.join cell701919488 cell701985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell702050560 cell702116096)
                    (ThetaLowerSegment.join cell702181632 cell702247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell702312704 cell702378240)
                    (ThetaLowerSegment.join cell702443776 cell702509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell702574848 cell702640384)
                    (ThetaLowerSegment.join cell702705920 cell702771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell702836992 cell702902528)
                    (ThetaLowerSegment.join cell702968064 cell703033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell703099136 cell703164672)
                    (ThetaLowerSegment.join cell703230208 cell703295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell703361280 cell703426816)
                    (ThetaLowerSegment.join cell703492352 cell703557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell703623424 cell703688960)
                    (ThetaLowerSegment.join cell703754496 cell703820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell703885568 cell703951104)
                    (ThetaLowerSegment.join cell704016640 cell704082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell704147712 cell704213248)
                    (ThetaLowerSegment.join cell704278784 cell704344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell704409856 cell704475392)
                    (ThetaLowerSegment.join cell704540928 cell704606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell704672000 cell704737536)
                    (ThetaLowerSegment.join cell704803072 cell704868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell704934144 cell704999680)
                    (ThetaLowerSegment.join cell705065216 cell705130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell705196288 cell705261824)
                    (ThetaLowerSegment.join cell705327360 cell705392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell705458432 cell705523968)
                    (ThetaLowerSegment.join cell705589504 cell705655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell705720576 cell705786112)
                    (ThetaLowerSegment.join cell705851648 cell705917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell705982720 cell706048256)
                    (ThetaLowerSegment.join cell706113792 cell706179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell706244864 cell706310400)
                    (ThetaLowerSegment.join cell706375936 cell706441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell706507008 cell706572544)
                    (ThetaLowerSegment.join cell706638080 cell706703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell706769152 cell706834688)
                    (ThetaLowerSegment.join cell706900224 cell706965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell707031296 cell707096832)
                    (ThetaLowerSegment.join cell707162368 cell707227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell707293440 cell707358976)
                    (ThetaLowerSegment.join cell707424512 cell707490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell707555584 cell707621120)
                    (ThetaLowerSegment.join cell707686656 cell707752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell707817728 cell707883264)
                    (ThetaLowerSegment.join cell707948800 cell708014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell708079872 cell708145408)
                    (ThetaLowerSegment.join cell708210944 cell708276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell708342016 cell708407552)
                    (ThetaLowerSegment.join cell708473088 cell708538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell708604160 cell708669696)
                    (ThetaLowerSegment.join cell708735232 cell708800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell708866304 cell708931840)
                    (ThetaLowerSegment.join cell708997376 cell709062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell709128448 cell709193984)
                    (ThetaLowerSegment.join cell709259520 cell709325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell709390592 cell709456128)
                    (ThetaLowerSegment.join cell709521664 cell709587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell709652736 cell709718272)
                    (ThetaLowerSegment.join cell709783808 cell709849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell709914880 cell709980416)
                    (ThetaLowerSegment.join cell710045952 cell710111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell710177024 cell710242560)
                    (ThetaLowerSegment.join cell710308096 cell710373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell710439168 cell710504704)
                    (ThetaLowerSegment.join cell710570240 cell710635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell710701312 cell710766848)
                    (ThetaLowerSegment.join cell710832384 cell710897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell710963456 cell711028992)
                    (ThetaLowerSegment.join cell711094528 cell711160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell711225600 cell711291136)
                    (ThetaLowerSegment.join cell711356672 cell711422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell711487744 cell711553280)
                    (ThetaLowerSegment.join cell711618816 cell711684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell711749888 cell711815424)
                    (ThetaLowerSegment.join cell711880960 cell711946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell712012032 cell712077568)
                    (ThetaLowerSegment.join cell712143104 cell712208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell712274176 cell712339712)
                    (ThetaLowerSegment.join cell712405248 cell712470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell712536320 cell712601856)
                    (ThetaLowerSegment.join cell712667392 cell712732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell712798464 cell712864000)
                  (ThetaLowerSegment.join cell712929536 cell712995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell713060608 cell713126144)
                  (ThetaLowerSegment.join cell713191680 cell713257216)))
              (ThetaLowerSegment.join cell713322752 cell713339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
