/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 745341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell713341184 :
    ThetaLowerSegment 713341184 713406720 (35665746715099 / 50000) (2229316910272 / 3125) := by
  exact
    packedTile32768 713341184 713406720 13 3261 26708 29 _ _ (1019273 / 50000) (2038549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713406720 :
    ThetaLowerSegment 713406720 713472256 (2229316910272 / 3125) (35672330213797 / 50000) := by
  exact
    packedTile32768 713406720 713472256 13 3198 26709 29 _ _ (407711 / 20000) (1019279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713472256 :
    ThetaLowerSegment 713472256 713537792 (35672330213797 / 50000) (35675630648913 / 50000) := by
  exact
    packedTile32768 713472256 713537792 13 3238 26710 29 _ _ (509641 / 25000) (2038567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713537792 :
    ThetaLowerSegment 713537792 713603328 (35675630648913 / 50000) (35678892365713 / 50000) := by
  exact
    packedTile32768 713537792 713603328 13 3200 26712 29 _ _ (2038573 / 100000) (127411 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713603328 :
    ThetaLowerSegment 713603328 713668864 (35678892365713 / 50000) (17841064307319 / 25000) := by
  exact
    packedTile32768 713603328 713668864 13 3175 26713 29 _ _ (1019291 / 50000) (407717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713668864 :
    ThetaLowerSegment 713668864 713734400 (17841064307319 / 25000) (14274167967923 / 20000) := by
  exact
    packedTile32768 713668864 713734400 13 3229 26714 29 _ _ (2038591 / 100000) (1019297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713734400 :
    ThetaLowerSegment 713734400 713799936 (14274167967923 / 20000) (17844355620561 / 25000) := by
  exact
    packedTile32768 713734400 713799936 13 3229 26715 29 _ _ (2038601 / 100000) (509651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713799936 :
    ThetaLowerSegment 713799936 713865472 (17844355620561 / 25000) (2230746147547 / 3125) := by
  exact
    packedTile32768 713799936 713865472 13 3166 26717 29 _ _ (203861 / 10000) (2038613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713865472 :
    ThetaLowerSegment 713865472 713931008 (2230746147547 / 3125) (4461902057513 / 6250) := by
  exact
    packedTile32768 713865472 713931008 13 3216 26718 29 _ _ (2038619 / 100000) (1019311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713931008 :
    ThetaLowerSegment 713931008 713996544 (4461902057513 / 6250) (3569843647303 / 5000) := by
  exact
    packedTile32768 713931008 713996544 13 3159 26719 29 _ _ (509657 / 25000) (2038631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell713996544 :
    ThetaLowerSegment 713996544 714062080 (3569843647303 / 5000) (71403594332249 / 100000) := by
  exact
    packedTile32768 713996544 714062080 13 3297 26720 29 _ _ (2038637 / 100000) (25483 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714062080 :
    ThetaLowerSegment 714062080 714127616 (71403594332249 / 100000) (4463132502581 / 6250) := by
  exact
    packedTile32768 714062080 714127616 13 3201 26721 29 _ _ (2038647 / 100000) (40773 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714127616 :
    ThetaLowerSegment 714127616 714193152 (4463132502581 / 6250) (892708403521 / 1250) := by
  exact
    packedTile32768 714127616 714193152 13 3214 26723 29 _ _ (63708 / 3125) (2038659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714193152 :
    ThetaLowerSegment 714193152 714258688 (892708403521 / 1250) (3571165916479 / 5000) := by
  exact
    packedTile32768 714193152 714258688 13 3260 26724 29 _ _ (407733 / 20000) (509667 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714258688 :
    ThetaLowerSegment 714258688 714324224 (3571165916479 / 5000) (8928723635107 / 12500) := by
  exact
    packedTile32768 714258688 714324224 13 3174 26725 29 _ _ (1019337 / 50000) (2038677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714324224 :
    ThetaLowerSegment 714324224 714389760 (8928723635107 / 12500) (35718170704009 / 50000) := by
  exact
    packedTile32768 714324224 714389760 13 3214 26726 29 _ _ (2038683 / 100000) (1019343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714389760 :
    ThetaLowerSegment 714389760 714455296 (35718170704009 / 50000) (35721445862707 / 50000) := by
  exact
    packedTile32768 714389760 714455296 13 3213 26728 29 _ _ (509673 / 25000) (407739 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714455296 :
    ThetaLowerSegment 714455296 714520832 (35721445862707 / 50000) (4465590894197 / 6250) := by
  exact
    packedTile32768 714455296 714520832 13 3219 26729 29 _ _ (1019351 / 50000) (407741 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714520832 :
    ThetaLowerSegment 714520832 714586368 (4465590894197 / 6250) (71455845666137 / 100000) := by
  exact
    packedTile32768 714520832 714586368 13 3135 26730 29 _ _ (2038711 / 100000) (1019357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714586368 :
    ThetaLowerSegment 714586368 714651904 (71455845666137 / 100000) (71462377725017 / 100000) := by
  exact
    packedTile32768 714586368 714651904 13 3204 26731 29 _ _ (12742 / 625) (2038723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714651904 :
    ThetaLowerSegment 714651904 714717440 (71462377725017 / 100000) (35734423306067 / 50000) := by
  exact
    packedTile32768 714651904 714717440 13 3173 26732 29 _ _ (2038729 / 100000) (509683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714717440 :
    ThetaLowerSegment 714717440 714782976 (35734423306067 / 50000) (3573767203507 / 5000) := by
  exact
    packedTile32768 714717440 714782976 13 3187 26734 29 _ _ (1019369 / 50000) (2038741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714782976 :
    ThetaLowerSegment 714782976 714848512 (3573767203507 / 5000) (35740980921451 / 50000) := by
  exact
    packedTile32768 714782976 714848512 13 3246 26735 29 _ _ (2038747 / 100000) (1631 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714848512 :
    ThetaLowerSegment 714848512 714914048 (35740980921451 / 50000) (14297708997851 / 20000) := by
  exact
    packedTile32768 714848512 714914048 13 3229 26736 29 _ _ (2038757 / 100000) (50969 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714914048 :
    ThetaLowerSegment 714914048 714979584 (14297708997851 / 20000) (14299013808091 / 20000) := by
  exact
    packedTile32768 714914048 714979584 13 3200 26737 29 _ _ (1019383 / 50000) (2038769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell714979584 :
    ThetaLowerSegment 714979584 715045120 (14299013808091 / 20000) (14300321070621 / 20000) := by
  exact
    packedTile32768 714979584 715045120 13 3206 26739 29 _ _ (81551 / 4000) (1019389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715045120 :
    ThetaLowerSegment 715045120 715110656 (14300321070621 / 20000) (71508051988113 / 100000) := by
  exact
    packedTile32768 715045120 715110656 13 3162 26740 29 _ _ (63712 / 3125) (2038787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715110656 :
    ThetaLowerSegment 715110656 715176192 (71508051988113 / 100000) (8939325838451 / 12500) := by
  exact
    packedTile32768 715110656 715176192 13 3215 26741 29 _ _ (2038793 / 100000) (509699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715176192 :
    ThetaLowerSegment 715176192 715241728 (8939325838451 / 12500) (17880277621497 / 25000) := by
  exact
    packedTile32768 715176192 715241728 13 3190 26742 29 _ _ (1019401 / 50000) (407761 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715241728 :
    ThetaLowerSegment 715241728 715307264 (17880277621497 / 25000) (143055375387 / 200) := by
  exact
    packedTile32768 715241728 715307264 13 3226 26744 29 _ _ (509703 / 25000) (407763 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715307264 :
    ThetaLowerSegment 715307264 715372800 (143055375387 / 200) (17883528514323 / 25000) := by
  exact
    packedTile32768 715307264 715372800 13 3152 26745 29 _ _ (2038821 / 100000) (254853 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715372800 :
    ThetaLowerSegment 715372800 715438336 (17883528514323 / 25000) (35770358913831 / 50000) := by
  exact
    packedTile32768 715372800 715438336 13 3239 26746 29 _ _ (203883 / 10000) (2038833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715438336 :
    ThetaLowerSegment 715438336 715503872 (35770358913831 / 50000) (1430948593713 / 2000) := by
  exact
    packedTile32768 715438336 715503872 13 3292 26747 29 _ _ (2038839 / 100000) (1019421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715503872 :
    ThetaLowerSegment 715503872 715569408 (1430948593713 / 2000) (286215815997 / 400) := by
  exact
    packedTile32768 715503872 715569408 13 3200 26748 29 _ _ (63714 / 3125) (2038851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715569408 :
    ThetaLowerSegment 715569408 715634944 (286215815997 / 400) (2862417094809 / 4000) := by
  exact
    packedTile32768 715569408 715634944 13 3175 26750 29 _ _ (2038857 / 100000) (101943 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715634944 :
    ThetaLowerSegment 715634944 715700480 (2862417094809 / 4000) (35783474852879 / 50000) := by
  exact
    packedTile32768 715634944 715700480 13 3199 26751 29 _ _ (2038867 / 100000) (203887 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715700480 :
    ThetaLowerSegment 715700480 715766016 (35783474852879 / 50000) (35786747248859 / 50000) := by
  exact
    packedTile32768 715700480 715766016 13 3210 26752 29 _ _ (509719 / 25000) (2038879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715766016 :
    ThetaLowerSegment 715766016 715831552 (35786747248859 / 50000) (71580094368463 / 100000) := by
  exact
    packedTile32768 715766016 715831552 13 3237 26753 29 _ _ (407777 / 20000) (254861 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715831552 :
    ThetaLowerSegment 715831552 715897088 (71580094368463 / 100000) (71586559701337 / 100000) := by
  exact
    packedTile32768 715831552 715897088 13 3171 26755 29 _ _ (1019447 / 50000) (2038897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715897088 :
    ThetaLowerSegment 715897088 715962624 (71586559701337 / 100000) (35796557387241 / 50000) := by
  exact
    packedTile32768 715897088 715962624 13 3215 26756 29 _ _ (2038903 / 100000) (1019453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell715962624 :
    ThetaLowerSegment 715962624 716028160 (35796557387241 / 50000) (35799830860457 / 50000) := by
  exact
    packedTile32768 715962624 716028160 13 3211 26757 29 _ _ (63716 / 3125) (407783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716028160 :
    ThetaLowerSegment 716028160 716093696 (35799830860457 / 50000) (4475384985333 / 6250) := by
  exact
    packedTile32768 716028160 716093696 13 3187 26758 29 _ _ (1019461 / 50000) (81557 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716093696 :
    ThetaLowerSegment 716093696 716159232 (4475384985333 / 6250) (71612649682701 / 100000) := by
  exact
    packedTile32768 716093696 716159232 13 3183 26759 29 _ _ (2038931 / 100000) (1019467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716159232 :
    ThetaLowerSegment 716159232 716224768 (71612649682701 / 100000) (71619225264201 / 100000) := by
  exact
    packedTile32768 716159232 716224768 13 3225 26761 29 _ _ (101947 / 5000) (2038943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716224768 :
    ThetaLowerSegment 716224768 716290304 (71619225264201 / 100000) (17906445121309 / 25000) := by
  exact
    packedTile32768 716224768 716290304 13 3215 26762 29 _ _ (2038949 / 100000) (254869 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716290304 :
    ThetaLowerSegment 716290304 716355840 (17906445121309 / 25000) (3581618112083 / 5000) := by
  exact
    packedTile32768 716290304 716355840 13 3228 26763 29 _ _ (1019479 / 50000) (2038961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716355840 :
    ThetaLowerSegment 716355840 716421376 (3581618112083 / 5000) (71638950144037 / 100000) := by
  exact
    packedTile32768 716355840 716421376 13 3231 26764 29 _ _ (2038967 / 100000) (203897 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716421376 :
    ThetaLowerSegment 716421376 716486912 (71638950144037 / 100000) (71645425931813 / 100000) := by
  exact
    packedTile32768 716421376 716486912 13 3176 26766 29 _ _ (63718 / 3125) (2038979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716486912 :
    ThetaLowerSegment 716486912 716552448 (71645425931813 / 100000) (71652058753271 / 100000) := by
  exact
    packedTile32768 716486912 716552448 13 3253 26767 29 _ _ (1019493 / 50000) (2038989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716552448 :
    ThetaLowerSegment 716552448 716617984 (71652058753271 / 100000) (71658550913351 / 100000) := by
  exact
    packedTile32768 716552448 716617984 13 3184 26768 29 _ _ (407799 / 20000) (1019499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716617984 :
    ThetaLowerSegment 716617984 716683520 (71658550913351 / 100000) (71665000283003 / 100000) := by
  exact
    packedTile32768 716617984 716683520 13 3163 26769 29 _ _ (509751 / 25000) (2039007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716683520 :
    ThetaLowerSegment 716683520 716749056 (71665000283003 / 100000) (17917900142021 / 25000) := by
  exact
    packedTile32768 716683520 716749056 13 3237 26770 29 _ _ (2039013 / 100000) (254877 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716749056 :
    ThetaLowerSegment 716749056 716814592 (17917900142021 / 25000) (35839088207017 / 50000) := by
  exact
    packedTile32768 716749056 716814592 13 3225 26772 29 _ _ (1019511 / 50000) (81561 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716814592 :
    ThetaLowerSegment 716814592 716880128 (35839088207017 / 50000) (17921206933289 / 25000) := by
  exact
    packedTile32768 716814592 716880128 13 3262 26773 29 _ _ (2039031 / 100000) (1019517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716880128 :
    ThetaLowerSegment 716880128 716945664 (17921206933289 / 25000) (17922834087209 / 25000) := by
  exact
    packedTile32768 716880128 716945664 13 3192 26774 29 _ _ (12744 / 625) (2039043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell716945664 :
    ThetaLowerSegment 716945664 717011200 (17922834087209 / 25000) (17924487756759 / 25000) := by
  exact
    packedTile32768 716945664 717011200 13 3244 26775 29 _ _ (40781 / 2000) (2039053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717011200 :
    ThetaLowerSegment 717011200 717076736 (17924487756759 / 25000) (71704510679839 / 100000) := by
  exact
    packedTile32768 717011200 717076736 13 3217 26777 29 _ _ (2039059 / 100000) (1019531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717076736 :
    ThetaLowerSegment 717076736 717142272 (71704510679839 / 100000) (71711052009983 / 100000) := by
  exact
    packedTile32768 717076736 717142272 13 3208 26778 29 _ _ (509767 / 25000) (2039071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717142272 :
    ThetaLowerSegment 717142272 717207808 (71711052009983 / 100000) (35858803821269 / 50000) := by
  exact
    packedTile32768 717142272 717207808 13 3215 26779 29 _ _ (2039077 / 100000) (50977 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717207808 :
    ThetaLowerSegment 717207808 717273344 (35858803821269 / 50000) (8965516844603 / 12500) := by
  exact
    packedTile32768 717207808 717273344 13 3201 26780 29 _ _ (1019543 / 50000) (2039089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717273344 :
    ThetaLowerSegment 717273344 717338880 (8965516844603 / 12500) (71730735307339 / 100000) := by
  exact
    packedTile32768 717273344 717338880 13 3237 26781 29 _ _ (407819 / 20000) (1019549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717338880 :
    ThetaLowerSegment 717338880 717404416 (71730735307339 / 100000) (71737280831179 / 100000) := by
  exact
    packedTile32768 717338880 717404416 13 3210 26783 29 _ _ (63722 / 3125) (2039107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717404416 :
    ThetaLowerSegment 717404416 717469952 (71737280831179 / 100000) (14348768947829 / 20000) := by
  exact
    packedTile32768 717404416 717469952 13 3219 26784 29 _ _ (1019557 / 50000) (2039117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717469952 :
    ThetaLowerSegment 717469952 717535488 (14348768947829 / 20000) (35875192103303 / 50000) := by
  exact
    packedTile32768 717469952 717535488 13 3207 26785 29 _ _ (2039123 / 100000) (1019563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717535488 :
    ThetaLowerSegment 717535488 717601024 (35875192103303 / 50000) (35878458792767 / 50000) := by
  exact
    packedTile32768 717535488 717601024 13 3204 26786 29 _ _ (509783 / 25000) (407827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717601024 :
    ThetaLowerSegment 717601024 717666560 (35878458792767 / 50000) (71763318449133 / 100000) := by
  exact
    packedTile32768 717601024 717666560 13 3139 26788 29 _ _ (2039141 / 100000) (254893 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717666560 :
    ThetaLowerSegment 717666560 717732096 (71763318449133 / 100000) (71770023174333 / 100000) := by
  exact
    packedTile32768 717666560 717732096 13 3288 26789 29 _ _ (40783 / 2000) (2039153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717732096 :
    ThetaLowerSegment 717732096 717797632 (71770023174333 / 100000) (71776683067627 / 100000) := by
  exact
    packedTile32768 717732096 717797632 13 3266 26790 29 _ _ (2039159 / 100000) (1019581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717797632 :
    ThetaLowerSegment 717797632 717863168 (71776683067627 / 100000) (71783173739371 / 100000) := by
  exact
    packedTile32768 717797632 717863168 13 3183 26791 29 _ _ (63724 / 3125) (2039171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717863168 :
    ThetaLowerSegment 717863168 717928704 (71783173739371 / 100000) (89737320153 / 125) := by
  exact
    packedTile32768 717863168 717928704 13 3277 26792 29 _ _ (2039177 / 100000) (101959 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717928704 :
    ThetaLowerSegment 717928704 717994240 (89737320153 / 125) (71796403951857 / 100000) := by
  exact
    packedTile32768 717928704 717994240 13 3211 26794 29 _ _ (2039187 / 100000) (203919 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell717994240 :
    ThetaLowerSegment 717994240 718059776 (71796403951857 / 100000) (14360587099329 / 20000) := by
  exact
    packedTile32768 717994240 718059776 13 3203 26795 29 _ _ (509799 / 25000) (2039199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718059776 :
    ThetaLowerSegment 718059776 718125312 (14360587099329 / 20000) (114895320237 / 160) := by
  exact
    packedTile32768 718059776 718125312 13 3256 26796 29 _ _ (407841 / 20000) (254901 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718125312 :
    ThetaLowerSegment 718125312 718190848 (114895320237 / 160) (71816033338863 / 100000) := by
  exact
    packedTile32768 718125312 718190848 13 3167 26797 29 _ _ (1019607 / 50000) (2039217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718190848 :
    ThetaLowerSegment 718190848 718256384 (71816033338863 / 100000) (71822575166247 / 100000) := by
  exact
    packedTile32768 718190848 718256384 13 3208 26799 29 _ _ (2039223 / 100000) (1019613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718256384 :
    ThetaLowerSegment 718256384 718321920 (71822575166247 / 100000) (2873164354623 / 4000) := by
  exact
    packedTile32768 718256384 718321920 13 3204 26800 29 _ _ (63726 / 3125) (407847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718321920 :
    ThetaLowerSegment 718321920 718387456 (2873164354623 / 4000) (71835671143113 / 100000) := by
  exact
    packedTile32768 718321920 718387456 13 3218 26801 29 _ _ (2039241 / 100000) (509811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718387456 :
    ThetaLowerSegment 718387456 718452992 (71835671143113 / 100000) (71842221214113 / 100000) := by
  exact
    packedTile32768 718387456 718452992 13 3212 26802 29 _ _ (8157 / 400) (2039253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718452992 :
    ThetaLowerSegment 718452992 718518528 (71842221214113 / 100000) (71848695864613 / 100000) := by
  exact
    packedTile32768 718452992 718518528 13 3175 26803 29 _ _ (101963 / 5000) (2039263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718518528 :
    ThetaLowerSegment 718518528 718584064 (71848695864613 / 100000) (35927607703803 / 50000) := by
  exact
    packedTile32768 718518528 718584064 13 3197 26805 29 _ _ (2039269 / 100000) (254909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718584064 :
    ThetaLowerSegment 718584064 718649600 (35927607703803 / 50000) (35930925609109 / 50000) := by
  exact
    packedTile32768 718584064 718649600 13 3254 26806 29 _ _ (1019639 / 50000) (2039281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718649600 :
    ThetaLowerSegment 718649600 718715136 (35930925609109 / 50000) (71868436075941 / 100000) := by
  exact
    packedTile32768 718649600 718715136 13 3229 26807 29 _ _ (2039287 / 100000) (203929 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718715136 :
    ThetaLowerSegment 718715136 718780672 (71868436075941 / 100000) (71875014844837 / 100000) := by
  exact
    packedTile32768 718715136 718780672 13 3226 26808 29 _ _ (63728 / 3125) (2039299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718780672 :
    ThetaLowerSegment 718780672 718846208 (71875014844837 / 100000) (71881344847557 / 100000) := by
  exact
    packedTile32768 718780672 718846208 13 3104 26810 29 _ _ (407861 / 20000) (509827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718846208 :
    ThetaLowerSegment 718846208 718911744 (71881344847557 / 100000) (71887939989033 / 100000) := by
  exact
    packedTile32768 718846208 718911744 13 3234 26811 29 _ _ (1019657 / 50000) (2039317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718911744 :
    ThetaLowerSegment 718911744 718977280 (71887939989033 / 100000) (17973616965489 / 25000) := by
  exact
    packedTile32768 718911744 718977280 13 3201 26812 29 _ _ (2039323 / 100000) (1019663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell718977280 :
    ThetaLowerSegment 718977280 719042816 (17973616965489 / 25000) (71901105890871 / 100000) := by
  exact
    packedTile32768 718977280 719042816 13 3255 26813 29 _ _ (2039333 / 100000) (254917 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719042816 :
    ThetaLowerSegment 719042816 719108352 (71901105890871 / 100000) (71907692965531 / 100000) := by
  exact
    packedTile32768 719042816 719108352 13 3230 26814 29 _ _ (1019671 / 50000) (407869 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719108352 :
    ThetaLowerSegment 719108352 719173888 (71907692965531 / 100000) (71914300462771 / 100000) := by
  exact
    packedTile32768 719108352 719173888 13 3240 26816 29 _ _ (2039351 / 100000) (1019677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719173888 :
    ThetaLowerSegment 719173888 719239424 (71914300462771 / 100000) (71920854965811 / 100000) := by
  exact
    packedTile32768 719173888 719239424 13 3214 26817 29 _ _ (12746 / 625) (2039363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719239424 :
    ThetaLowerSegment 719239424 719304960 (71920854965811 / 100000) (71927401340301 / 100000) := by
  exact
    packedTile32768 719239424 719304960 13 3210 26818 29 _ _ (2039369 / 100000) (509843 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719304960 :
    ThetaLowerSegment 719304960 719370496 (71927401340301 / 100000) (71934088460763 / 100000) := by
  exact
    packedTile32768 719304960 719370496 13 3279 26819 29 _ _ (1019689 / 50000) (2039381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719370496 :
    ThetaLowerSegment 719370496 719436032 (71934088460763 / 100000) (2248142099981 / 3125) := by
  exact
    packedTile32768 719370496 719436032 13 3167 26821 29 _ _ (2039387 / 100000) (203939 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719436032 :
    ThetaLowerSegment 719436032 719501568 (2248142099981 / 3125) (2248348588826 / 3125) := by
  exact
    packedTile32768 719436032 719501568 13 3240 26822 29 _ _ (509849 / 25000) (2039399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719501568 :
    ThetaLowerSegment 719501568 719567104 (2248348588826 / 3125) (71953756396417 / 100000) := by
  exact
    packedTile32768 719501568 719567104 13 3237 26823 29 _ _ (407881 / 20000) (127463 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719567104 :
    ThetaLowerSegment 719567104 719632640 (71953756396417 / 100000) (35980095375371 / 50000) := by
  exact
    packedTile32768 719567104 719632640 13 3155 26824 29 _ _ (407883 / 20000) (1019709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719632640 :
    ThetaLowerSegment 719632640 719698176 (35980095375371 / 50000) (35983374769163 / 50000) := by
  exact
    packedTile32768 719632640 719698176 13 3216 26825 29 _ _ (63732 / 3125) (2039427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719698176 :
    ThetaLowerSegment 719698176 719763712 (35983374769163 / 50000) (35986650098561 / 50000) := by
  exact
    packedTile32768 719698176 719763712 13 3212 26827 29 _ _ (2039433 / 100000) (509859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719763712 :
    ThetaLowerSegment 719763712 719829248 (35986650098561 / 50000) (35989970310137 / 50000) := by
  exact
    packedTile32768 719763712 719829248 13 3256 26828 29 _ _ (1019721 / 50000) (407889 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719829248 :
    ThetaLowerSegment 719829248 719894784 (35989970310137 / 50000) (17996615696143 / 25000) := by
  exact
    packedTile32768 719829248 719894784 13 3198 26829 29 _ _ (2039451 / 100000) (1019727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719894784 :
    ThetaLowerSegment 719894784 719960320 (17996615696143 / 25000) (17998216672243 / 25000) := by
  exact
    packedTile32768 719894784 719960320 13 3140 26830 29 _ _ (101973 / 5000) (2039463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell719960320 :
    ThetaLowerSegment 719960320 720025856 (17998216672243 / 25000) (8999914946111 / 12500) := by
  exact
    packedTile32768 719960320 720025856 13 3164 26832 29 _ _ (2039469 / 100000) (127467 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720025856 :
    ThetaLowerSegment 720025856 720091392 (8999914946111 / 12500) (36002905613681 / 50000) := by
  exact
    packedTile32768 720025856 720091392 13 3183 26833 29 _ _ (1019739 / 50000) (2039481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720091392 :
    ThetaLowerSegment 720091392 720156928 (36002905613681 / 50000) (14402495662073 / 20000) := by
  exact
    packedTile32768 720091392 720156928 13 3269 26834 29 _ _ (2039487 / 100000) (203949 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720156928 :
    ThetaLowerSegment 720156928 720222464 (14402495662073 / 20000) (72018978184117 / 100000) := by
  exact
    packedTile32768 720156928 720222464 13 3187 26835 29 _ _ (254937 / 12500) (2039499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720222464 :
    ThetaLowerSegment 720222464 720288000 (72018978184117 / 100000) (72025514800847 / 100000) := by
  exact
    packedTile32768 720222464 720288000 13 3205 26836 29 _ _ (1019753 / 50000) (2039509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720288000 :
    ThetaLowerSegment 720288000 720353536 (72025514800847 / 100000) (72032077960117 / 100000) := by
  exact
    packedTile32768 720288000 720353536 13 3218 26838 29 _ _ (407903 / 20000) (1019759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720353536 :
    ThetaLowerSegment 720353536 720419072 (72032077960117 / 100000) (72038643187873 / 100000) := by
  exact
    packedTile32768 720353536 720419072 13 3219 26839 29 _ _ (509881 / 25000) (2039527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720419072 :
    ThetaLowerSegment 720419072 720484608 (72038643187873 / 100000) (72045373646773 / 100000) := by
  exact
    packedTile32768 720419072 720484608 13 3300 26840 29 _ _ (2039533 / 100000) (127471 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720484608 :
    ThetaLowerSegment 720484608 720550144 (72045373646773 / 100000) (72052051107281 / 100000) := by
  exact
    packedTile32768 720484608 720550144 13 3274 26841 29 _ _ (1019771 / 50000) (407909 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720550144 :
    ThetaLowerSegment 720550144 720615680 (72052051107281 / 100000) (72058663331623 / 100000) := by
  exact
    packedTile32768 720550144 720615680 13 3242 26843 29 _ _ (2039551 / 100000) (1019777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720615680 :
    ThetaLowerSegment 720615680 720681216 (72058663331623 / 100000) (72065253149983 / 100000) := by
  exact
    packedTile32768 720615680 720681216 13 3231 26844 29 _ _ (50989 / 2500) (2039563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720681216 :
    ThetaLowerSegment 720681216 720746752 (72065253149983 / 100000) (36035884786469 / 50000) := by
  exact
    packedTile32768 720681216 720746752 13 3195 26845 29 _ _ (2039569 / 100000) (509893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720746752 :
    ThetaLowerSegment 720746752 720812288 (36035884786469 / 50000) (3603911649781 / 5000) := by
  exact
    packedTile32768 720746752 720812288 13 3169 26846 29 _ _ (1019789 / 50000) (2039581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720812288 :
    ThetaLowerSegment 720812288 720877824 (3603911649781 / 5000) (36042434905859 / 50000) := by
  exact
    packedTile32768 720812288 720877824 13 3254 26847 29 _ _ (2039587 / 100000) (203959 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720877824 :
    ThetaLowerSegment 720877824 720943360 (36042434905859 / 50000) (36045698261059 / 50000) := by
  exact
    packedTile32768 720877824 720943360 13 3200 26849 29 _ _ (2039597 / 100000) (5099 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell720943360 :
    ThetaLowerSegment 720943360 721008896 (36045698261059 / 50000) (36048971828689 / 50000) := by
  exact
    packedTile32768 720943360 721008896 13 3210 26850 29 _ _ (1019803 / 50000) (2039609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721008896 :
    ThetaLowerSegment 721008896 721074432 (36048971828689 / 50000) (36052243371149 / 50000) := by
  exact
    packedTile32768 721008896 721074432 13 3208 26851 29 _ _ (407923 / 20000) (1019809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721074432 :
    ThetaLowerSegment 721074432 721139968 (36052243371149 / 50000) (36055506769549 / 50000) := by
  exact
    packedTile32768 721074432 721139968 13 3200 26852 29 _ _ (254953 / 12500) (2039627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721139968 :
    ThetaLowerSegment 721139968 721205504 (36055506769549 / 50000) (72117607672587 / 100000) := by
  exact
    packedTile32768 721139968 721205504 13 3233 26854 29 _ _ (2039633 / 100000) (509909 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721205504 :
    ThetaLowerSegment 721205504 721271040 (72117607672587 / 100000) (14424820378543 / 20000) := by
  exact
    packedTile32768 721205504 721271040 13 3184 26855 29 _ _ (1019821 / 50000) (407929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721271040 :
    ThetaLowerSegment 721271040 721336576 (14424820378543 / 20000) (72130661410331 / 100000) := by
  exact
    packedTile32768 721271040 721336576 13 3216 26856 29 _ _ (2039651 / 100000) (1019827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721336576 :
    ThetaLowerSegment 721336576 721402112 (72130661410331 / 100000) (72137076141031 / 100000) := by
  exact
    packedTile32768 721336576 721402112 13 3145 26857 29 _ _ (101983 / 5000) (2039663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721402112 :
    ThetaLowerSegment 721402112 721467648 (72137076141031 / 100000) (7214366631157 / 10000) := by
  exact
    packedTile32768 721402112 721467648 13 3231 26858 29 _ _ (2039669 / 100000) (254959 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721467648 :
    ThetaLowerSegment 721467648 721533184 (7214366631157 / 10000) (18037574326187 / 25000) := by
  exact
    packedTile32768 721467648 721533184 13 3251 26860 29 _ _ (1019839 / 50000) (2039681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721533184 :
    ThetaLowerSegment 721533184 721598720 (18037574326187 / 25000) (36078393794391 / 50000) := by
  exact
    packedTile32768 721533184 721598720 13 3182 26861 29 _ _ (2039687 / 100000) (203969 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721598720 :
    ThetaLowerSegment 721598720 721664256 (36078393794391 / 50000) (36081743995071 / 50000) := by
  exact
    packedTile32768 721598720 721664256 13 3285 26862 29 _ _ (127481 / 6250) (2039699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721664256 :
    ThetaLowerSegment 721664256 721729792 (36081743995071 / 50000) (18042507331821 / 25000) := by
  exact
    packedTile32768 721664256 721729792 13 3207 26863 29 _ _ (1019853 / 50000) (2039709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721729792 :
    ThetaLowerSegment 721729792 721795328 (18042507331821 / 25000) (18044143183251 / 25000) := by
  exact
    packedTile32768 721729792 721795328 13 3208 26865 29 _ _ (407943 / 20000) (1019859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721795328 :
    ThetaLowerSegment 721795328 721860864 (18044143183251 / 25000) (18045769863141 / 25000) := by
  exact
    packedTile32768 721795328 721860864 13 3190 26866 29 _ _ (509931 / 25000) (2039727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721860864 :
    ThetaLowerSegment 721860864 721926400 (18045769863141 / 25000) (18047409808473 / 25000) := by
  exact
    packedTile32768 721860864 721926400 13 3216 26867 29 _ _ (2039733 / 100000) (254967 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721926400 :
    ThetaLowerSegment 721926400 721991936 (18047409808473 / 25000) (36098090343243 / 50000) := by
  exact
    packedTile32768 721926400 721991936 13 3207 26868 29 _ _ (1019871 / 50000) (407949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell721991936 :
    ThetaLowerSegment 721991936 722057472 (36098090343243 / 50000) (18050706548811 / 25000) := by
  exact
    packedTile32768 721991936 722057472 13 3258 26869 29 _ _ (2039751 / 100000) (1019877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722057472 :
    ThetaLowerSegment 722057472 722123008 (18050706548811 / 25000) (18052333257411 / 25000) := by
  exact
    packedTile32768 722057472 722123008 13 3190 26871 29 _ _ (25497 / 1250) (2039763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722123008 :
    ThetaLowerSegment 722123008 722188544 (18052333257411 / 25000) (7221592964259 / 10000) := by
  exact
    packedTile32768 722123008 722188544 13 3234 26872 29 _ _ (2039769 / 100000) (509943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722188544 :
    ThetaLowerSegment 722188544 722254080 (7221592964259 / 10000) (4513904705637 / 6250) := by
  exact
    packedTile32768 722188544 722254080 13 3209 26873 29 _ _ (1019889 / 50000) (2039781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722254080 :
    ThetaLowerSegment 722254080 722319616 (4513904705637 / 6250) (72229037284971 / 100000) := by
  exact
    packedTile32768 722254080 722319616 13 3217 26874 29 _ _ (2039787 / 100000) (203979 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722319616 :
    ThetaLowerSegment 722319616 722385152 (72229037284971 / 100000) (72235601348499 / 100000) := by
  exact
    packedTile32768 722319616 722385152 13 3218 26876 29 _ _ (509949 / 25000) (2039799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722385152 :
    ThetaLowerSegment 722385152 722450688 (72235601348499 / 100000) (72242128724499 / 100000) := by
  exact
    packedTile32768 722385152 722450688 13 3200 26877 29 _ _ (407961 / 20000) (63744 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722450688 :
    ThetaLowerSegment 722450688 722516224 (72242128724499 / 100000) (72248709164463 / 100000) := by
  exact
    packedTile32768 722450688 722516224 13 3226 26878 29 _ _ (1019907 / 50000) (2039817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722516224 :
    ThetaLowerSegment 722516224 722581760 (72248709164463 / 100000) (72255279437567 / 100000) := by
  exact
    packedTile32768 722516224 722581760 13 3221 26879 29 _ _ (127489 / 6250) (2039827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722581760 :
    ThetaLowerSegment 722581760 722647296 (72255279437567 / 100000) (36131024821647 / 50000) := by
  exact
    packedTile32768 722581760 722647296 13 3319 26880 29 _ _ (2039833 / 100000) (509959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722647296 :
    ThetaLowerSegment 722647296 722712832 (36131024821647 / 50000) (2258396159061 / 3125) := by
  exact
    packedTile32768 722647296 722712832 13 3249 26882 29 _ _ (1019921 / 50000) (407969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722712832 :
    ThetaLowerSegment 722712832 722778368 (2258396159061 / 3125) (14455001349521 / 20000) := by
  exact
    packedTile32768 722712832 722778368 13 3103 26883 29 _ _ (2039851 / 100000) (1019927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722778368 :
    ThetaLowerSegment 722778368 722843904 (14455001349521 / 20000) (2891267246781 / 4000) := by
  exact
    packedTile32768 722778368 722843904 13 3272 26884 29 _ _ (101993 / 5000) (2039863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722843904 :
    ThetaLowerSegment 722843904 722909440 (2891267246781 / 4000) (4518007819731 / 6250) := by
  exact
    packedTile32768 722843904 722909440 13 3159 26885 29 _ _ (2039869 / 100000) (63746 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722909440 :
    ThetaLowerSegment 722909440 722974976 (4518007819731 / 6250) (36147313103441 / 50000) := by
  exact
    packedTile32768 722909440 722974976 13 3187 26886 29 _ _ (1019939 / 50000) (2039881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell722974976 :
    ThetaLowerSegment 722974976 723040512 (36147313103441 / 50000) (72301204842457 / 100000) := by
  exact
    packedTile32768 722974976 723040512 13 3225 26888 29 _ _ (2039887 / 100000) (203989 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723040512 :
    ThetaLowerSegment 723040512 723106048 (72301204842457 / 100000) (72307797786329 / 100000) := by
  exact
    packedTile32768 723040512 723106048 13 3232 26889 29 _ _ (254987 / 12500) (2039899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723106048 :
    ThetaLowerSegment 723106048 723171584 (72307797786329 / 100000) (72314456036249 / 100000) := by
  exact
    packedTile32768 723106048 723171584 13 3264 26890 29 _ _ (407981 / 20000) (509977 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723171584 :
    ThetaLowerSegment 723171584 723237120 (72314456036249 / 100000) (72321030679071 / 100000) := by
  exact
    packedTile32768 723171584 723237120 13 3223 26891 29 _ _ (1019957 / 50000) (2039917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723237120 :
    ThetaLowerSegment 723237120 723302656 (72321030679071 / 100000) (7232766654859 / 10000) := by
  exact
    packedTile32768 723237120 723302656 13 3253 26893 29 _ _ (2039923 / 100000) (1019963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723302656 :
    ThetaLowerSegment 723302656 723368192 (7232766654859 / 10000) (36167080846039 / 50000) := by
  exact
    packedTile32768 723302656 723368192 13 3184 26894 29 _ _ (509983 / 25000) (407987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723368192 :
    ThetaLowerSegment 723368192 723433728 (36167080846039 / 50000) (4521292328977 / 6250) := by
  exact
    packedTile32768 723368192 723433728 13 3194 26895 29 _ _ (2039941 / 100000) (254993 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723433728 :
    ThetaLowerSegment 723433728 723499264 (4521292328977 / 6250) (9043397578029 / 12500) := by
  exact
    packedTile32768 723433728 723499264 13 3188 26896 29 _ _ (40799 / 2000) (2039953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723499264 :
    ThetaLowerSegment 723499264 723564800 (9043397578029 / 12500) (4522113793377 / 6250) := by
  exact
    packedTile32768 723499264 723564800 13 3255 26897 29 _ _ (50999 / 2500) (2039963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723564800 :
    ThetaLowerSegment 723564800 723630336 (4522113793377 / 6250) (72360334315049 / 100000) := by
  exact
    packedTile32768 723564800 723630336 13 3193 26899 29 _ _ (2039969 / 100000) (509993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723630336 :
    ThetaLowerSegment 723630336 723695872 (72360334315049 / 100000) (72366901004231 / 100000) := by
  exact
    packedTile32768 723630336 723695872 13 3219 26900 29 _ _ (1019989 / 50000) (2039981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723695872 :
    ThetaLowerSegment 723695872 723761408 (72366901004231 / 100000) (18093356730661 / 25000) := by
  exact
    packedTile32768 723695872 723761408 13 3199 26901 29 _ _ (2039987 / 100000) (203999 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723761408 :
    ThetaLowerSegment 723761408 723826944 (18093356730661 / 25000) (1809501473741 / 2500) := by
  exact
    packedTile32768 723761408 723826944 13 3251 26902 29 _ _ (509999 / 25000) (2039999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723826944 :
    ThetaLowerSegment 723826944 723892480 (1809501473741 / 2500) (723866114457 / 1000) := by
  exact
    packedTile32768 723826944 723892480 13 3212 26904 29 _ _ (408001 / 20000) (255001 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723892480 :
    ThetaLowerSegment 723892480 723958016 (723866114457 / 1000) (36196591165397 / 50000) := by
  exact
    packedTile32768 723892480 723958016 13 3221 26905 29 _ _ (1020007 / 50000) (2040017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell723958016 :
    ThetaLowerSegment 723958016 724023552 (36196591165397 / 50000) (72399692044187 / 100000) := by
  exact
    packedTile32768 723958016 724023552 13 3191 26906 29 _ _ (2040023 / 100000) (1020013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724023552 :
    ThetaLowerSegment 724023552 724089088 (72399692044187 / 100000) (72406265027291 / 100000) := by
  exact
    packedTile32768 724023552 724089088 13 3222 26907 29 _ _ (63751 / 3125) (408007 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724089088 :
    ThetaLowerSegment 724089088 724154624 (72406265027291 / 100000) (7241275031763 / 10000) := by
  exact
    packedTile32768 724089088 724154624 13 3179 26908 29 _ _ (2040041 / 100000) (510011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724154624 :
    ThetaLowerSegment 724154624 724220160 (7241275031763 / 10000) (7241932335873 / 10000) := by
  exact
    packedTile32768 724154624 724220160 13 3222 26910 29 _ _ (40801 / 2000) (2040053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724220160 :
    ThetaLowerSegment 724220160 724285696 (7241932335873 / 10000) (2897038550031 / 4000) := by
  exact
    packedTile32768 724220160 724285696 13 3255 26911 29 _ _ (2040059 / 100000) (1020031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724285696 :
    ThetaLowerSegment 724285696 724351232 (2897038550031 / 4000) (14486494313539 / 20000) := by
  exact
    packedTile32768 724285696 724351232 13 3190 26912 29 _ _ (510017 / 25000) (2040071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724351232 :
    ThetaLowerSegment 724351232 724416768 (14486494313539 / 20000) (14487799962819 / 20000) := by
  exact
    packedTile32768 724351232 724416768 13 3200 26913 29 _ _ (2040077 / 100000) (25501 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724416768 :
    ThetaLowerSegment 724416768 724482304 (14487799962819 / 20000) (2897825611761 / 4000) := by
  exact
    packedTile32768 724416768 724482304 13 3255 26914 29 _ _ (1020043 / 50000) (2040089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724482304 :
    ThetaLowerSegment 724482304 724547840 (2897825611761 / 4000) (452825760474 / 625) := by
  exact
    packedTile32768 724482304 724547840 13 3177 26916 29 _ _ (408019 / 20000) (1020049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724547840 :
    ThetaLowerSegment 724547840 724613376 (452825760474 / 625) (90573414516 / 125) := by
  exact
    packedTile32768 724547840 724613376 13 3240 26917 29 _ _ (255013 / 12500) (2040107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724613376 :
    ThetaLowerSegment 724613376 724678912 (90573414516 / 125) (72465282415643 / 100000) := by
  exact
    packedTile32768 724613376 724678912 13 3211 26918 29 _ _ (2040113 / 100000) (510029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724678912 :
    ThetaLowerSegment 724678912 724744448 (72465282415643 / 100000) (72471857728849 / 100000) := by
  exact
    packedTile32768 724678912 724744448 13 3223 26919 29 _ _ (1020061 / 50000) (16321 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724744448 :
    ThetaLowerSegment 724744448 724809984 (72471857728849 / 100000) (452991201258 / 625) := by
  exact
    packedTile32768 724744448 724809984 13 3301 26921 29 _ _ (2040131 / 100000) (1020067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724809984 :
    ThetaLowerSegment 724809984 724875520 (452991201258 / 625) (72485183896851 / 100000) := by
  exact
    packedTile32768 724809984 724875520 13 3231 26922 29 _ _ (2040141 / 100000) (127509 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724875520 :
    ThetaLowerSegment 724875520 724941056 (72485183896851 / 100000) (72491673614001 / 100000) := by
  exact
    packedTile32768 724875520 724941056 13 3181 26923 29 _ _ (40803 / 2000) (2040153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell724941056 :
    ThetaLowerSegment 724941056 725006592 (72491673614001 / 100000) (72498096034533 / 100000) := by
  exact
    packedTile32768 724941056 725006592 13 3148 26924 29 _ _ (2040159 / 100000) (1020081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725006592 :
    ThetaLowerSegment 725006592 725072128 (72498096034533 / 100000) (72504506242389 / 100000) := by
  exact
    packedTile32768 725006592 725072128 13 3142 26925 29 _ _ (255021 / 12500) (2040171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725072128 :
    ThetaLowerSegment 725072128 725137664 (72504506242389 / 100000) (3625554086643 / 5000) := by
  exact
    packedTile32768 725072128 725137664 13 3223 26927 29 _ _ (2040177 / 100000) (102009 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725137664 :
    ThetaLowerSegment 725137664 725203200 (3625554086643 / 5000) (2266173920124 / 3125) := by
  exact
    packedTile32768 725137664 725203200 13 3178 26928 29 _ _ (1020093 / 50000) (2040189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725203200 :
    ThetaLowerSegment 725203200 725268736 (2266173920124 / 3125) (72524083866993 / 100000) := by
  exact
    packedTile32768 725203200 725268736 13 3195 26929 29 _ _ (408039 / 20000) (1020099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725268736 :
    ThetaLowerSegment 725268736 725334272 (72524083866993 / 100000) (72530675766117 / 100000) := by
  exact
    packedTile32768 725268736 725334272 13 3231 26930 29 _ _ (510051 / 25000) (2040207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725334272 :
    ThetaLowerSegment 725334272 725399808 (72530675766117 / 100000) (72537184045587 / 100000) := by
  exact
    packedTile32768 725334272 725399808 13 3190 26932 29 _ _ (2040213 / 100000) (255027 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725399808 :
    ThetaLowerSegment 725399808 725465344 (72537184045587 / 100000) (72543708675543 / 100000) := by
  exact
    packedTile32768 725399808 725465344 13 3198 26933 29 _ _ (1020111 / 50000) (81609 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725465344 :
    ThetaLowerSegment 725465344 725530880 (72543708675543 / 100000) (36275164612569 / 50000) := by
  exact
    packedTile32768 725465344 725530880 13 3245 26934 29 _ _ (2040231 / 100000) (1020117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725530880 :
    ThetaLowerSegment 725530880 725596416 (36275164612569 / 50000) (36278458580049 / 50000) := by
  exact
    packedTile32768 725530880 725596416 13 3229 26935 29 _ _ (25503 / 1250) (2040243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725596416 :
    ThetaLowerSegment 725596416 725661952 (36278458580049 / 50000) (4535219197773 / 6250) := by
  exact
    packedTile32768 725596416 725661952 13 3230 26936 29 _ _ (2040249 / 100000) (510063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725661952 :
    ThetaLowerSegment 725661952 725727488 (4535219197773 / 6250) (36285023095629 / 50000) := by
  exact
    packedTile32768 725661952 725727488 13 3205 26938 29 _ _ (1020129 / 50000) (2040261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725727488 :
    ThetaLowerSegment 725727488 725793024 (36285023095629 / 50000) (72576585246993 / 100000) := by
  exact
    packedTile32768 725727488 725793024 13 3205 26939 29 _ _ (2040267 / 100000) (204027 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725793024 :
    ThetaLowerSegment 725793024 725858560 (72576585246993 / 100000) (72583075364949 / 100000) := by
  exact
    packedTile32768 725793024 725858560 13 3181 26940 29 _ _ (510069 / 25000) (2040279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725858560 :
    ThetaLowerSegment 725858560 725924096 (72583075364949 / 100000) (36294803158617 / 50000) := by
  exact
    packedTile32768 725858560 725924096 13 3201 26941 29 _ _ (408057 / 20000) (63759 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725924096 :
    ThetaLowerSegment 725924096 725989632 (36294803158617 / 50000) (36298094152839 / 50000) := by
  exact
    packedTile32768 725924096 725989632 13 3226 26942 29 _ _ (1020147 / 50000) (2040297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell725989632 :
    ThetaLowerSegment 725989632 726055168 (36298094152839 / 50000) (3630135251673 / 5000) := by
  exact
    packedTile32768 725989632 726055168 13 3194 26944 29 _ _ (2040303 / 100000) (1020153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726055168 :
    ThetaLowerSegment 726055168 726120704 (3630135251673 / 5000) (18152306977731 / 25000) := by
  exact
    packedTile32768 726055168 726120704 13 3197 26945 29 _ _ (255039 / 12500) (408063 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726120704 :
    ThetaLowerSegment 726120704 726186240 (18152306977731 / 25000) (72615856913853 / 100000) := by
  exact
    packedTile32768 726120704 726186240 13 3249 26946 29 _ _ (2040321 / 100000) (510081 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726186240 :
    ThetaLowerSegment 726186240 726251776 (72615856913853 / 100000) (72622392090843 / 100000) := by
  exact
    packedTile32768 726186240 726251776 13 3203 26947 29 _ _ (204033 / 10000) (2040333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726251776 :
    ThetaLowerSegment 726251776 726317312 (72622392090843 / 100000) (72628994627847 / 100000) := by
  exact
    packedTile32768 726251776 726317312 13 3236 26949 29 _ _ (2040339 / 100000) (1020171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726317312 :
    ThetaLowerSegment 726317312 726382848 (72628994627847 / 100000) (72635654323719 / 100000) := by
  exact
    packedTile32768 726317312 726382848 13 3264 26950 29 _ _ (510087 / 25000) (2040351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726382848 :
    ThetaLowerSegment 726382848 726448384 (72635654323719 / 100000) (36321066228597 / 50000) := by
  exact
    packedTile32768 726382848 726448384 13 3175 26951 29 _ _ (2040357 / 100000) (51009 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726448384 :
    ThetaLowerSegment 726448384 726513920 (36321066228597 / 50000) (4540541989389 / 6250) := by
  exact
    packedTile32768 726448384 726513920 13 3205 26952 29 _ _ (1020183 / 50000) (2040369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726513920 :
    ThetaLowerSegment 726513920 726579456 (4540541989389 / 6250) (36327598474737 / 50000) := by
  exact
    packedTile32768 726513920 726579456 13 3198 26953 29 _ _ (16323 / 800) (1020189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726579456 :
    ThetaLowerSegment 726579456 726644992 (36327598474737 / 50000) (7266163232061 / 10000) := by
  exact
    packedTile32768 726579456 726644992 13 3154 26955 29 _ _ (63762 / 3125) (2040387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726644992 :
    ThetaLowerSegment 726644992 726710528 (7266163232061 / 10000) (72668057518167 / 100000) := by
  exact
    packedTile32768 726644992 726710528 13 3149 26956 29 _ _ (2040393 / 100000) (510099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726710528 :
    ThetaLowerSegment 726710528 726776064 (72668057518167 / 100000) (2906985839049 / 4000) := by
  exact
    packedTile32768 726710528 726776064 13 3229 26957 29 _ _ (1020201 / 50000) (408081 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726776064 :
    ThetaLowerSegment 726776064 726841600 (2906985839049 / 4000) (72681065109231 / 100000) := by
  exact
    packedTile32768 726776064 726841600 13 3146 26958 29 _ _ (2040411 / 100000) (1020207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726841600 :
    ThetaLowerSegment 726841600 726907136 (72681065109231 / 100000) (72687702595491 / 100000) := by
  exact
    packedTile32768 726841600 726907136 13 3253 26960 29 _ _ (102021 / 5000) (2040423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726907136 :
    ThetaLowerSegment 726907136 726972672 (72687702595491 / 100000) (36347114963931 / 50000) := by
  exact
    packedTile32768 726907136 726972672 13 3199 26961 29 _ _ (2040429 / 100000) (127527 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell726972672 :
    ThetaLowerSegment 726972672 727038208 (36347114963931 / 50000) (2271901725939 / 3125) := by
  exact
    packedTile32768 726972672 727038208 13 3247 26962 29 _ _ (1020219 / 50000) (2040441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727038208 :
    ThetaLowerSegment 727038208 727103744 (2271901725939 / 3125) (7270743771207 / 10000) := by
  exact
    packedTile32768 727038208 727103744 13 3226 26963 29 _ _ (2040447 / 100000) (40809 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727103744 :
    ThetaLowerSegment 727103744 727169280 (7270743771207 / 10000) (36357033576807 / 50000) := by
  exact
    packedTile32768 727103744 727169280 13 3249 26964 29 _ _ (255057 / 12500) (2040459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727169280 :
    ThetaLowerSegment 727169280 727234816 (36357033576807 / 50000) (72720708867189 / 100000) := by
  exact
    packedTile32768 727169280 727234816 13 3255 26966 29 _ _ (408093 / 20000) (510117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727234816 :
    ThetaLowerSegment 727234816 727300352 (72720708867189 / 100000) (14545447268703 / 20000) := by
  exact
    packedTile32768 727234816 727300352 13 3199 26967 29 _ _ (1020237 / 50000) (2040477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727300352 :
    ThetaLowerSegment 727300352 727365888 (14545447268703 / 20000) (72733843430707 / 100000) := by
  exact
    packedTile32768 727300352 727365888 13 3238 26968 29 _ _ (510121 / 25000) (2040487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727365888 :
    ThetaLowerSegment 727365888 727431424 (72733843430707 / 100000) (72740540328733 / 100000) := by
  exact
    packedTile32768 727365888 727431424 13 3282 26969 29 _ _ (2040493 / 100000) (127531 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727431424 :
    ThetaLowerSegment 727431424 727496960 (72740540328733 / 100000) (14549410314123 / 20000) := by
  exact
    packedTile32768 727431424 727496960 13 3191 26970 29 _ _ (1020251 / 50000) (408101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727496960 :
    ThetaLowerSegment 727496960 727562496 (14549410314123 / 20000) (18188404993881 / 25000) := by
  exact
    packedTile32768 727496960 727562496 13 3219 26972 29 _ _ (2040511 / 100000) (1020257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727562496 :
    ThetaLowerSegment 727562496 727628032 (18188404993881 / 25000) (18190057815081 / 25000) := by
  exact
    packedTile32768 727562496 727628032 13 3240 26973 29 _ _ (51013 / 2500) (2040523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727628032 :
    ThetaLowerSegment 727628032 727693568 (18190057815081 / 25000) (18191694319339 / 25000) := by
  exact
    packedTile32768 727628032 727693568 13 3208 26974 29 _ _ (2040529 / 100000) (510133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727693568 :
    ThetaLowerSegment 727693568 727759104 (18191694319339 / 25000) (2274163930713 / 3125) := by
  exact
    packedTile32768 727693568 727759104 13 3170 26975 29 _ _ (1020269 / 50000) (2040541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727759104 :
    ThetaLowerSegment 727759104 727824640 (2274163930713 / 3125) (18194954086039 / 25000) := by
  exact
    packedTile32768 727759104 727824640 13 3220 26977 29 _ _ (2040547 / 100000) (40811 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727824640 :
    ThetaLowerSegment 727824640 727890176 (18194954086039 / 25000) (454915415726 / 625) := by
  exact
    packedTile32768 727824640 727890176 13 3259 26978 29 _ _ (510139 / 25000) (2040559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727890176 :
    ThetaLowerSegment 727890176 727955712 (454915415726 / 625) (2911719934589 / 4000) := by
  exact
    packedTile32768 727890176 727955712 13 3201 26979 29 _ _ (408113 / 20000) (255071 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell727955712 :
    ThetaLowerSegment 727955712 728021248 (2911719934589 / 4000) (72799481268323 / 100000) := by
  exact
    packedTile32768 727955712 728021248 13 3177 26980 29 _ _ (1020287 / 50000) (2040577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728021248 :
    ThetaLowerSegment 728021248 728086784 (72799481268323 / 100000) (4550381179937 / 6250) := by
  exact
    packedTile32768 728021248 728086784 13 3243 26981 29 _ _ (2040583 / 100000) (1020293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728086784 :
    ThetaLowerSegment 728086784 728152320 (4550381179937 / 6250) (4550787512819 / 6250) := by
  exact
    packedTile32768 728086784 728152320 13 3186 26983 29 _ _ (127537 / 6250) (408119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728152320 :
    ThetaLowerSegment 728152320 728217856 (4550787512819 / 6250) (72819197468137 / 100000) := by
  exact
    packedTile32768 728152320 728217856 13 3233 26984 29 _ _ (2040601 / 100000) (510151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728217856 :
    ThetaLowerSegment 728217856 728283392 (72819197468137 / 100000) (72825692729767 / 100000) := by
  exact
    packedTile32768 728217856 728283392 13 3183 26985 29 _ _ (204061 / 10000) (2040613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728283392 :
    ThetaLowerSegment 728283392 728348928 (72825692729767 / 100000) (18208063329963 / 25000) := by
  exact
    packedTile32768 728283392 728348928 13 3215 26986 29 _ _ (2040619 / 100000) (1020311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728348928 :
    ThetaLowerSegment 728348928 728414464 (18208063329963 / 25000) (18209686649537 / 25000) := by
  exact
    packedTile32768 728348928 728414464 13 3182 26987 29 _ _ (510157 / 25000) (2040631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728414464 :
    ThetaLowerSegment 728414464 728480000 (18209686649537 / 25000) (36422668927829 / 50000) := by
  exact
    packedTile32768 728414464 728480000 13 3230 26989 29 _ _ (2040637 / 100000) (12754 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728480000 :
    ThetaLowerSegment 728480000 728545536 (36422668927829 / 50000) (9106488847053 / 12500) := by
  exact
    packedTile32768 728480000 728545536 13 3221 26990 29 _ _ (1020323 / 50000) (2040649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728545536 :
    ThetaLowerSegment 728545536 728611072 (9106488847053 / 12500) (72858332717709 / 100000) := by
  exact
    packedTile32768 728545536 728611072 13 3147 26991 29 _ _ (408131 / 20000) (1020329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728611072 :
    ThetaLowerSegment 728611072 728676608 (72858332717709 / 100000) (14572988485681 / 20000) := by
  exact
    packedTile32768 728611072 728676608 13 3239 26992 29 _ _ (255083 / 12500) (2040667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728676608 :
    ThetaLowerSegment 728676608 728742144 (14572988485681 / 20000) (9108947082041 / 12500) := by
  exact
    packedTile32768 728676608 728742144 13 3251 26994 29 _ _ (2040673 / 100000) (510169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728742144 :
    ThetaLowerSegment 728742144 728807680 (9108947082041 / 12500) (36439021788793 / 50000) := by
  exact
    packedTile32768 728742144 728807680 13 3169 26995 29 _ _ (1020341 / 50000) (408137 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728807680 :
    ThetaLowerSegment 728807680 728873216 (36439021788793 / 50000) (9110568152389 / 12500) := by
  exact
    packedTile32768 728807680 728873216 13 3186 26996 29 _ _ (2040691 / 100000) (1020347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728873216 :
    ThetaLowerSegment 728873216 728938752 (9110568152389 / 12500) (4555691961107 / 6250) := by
  exact
    packedTile32768 728873216 728938752 13 3198 26997 29 _ _ (20407 / 1000) (2040703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell728938752 :
    ThetaLowerSegment 728938752 729004288 (4555691961107 / 6250) (72897505733189 / 100000) := by
  exact
    packedTile32768 728938752 729004288 13 3153 26998 29 _ _ (2040709 / 100000) (255089 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729004288 :
    ThetaLowerSegment 729004288 729069824 (72897505733189 / 100000) (2916159563771 / 4000) := by
  exact
    packedTile32768 729004288 729069824 13 3177 27000 29 _ _ (1020359 / 50000) (2040721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729069824 :
    ThetaLowerSegment 729069824 729135360 (2916159563771 / 4000) (2278452392669 / 3125) := by
  exact
    packedTile32768 729069824 729135360 13 3179 27001 29 _ _ (2040727 / 100000) (204073 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729135360 :
    ThetaLowerSegment 729135360 729200896 (2278452392669 / 3125) (9114619742471 / 12500) := by
  exact
    packedTile32768 729135360 729200896 13 3176 27002 29 _ _ (408147 / 20000) (1020369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729200896 :
    ThetaLowerSegment 729200896 729266432 (9114619742471 / 12500) (2278861879814 / 3125) := by
  exact
    packedTile32768 729200896 729266432 13 3245 27003 29 _ _ (255093 / 12500) (2040747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729266432 :
    ThetaLowerSegment 729266432 729331968 (2278861879814 / 3125) (18232541926183 / 25000) := by
  exact
    packedTile32768 729266432 729331968 13 3228 27004 29 _ _ (2040753 / 100000) (510189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729331968 :
    ThetaLowerSegment 729331968 729397504 (18232541926183 / 25000) (36468341928899 / 50000) := by
  exact
    packedTile32768 729331968 729397504 13 3193 27006 29 _ _ (1020381 / 50000) (408153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729397504 :
    ThetaLowerSegment 729397504 729463040 (36468341928899 / 50000) (18235800520093 / 25000) := by
  exact
    packedTile32768 729397504 729463040 13 3194 27007 29 _ _ (2040771 / 100000) (1020387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729463040 :
    ThetaLowerSegment 729463040 729528576 (18235800520093 / 25000) (18237423960583 / 25000) := by
  exact
    packedTile32768 729463040 729528576 13 3182 27008 29 _ _ (102039 / 5000) (2040783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729528576 :
    ThetaLowerSegment 729528576 729594112 (18237423960583 / 25000) (14591231804219 / 20000) := by
  exact
    packedTile32768 729528576 729594112 13 3167 27009 29 _ _ (2040789 / 100000) (255099 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729594112 :
    ThetaLowerSegment 729594112 729659648 (14591231804219 / 20000) (72962742635443 / 100000) := by
  exact
    packedTile32768 729594112 729659648 13 3226 27010 29 _ _ (1020399 / 50000) (2040801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729659648 :
    ThetaLowerSegment 729659648 729725184 (72962742635443 / 100000) (72969260973001 / 100000) := by
  exact
    packedTile32768 729659648 729725184 13 3194 27012 29 _ _ (2040807 / 100000) (204081 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729725184 :
    ThetaLowerSegment 729725184 729790720 (72969260973001 / 100000) (72975781380121 / 100000) := by
  exact
    packedTile32768 729725184 729790720 13 3195 27013 29 _ _ (127551 / 6250) (2040819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729790720 :
    ThetaLowerSegment 729790720 729856256 (72975781380121 / 100000) (72982422224671 / 100000) := by
  exact
    packedTile32768 729790720 729856256 13 3254 27014 29 _ _ (81633 / 4000) (510207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729856256 :
    ThetaLowerSegment 729856256 729921792 (72982422224671 / 100000) (72988942689301 / 100000) := by
  exact
    packedTile32768 729856256 729921792 13 3195 27015 29 _ _ (1020417 / 50000) (2040837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729921792 :
    ThetaLowerSegment 729921792 729987328 (72988942689301 / 100000) (36497707101227 / 50000) := by
  exact
    packedTile32768 729921792 729987328 13 3171 27017 29 _ _ (2040843 / 100000) (1020423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell729987328 :
    ThetaLowerSegment 729987328 730052864 (36497707101227 / 50000) (36501005118059 / 50000) := by
  exact
    packedTile32768 729987328 730052864 13 3232 27018 29 _ _ (510213 / 25000) (408171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730052864 :
    ThetaLowerSegment 730052864 730118400 (36501005118059 / 50000) (2281518053963 / 3125) := by
  exact
    packedTile32768 730052864 730118400 13 3218 27019 29 _ _ (2040861 / 100000) (63777 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730118400 :
    ThetaLowerSegment 730118400 730183936 (2281518053963 / 3125) (36507577725413 / 50000) := by
  exact
    packedTile32768 730118400 730183936 13 3223 27020 29 _ _ (204087 / 10000) (2040873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730183936 :
    ThetaLowerSegment 730183936 730249472 (36507577725413 / 50000) (73021639323409 / 100000) := by
  exact
    packedTile32768 730183936 730249472 13 3177 27021 29 _ _ (2040879 / 100000) (1020441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730249472 :
    ThetaLowerSegment 730249472 730315008 (73021639323409 / 100000) (14605614440477 / 20000) := by
  exact
    packedTile32768 730249472 730315008 13 3152 27023 29 _ _ (255111 / 12500) (2040891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730315008 :
    ThetaLowerSegment 730315008 730380544 (14605614440477 / 20000) (730345928683 / 1000) := by
  exact
    packedTile32768 730315008 730380544 13 3195 27024 29 _ _ (2040897 / 100000) (20409 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730380544 :
    ThetaLowerSegment 730380544 730446080 (730345928683 / 1000) (7304109315391 / 10000) := by
  exact
    packedTile32768 730380544 730446080 13 3185 27025 29 _ _ (1020453 / 50000) (2040909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730446080 :
    ThetaLowerSegment 730446080 730511616 (7304109315391 / 10000) (1826189275453 / 2500) := by
  exact
    packedTile32768 730446080 730511616 13 3174 27026 29 _ _ (408183 / 20000) (1020459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730511616 :
    ThetaLowerSegment 730511616 730577152 (1826189275453 / 2500) (9131755603631 / 12500) := by
  exact
    packedTile32768 730511616 730577152 13 3172 27027 29 _ _ (510231 / 25000) (2040927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730577152 :
    ThetaLowerSegment 730577152 730642688 (9131755603631 / 12500) (36530334848783 / 50000) := by
  exact
    packedTile32768 730577152 730642688 13 3246 27029 29 _ _ (2040933 / 100000) (255117 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730642688 :
    ThetaLowerSegment 730642688 730708224 (36530334848783 / 50000) (2283352509647 / 3125) := by
  exact
    packedTile32768 730642688 730708224 13 3239 27030 29 _ _ (1020471 / 50000) (408189 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730708224 :
    ThetaLowerSegment 730708224 730773760 (2283352509647 / 3125) (73073858293777 / 100000) := by
  exact
    packedTile32768 730708224 730773760 13 3223 27031 29 _ _ (2040951 / 100000) (1020477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730773760 :
    ThetaLowerSegment 730773760 730839296 (73073858293777 / 100000) (73080505700497 / 100000) := by
  exact
    packedTile32768 730773760 730839296 13 3257 27032 29 _ _ (12756 / 625) (2040963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730839296 :
    ThetaLowerSegment 730839296 730904832 (73080505700497 / 100000) (36543560240513 / 50000) := by
  exact
    packedTile32768 730839296 730904832 13 3241 27034 29 _ _ (2040969 / 100000) (510243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730904832 :
    ThetaLowerSegment 730904832 730970368 (36543560240513 / 50000) (9136711298651 / 12500) := by
  exact
    packedTile32768 730904832 730970368 13 3219 27035 29 _ _ (1020489 / 50000) (2040981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell730970368 :
    ThetaLowerSegment 730970368 731035904 (9136711298651 / 12500) (36550129142687 / 50000) := by
  exact
    packedTile32768 730970368 731035904 13 3218 27036 29 _ _ (2040987 / 100000) (204099 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731035904 :
    ThetaLowerSegment 731035904 731101440 (36550129142687 / 50000) (36553424330729 / 50000) := by
  exact
    packedTile32768 731035904 731101440 13 3229 27037 29 _ _ (510249 / 25000) (2040999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731101440 :
    ThetaLowerSegment 731101440 731166976 (36553424330729 / 50000) (73113443148613 / 100000) := by
  exact
    packedTile32768 731101440 731166976 13 3231 27038 29 _ _ (408201 / 20000) (127563 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731166976 :
    ThetaLowerSegment 731166976 731232512 (73113443148613 / 100000) (23398413359 / 32) := by
  exact
    packedTile32768 731166976 731232512 13 3233 27040 29 _ _ (1020507 / 50000) (2041017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731232512 :
    ThetaLowerSegment 731232512 731298048 (23398413359 / 32) (14625339096371 / 20000) := by
  exact
    packedTile32768 731232512 731298048 13 3260 27041 29 _ _ (2041023 / 100000) (1020513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731298048 :
    ThetaLowerSegment 731298048 731363584 (14625339096371 / 20000) (73133296179343 / 100000) := by
  exact
    packedTile32768 731298048 731363584 13 3234 27042 29 _ _ (255129 / 12500) (408207 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731363584 :
    ThetaLowerSegment 731363584 731429120 (73133296179343 / 100000) (3656986987289 / 5000) := by
  exact
    packedTile32768 731363584 731429120 13 3157 27043 29 _ _ (2041041 / 100000) (510261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731429120 :
    ThetaLowerSegment 731429120 731494656 (3656986987289 / 5000) (914329358321 / 1250) := by
  exact
    packedTile32768 731429120 731494656 13 3238 27044 29 _ _ (40821 / 2000) (2041053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731494656 :
    ThetaLowerSegment 731494656 731560192 (914329358321 / 1250) (14630541312893 / 20000) := by
  exact
    packedTile32768 731494656 731560192 13 3115 27046 29 _ _ (2041059 / 100000) (1020531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731560192 :
    ThetaLowerSegment 731560192 731625728 (14630541312893 / 20000) (73159191037501 / 100000) := by
  exact
    packedTile32768 731560192 731625728 13 3177 27047 29 _ _ (510267 / 25000) (2041071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731625728 :
    ThetaLowerSegment 731625728 731691264 (73159191037501 / 100000) (73165697987789 / 100000) := by
  exact
    packedTile32768 731625728 731691264 13 3188 27048 29 _ _ (510269 / 25000) (2041079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731691264 :
    ThetaLowerSegment 731691264 731756800 (73165697987789 / 100000) (36586132079117 / 50000) := by
  exact
    packedTile32768 731691264 731756800 13 3217 27049 29 _ _ (408217 / 20000) (63784 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731756800 :
    ThetaLowerSegment 731756800 731822336 (36586132079117 / 50000) (36589440692491 / 50000) := by
  exact
    packedTile32768 731756800 731822336 13 3242 27051 29 _ _ (1020547 / 50000) (2041097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731822336 :
    ThetaLowerSegment 731822336 731887872 (36589440692491 / 50000) (14637107484373 / 20000) := by
  exact
    packedTile32768 731822336 731887872 13 3261 27052 29 _ _ (2041103 / 100000) (1020553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731887872 :
    ThetaLowerSegment 731887872 731953408 (14637107484373 / 20000) (2927681126321 / 4000) := by
  exact
    packedTile32768 731887872 731953408 13 3180 27053 29 _ _ (255139 / 12500) (408223 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell731953408 :
    ThetaLowerSegment 731953408 732018944 (2927681126321 / 4000) (73198474018143 / 100000) := by
  exact
    packedTile32768 731953408 732018944 13 3158 27054 29 _ _ (2041121 / 100000) (510281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732018944 :
    ThetaLowerSegment 732018944 732084480 (73198474018143 / 100000) (73205015839793 / 100000) := by
  exact
    packedTile32768 732018944 732084480 13 3205 27055 29 _ _ (204113 / 10000) (2041133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732084480 :
    ThetaLowerSegment 732084480 732150016 (73205015839793 / 100000) (73211702611157 / 100000) := by
  exact
    packedTile32768 732084480 732150016 13 3276 27057 29 _ _ (2041139 / 100000) (1020571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732150016 :
    ThetaLowerSegment 732150016 732215552 (73211702611157 / 100000) (73218203667537 / 100000) := by
  exact
    packedTile32768 732150016 732215552 13 3185 27058 29 _ _ (510287 / 25000) (2041151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732215552 :
    ThetaLowerSegment 732215552 732281088 (73218203667537 / 100000) (18306195579137 / 25000) := by
  exact
    packedTile32768 732215552 732281088 13 3223 27059 29 _ _ (2041157 / 100000) (51029 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732281088 :
    ThetaLowerSegment 732281088 732346624 (18306195579137 / 25000) (18307830553103 / 25000) := by
  exact
    packedTile32768 732281088 732346624 13 3204 27060 29 _ _ (1020583 / 50000) (2041169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732346624 :
    ThetaLowerSegment 732346624 732412160 (18307830553103 / 25000) (36618973933231 / 50000) := by
  exact
    packedTile32768 732346624 732412160 13 3246 27061 29 _ _ (81647 / 4000) (1020589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732412160 :
    ThetaLowerSegment 732412160 732477696 (36618973933231 / 50000) (36622235745263 / 50000) := by
  exact
    packedTile32768 732412160 732477696 13 3196 27063 29 _ _ (63787 / 3125) (2041187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732477696 :
    ThetaLowerSegment 732477696 732543232 (36622235745263 / 50000) (36625497571677 / 50000) := by
  exact
    packedTile32768 732477696 732543232 13 3196 27064 29 _ _ (2041193 / 100000) (510299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732543232 :
    ThetaLowerSegment 732543232 732608768 (36625497571677 / 50000) (9157194700973 / 12500) := by
  exact
    packedTile32768 732543232 732608768 13 3215 27065 29 _ _ (1020601 / 50000) (408241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732608768 :
    ThetaLowerSegment 732608768 732674304 (9157194700973 / 12500) (73263964969113 / 100000) := by
  exact
    packedTile32768 732608768 732674304 13 3139 27066 29 _ _ (2041211 / 100000) (1020607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732674304 :
    ThetaLowerSegment 732674304 732739840 (73263964969113 / 100000) (73270429512853 / 100000) := by
  exact
    packedTile32768 732674304 732739840 13 3167 27067 29 _ _ (102061 / 5000) (2041223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732739840 :
    ThetaLowerSegment 732739840 732805376 (73270429512853 / 100000) (73277043094813 / 100000) := by
  exact
    packedTile32768 732739840 732805376 13 3240 27069 29 _ _ (2041229 / 100000) (127577 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732805376 :
    ThetaLowerSegment 732805376 732870912 (73277043094813 / 100000) (73283564850223 / 100000) := by
  exact
    packedTile32768 732805376 732870912 13 3195 27070 29 _ _ (1020619 / 50000) (2041241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732870912 :
    ThetaLowerSegment 732870912 732936448 (73283564850223 / 100000) (36645102513357 / 50000) := by
  exact
    packedTile32768 732870912 732936448 13 3253 27071 29 _ _ (2041247 / 100000) (1633 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell732936448 :
    ThetaLowerSegment 732936448 733001984 (36645102513357 / 50000) (36648372603867 / 50000) := by
  exact
    packedTile32768 732936448 733001984 13 3204 27072 29 _ _ (408251 / 20000) (1020629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733001984 :
    ThetaLowerSegment 733001984 733067520 (36648372603867 / 50000) (36651659038907 / 50000) := by
  exact
    packedTile32768 733001984 733067520 13 3220 27074 29 _ _ (127579 / 6250) (2041267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733067520 :
    ThetaLowerSegment 733067520 733133056 (36651659038907 / 50000) (916374198561 / 1250) := by
  exact
    packedTile32768 733067520 733133056 13 3242 27075 29 _ _ (2041273 / 100000) (510319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733133056 :
    ThetaLowerSegment 733133056 733198592 (916374198561 / 1250) (18329130265153 / 25000) := by
  exact
    packedTile32768 733133056 733198592 13 3226 27076 29 _ _ (1020641 / 50000) (408257 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733198592 :
    ThetaLowerSegment 733198592 733264128 (18329130265153 / 25000) (73323108306669 / 100000) := by
  exact
    packedTile32768 733198592 733264128 13 3227 27077 29 _ _ (2041291 / 100000) (1020647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733264128 :
    ThetaLowerSegment 733264128 733329664 (73323108306669 / 100000) (73329681292669 / 100000) := by
  exact
    packedTile32768 733264128 733329664 13 3220 27078 29 _ _ (20413 / 1000) (2041303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733329664 :
    ThetaLowerSegment 733329664 733395200 (73329681292669 / 100000) (36668103678771 / 50000) := by
  exact
    packedTile32768 733329664 733395200 13 3197 27080 29 _ _ (2041309 / 100000) (63791 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733395200 :
    ThetaLowerSegment 733395200 733460736 (36668103678771 / 50000) (36671404489977 / 50000) := by
  exact
    packedTile32768 733395200 733460736 13 3234 27081 29 _ _ (1020659 / 50000) (2041321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733460736 :
    ThetaLowerSegment 733460736 733526272 (36671404489977 / 50000) (7334931673043 / 10000) := by
  exact
    packedTile32768 733460736 733526272 13 3188 27082 29 _ _ (2041327 / 100000) (204133 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733526272 :
    ThetaLowerSegment 733526272 733591808 (7334931673043 / 10000) (7335592045239 / 10000) := by
  exact
    packedTile32768 733526272 733591808 13 3235 27083 29 _ _ (255167 / 12500) (2041339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733591808 :
    ThetaLowerSegment 733591808 733657344 (7335592045239 / 10000) (1467245299053 / 2000) := by
  exact
    packedTile32768 733591808 733657344 13 3108 27084 29 _ _ (408269 / 20000) (510337 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733657344 :
    ThetaLowerSegment 733657344 733722880 (1467245299053 / 2000) (36684370063769 / 50000) := by
  exact
    packedTile32768 733657344 733722880 13 3172 27086 29 _ _ (1020677 / 50000) (2041357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733722880 :
    ThetaLowerSegment 733722880 733788416 (36684370063769 / 50000) (2935010817911 / 4000) := by
  exact
    packedTile32768 733722880 733788416 13 3199 27087 29 _ _ (2041363 / 100000) (1020683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733788416 :
    ThetaLowerSegment 733788416 733853952 (2935010817911 / 4000) (73381835500127 / 100000) := by
  exact
    packedTile32768 733788416 733853952 13 3216 27088 29 _ _ (510343 / 25000) (16331 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733853952 :
    ThetaLowerSegment 733853952 733919488 (73381835500127 / 100000) (73388392415899 / 100000) := by
  exact
    packedTile32768 733853952 733919488 13 3212 27089 29 _ _ (2041381 / 100000) (255173 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733919488 :
    ThetaLowerSegment 733919488 733985024 (73388392415899 / 100000) (36697555313549 / 50000) := by
  exact
    packedTile32768 733919488 733985024 13 3291 27090 29 _ _ (2041389 / 100000) (127587 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell733985024 :
    ThetaLowerSegment 733985024 734050560 (36697555313549 / 50000) (917519747717 / 1250) := by
  exact
    packedTile32768 733985024 734050560 13 3169 27092 29 _ _ (1020699 / 50000) (2041401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734050560 :
    ThetaLowerSegment 734050560 734116096 (917519747717 / 1250) (36704017373147 / 50000) := by
  exact
    packedTile32768 734050560 734116096 13 3162 27093 29 _ _ (2041407 / 100000) (204141 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734116096 :
    ThetaLowerSegment 734116096 734181632 (36704017373147 / 50000) (36707306094323 / 50000) := by
  exact
    packedTile32768 734116096 734181632 13 3222 27094 29 _ _ (255177 / 12500) (2041419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734181632 :
    ThetaLowerSegment 734181632 734247168 (36707306094323 / 50000) (36710629534223 / 50000) := by
  exact
    packedTile32768 734181632 734247168 13 3256 27095 29 _ _ (81657 / 4000) (510357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734247168 :
    ThetaLowerSegment 734247168 734312704 (36710629534223 / 50000) (18356945362519 / 25000) := by
  exact
    packedTile32768 734247168 734312704 13 3195 27096 29 _ _ (1020717 / 50000) (2041437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734312704 :
    ThetaLowerSegment 734312704 734378240 (18356945362519 / 25000) (73434271197373 / 100000) := by
  exact
    packedTile32768 734312704 734378240 13 3179 27098 29 _ _ (2041443 / 100000) (1020723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734378240 :
    ThetaLowerSegment 734378240 734443776 (73434271197373 / 100000) (73440895709113 / 100000) := by
  exact
    packedTile32768 734378240 734443776 13 3245 27099 29 _ _ (510363 / 25000) (408291 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734443776 :
    ThetaLowerSegment 734443776 734509312 (73440895709113 / 100000) (9180933396509 / 12500) := by
  exact
    packedTile32768 734443776 734509312 13 3219 27100 29 _ _ (2041461 / 100000) (255183 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734509312 :
    ThetaLowerSegment 734509312 734574848 (9180933396509 / 12500) (36726986668481 / 50000) := by
  exact
    packedTile32768 734509312 734574848 13 3187 27101 29 _ _ (204147 / 10000) (2041473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734574848 :
    ThetaLowerSegment 734574848 734640384 (36726986668481 / 50000) (36730257117839 / 50000) := by
  exact
    packedTile32768 734574848 734640384 13 3204 27103 29 _ _ (2041479 / 100000) (1020741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734640384 :
    ThetaLowerSegment 734640384 734705920 (36730257117839 / 50000) (36733508187479 / 50000) := by
  exact
    packedTile32768 734640384 734705920 13 3185 27104 29 _ _ (127593 / 6250) (2041491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734705920 :
    ThetaLowerSegment 734705920 734771456 (36733508187479 / 50000) (18368382187597 / 25000) := by
  exact
    packedTile32768 734705920 734771456 13 3190 27105 29 _ _ (2041497 / 100000) (4083 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734771456 :
    ThetaLowerSegment 734771456 734836992 (18368382187597 / 25000) (36740054262113 / 50000) := by
  exact
    packedTile32768 734771456 734836992 13 3223 27106 29 _ _ (1020753 / 50000) (2041509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734836992 :
    ThetaLowerSegment 734836992 734902528 (36740054262113 / 50000) (7348669444839 / 10000) := by
  exact
    packedTile32768 734836992 734902528 13 3226 27107 29 _ _ (1020757 / 50000) (2041517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734902528 :
    ThetaLowerSegment 734902528 734968064 (7348669444839 / 10000) (4593328493957 / 6250) := by
  exact
    packedTile32768 734902528 734968064 13 3214 27109 29 _ _ (2041523 / 100000) (1020763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell734968064 :
    ThetaLowerSegment 734968064 735033600 (4593328493957 / 6250) (3674992400507 / 5000) := by
  exact
    packedTile32768 734968064 735033600 13 3229 27110 29 _ _ (510383 / 25000) (408307 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735033600 :
    ThetaLowerSegment 735033600 735099136 (3674992400507 / 5000) (36753212927621 / 50000) := by
  exact
    packedTile32768 735033600 735099136 13 3222 27111 29 _ _ (2041541 / 100000) (255193 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735099136 :
    ThetaLowerSegment 735099136 735164672 (36753212927621 / 50000) (4594554439287 / 6250) := by
  exact
    packedTile32768 735099136 735164672 13 3157 27112 29 _ _ (40831 / 2000) (2041553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735164672 :
    ThetaLowerSegment 735164672 735230208 (4594554439287 / 6250) (36759761213907 / 50000) := by
  exact
    packedTile32768 735164672 735230208 13 3258 27113 29 _ _ (2041559 / 100000) (1020781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735230208 :
    ThetaLowerSegment 735230208 735295744 (36759761213907 / 50000) (36763021598003 / 50000) := by
  exact
    packedTile32768 735230208 735295744 13 3194 27115 29 _ _ (63799 / 3125) (2041571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735295744 :
    ThetaLowerSegment 735295744 735361280 (36763021598003 / 50000) (9191576623849 / 12500) := by
  exact
    packedTile32768 735295744 735361280 13 3218 27116 29 _ _ (2041577 / 100000) (102079 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735361280 :
    ThetaLowerSegment 735361280 735426816 (9191576623849 / 12500) (2298096017778 / 3125) := by
  exact
    packedTile32768 735361280 735426816 13 3164 27117 29 _ _ (1020793 / 50000) (2041589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735426816 :
    ThetaLowerSegment 735426816 735492352 (2298096017778 / 3125) (9193190501137 / 12500) := by
  exact
    packedTile32768 735426816 735492352 13 3160 27118 29 _ _ (408319 / 20000) (1020799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735492352 :
    ThetaLowerSegment 735492352 735557888 (9193190501137 / 12500) (9194017350757 / 12500) := by
  exact
    packedTile32768 735492352 735557888 13 3240 27119 29 _ _ (510401 / 25000) (2041607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735557888 :
    ThetaLowerSegment 735557888 735623424 (9194017350757 / 12500) (2298713220117 / 3125) := by
  exact
    packedTile32768 735557888 735623424 13 3274 27121 29 _ _ (510403 / 25000) (408323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735623424 :
    ThetaLowerSegment 735623424 735688960 (2298713220117 / 3125) (73565305190419 / 100000) := by
  exact
    packedTile32768 735623424 735688960 13 3175 27122 29 _ _ (2041621 / 100000) (255203 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735688960 :
    ThetaLowerSegment 735688960 735754496 (73565305190419 / 100000) (73571893530429 / 100000) := by
  exact
    packedTile32768 735688960 735754496 13 3227 27123 29 _ _ (204163 / 10000) (2041633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735754496 :
    ThetaLowerSegment 735754496 735820032 (73571893530429 / 100000) (1471570127983 / 2000) := by
  exact
    packedTile32768 735754496 735820032 13 3239 27124 29 _ _ (2041639 / 100000) (1020821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735820032 :
    ThetaLowerSegment 735820032 735885568 (1471570127983 / 2000) (36792487170007 / 50000) := by
  exact
    packedTile32768 735820032 735885568 13 3168 27126 29 _ _ (127603 / 6250) (2041651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735885568 :
    ThetaLowerSegment 735885568 735951104 (36792487170007 / 50000) (36795774237777 / 50000) := by
  exact
    packedTile32768 735885568 735951104 13 3220 27127 29 _ _ (2041657 / 100000) (102083 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell735951104 :
    ThetaLowerSegment 735951104 736016640 (36795774237777 / 50000) (36799071528367 / 50000) := by
  exact
    packedTile32768 735951104 736016640 13 3230 27128 29 _ _ (1020833 / 50000) (2041669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736016640 :
    ThetaLowerSegment 736016640 736082176 (36799071528367 / 50000) (18401182375071 / 25000) := by
  exact
    packedTile32768 736016640 736082176 13 3226 27129 29 _ _ (81667 / 4000) (1020839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736082176 :
    ThetaLowerSegment 736082176 736147712 (18401182375071 / 25000) (3680564573633 / 5000) := by
  exact
    packedTile32768 736082176 736147712 13 3214 27130 29 _ _ (510421 / 25000) (2041687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736147712 :
    ThetaLowerSegment 736147712 736213248 (3680564573633 / 5000) (7361784530719 / 10000) := by
  exact
    packedTile32768 736147712 736213248 13 3210 27132 29 _ _ (2041693 / 100000) (63803 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736213248 :
    ThetaLowerSegment 736213248 736278784 (7361784530719 / 10000) (36812154667861 / 50000) := by
  exact
    packedTile32768 736213248 736278784 13 3166 27133 29 _ _ (1020851 / 50000) (408341 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736278784 :
    ThetaLowerSegment 736278784 736344320 (36812154667861 / 50000) (18407720400053 / 25000) := by
  exact
    packedTile32768 736278784 736344320 13 3219 27134 29 _ _ (204171 / 10000) (2041713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736344320 :
    ThetaLowerSegment 736344320 736409856 (18407720400053 / 25000) (73637392642103 / 100000) := by
  exact
    packedTile32768 736344320 736409856 13 3189 27135 29 _ _ (2041719 / 100000) (1020861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736409856 :
    ThetaLowerSegment 736409856 736475392 (73637392642103 / 100000) (73643901670967 / 100000) := by
  exact
    packedTile32768 736409856 736475392 13 3188 27136 29 _ _ (63804 / 3125) (2041731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736475392 :
    ThetaLowerSegment 736475392 736540928 (73643901670967 / 100000) (36825228844237 / 50000) := by
  exact
    packedTile32768 736475392 736540928 13 3211 27138 29 _ _ (2041737 / 100000) (102087 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736540928 :
    ThetaLowerSegment 736540928 736606464 (36825228844237 / 50000) (36828518097043 / 50000) := by
  exact
    packedTile32768 736540928 736606464 13 3222 27139 29 _ _ (1020873 / 50000) (2041749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736606464 :
    ThetaLowerSegment 736606464 736672000 (36828518097043 / 50000) (36831821656633 / 50000) := by
  exact
    packedTile32768 736606464 736672000 13 3236 27140 29 _ _ (408351 / 20000) (1020879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736672000 :
    ThetaLowerSegment 736672000 736737536 (36831821656633 / 50000) (36835095625207 / 50000) := by
  exact
    packedTile32768 736672000 736737536 13 3207 27141 29 _ _ (510441 / 25000) (2041767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736737536 :
    ThetaLowerSegment 736737536 736803072 (36835095625207 / 50000) (4604796583859 / 6250) := by
  exact
    packedTile32768 736737536 736803072 13 3210 27142 29 _ _ (2041773 / 100000) (127611 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736803072 :
    ThetaLowerSegment 736803072 736868608 (4604796583859 / 6250) (18420824865491 / 25000) := by
  exact
    packedTile32768 736803072 736868608 13 3210 27144 29 _ _ (1020891 / 50000) (408357 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736868608 :
    ThetaLowerSegment 736868608 736934144 (18420824865491 / 25000) (73689778064807 / 100000) := by
  exact
    packedTile32768 736868608 736934144 13 3173 27145 29 _ _ (2041791 / 100000) (1020897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736934144 :
    ThetaLowerSegment 736934144 736999680 (73689778064807 / 100000) (18424075403153 / 25000) := by
  exact
    packedTile32768 736934144 736999680 13 3195 27146 29 _ _ (2041799 / 100000) (1020901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell736999680 :
    ThetaLowerSegment 736999680 737065216 (18424075403153 / 25000) (737028578581 / 1000) := by
  exact
    packedTile32768 736999680 737065216 13 3211 27147 29 _ _ (127613 / 6250) (2041811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737065216 :
    ThetaLowerSegment 737065216 737130752 (737028578581 / 1000) (73709426383389 / 100000) := by
  exact
    packedTile32768 737065216 737130752 13 3217 27148 29 _ _ (2041817 / 100000) (102091 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737130752 :
    ThetaLowerSegment 737130752 737196288 (73709426383389 / 100000) (14743210830117 / 20000) := by
  exact
    packedTile32768 737130752 737196288 13 3246 27150 29 _ _ (1020913 / 50000) (2041829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737196288 :
    ThetaLowerSegment 737196288 737261824 (14743210830117 / 20000) (7372265948681 / 10000) := by
  exact
    packedTile32768 737196288 737261824 13 3235 27151 29 _ _ (408367 / 20000) (1020919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737261824 :
    ThetaLowerSegment 737261824 737327360 (7372265948681 / 10000) (7372923422449 / 10000) := by
  exact
    packedTile32768 737261824 737327360 13 3220 27152 29 _ _ (510461 / 25000) (2041847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737327360 :
    ThetaLowerSegment 737327360 737392896 (7372923422449 / 10000) (14747147505259 / 20000) := by
  exact
    packedTile32768 737327360 737392896 13 3185 27153 29 _ _ (2041853 / 100000) (63808 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737392896 :
    ThetaLowerSegment 737392896 737458432 (14747147505259 / 20000) (73742328656831 / 100000) := by
  exact
    packedTile32768 737392896 737458432 13 3228 27154 29 _ _ (1020931 / 50000) (408373 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737458432 :
    ThetaLowerSegment 737458432 737523968 (73742328656831 / 100000) (73748817722869 / 100000) := by
  exact
    packedTile32768 737458432 737523968 13 3178 27156 29 _ _ (2041871 / 100000) (1020937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737523968 :
    ThetaLowerSegment 737523968 737589504 (73748817722869 / 100000) (73755351735669 / 100000) := by
  exact
    packedTile32768 737523968 737589504 13 3200 27157 29 _ _ (2041879 / 100000) (1020941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737589504 :
    ThetaLowerSegment 737589504 737655040 (73755351735669 / 100000) (73761816353077 / 100000) := by
  exact
    packedTile32768 737589504 737655040 13 3166 27158 29 _ _ (63809 / 3125) (2041891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737655040 :
    ThetaLowerSegment 737655040 737720576 (73761816353077 / 100000) (14753696220977 / 20000) := by
  exact
    packedTile32768 737655040 737720576 13 3264 27159 29 _ _ (2041897 / 100000) (20419 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737720576 :
    ThetaLowerSegment 737720576 737786112 (14753696220977 / 20000) (73774992743119 / 100000) := by
  exact
    packedTile32768 737720576 737786112 13 3189 27161 29 _ _ (1020953 / 50000) (2041909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737786112 :
    ThetaLowerSegment 737786112 737851648 (73774992743119 / 100000) (9222681415033 / 12500) := by
  exact
    packedTile32768 737786112 737851648 13 3163 27162 29 _ _ (408383 / 20000) (1020959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737851648 :
    ThetaLowerSegment 737851648 737917184 (9222681415033 / 12500) (18447001984557 / 25000) := by
  exact
    packedTile32768 737851648 737917184 13 3211 27163 29 _ _ (510481 / 25000) (2041927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737917184 :
    ThetaLowerSegment 737917184 737982720 (18447001984557 / 25000) (18448635530957 / 25000) := by
  exact
    packedTile32768 737917184 737982720 13 3200 27164 29 _ _ (2041933 / 100000) (127621 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell737982720 :
    ThetaLowerSegment 737982720 738048256 (18448635530957 / 25000) (7380118047727 / 10000) := by
  exact
    packedTile32768 737982720 738048256 13 3251 27165 29 _ _ (1020971 / 50000) (408389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738048256 :
    ThetaLowerSegment 738048256 738113792 (7380118047727 / 10000) (3690388288301 / 5000) := by
  exact
    packedTile32768 738048256 738113792 13 3225 27167 29 _ _ (40839 / 2000) (2041953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738113792 :
    ThetaLowerSegment 738113792 738179328 (3690388288301 / 5000) (73814257153681 / 100000) := by
  exact
    packedTile32768 738113792 738179328 13 3179 27168 29 _ _ (2041959 / 100000) (1020981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738179328 :
    ThetaLowerSegment 738179328 738244864 (73814257153681 / 100000) (73820905801489 / 100000) := by
  exact
    packedTile32768 738179328 738244864 13 3256 27169 29 _ _ (127623 / 6250) (2041971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738244864 :
    ThetaLowerSegment 738244864 738310400 (73820905801489 / 100000) (73827472799521 / 100000) := by
  exact
    packedTile32768 738244864 738310400 13 3216 27170 29 _ _ (2041977 / 100000) (102099 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738310400 :
    ThetaLowerSegment 738310400 738375936 (73827472799521 / 100000) (73834068414301 / 100000) := by
  exact
    packedTile32768 738310400 738375936 13 3230 27171 29 _ _ (1020993 / 50000) (2041989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738375936 :
    ThetaLowerSegment 738375936 738441472 (73834068414301 / 100000) (73840631386231 / 100000) := by
  exact
    packedTile32768 738375936 738441472 13 3214 27173 29 _ _ (408399 / 20000) (1020999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738441472 :
    ThetaLowerSegment 738441472 738507008 (73840631386231 / 100000) (73847063698831 / 100000) := by
  exact
    packedTile32768 738441472 738507008 13 3150 27174 29 _ _ (510501 / 25000) (2042007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738507008 :
    ThetaLowerSegment 738507008 738572544 (73847063698831 / 100000) (73853565468223 / 100000) := by
  exact
    packedTile32768 738507008 738572544 13 3184 27175 29 _ _ (2042013 / 100000) (63813 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738572544 :
    ThetaLowerSegment 738572544 738638080 (73853565468223 / 100000) (73860136691801 / 100000) := by
  exact
    packedTile32768 738572544 738638080 13 3218 27176 29 _ _ (2042021 / 100000) (255253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738638080 :
    ThetaLowerSegment 738638080 738703616 (73860136691801 / 100000) (73866734490731 / 100000) := by
  exact
    packedTile32768 738638080 738703616 13 3231 27177 29 _ _ (204203 / 10000) (2042033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738703616 :
    ThetaLowerSegment 738703616 738769152 (73866734490731 / 100000) (36936692705877 / 50000) := by
  exact
    packedTile32768 738703616 738769152 13 3257 27179 29 _ _ (2042039 / 100000) (1021021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738769152 :
    ThetaLowerSegment 738769152 738834688 (36936692705877 / 50000) (36940010012853 / 50000) := by
  exact
    packedTile32768 738769152 738834688 13 3249 27180 29 _ _ (63814 / 3125) (2042051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738834688 :
    ThetaLowerSegment 738834688 738900224 (36940010012853 / 50000) (73886523977251 / 100000) := by
  exact
    packedTile32768 738834688 738900224 13 3185 27181 29 _ _ (2042057 / 100000) (102103 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738900224 :
    ThetaLowerSegment 738900224 738965760 (73886523977251 / 100000) (14778611309277 / 20000) := by
  exact
    packedTile32768 738900224 738965760 13 3199 27182 29 _ _ (1021033 / 50000) (2042069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell738965760 :
    ThetaLowerSegment 738965760 739031296 (14778611309277 / 20000) (7389962181751 / 10000) := by
  exact
    packedTile32768 738965760 739031296 13 3215 27183 29 _ _ (81683 / 4000) (1021039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739031296 :
    ThetaLowerSegment 739031296 739096832 (7389962181751 / 10000) (36953029233139 / 50000) := by
  exact
    packedTile32768 739031296 739096832 13 3152 27185 29 _ _ (510521 / 25000) (2042087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739096832 :
    ThetaLowerSegment 739096832 739162368 (36953029233139 / 50000) (36956298622431 / 50000) := by
  exact
    packedTile32768 739096832 739162368 13 3202 27186 29 _ _ (510523 / 25000) (408419 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739162368 :
    ThetaLowerSegment 739162368 739227904 (36956298622431 / 50000) (73919166683779 / 100000) := by
  exact
    packedTile32768 739162368 739227904 13 3217 27187 29 _ _ (2042101 / 100000) (255263 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739227904 :
    ThetaLowerSegment 739227904 739293440 (73919166683779 / 100000) (73925754530639 / 100000) := by
  exact
    packedTile32768 739227904 739293440 13 3226 27188 29 _ _ (204211 / 10000) (2042113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739293440 :
    ThetaLowerSegment 739293440 739358976 (73925754530639 / 100000) (73932281142963 / 100000) := by
  exact
    packedTile32768 739293440 739358976 13 3196 27189 29 _ _ (2042119 / 100000) (1021061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739358976 :
    ThetaLowerSegment 739358976 739424512 (73932281142963 / 100000) (14787803624647 / 20000) := by
  exact
    packedTile32768 739358976 739424512 13 3299 27191 29 _ _ (127633 / 6250) (2042131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739424512 :
    ThetaLowerSegment 739424512 739490048 (14787803624647 / 20000) (73945495781799 / 100000) := by
  exact
    packedTile32768 739424512 739490048 13 3172 27192 29 _ _ (2042137 / 100000) (102107 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739490048 :
    ThetaLowerSegment 739490048 739555584 (73945495781799 / 100000) (73952081702649 / 100000) := by
  exact
    packedTile32768 739490048 739555584 13 3225 27193 29 _ _ (1021073 / 50000) (2042149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739555584 :
    ThetaLowerSegment 739555584 739621120 (73952081702649 / 100000) (36979295025317 / 50000) := by
  exact
    packedTile32768 739555584 739621120 13 3187 27194 29 _ _ (408431 / 20000) (1021079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739621120 :
    ThetaLowerSegment 739621120 739686656 (36979295025317 / 50000) (7396523116471 / 10000) := by
  exact
    packedTile32768 739621120 739686656 13 3252 27195 29 _ _ (2042163 / 100000) (1021083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739686656 :
    ThetaLowerSegment 739686656 739752192 (7396523116471 / 10000) (36985889184071 / 50000) := by
  exact
    packedTile32768 739686656 739752192 13 3206 27197 29 _ _ (510543 / 25000) (81687 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739752192 :
    ThetaLowerSegment 739752192 739817728 (36985889184071 / 50000) (36989173011119 / 50000) := by
  exact
    packedTile32768 739752192 739817728 13 3216 27198 29 _ _ (2042181 / 100000) (255273 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739817728 :
    ThetaLowerSegment 739817728 739883264 (36989173011119 / 50000) (36992485443299 / 50000) := by
  exact
    packedTile32768 739817728 739883264 13 3244 27199 29 _ _ (204219 / 10000) (2042193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739883264 :
    ThetaLowerSegment 739883264 739948800 (36992485443299 / 50000) (73991569231567 / 100000) := by
  exact
    packedTile32768 739883264 739948800 13 3231 27200 29 _ _ (2042199 / 100000) (1021101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell739948800 :
    ThetaLowerSegment 739948800 740014336 (73991569231567 / 100000) (73998128803663 / 100000) := by
  exact
    packedTile32768 739948800 740014336 13 3212 27201 29 _ _ (63819 / 3125) (2042211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740014336 :
    ThetaLowerSegment 740014336 740079872 (73998128803663 / 100000) (74004684320233 / 100000) := by
  exact
    packedTile32768 740014336 740079872 13 3210 27203 29 _ _ (2042217 / 100000) (102111 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740079872 :
    ThetaLowerSegment 740079872 740145408 (74004684320233 / 100000) (74011137751233 / 100000) := by
  exact
    packedTile32768 740079872 740145408 13 3160 27204 29 _ _ (81689 / 4000) (510557 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740145408 :
    ThetaLowerSegment 740145408 740210944 (74011137751233 / 100000) (74017703533543 / 100000) := by
  exact
    packedTile32768 740145408 740210944 13 3215 27205 29 _ _ (1021117 / 50000) (2042237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740210944 :
    ThetaLowerSegment 740210944 740276480 (74017703533543 / 100000) (4626519386853 / 6250) := by
  exact
    packedTile32768 740210944 740276480 13 3235 27206 29 _ _ (2042243 / 100000) (1021123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740276480 :
    ThetaLowerSegment 740276480 740342016 (4626519386853 / 6250) (1850770420113 / 2500) := by
  exact
    packedTile32768 740276480 740342016 13 3186 27208 29 _ _ (510563 / 25000) (408451 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740342016 :
    ThetaLowerSegment 740342016 740407552 (1850770420113 / 2500) (74037411265289 / 100000) := by
  exact
    packedTile32768 740342016 740407552 13 3229 27209 29 _ _ (2042261 / 100000) (255283 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740407552 :
    ThetaLowerSegment 740407552 740473088 (74037411265289 / 100000) (74044052727329 / 100000) := by
  exact
    packedTile32768 740407552 740473088 13 3252 27210 29 _ _ (204227 / 10000) (2042273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740473088 :
    ThetaLowerSegment 740473088 740538624 (74044052727329 / 100000) (2962022050237 / 4000) := by
  exact
    packedTile32768 740473088 740538624 13 3182 27211 29 _ _ (1021139 / 50000) (2042281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740538624 :
    ThetaLowerSegment 740538624 740604160 (2962022050237 / 4000) (7405711720863 / 10000) := by
  exact
    packedTile32768 740538624 740604160 13 3215 27212 29 _ _ (2042287 / 100000) (204229 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740604160 :
    ThetaLowerSegment 740604160 740669696 (7405711720863 / 10000) (1481272846887 / 2000) := by
  exact
    packedTile32768 740604160 740669696 13 3195 27214 29 _ _ (255287 / 12500) (2042299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740669696 :
    ThetaLowerSegment 740669696 740735232 (1481272846887 / 2000) (1481406005173 / 2000) := by
  exact
    packedTile32768 740669696 740735232 13 3260 27215 29 _ _ (408461 / 20000) (510577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740735232 :
    ThetaLowerSegment 740735232 740800768 (1481406005173 / 2000) (18519219638011 / 25000) := by
  exact
    packedTile32768 740735232 740800768 13 3221 27216 29 _ _ (1021157 / 50000) (2042317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740800768 :
    ThetaLowerSegment 740800768 740866304 (18519219638011 / 25000) (74083440535843 / 100000) := by
  exact
    packedTile32768 740800768 740866304 13 3213 27217 29 _ _ (2042323 / 100000) (1021163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740866304 :
    ThetaLowerSegment 740866304 740931840 (74083440535843 / 100000) (74089953532591 / 100000) := by
  exact
    packedTile32768 740866304 740931840 13 3189 27218 29 _ _ (510583 / 25000) (408467 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740931840 :
    ThetaLowerSegment 740931840 740997376 (74089953532591 / 100000) (74096491062931 / 100000) := by
  exact
    packedTile32768 740931840 740997376 13 3201 27220 29 _ _ (102117 / 5000) (2042343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell740997376 :
    ThetaLowerSegment 740997376 741062912 (74096491062931 / 100000) (3705153473453 / 5000) := by
  exact
    packedTile32768 740997376 741062912 13 3221 27221 29 _ _ (2042349 / 100000) (127647 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741062912 :
    ThetaLowerSegment 741062912 741128448 (3705153473453 / 5000) (18527395126591 / 25000) := by
  exact
    packedTile32768 741062912 741128448 13 3188 27222 29 _ _ (1021179 / 50000) (2042361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741128448 :
    ThetaLowerSegment 741128448 741193984 (18527395126591 / 25000) (2316132456962 / 3125) := by
  exact
    packedTile32768 741128448 741193984 13 3260 27223 29 _ _ (2042367 / 100000) (204237 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741193984 :
    ThetaLowerSegment 741193984 741259520 (2316132456962 / 3125) (9265357756019 / 12500) := by
  exact
    packedTile32768 741193984 741259520 13 3243 27224 29 _ _ (255297 / 12500) (2042379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741259520 :
    ThetaLowerSegment 741259520 741325056 (9265357756019 / 12500) (74129452824547 / 100000) := by
  exact
    packedTile32768 741259520 741325056 13 3227 27226 29 _ _ (408477 / 20000) (510597 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741325056 :
    ThetaLowerSegment 741325056 741390592 (74129452824547 / 100000) (1482722669841 / 2000) := by
  exact
    packedTile32768 741325056 741390592 13 3271 27227 29 _ _ (2042393 / 100000) (510599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741390592 :
    ThetaLowerSegment 741390592 741456128 (1482722669841 / 2000) (37071401988491 / 50000) := by
  exact
    packedTile32768 741390592 741456128 13 3266 27228 29 _ _ (1021201 / 50000) (408481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741456128 :
    ThetaLowerSegment 741456128 741521664 (37071401988491 / 50000) (9268668993331 / 12500) := by
  exact
    packedTile32768 741456128 741521664 13 3206 27229 29 _ _ (2042411 / 100000) (1021207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741521664 :
    ThetaLowerSegment 741521664 741587200 (9268668993331 / 12500) (18538982645367 / 25000) := by
  exact
    packedTile32768 741521664 741587200 13 3221 27230 29 _ _ (102121 / 5000) (2042423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741587200 :
    ThetaLowerSegment 741587200 741652736 (18538982645367 / 25000) (14832482241737 / 20000) := by
  exact
    packedTile32768 741587200 741652736 13 3173 27232 29 _ _ (2042429 / 100000) (63826 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741652736 :
    ThetaLowerSegment 741652736 741718272 (14832482241737 / 20000) (74168942925409 / 100000) := by
  exact
    packedTile32768 741652736 741718272 13 3198 27233 29 _ _ (1021219 / 50000) (2042441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741718272 :
    ThetaLowerSegment 741718272 741783808 (74168942925409 / 100000) (37087771035833 / 50000) := by
  exact
    packedTile32768 741718272 741783808 13 3231 27234 29 _ _ (2042447 / 100000) (40849 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741783808 :
    ThetaLowerSegment 741783808 741849344 (37087771035833 / 50000) (37091067558203 / 50000) := by
  exact
    packedTile32768 741783808 741849344 13 3228 27235 29 _ _ (408491 / 20000) (1021229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741849344 :
    ThetaLowerSegment 741849344 741914880 (37091067558203 / 50000) (37094354904011 / 50000) := by
  exact
    packedTile32768 741849344 741914880 13 3219 27236 29 _ _ (63827 / 3125) (2042467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741914880 :
    ThetaLowerSegment 741914880 741980416 (37094354904011 / 50000) (4637200049201 / 6250) := by
  exact
    packedTile32768 741914880 741980416 13 3178 27238 29 _ _ (2042473 / 100000) (510619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell741980416 :
    ThetaLowerSegment 741980416 742045952 (4637200049201 / 6250) (37100912278171 / 50000) := by
  exact
    packedTile32768 741980416 742045952 13 3243 27239 29 _ _ (1021241 / 50000) (408497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742045952 :
    ThetaLowerSegment 742045952 742111488 (37100912278171 / 50000) (37104151668897 / 50000) := by
  exact
    packedTile32768 742045952 742111488 13 3172 27240 29 _ _ (2042491 / 100000) (1021247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742111488 :
    ThetaLowerSegment 742111488 742177024 (37104151668897 / 50000) (37107466646397 / 50000) := by
  exact
    packedTile32768 742111488 742177024 13 3246 27241 29 _ _ (817 / 40) (2042503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742177024 :
    ThetaLowerSegment 742177024 742242560 (37107466646397 / 50000) (1484429672319 / 2000) := by
  exact
    packedTile32768 742177024 742242560 13 3207 27242 29 _ _ (510627 / 25000) (2042511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742242560 :
    ThetaLowerSegment 742242560 742308096 (1484429672319 / 2000) (74228062563207 / 100000) := by
  exact
    packedTile32768 742242560 742308096 13 3221 27244 29 _ _ (2042517 / 100000) (51063 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742308096 :
    ThetaLowerSegment 742308096 742373632 (74228062563207 / 100000) (118775416659 / 160) := by
  exact
    packedTile32768 742308096 742373632 13 3218 27245 29 _ _ (1021263 / 50000) (2042529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742373632 :
    ThetaLowerSegment 742373632 742439168 (118775416659 / 160) (3712061742123 / 5000) := by
  exact
    packedTile32768 742373632 742439168 13 3231 27246 29 _ _ (408507 / 20000) (1021269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742439168 :
    ThetaLowerSegment 742439168 742504704 (3712061742123 / 5000) (3712391612979 / 5000) := by
  exact
    packedTile32768 742439168 742504704 13 3230 27247 29 _ _ (127659 / 6250) (2042547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742504704 :
    ThetaLowerSegment 742504704 742570240 (3712391612979 / 5000) (18563577297993 / 25000) := by
  exact
    packedTile32768 742504704 742570240 13 3171 27248 29 _ _ (255319 / 12500) (408511 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742570240 :
    ThetaLowerSegment 742570240 742635776 (18563577297993 / 25000) (74260798408269 / 100000) := by
  exact
    packedTile32768 742570240 742635776 13 3177 27250 29 _ _ (2042561 / 100000) (510641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742635776 :
    ThetaLowerSegment 742635776 742701312 (74260798408269 / 100000) (74267348930259 / 100000) := by
  exact
    packedTile32768 742635776 742701312 13 3207 27251 29 _ _ (204257 / 10000) (2042573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742701312 :
    ThetaLowerSegment 742701312 742766848 (74267348930259 / 100000) (74273848416637 / 100000) := by
  exact
    packedTile32768 742701312 742766848 13 3182 27252 29 _ _ (2042579 / 100000) (1021291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742766848 :
    ThetaLowerSegment 742766848 742832384 (74273848416637 / 100000) (74280429635173 / 100000) := by
  exact
    packedTile32768 742766848 742832384 13 3222 27253 29 _ _ (510647 / 25000) (2042591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742832384 :
    ThetaLowerSegment 742832384 742897920 (74280429635173 / 100000) (74286908752857 / 100000) := by
  exact
    packedTile32768 742832384 742897920 13 3172 27254 29 _ _ (2042597 / 100000) (10213 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742897920 :
    ThetaLowerSegment 742897920 742963456 (74286908752857 / 100000) (37146743991781 / 50000) := by
  exact
    packedTile32768 742897920 742963456 13 3221 27256 29 _ _ (408521 / 20000) (127663 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell742963456 :
    ThetaLowerSegment 742963456 743028992 (37146743991781 / 50000) (3714999889719 / 5000) := by
  exact
    packedTile32768 742963456 743028992 13 3187 27257 29 _ _ (1021307 / 50000) (2042617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743028992 :
    ThetaLowerSegment 743028992 743094528 (3714999889719 / 5000) (74306479037159 / 100000) := by
  exact
    packedTile32768 743028992 743094528 13 3173 27258 29 _ _ (2042623 / 100000) (1021313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743094528 :
    ThetaLowerSegment 743094528 743160064 (74306479037159 / 100000) (74313005246399 / 100000) := by
  exact
    packedTile32768 743094528 743160064 13 3195 27259 29 _ _ (255329 / 12500) (408527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743160064 :
    ThetaLowerSegment 743160064 743225600 (74313005246399 / 100000) (74319504930061 / 100000) := by
  exact
    packedTile32768 743160064 743225600 13 3182 27260 29 _ _ (2042641 / 100000) (510661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743225600 :
    ThetaLowerSegment 743225600 743291136 (74319504930061 / 100000) (74326037324761 / 100000) := by
  exact
    packedTile32768 743225600 743291136 13 3198 27262 29 _ _ (40853 / 2000) (2042653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743291136 :
    ThetaLowerSegment 743291136 743356672 (74326037324761 / 100000) (74332530934543 / 100000) := by
  exact
    packedTile32768 743291136 743356672 13 3179 27263 29 _ _ (1021329 / 50000) (2042661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743356672 :
    ThetaLowerSegment 743356672 743422208 (74332530934543 / 100000) (74339149175623 / 100000) := by
  exact
    packedTile32768 743356672 743422208 13 3240 27264 29 _ _ (2042667 / 100000) (204267 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743422208 :
    ThetaLowerSegment 743422208 743487744 (74339149175623 / 100000) (74345712293611 / 100000) := by
  exact
    packedTile32768 743422208 743487744 13 3213 27265 29 _ _ (510669 / 25000) (2042679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743487744 :
    ThetaLowerSegment 743487744 743553280 (74345712293611 / 100000) (37176107079983 / 50000) := by
  exact
    packedTile32768 743487744 743553280 13 3183 27266 29 _ _ (408537 / 20000) (63834 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743553280 :
    ThetaLowerSegment 743553280 743618816 (37176107079983 / 50000) (743588753851 / 1000) := by
  exact
    packedTile32768 743553280 743618816 13 3261 27268 29 _ _ (1021347 / 50000) (2042697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743618816 :
    ThetaLowerSegment 743618816 743684352 (743588753851 / 1000) (1487307219279 / 2000) := by
  exact
    packedTile32768 743618816 743684352 13 3175 27269 29 _ _ (1021351 / 50000) (408541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743684352 :
    ThetaLowerSegment 743684352 743749888 (1487307219279 / 2000) (3718595903313 / 5000) := by
  exact
    packedTile32768 743684352 743749888 13 3210 27270 29 _ _ (2042711 / 100000) (1021357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743749888 :
    ThetaLowerSegment 743749888 743815424 (3718595903313 / 5000) (3718919163753 / 5000) := by
  exact
    packedTile32768 743749888 743815424 13 3165 27271 29 _ _ (12767 / 625) (2042723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743815424 :
    ThetaLowerSegment 743815424 743880960 (3718919163753 / 5000) (14876969702469 / 20000) := by
  exact
    packedTile32768 743815424 743880960 13 3165 27272 29 _ _ (2042729 / 100000) (510683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743880960 :
    ThetaLowerSegment 743880960 743946496 (14876969702469 / 20000) (14878272969313 / 20000) := by
  exact
    packedTile32768 743880960 743946496 13 3190 27274 29 _ _ (1021369 / 50000) (2042741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell743946496 :
    ThetaLowerSegment 743946496 744012032 (14878272969313 / 20000) (74397997642827 / 100000) := by
  exact
    packedTile32768 743946496 744012032 13 3247 27275 29 _ _ (1021373 / 50000) (2042749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744012032 :
    ThetaLowerSegment 744012032 744077568 (74397997642827 / 100000) (74404522202297 / 100000) := by
  exact
    packedTile32768 744012032 744077568 13 3194 27276 29 _ _ (408551 / 20000) (1021379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744077568 :
    ThetaLowerSegment 744077568 744143104 (74404522202297 / 100000) (14882218754817 / 20000) := by
  exact
    packedTile32768 744077568 744143104 13 3217 27277 29 _ _ (510691 / 25000) (2042767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744143104 :
    ThetaLowerSegment 744143104 744208640 (14882218754817 / 20000) (37208836772959 / 50000) := by
  exact
    packedTile32768 744143104 744208640 13 3221 27278 29 _ _ (2042773 / 100000) (255347 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744208640 :
    ThetaLowerSegment 744208640 744274176 (37208836772959 / 50000) (18606065379467 / 25000) := by
  exact
    packedTile32768 744208640 744274176 13 3225 27280 29 _ _ (1021391 / 50000) (408557 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744274176 :
    ThetaLowerSegment 744274176 744339712 (18606065379467 / 25000) (9303850827529 / 12500) := by
  exact
    packedTile32768 744274176 744339712 13 3204 27281 29 _ _ (2042791 / 100000) (1021397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744339712 :
    ThetaLowerSegment 744339712 744405248 (9303850827529 / 12500) (74437353791027 / 100000) := by
  exact
    packedTile32768 744339712 744405248 13 3205 27282 29 _ _ (2042799 / 100000) (1021401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744405248 :
    ThetaLowerSegment 744405248 744470784 (74437353791027 / 100000) (74443911204707 / 100000) := by
  exact
    packedTile32768 744405248 744470784 13 3210 27283 29 _ _ (255351 / 12500) (2042811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744470784 :
    ThetaLowerSegment 744470784 744536320 (74443911204707 / 100000) (2978014169981 / 4000) := by
  exact
    packedTile32768 744470784 744536320 13 3154 27284 29 _ _ (2042817 / 100000) (102141 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744536320 :
    ThetaLowerSegment 744536320 744601856 (2978014169981 / 4000) (14891382344197 / 20000) := by
  exact
    packedTile32768 744536320 744601856 13 3210 27286 29 _ _ (1021413 / 50000) (2042829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744601856 :
    ThetaLowerSegment 744601856 744667392 (14891382344197 / 20000) (14892724895359 / 20000) := by
  exact
    packedTile32768 744601856 744667392 13 3286 27287 29 _ _ (408567 / 20000) (1021419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744667392 :
    ThetaLowerSegment 744667392 744732928 (14892724895359 / 20000) (74470137060279 / 100000) := by
  exact
    packedTile32768 744667392 744732928 13 3188 27288 29 _ _ (2042843 / 100000) (1021423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744732928 :
    ThetaLowerSegment 744732928 744798464 (74470137060279 / 100000) (74476612901119 / 100000) := by
  exact
    packedTile32768 744732928 744798464 13 3170 27289 29 _ _ (510713 / 25000) (408571 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744798464 :
    ThetaLowerSegment 744798464 744864000 (74476612901119 / 100000) (14896624291253 / 20000) := by
  exact
    packedTile32768 744798464 744864000 13 3186 27290 29 _ _ (2042861 / 100000) (127679 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744864000 :
    ThetaLowerSegment 744864000 744929536 (14896624291253 / 20000) (2979587816477 / 4000) := by
  exact
    packedTile32768 744864000 744929536 13 3218 27292 29 _ _ (204287 / 10000) (2042873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744929536 :
    ThetaLowerSegment 744929536 744995072 (2979587816477 / 4000) (37248127548197 / 50000) := by
  exact
    packedTile32768 744929536 744995072 13 3211 27293 29 _ _ (2042879 / 100000) (1021441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell744995072 :
    ThetaLowerSegment 744995072 745060608 (37248127548197 / 50000) (74502831149647 / 100000) := by
  exact
    packedTile32768 744995072 745060608 13 3219 27294 29 _ _ (2042887 / 100000) (204289 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745060608 :
    ThetaLowerSegment 745060608 745126144 (74502831149647 / 100000) (74509413360559 / 100000) := by
  exact
    packedTile32768 745060608 745126144 13 3222 27295 29 _ _ (127681 / 6250) (2042899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745126144 :
    ThetaLowerSegment 745126144 745191680 (74509413360559 / 100000) (74515791309969 / 100000) := by
  exact
    packedTile32768 745126144 745191680 13 3122 27296 29 _ _ (408581 / 20000) (510727 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745191680 :
    ThetaLowerSegment 745191680 745257216 (74515791309969 / 100000) (74522320463113 / 100000) := by
  exact
    packedTile32768 745191680 745257216 13 3196 27298 29 _ _ (1021457 / 50000) (2042917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745257216 :
    ThetaLowerSegment 745257216 745322752 (74522320463113 / 100000) (74528894586109 / 100000) := by
  exact
    packedTile32768 745257216 745322752 13 3218 27299 29 _ _ (1021461 / 50000) (81717 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745322752 :
    ThetaLowerSegment 745322752 745339136 (74528894586109 / 100000) (931631637173 / 1250) := by
  exact
    packedTile32768 745322752 745339136 11 801 27300 29 _ _ (2042931 / 100000) (1021467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell745339136 :
    ThetaLowerSegment 745339136 745341184 (931631637173 / 1250) (465816840053 / 625) := by
  exact
    packedTile32768 745339136 745341184 8 80 27300 29 _ _ (2042933 / 100000) (255367 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_713341184_745341184 :
    ThetaLowerSegment 713341184 745341184 (35665746715099 / 50000) (465816840053 / 625) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell713341184 cell713406720)
                    (ThetaLowerSegment.join cell713472256 cell713537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell713603328 cell713668864)
                    (ThetaLowerSegment.join cell713734400 cell713799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell713865472 cell713931008)
                    (ThetaLowerSegment.join cell713996544 cell714062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell714127616 cell714193152)
                    (ThetaLowerSegment.join cell714258688 cell714324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell714389760 cell714455296)
                    (ThetaLowerSegment.join cell714520832 cell714586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell714651904 cell714717440)
                    (ThetaLowerSegment.join cell714782976 cell714848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell714914048 cell714979584)
                    (ThetaLowerSegment.join cell715045120 cell715110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell715176192 cell715241728)
                    (ThetaLowerSegment.join cell715307264 cell715372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell715438336 cell715503872)
                    (ThetaLowerSegment.join cell715569408 cell715634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell715700480 cell715766016)
                    (ThetaLowerSegment.join cell715831552 cell715897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell715962624 cell716028160)
                    (ThetaLowerSegment.join cell716093696 cell716159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell716224768 cell716290304)
                    (ThetaLowerSegment.join cell716355840 cell716421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell716486912 cell716552448)
                    (ThetaLowerSegment.join cell716617984 cell716683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell716749056 cell716814592)
                    (ThetaLowerSegment.join cell716880128 cell716945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell717011200 cell717076736)
                    (ThetaLowerSegment.join cell717142272 cell717207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell717273344 cell717338880)
                    (ThetaLowerSegment.join cell717404416 cell717469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell717535488 cell717601024)
                    (ThetaLowerSegment.join cell717666560 cell717732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell717797632 cell717863168)
                    (ThetaLowerSegment.join cell717928704 cell717994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell718059776 cell718125312)
                    (ThetaLowerSegment.join cell718190848 cell718256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell718321920 cell718387456)
                    (ThetaLowerSegment.join cell718452992 cell718518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell718584064 cell718649600)
                    (ThetaLowerSegment.join cell718715136 cell718780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell718846208 cell718911744)
                    (ThetaLowerSegment.join cell718977280 cell719042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell719108352 cell719173888)
                    (ThetaLowerSegment.join cell719239424 cell719304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell719370496 cell719436032)
                    (ThetaLowerSegment.join cell719501568 cell719567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell719632640 cell719698176)
                    (ThetaLowerSegment.join cell719763712 cell719829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell719894784 cell719960320)
                    (ThetaLowerSegment.join cell720025856 cell720091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell720156928 cell720222464)
                    (ThetaLowerSegment.join cell720288000 cell720353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell720419072 cell720484608)
                    (ThetaLowerSegment.join cell720550144 cell720615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell720681216 cell720746752)
                    (ThetaLowerSegment.join cell720812288 cell720877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell720943360 cell721008896)
                    (ThetaLowerSegment.join cell721074432 cell721139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell721205504 cell721271040)
                    (ThetaLowerSegment.join cell721336576 cell721402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell721467648 cell721533184)
                    (ThetaLowerSegment.join cell721598720 cell721664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell721729792 cell721795328)
                    (ThetaLowerSegment.join cell721860864 cell721926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell721991936 cell722057472)
                    (ThetaLowerSegment.join cell722123008 cell722188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell722254080 cell722319616)
                    (ThetaLowerSegment.join cell722385152 cell722450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell722516224 cell722581760)
                    (ThetaLowerSegment.join cell722647296 cell722712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell722778368 cell722843904)
                    (ThetaLowerSegment.join cell722909440 cell722974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell723040512 cell723106048)
                    (ThetaLowerSegment.join cell723171584 cell723237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell723302656 cell723368192)
                    (ThetaLowerSegment.join cell723433728 cell723499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell723564800 cell723630336)
                    (ThetaLowerSegment.join cell723695872 cell723761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell723826944 cell723892480)
                    (ThetaLowerSegment.join cell723958016 cell724023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell724089088 cell724154624)
                    (ThetaLowerSegment.join cell724220160 cell724285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell724351232 cell724416768)
                    (ThetaLowerSegment.join cell724482304 cell724547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell724613376 cell724678912)
                    (ThetaLowerSegment.join cell724744448 cell724809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell724875520 cell724941056)
                    (ThetaLowerSegment.join cell725006592 cell725072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell725137664 cell725203200)
                    (ThetaLowerSegment.join cell725268736 cell725334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell725399808 cell725465344)
                    (ThetaLowerSegment.join cell725530880 cell725596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell725661952 cell725727488)
                    (ThetaLowerSegment.join cell725793024 cell725858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell725924096 cell725989632)
                    (ThetaLowerSegment.join cell726055168 cell726120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell726186240 cell726251776)
                    (ThetaLowerSegment.join cell726317312 cell726382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell726448384 cell726513920)
                    (ThetaLowerSegment.join cell726579456 cell726644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell726710528 cell726776064)
                    (ThetaLowerSegment.join cell726841600 cell726907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell726972672 cell727038208)
                    (ThetaLowerSegment.join cell727103744 cell727169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell727234816 cell727300352)
                    (ThetaLowerSegment.join cell727365888 cell727431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell727496960 cell727562496)
                    (ThetaLowerSegment.join cell727628032 cell727693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell727759104 cell727824640)
                    (ThetaLowerSegment.join cell727890176 cell727955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell728021248 cell728086784)
                    (ThetaLowerSegment.join cell728152320 cell728217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell728283392 cell728348928)
                    (ThetaLowerSegment.join cell728414464 cell728480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell728545536 cell728611072)
                    (ThetaLowerSegment.join cell728676608 cell728742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell728807680 cell728873216)
                    (ThetaLowerSegment.join cell728938752 cell729004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell729069824 cell729135360)
                    (ThetaLowerSegment.join cell729200896 cell729266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell729331968 cell729397504)
                    (ThetaLowerSegment.join cell729463040 cell729528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell729594112 cell729659648)
                    (ThetaLowerSegment.join cell729725184 cell729790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell729856256 cell729921792)
                    (ThetaLowerSegment.join cell729987328 cell730052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell730118400 cell730183936)
                    (ThetaLowerSegment.join cell730249472 cell730315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell730380544 cell730446080)
                    (ThetaLowerSegment.join cell730511616 cell730577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell730642688 cell730708224)
                    (ThetaLowerSegment.join cell730773760 cell730839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell730904832 cell730970368)
                    (ThetaLowerSegment.join cell731035904 cell731101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell731166976 cell731232512)
                    (ThetaLowerSegment.join cell731298048 cell731363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell731429120 cell731494656)
                    (ThetaLowerSegment.join cell731560192 cell731625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell731691264 cell731756800)
                    (ThetaLowerSegment.join cell731822336 cell731887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell731953408 cell732018944)
                    (ThetaLowerSegment.join cell732084480 cell732150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell732215552 cell732281088)
                    (ThetaLowerSegment.join cell732346624 cell732412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell732477696 cell732543232)
                    (ThetaLowerSegment.join cell732608768 cell732674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell732739840 cell732805376)
                    (ThetaLowerSegment.join cell732870912 cell732936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell733001984 cell733067520)
                    (ThetaLowerSegment.join cell733133056 cell733198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell733264128 cell733329664)
                    (ThetaLowerSegment.join cell733395200 cell733460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell733526272 cell733591808)
                    (ThetaLowerSegment.join cell733657344 cell733722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell733788416 cell733853952)
                    (ThetaLowerSegment.join cell733919488 cell733985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell734050560 cell734116096)
                    (ThetaLowerSegment.join cell734181632 cell734247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell734312704 cell734378240)
                    (ThetaLowerSegment.join cell734443776 cell734509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell734574848 cell734640384)
                    (ThetaLowerSegment.join cell734705920 cell734771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell734836992 cell734902528)
                    (ThetaLowerSegment.join cell734968064 cell735033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell735099136 cell735164672)
                    (ThetaLowerSegment.join cell735230208 cell735295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell735361280 cell735426816)
                    (ThetaLowerSegment.join cell735492352 cell735557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell735623424 cell735688960)
                    (ThetaLowerSegment.join cell735754496 cell735820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell735885568 cell735951104)
                    (ThetaLowerSegment.join cell736016640 cell736082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell736147712 cell736213248)
                    (ThetaLowerSegment.join cell736278784 cell736344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell736409856 cell736475392)
                    (ThetaLowerSegment.join cell736540928 cell736606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell736672000 cell736737536)
                    (ThetaLowerSegment.join cell736803072 cell736868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell736934144 cell736999680)
                    (ThetaLowerSegment.join cell737065216 cell737130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell737196288 cell737261824)
                    (ThetaLowerSegment.join cell737327360 cell737392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell737458432 cell737523968)
                    (ThetaLowerSegment.join cell737589504 cell737655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell737720576 cell737786112)
                    (ThetaLowerSegment.join cell737851648 cell737917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell737982720 cell738048256)
                    (ThetaLowerSegment.join cell738113792 cell738179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell738244864 cell738310400)
                    (ThetaLowerSegment.join cell738375936 cell738441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell738507008 cell738572544)
                    (ThetaLowerSegment.join cell738638080 cell738703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell738769152 cell738834688)
                    (ThetaLowerSegment.join cell738900224 cell738965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell739031296 cell739096832)
                    (ThetaLowerSegment.join cell739162368 cell739227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell739293440 cell739358976)
                    (ThetaLowerSegment.join cell739424512 cell739490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell739555584 cell739621120)
                    (ThetaLowerSegment.join cell739686656 cell739752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell739817728 cell739883264)
                    (ThetaLowerSegment.join cell739948800 cell740014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell740079872 cell740145408)
                    (ThetaLowerSegment.join cell740210944 cell740276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell740342016 cell740407552)
                    (ThetaLowerSegment.join cell740473088 cell740538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell740604160 cell740669696)
                    (ThetaLowerSegment.join cell740735232 cell740800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell740866304 cell740931840)
                    (ThetaLowerSegment.join cell740997376 cell741062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell741128448 cell741193984)
                    (ThetaLowerSegment.join cell741259520 cell741325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell741390592 cell741456128)
                    (ThetaLowerSegment.join cell741521664 cell741587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell741652736 cell741718272)
                    (ThetaLowerSegment.join cell741783808 cell741849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell741914880 cell741980416)
                    (ThetaLowerSegment.join cell742045952 cell742111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell742177024 cell742242560)
                    (ThetaLowerSegment.join cell742308096 cell742373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell742439168 cell742504704)
                    (ThetaLowerSegment.join cell742570240 cell742635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell742701312 cell742766848)
                    (ThetaLowerSegment.join cell742832384 cell742897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell742963456 cell743028992)
                    (ThetaLowerSegment.join cell743094528 cell743160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell743225600 cell743291136)
                    (ThetaLowerSegment.join cell743356672 cell743422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell743487744 cell743553280)
                    (ThetaLowerSegment.join cell743618816 cell743684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell743749888 cell743815424)
                    (ThetaLowerSegment.join cell743880960 cell743946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell744012032 cell744077568)
                    (ThetaLowerSegment.join cell744143104 cell744208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell744274176 cell744339712)
                    (ThetaLowerSegment.join cell744405248 cell744470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell744536320 cell744601856)
                    (ThetaLowerSegment.join cell744667392 cell744732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell744798464 cell744864000)
                  (ThetaLowerSegment.join cell744929536 cell744995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell745060608 cell745126144)
                  (ThetaLowerSegment.join cell745191680 cell745257216)))
              (ThetaLowerSegment.join cell745322752 cell745339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
