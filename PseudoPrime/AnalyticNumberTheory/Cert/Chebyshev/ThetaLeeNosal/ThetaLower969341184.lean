/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 969341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell937341184 :
    ThetaLowerSegment 937341184 937406720 (46864982813727 / 50000) (23434121882133 / 25000) := by
  exact
    packedTile32768 937341184 937406720 13 3157 30616 30 _ _ (1032927 / 50000) (2065857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937406720 :
    ThetaLowerSegment 937406720 937472256 (23434121882133 / 25000) (93743108613037 / 100000) := by
  exact
    packedTile32768 937406720 937472256 13 3205 30617 30 _ _ (2065861 / 100000) (258233 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937472256 :
    ThetaLowerSegment 937472256 937537792 (93743108613037 / 100000) (749997193209 / 800) := by
  exact
    packedTile32768 937472256 937537792 13 3166 30618 30 _ _ (516467 / 25000) (2065871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937537792 :
    ThetaLowerSegment 937537792 937603328 (749997193209 / 800) (187512639723 / 200) := by
  exact
    packedTile32768 937537792 937603328 13 3229 30619 30 _ _ (16527 / 800) (1032939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937603328 :
    ThetaLowerSegment 937603328 937668864 (187512639723 / 200) (2344068618863 / 2500) := by
  exact
    packedTile32768 937603328 937668864 13 3110 30620 30 _ _ (1032941 / 50000) (413177 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937668864 :
    ThetaLowerSegment 937668864 937734400 (2344068618863 / 2500) (93769287424983 / 100000) := by
  exact
    packedTile32768 937668864 937734400 13 3167 30621 30 _ _ (2065889 / 100000) (516473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937734400 :
    ThetaLowerSegment 937734400 937799936 (93769287424983 / 100000) (18755176353003 / 20000) := by
  exact
    packedTile32768 937734400 937799936 13 3192 30622 30 _ _ (258237 / 12500) (2065899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937799936 :
    ThetaLowerSegment 937799936 937865472 (18755176353003 / 20000) (18756469608281 / 20000) := by
  exact
    packedTile32768 937799936 937865472 13 3130 30623 30 _ _ (2065903 / 100000) (1032953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937865472 :
    ThetaLowerSegment 937865472 937931008 (18756469608281 / 20000) (18757769065671 / 20000) := by
  exact
    packedTile32768 937865472 937931008 13 3145 30624 30 _ _ (206591 / 10000) (2065913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937931008 :
    ThetaLowerSegment 937931008 937996544 (18757769065671 / 20000) (23448850120749 / 25000) := by
  exact
    packedTile32768 937931008 937996544 13 3173 30625 30 _ _ (2065917 / 100000) (12912 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937996544 :
    ThetaLowerSegment 937996544 938062080 (23448850120749 / 25000) (4690098092881 / 5000) := by
  exact
    packedTile32768 937996544 938062080 13 3176 30626 30 _ _ (516481 / 25000) (2065927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938062080 :
    ThetaLowerSegment 938062080 938127616 (4690098092881 / 5000) (46904325671099 / 50000) := by
  exact
    packedTile32768 938062080 938127616 13 3238 30627 30 _ _ (2065931 / 100000) (1032967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938127616 :
    ThetaLowerSegment 938127616 938193152 (46904325671099 / 50000) (46907565061883 / 50000) := by
  exact
    packedTile32768 938127616 938193152 13 3136 30628 30 _ _ (1032969 / 50000) (2065941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938193152 :
    ThetaLowerSegment 938193152 938258688 (46907565061883 / 50000) (93821697762921 / 100000) := by
  exact
    packedTile32768 938193152 938258688 13 3179 30629 30 _ _ (413189 / 20000) (516487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938258688 :
    ThetaLowerSegment 938258688 938324224 (93821697762921 / 100000) (93828222039337 / 100000) := by
  exact
    packedTile32768 938258688 938324224 13 3158 30631 30 _ _ (64561 / 3125) (413191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938324224 :
    ThetaLowerSegment 938324224 938389760 (93828222039337 / 100000) (11729344066967 / 12500) := by
  exact
    packedTile32768 938324224 938389760 13 3161 30632 30 _ _ (2065959 / 100000) (1032981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938389760 :
    ThetaLowerSegment 938389760 938455296 (11729344066967 / 12500) (46920643593097 / 50000) := by
  exact
    packedTile32768 938389760 938455296 13 3163 30633 30 _ _ (1032983 / 50000) (2065969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938455296 :
    ThetaLowerSegment 938455296 938520832 (46920643593097 / 50000) (117309929689 / 125) := by
  exact
    packedTile32768 938455296 938520832 13 3222 30634 30 _ _ (2065973 / 100000) (258247 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938520832 :
    ThetaLowerSegment 938520832 938586368 (117309929689 / 125) (586590141653 / 625) := by
  exact
    packedTile32768 938520832 938586368 13 3136 30635 30 _ _ (103299 / 5000) (2065983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938586368 :
    ThetaLowerSegment 938586368 938651904 (586590141653 / 625) (46930514845453 / 50000) := by
  exact
    packedTile32768 938586368 938651904 13 3198 30636 30 _ _ (2065987 / 100000) (206599 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938651904 :
    ThetaLowerSegment 938651904 938717440 (46930514845453 / 50000) (9386757062791 / 10000) := by
  exact
    packedTile32768 938651904 938717440 13 3166 30637 30 _ _ (1032997 / 50000) (2065997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938717440 :
    ThetaLowerSegment 938717440 938782976 (9386757062791 / 10000) (18774826036217 / 20000) := by
  exact
    packedTile32768 938717440 938782976 13 3175 30638 30 _ _ (2066001 / 100000) (516501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938782976 :
    ThetaLowerSegment 938782976 938848512 (18774826036217 / 20000) (93880625710237 / 100000) := by
  exact
    packedTile32768 938782976 938848512 13 3144 30639 30 _ _ (258251 / 12500) (2066011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938848512 :
    ThetaLowerSegment 938848512 938914048 (93880625710237 / 100000) (93887203901997 / 100000) := by
  exact
    packedTile32768 938848512 938914048 13 3184 30640 30 _ _ (413203 / 20000) (1033009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938914048 :
    ThetaLowerSegment 938914048 938979584 (93887203901997 / 100000) (18778764687297 / 20000) := by
  exact
    packedTile32768 938914048 938979584 13 3204 30641 30 _ _ (1033011 / 50000) (82641 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell938979584 :
    ThetaLowerSegment 938979584 939045120 (18778764687297 / 20000) (93900211598153 / 100000) := by
  exact
    packedTile32768 938979584 939045120 13 3092 30642 30 _ _ (2066029 / 100000) (129127 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939045120 :
    ThetaLowerSegment 939045120 939110656 (93900211598153 / 100000) (93906789856777 / 100000) := by
  exact
    packedTile32768 939045120 939110656 13 3184 30643 30 _ _ (516509 / 25000) (2066039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939110656 :
    ThetaLowerSegment 939110656 939176192 (93906789856777 / 100000) (23478334286761 / 25000) := by
  exact
    packedTile32768 939110656 939176192 13 3169 30644 30 _ _ (2066043 / 100000) (1033023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939176192 :
    ThetaLowerSegment 939176192 939241728 (23478334286761 / 25000) (5869993424359 / 6250) := by
  exact
    packedTile32768 939176192 939241728 13 3174 30645 30 _ _ (41321 / 2000) (2066053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939241728 :
    ThetaLowerSegment 939241728 939307264 (5869993424359 / 6250) (46963193170419 / 50000) := by
  exact
    packedTile32768 939241728 939307264 13 3142 30647 30 _ _ (2066057 / 100000) (103303 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939307264 :
    ThetaLowerSegment 939307264 939372800 (46963193170419 / 50000) (46966516434363 / 50000) := by
  exact
    packedTile32768 939307264 939372800 13 3217 30648 30 _ _ (129129 / 6250) (2066067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939372800 :
    ThetaLowerSegment 939372800 939438336 (46966516434363 / 50000) (93939501737027 / 100000) := by
  exact
    packedTile32768 939372800 939438336 13 3131 30649 30 _ _ (2066071 / 100000) (1033037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939438336 :
    ThetaLowerSegment 939438336 939503872 (93939501737027 / 100000) (93945999552337 / 100000) := by
  exact
    packedTile32768 939438336 939503872 13 3145 30650 30 _ _ (1033039 / 50000) (2066081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939503872 :
    ThetaLowerSegment 939503872 939569408 (93945999552337 / 100000) (93952441605367 / 100000) := by
  exact
    packedTile32768 939503872 939569408 13 3118 30651 30 _ _ (413217 / 20000) (258261 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939569408 :
    ThetaLowerSegment 939569408 939634944 (93952441605367 / 100000) (93958887812407 / 100000) := by
  exact
    packedTile32768 939569408 939634944 13 3120 30652 30 _ _ (516523 / 25000) (413219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939634944 :
    ThetaLowerSegment 939634944 939700480 (93958887812407 / 100000) (93965437346237 / 100000) := by
  exact
    packedTile32768 939634944 939700480 13 3170 30653 30 _ _ (2066099 / 100000) (1033051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939700480 :
    ThetaLowerSegment 939700480 939766016 (93965437346237 / 100000) (93971976571727 / 100000) := by
  exact
    packedTile32768 939700480 939766016 13 3165 30654 30 _ _ (1033053 / 50000) (2066109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939766016 :
    ThetaLowerSegment 939766016 939831552 (93971976571727 / 100000) (46989231050217 / 50000) := by
  exact
    packedTile32768 939766016 939831552 13 3139 30655 30 _ _ (2066113 / 100000) (516529 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939831552 :
    ThetaLowerSegment 939831552 939897088 (46989231050217 / 50000) (46992522379377 / 50000) := by
  exact
    packedTile32768 939831552 939897088 13 3186 30656 30 _ _ (51653 / 2500) (2066123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939897088 :
    ThetaLowerSegment 939897088 939962624 (46992522379377 / 50000) (93991596447471 / 100000) := by
  exact
    packedTile32768 939897088 939962624 13 3171 30657 30 _ _ (2066127 / 100000) (206613 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell939962624 :
    ThetaLowerSegment 939962624 940028160 (93991596447471 / 100000) (93998079975963 / 100000) := by
  exact
    packedTile32768 939962624 940028160 13 3138 30658 30 _ _ (1033067 / 50000) (2066137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940028160 :
    ThetaLowerSegment 940028160 940093696 (93998079975963 / 100000) (94004741214547 / 100000) := by
  exact
    packedTile32768 940028160 940093696 13 3224 30659 30 _ _ (2066141 / 100000) (64567 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940093696 :
    ThetaLowerSegment 940093696 940159232 (94004741214547 / 100000) (94011195860899 / 100000) := by
  exact
    packedTile32768 940093696 940159232 13 3124 30660 30 _ _ (516537 / 25000) (2066151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940159232 :
    ThetaLowerSegment 940159232 940224768 (94011195860899 / 100000) (3760709740117 / 4000) := by
  exact
    packedTile32768 940159232 940224768 13 3169 30662 30 _ _ (1033077 / 50000) (2066157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940224768 :
    ThetaLowerSegment 940224768 940290304 (3760709740117 / 4000) (47012157980533 / 50000) := by
  exact
    packedTile32768 940224768 940290304 13 3181 30663 30 _ _ (2066161 / 100000) (516541 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940290304 :
    ThetaLowerSegment 940290304 940355840 (47012157980533 / 50000) (47015427691393 / 50000) := by
  exact
    packedTile32768 940290304 940355840 13 3165 30664 30 _ _ (258271 / 12500) (2066171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940355840 :
    ThetaLowerSegment 940355840 940421376 (47015427691393 / 50000) (47018721174343 / 50000) := by
  exact
    packedTile32768 940355840 940421376 13 3188 30665 30 _ _ (82647 / 4000) (1033089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940421376 :
    ThetaLowerSegment 940421376 940486912 (47018721174343 / 50000) (940440066089 / 1000) := by
  exact
    packedTile32768 940421376 940486912 13 3177 30666 30 _ _ (1033091 / 50000) (413237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940486912 :
    ThetaLowerSegment 940486912 940552448 (940440066089 / 1000) (11756320070051 / 12500) := by
  exact
    packedTile32768 940486912 940552448 13 3172 30667 30 _ _ (2066189 / 100000) (129137 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940552448 :
    ThetaLowerSegment 940552448 940617984 (11756320070051 / 12500) (5878571982853 / 6250) := by
  exact
    packedTile32768 940552448 940617984 13 3190 30668 30 _ _ (516549 / 25000) (2066199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940617984 :
    ThetaLowerSegment 940617984 940683520 (5878571982853 / 6250) (5878981091047 / 6250) := by
  exact
    packedTile32768 940617984 940683520 13 3168 30669 30 _ _ (2066203 / 100000) (1033103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940683520 :
    ThetaLowerSegment 940683520 940749056 (5878981091047 / 6250) (2939700782391 / 3125) := by
  exact
    packedTile32768 940683520 940749056 13 3256 30670 30 _ _ (206621 / 10000) (2066213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940749056 :
    ThetaLowerSegment 940749056 940814592 (2939700782391 / 3125) (940769625471 / 1000) := by
  exact
    packedTile32768 940749056 940814592 13 3164 30671 30 _ _ (2066217 / 100000) (103311 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940814592 :
    ThetaLowerSegment 940814592 940880128 (940769625471 / 1000) (23520923059667 / 25000) := by
  exact
    packedTile32768 940814592 940880128 13 3257 30672 30 _ _ (129139 / 6250) (2066227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940880128 :
    ThetaLowerSegment 940880128 940945664 (23520923059667 / 25000) (23522542984771 / 25000) := by
  exact
    packedTile32768 940880128 940945664 13 3136 30673 30 _ _ (2066231 / 100000) (1033117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell940945664 :
    ThetaLowerSegment 940945664 941011200 (23522542984771 / 25000) (23524144319221 / 25000) := by
  exact
    packedTile32768 940945664 941011200 13 3100 30674 30 _ _ (1033119 / 50000) (2066241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941011200 :
    ThetaLowerSegment 941011200 941076736 (23524144319221 / 25000) (47051580166727 / 50000) := by
  exact
    packedTile32768 941011200 941076736 13 3186 30675 30 _ _ (413249 / 20000) (258281 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941076736 :
    ThetaLowerSegment 941076736 941142272 (47051580166727 / 50000) (47054831414249 / 50000) := by
  exact
    packedTile32768 941076736 941142272 13 3147 30676 30 _ _ (516563 / 25000) (413251 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941142272 :
    ThetaLowerSegment 941142272 941207808 (47054831414249 / 50000) (150585884389 / 160) := by
  exact
    packedTile32768 941142272 941207808 13 3153 30678 30 _ _ (2066259 / 100000) (1033131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941207808 :
    ThetaLowerSegment 941207808 941273344 (150585884389 / 160) (94122734005143 / 100000) := by
  exact
    packedTile32768 941207808 941273344 13 3173 30679 30 _ _ (1033133 / 50000) (2066269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941273344 :
    ThetaLowerSegment 941273344 941338880 (94122734005143 / 100000) (94129403934387 / 100000) := by
  exact
    packedTile32768 941273344 941338880 13 3228 30680 30 _ _ (2066273 / 100000) (516569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941338880 :
    ThetaLowerSegment 941338880 941404416 (94129403934387 / 100000) (94135912716387 / 100000) := by
  exact
    packedTile32768 941338880 941404416 13 3150 30681 30 _ _ (51657 / 2500) (2066283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941404416 :
    ThetaLowerSegment 941404416 941469952 (94135912716387 / 100000) (94142479376473 / 100000) := by
  exact
    packedTile32768 941404416 941469952 13 3178 30682 30 _ _ (2066287 / 100000) (206629 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941469952 :
    ThetaLowerSegment 941469952 941535488 (94142479376473 / 100000) (18829815410643 / 20000) := by
  exact
    packedTile32768 941469952 941535488 13 3193 30683 30 _ _ (1033147 / 50000) (2066297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941535488 :
    ThetaLowerSegment 941535488 941601024 (18829815410643 / 20000) (47077864238067 / 50000) := by
  exact
    packedTile32768 941535488 941601024 13 3219 30684 30 _ _ (2066301 / 100000) (64572 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941601024 :
    ThetaLowerSegment 941601024 941666560 (47077864238067 / 50000) (47081189960793 / 50000) := by
  exact
    packedTile32768 941601024 941666560 13 3219 30685 30 _ _ (516577 / 25000) (2066311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941666560 :
    ThetaLowerSegment 941666560 941732096 (47081189960793 / 50000) (94168799962291 / 100000) := by
  exact
    packedTile32768 941666560 941732096 13 3107 30686 30 _ _ (413263 / 20000) (1033159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941732096 :
    ThetaLowerSegment 941732096 941797632 (94168799962291 / 100000) (94175339871421 / 100000) := by
  exact
    packedTile32768 941732096 941797632 13 3165 30687 30 _ _ (1033161 / 50000) (82653 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941797632 :
    ThetaLowerSegment 941797632 941863168 (94175339871421 / 100000) (18836351577859 / 20000) := by
  exact
    packedTile32768 941797632 941863168 13 3106 30688 30 _ _ (2066329 / 100000) (516583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941863168 :
    ThetaLowerSegment 941863168 941928704 (18836351577859 / 20000) (94188304041743 / 100000) := by
  exact
    packedTile32768 941863168 941928704 13 3168 30689 30 _ _ (64573 / 3125) (2066339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941928704 :
    ThetaLowerSegment 941928704 941994240 (94188304041743 / 100000) (47097355885693 / 50000) := by
  exact
    packedTile32768 941928704 941994240 13 3101 30690 30 _ _ (2066343 / 100000) (1033173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell941994240 :
    ThetaLowerSegment 941994240 942059776 (47097355885693 / 50000) (47100682707583 / 50000) := by
  exact
    packedTile32768 941994240 942059776 13 3220 30691 30 _ _ (2066349 / 100000) (129147 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942059776 :
    ThetaLowerSegment 942059776 942125312 (47100682707583 / 50000) (47103893824807 / 50000) := by
  exact
    packedTile32768 942059776 942125312 13 3108 30692 30 _ _ (516589 / 25000) (2066359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942125312 :
    ThetaLowerSegment 942125312 942190848 (47103893824807 / 50000) (11776807750263 / 12500) := by
  exact
    packedTile32768 942125312 942190848 13 3230 30694 30 _ _ (2066363 / 100000) (1033183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942190848 :
    ThetaLowerSegment 942190848 942256384 (11776807750263 / 12500) (47110490699727 / 50000) := by
  exact
    packedTile32768 942190848 942256384 13 3155 30695 30 _ _ (206637 / 10000) (2066373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942256384 :
    ThetaLowerSegment 942256384 942321920 (47110490699727 / 50000) (11778439410441 / 12500) := by
  exact
    packedTile32768 942256384 942321920 13 3162 30696 30 _ _ (2066377 / 100000) (103319 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942321920 :
    ThetaLowerSegment 942321920 942387456 (11778439410441 / 12500) (2355852056297 / 2500) := by
  exact
    packedTile32768 942321920 942387456 13 3178 30697 30 _ _ (129149 / 6250) (2066387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942387456 :
    ThetaLowerSegment 942387456 942452992 (2355852056297 / 2500) (47120303957329 / 50000) := by
  exact
    packedTile32768 942387456 942452992 13 3158 30698 30 _ _ (2066391 / 100000) (1033197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942452992 :
    ThetaLowerSegment 942452992 942518528 (47120303957329 / 50000) (47123610194129 / 50000) := by
  exact
    packedTile32768 942452992 942518528 13 3200 30699 30 _ _ (1033199 / 50000) (2066401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942518528 :
    ThetaLowerSegment 942518528 942584064 (47123610194129 / 50000) (94253839083473 / 100000) := by
  exact
    packedTile32768 942518528 942584064 13 3203 30700 30 _ _ (413281 / 20000) (258301 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942584064 :
    ThetaLowerSegment 942584064 942649600 (94253839083473 / 100000) (94260428871341 / 100000) := by
  exact
    packedTile32768 942584064 942649600 13 3189 30701 30 _ _ (516603 / 25000) (413283 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942649600 :
    ThetaLowerSegment 942649600 942715136 (94260428871341 / 100000) (23566713342003 / 25000) := by
  exact
    packedTile32768 942649600 942715136 13 3109 30702 30 _ _ (2066419 / 100000) (1033211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942715136 :
    ThetaLowerSegment 942715136 942780672 (23566713342003 / 25000) (23568368549229 / 25000) := by
  exact
    packedTile32768 942715136 942780672 13 3204 30703 30 _ _ (1033213 / 50000) (2066429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942780672 :
    ThetaLowerSegment 942780672 942846208 (23568368549229 / 25000) (94279931800041 / 100000) := by
  exact
    packedTile32768 942780672 942846208 13 3125 30704 30 _ _ (2066433 / 100000) (516609 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942846208 :
    ThetaLowerSegment 942846208 942911744 (94279931800041 / 100000) (94286476215521 / 100000) := by
  exact
    packedTile32768 942846208 942911744 13 3167 30705 30 _ _ (51661 / 2500) (2066443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942911744 :
    ThetaLowerSegment 942911744 942977280 (94286476215521 / 100000) (11786617766023 / 12500) := by
  exact
    packedTile32768 942911744 942977280 13 3129 30706 30 _ _ (2066447 / 100000) (41329 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell942977280 :
    ThetaLowerSegment 942977280 943042816 (11786617766023 / 12500) (47149763958541 / 50000) := by
  exact
    packedTile32768 942977280 943042816 13 3187 30707 30 _ _ (1033227 / 50000) (2066457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943042816 :
    ThetaLowerSegment 943042816 943108352 (47149763958541 / 50000) (23576511383769 / 25000) := by
  exact
    packedTile32768 943042816 943108352 13 3154 30709 30 _ _ (2066461 / 100000) (64577 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943108352 :
    ThetaLowerSegment 943108352 943173888 (23576511383769 / 25000) (5894539460537 / 6250) := by
  exact
    packedTile32768 943108352 943173888 13 3187 30710 30 _ _ (516617 / 25000) (2066471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943173888 :
    ThetaLowerSegment 943173888 943239424 (5894539460537 / 6250) (5894944489637 / 6250) := by
  exact
    packedTile32768 943173888 943239424 13 3136 30711 30 _ _ (82659 / 4000) (1033239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943239424 :
    ThetaLowerSegment 943239424 943304960 (5894944489637 / 6250) (23581423911461 / 25000) := by
  exact
    packedTile32768 943239424 943304960 13 3186 30712 30 _ _ (1033241 / 50000) (413297 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943304960 :
    ThetaLowerSegment 943304960 943370496 (23581423911461 / 25000) (4716609634363 / 5000) := by
  exact
    packedTile32768 943304960 943370496 13 3144 30713 30 _ _ (2066489 / 100000) (516623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943370496 :
    ThetaLowerSegment 943370496 943436032 (4716609634363 / 5000) (18867752414973 / 20000) := by
  exact
    packedTile32768 943370496 943436032 13 3179 30714 30 _ _ (413299 / 20000) (1033249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943436032 :
    ThetaLowerSegment 943436032 943501568 (18867752414973 / 20000) (94345356282747 / 100000) := by
  exact
    packedTile32768 943436032 943501568 13 3191 30715 30 _ _ (1033251 / 50000) (413301 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943501568 :
    ThetaLowerSegment 943501568 943567104 (94345356282747 / 100000) (94351902983259 / 100000) := by
  exact
    packedTile32768 943501568 943567104 13 3168 30716 30 _ _ (2066509 / 100000) (129157 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943567104 :
    ThetaLowerSegment 943567104 943632640 (94351902983259 / 100000) (94358524100523 / 100000) := by
  exact
    packedTile32768 943567104 943632640 13 3204 30717 30 _ _ (516629 / 25000) (2066519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943632640 :
    ThetaLowerSegment 943632640 943698176 (94358524100523 / 100000) (94365050180157 / 100000) := by
  exact
    packedTile32768 943632640 943698176 13 3158 30718 30 _ _ (2066523 / 100000) (1033263 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943698176 :
    ThetaLowerSegment 943698176 943763712 (94365050180157 / 100000) (94371611412907 / 100000) := by
  exact
    packedTile32768 943698176 943763712 13 3175 30719 30 _ _ (206653 / 10000) (2066533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943763712 :
    ThetaLowerSegment 943763712 943829248 (94371611412907 / 100000) (4718908013433 / 5000) := by
  exact
    packedTile32768 943763712 943829248 13 3169 30720 30 _ _ (2066537 / 100000) (103327 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943829248 :
    ThetaLowerSegment 943829248 943894784 (4718908013433 / 5000) (23596215517713 / 25000) := by
  exact
    packedTile32768 943829248 943894784 13 3243 30721 30 _ _ (129159 / 6250) (2066547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943894784 :
    ThetaLowerSegment 943894784 943960320 (23596215517713 / 25000) (47195805713209 / 50000) := by
  exact
    packedTile32768 943894784 943960320 13 3266 30722 30 _ _ (2066551 / 100000) (1033277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell943960320 :
    ThetaLowerSegment 943960320 944025856 (47195805713209 / 50000) (47199079141081 / 50000) := by
  exact
    packedTile32768 943960320 944025856 13 3168 30723 30 _ _ (1033279 / 50000) (2066561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944025856 :
    ThetaLowerSegment 944025856 944091392 (47199079141081 / 50000) (94404760957337 / 100000) := by
  exact
    packedTile32768 944025856 944091392 13 3195 30725 30 _ _ (413313 / 20000) (258321 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944091392 :
    ThetaLowerSegment 944091392 944156928 (94404760957337 / 100000) (94411322323437 / 100000) := by
  exact
    packedTile32768 944091392 944156928 13 3175 30726 30 _ _ (516643 / 25000) (82663 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944156928 :
    ThetaLowerSegment 944156928 944222464 (94411322323437 / 100000) (23604465761493 / 25000) := by
  exact
    packedTile32768 944156928 944222464 13 3165 30727 30 _ _ (2066579 / 100000) (1033291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944222464 :
    ThetaLowerSegment 944222464 944288000 (23604465761493 / 25000) (47212222561191 / 50000) := by
  exact
    packedTile32768 944222464 944288000 13 3185 30728 30 _ _ (1033293 / 50000) (2066589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944288000 :
    ThetaLowerSegment 944288000 944353536 (47212222561191 / 50000) (94430824694973 / 100000) := by
  exact
    packedTile32768 944288000 944353536 13 3087 30729 30 _ _ (2066593 / 100000) (516649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944353536 :
    ThetaLowerSegment 944353536 944419072 (94430824694973 / 100000) (94437444014773 / 100000) := by
  exact
    packedTile32768 944353536 944419072 13 3203 30730 30 _ _ (10333 / 500) (2066603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944419072 :
    ThetaLowerSegment 944419072 944484608 (94437444014773 / 100000) (2951375042462 / 3125) := by
  exact
    packedTile32768 944419072 944484608 13 3173 30731 30 _ _ (2066607 / 100000) (206661 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944484608 :
    ThetaLowerSegment 944484608 944550144 (2951375042462 / 3125) (23612635030579 / 25000) := by
  exact
    packedTile32768 944484608 944550144 13 3164 30732 30 _ _ (2066613 / 100000) (258327 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944550144 :
    ThetaLowerSegment 944550144 944615680 (23612635030579 / 25000) (5903563686001 / 6250) := by
  exact
    packedTile32768 944550144 944615680 13 3135 30733 30 _ _ (103331 / 5000) (2066623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944615680 :
    ThetaLowerSegment 944615680 944681216 (5903563686001 / 6250) (94463493718407 / 100000) := by
  exact
    packedTile32768 944615680 944681216 13 3133 30734 30 _ _ (2066627 / 100000) (206663 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944681216 :
    ThetaLowerSegment 944681216 944746752 (94463493718407 / 100000) (94470113147109 / 100000) := by
  exact
    packedTile32768 944681216 944746752 13 3203 30735 30 _ _ (1033317 / 50000) (2066637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944746752 :
    ThetaLowerSegment 944746752 944812288 (94470113147109 / 100000) (94476606533131 / 100000) := by
  exact
    packedTile32768 944746752 944812288 13 3142 30736 30 _ _ (2066641 / 100000) (516661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944812288 :
    ThetaLowerSegment 944812288 944877824 (94476606533131 / 100000) (94483219806731 / 100000) := by
  exact
    packedTile32768 944812288 944877824 13 3200 30737 30 _ _ (258331 / 12500) (2066651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944877824 :
    ThetaLowerSegment 944877824 944943360 (94483219806731 / 100000) (23622445359089 / 25000) := by
  exact
    packedTile32768 944877824 944943360 13 3175 30738 30 _ _ (413331 / 20000) (1033329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell944943360 :
    ThetaLowerSegment 944943360 945008896 (23622445359089 / 25000) (4724812711087 / 5000) := by
  exact
    packedTile32768 944943360 945008896 13 3132 30739 30 _ _ (1033331 / 50000) (413333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945008896 :
    ThetaLowerSegment 945008896 945074432 (4724812711087 / 5000) (11812861545321 / 12500) := by
  exact
    packedTile32768 945008896 945074432 13 3212 30740 30 _ _ (2066669 / 100000) (129167 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945074432 :
    ThetaLowerSegment 945074432 945139968 (11812861545321 / 12500) (2362735163133 / 2500) := by
  exact
    packedTile32768 945074432 945139968 13 3152 30742 30 _ _ (516669 / 25000) (2066679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945139968 :
    ThetaLowerSegment 945139968 945205504 (2362735163133 / 2500) (94516017844237 / 100000) := by
  exact
    packedTile32768 945139968 945205504 13 3199 30743 30 _ _ (2066683 / 100000) (1033343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945205504 :
    ThetaLowerSegment 945205504 945271040 (94516017844237 / 100000) (94522583718367 / 100000) := by
  exact
    packedTile32768 945205504 945271040 13 3177 30744 30 _ _ (206669 / 10000) (2066693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945271040 :
    ThetaLowerSegment 945271040 945336576 (94522583718367 / 100000) (47264510739761 / 50000) := by
  exact
    packedTile32768 945271040 945336576 13 3115 30745 30 _ _ (2066697 / 100000) (20667 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945336576 :
    ThetaLowerSegment 945336576 945402112 (47264510739761 / 50000) (47267715164313 / 50000) := by
  exact
    packedTile32768 945336576 945402112 13 3101 30746 30 _ _ (129169 / 6250) (2066707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945402112 :
    ThetaLowerSegment 945402112 945467648 (47267715164313 / 50000) (23635509917601 / 25000) := by
  exact
    packedTile32768 945402112 945467648 13 3198 30747 30 _ _ (2066711 / 100000) (1033357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945467648 :
    ThetaLowerSegment 945467648 945533184 (23635509917601 / 25000) (23637177759027 / 25000) := by
  exact
    packedTile32768 945467648 945533184 13 3228 30748 30 _ _ (1033359 / 50000) (2066721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945533184 :
    ThetaLowerSegment 945533184 945598720 (23637177759027 / 25000) (5909700680193 / 6250) := by
  exact
    packedTile32768 945533184 945598720 13 3145 30749 30 _ _ (516681 / 25000) (2066727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945598720 :
    ThetaLowerSegment 945598720 945664256 (5909700680193 / 6250) (94561764487089 / 100000) := by
  exact
    packedTile32768 945598720 945664256 13 3171 30750 30 _ _ (2066731 / 100000) (1033367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945664256 :
    ThetaLowerSegment 945664256 945729792 (94561764487089 / 100000) (94568332580453 / 100000) := by
  exact
    packedTile32768 945664256 945729792 13 3178 30751 30 _ _ (1033369 / 50000) (2066741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945729792 :
    ThetaLowerSegment 945729792 945795328 (94568332580453 / 100000) (47287453448149 / 50000) := by
  exact
    packedTile32768 945729792 945795328 13 3181 30752 30 _ _ (413349 / 20000) (516687 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945795328 :
    ThetaLowerSegment 945795328 945860864 (47287453448149 / 50000) (47290727183317 / 50000) := by
  exact
    packedTile32768 945795328 945860864 13 3168 30753 30 _ _ (64586 / 3125) (413351 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945860864 :
    ThetaLowerSegment 945860864 945926400 (47290727183317 / 50000) (94587979124797 / 100000) := by
  exact
    packedTile32768 945860864 945926400 13 3157 30754 30 _ _ (2066759 / 100000) (1033381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945926400 :
    ThetaLowerSegment 945926400 945991936 (94587979124797 / 100000) (94594563841273 / 100000) := by
  exact
    packedTile32768 945926400 945991936 13 3186 30755 30 _ _ (1033383 / 50000) (2066769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell945991936 :
    ThetaLowerSegment 945991936 946057472 (94594563841273 / 100000) (94601115511683 / 100000) := by
  exact
    packedTile32768 945991936 946057472 13 3170 30756 30 _ _ (2066773 / 100000) (258347 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946057472 :
    ThetaLowerSegment 946057472 946123008 (94601115511683 / 100000) (94607741608363 / 100000) := by
  exact
    packedTile32768 946057472 946123008 13 3206 30758 30 _ _ (103339 / 5000) (2066783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946123008 :
    ThetaLowerSegment 946123008 946188544 (94607741608363 / 100000) (3784568095381 / 4000) := by
  exact
    packedTile32768 946123008 946188544 13 3126 30759 30 _ _ (2066787 / 100000) (206679 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946188544 :
    ThetaLowerSegment 946188544 946254080 (3784568095381 / 4000) (94620886396321 / 100000) := by
  exact
    packedTile32768 946188544 946254080 13 3234 30760 30 _ _ (1033397 / 50000) (2066797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946254080 :
    ThetaLowerSegment 946254080 946319616 (94620886396321 / 100000) (94627438155491 / 100000) := by
  exact
    packedTile32768 946254080 946319616 13 3170 30761 30 _ _ (2066801 / 100000) (516701 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946319616 :
    ThetaLowerSegment 946319616 946385152 (94627438155491 / 100000) (94634012671739 / 100000) := by
  exact
    packedTile32768 946319616 946385152 13 3181 30762 30 _ _ (258351 / 12500) (2066811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946385152 :
    ThetaLowerSegment 946385152 946450688 (94634012671739 / 100000) (94640473535429 / 100000) := by
  exact
    packedTile32768 946385152 946450688 13 3126 30763 30 _ _ (413363 / 20000) (1033409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946450688 :
    ThetaLowerSegment 946450688 946516224 (94640473535429 / 100000) (11830887728797 / 12500) := by
  exact
    packedTile32768 946450688 946516224 13 3207 30764 30 _ _ (2066821 / 100000) (258353 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946516224 :
    ThetaLowerSegment 946516224 946581760 (11830887728797 / 12500) (23663426336459 / 25000) := by
  exact
    packedTile32768 946516224 946581760 13 3195 30765 30 _ _ (516707 / 25000) (2066831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946581760 :
    ThetaLowerSegment 946581760 946647296 (23663426336459 / 25000) (47330128606393 / 50000) := by
  exact
    packedTile32768 946581760 946647296 13 3170 30766 30 _ _ (413367 / 20000) (1033419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946647296 :
    ThetaLowerSegment 946647296 946712832 (47330128606393 / 50000) (47333328077809 / 50000) := by
  exact
    packedTile32768 946647296 946712832 13 3096 30767 30 _ _ (1033421 / 50000) (413369 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946712832 :
    ThetaLowerSegment 946712832 946778368 (47333328077809 / 50000) (5917072920623 / 6250) := by
  exact
    packedTile32768 946712832 946778368 13 3150 30768 30 _ _ (2066849 / 100000) (516713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946778368 :
    ThetaLowerSegment 946778368 946843904 (5917072920623 / 6250) (2958737332879 / 3125) := by
  exact
    packedTile32768 946778368 946843904 13 3110 30769 30 _ _ (258357 / 12500) (2066859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946843904 :
    ThetaLowerSegment 946843904 946909440 (2958737332879 / 3125) (94686111471167 / 100000) := by
  exact
    packedTile32768 946843904 946909440 13 3153 30770 30 _ _ (2066863 / 100000) (1033433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946909440 :
    ThetaLowerSegment 946909440 946974976 (94686111471167 / 100000) (94692770926307 / 100000) := by
  exact
    packedTile32768 946909440 946974976 13 3222 30771 30 _ _ (206687 / 10000) (2066873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell946974976 :
    ThetaLowerSegment 946974976 947040512 (94692770926307 / 100000) (23674857084281 / 25000) := by
  exact
    packedTile32768 946974976 947040512 13 3221 30772 30 _ _ (2066877 / 100000) (12918 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947040512 :
    ThetaLowerSegment 947040512 947106048 (23674857084281 / 25000) (4735304598557 / 5000) := by
  exact
    packedTile32768 947040512 947106048 13 3224 30774 30 _ _ (516721 / 25000) (2066887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947106048 :
    ThetaLowerSegment 947106048 947171584 (4735304598557 / 5000) (9471264401561 / 10000) := by
  exact
    packedTile32768 947106048 947171584 13 3170 30775 30 _ _ (2066891 / 100000) (1033447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947171584 :
    ThetaLowerSegment 947171584 947237120 (9471264401561 / 10000) (47359655914279 / 50000) := by
  exact
    packedTile32768 947171584 947237120 13 3226 30776 30 _ _ (1033449 / 50000) (2066901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947237120 :
    ThetaLowerSegment 947237120 947302656 (47359655914279 / 50000) (11840730922771 / 12500) := by
  exact
    packedTile32768 947237120 947302656 13 3162 30777 30 _ _ (413381 / 20000) (516727 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947302656 :
    ThetaLowerSegment 947302656 947368192 (11840730922771 / 12500) (3789297385101 / 4000) := by
  exact
    packedTile32768 947302656 947368192 13 3187 30778 30 _ _ (2066911 / 100000) (1033457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947368192 :
    ThetaLowerSegment 947368192 947433728 (3789297385101 / 4000) (94739088036567 / 100000) := by
  exact
    packedTile32768 947368192 947433728 13 3219 30779 30 _ _ (1033459 / 50000) (2066921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947433728 :
    ThetaLowerSegment 947433728 947499264 (94739088036567 / 100000) (94745536842567 / 100000) := by
  exact
    packedTile32768 947433728 947499264 13 3120 30780 30 _ _ (82677 / 4000) (129183 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947499264 :
    ThetaLowerSegment 947499264 947564800 (94745536842567 / 100000) (94752115887123 / 100000) := by
  exact
    packedTile32768 947499264 947564800 13 3183 30781 30 _ _ (516733 / 25000) (413387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947564800 :
    ThetaLowerSegment 947564800 947630336 (94752115887123 / 100000) (94758668083753 / 100000) := by
  exact
    packedTile32768 947564800 947630336 13 3170 30782 30 _ _ (2066939 / 100000) (1033471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947630336 :
    ThetaLowerSegment 947630336 947695872 (94758668083753 / 100000) (94765342252387 / 100000) := by
  exact
    packedTile32768 947630336 947695872 13 3229 30783 30 _ _ (1033473 / 50000) (2066949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947695872 :
    ThetaLowerSegment 947695872 947761408 (94765342252387 / 100000) (94771964769799 / 100000) := by
  exact
    packedTile32768 947695872 947761408 13 3204 30784 30 _ _ (2066953 / 100000) (516739 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947761408 :
    ThetaLowerSegment 947761408 947826944 (94771964769799 / 100000) (94778527367799 / 100000) := by
  exact
    packedTile32768 947761408 947826944 13 3175 30785 30 _ _ (25837 / 1250) (2066963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947826944 :
    ThetaLowerSegment 947826944 947892480 (94778527367799 / 100000) (2369625596127 / 2500) := by
  exact
    packedTile32768 947826944 947892480 13 3143 30786 30 _ _ (2066967 / 100000) (206697 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947892480 :
    ThetaLowerSegment 947892480 947958016 (2369625596127 / 2500) (47395784975869 / 50000) := by
  exact
    packedTile32768 947892480 947958016 13 3167 30787 30 _ _ (1033487 / 50000) (2066977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell947958016 :
    ThetaLowerSegment 947958016 948023552 (47395784975869 / 50000) (9479812641547 / 10000) := by
  exact
    packedTile32768 947958016 948023552 13 3172 30788 30 _ _ (2066981 / 100000) (258373 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948023552 :
    ThetaLowerSegment 948023552 948089088 (9479812641547 / 10000) (94804680831247 / 100000) := by
  exact
    packedTile32768 948023552 948089088 13 3171 30789 30 _ _ (2066987 / 100000) (206699 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948089088 :
    ThetaLowerSegment 948089088 948154624 (94804680831247 / 100000) (18962245400249 / 20000) := by
  exact
    packedTile32768 948089088 948154624 13 3167 30791 30 _ _ (1033497 / 50000) (2066997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948154624 :
    ThetaLowerSegment 948154624 948220160 (18962245400249 / 20000) (47408892797709 / 50000) := by
  exact
    packedTile32768 948154624 948220160 13 3173 30792 30 _ _ (2067001 / 100000) (516751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948220160 :
    ThetaLowerSegment 948220160 948285696 (47408892797709 / 50000) (47412120430701 / 50000) := by
  exact
    packedTile32768 948220160 948285696 13 3123 30793 30 _ _ (64594 / 3125) (2067011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948285696 :
    ThetaLowerSegment 948285696 948351232 (47412120430701 / 50000) (23707721061903 / 25000) := by
  exact
    packedTile32768 948285696 948351232 13 3214 30794 30 _ _ (413403 / 20000) (1033509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948351232 :
    ThetaLowerSegment 948351232 948416768 (23707721061903 / 25000) (47418671845681 / 50000) := by
  exact
    packedTile32768 948351232 948416768 13 3125 30795 30 _ _ (1033511 / 50000) (82681 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948416768 :
    ThetaLowerSegment 948416768 948482304 (47418671845681 / 50000) (11855481854089 / 12500) := by
  exact
    packedTile32768 948416768 948482304 13 3150 30796 30 _ _ (2067029 / 100000) (258379 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948482304 :
    ThetaLowerSegment 948482304 948547840 (11855481854089 / 12500) (23712620954291 / 25000) := by
  exact
    packedTile32768 948482304 948547840 13 3207 30797 30 _ _ (516759 / 25000) (2067039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948547840 :
    ThetaLowerSegment 948547840 948613376 (23712620954291 / 25000) (47428522305823 / 50000) := by
  exact
    packedTile32768 948547840 948613376 13 3174 30798 30 _ _ (2067043 / 100000) (1033523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948613376 :
    ThetaLowerSegment 948613376 948678912 (47428522305823 / 50000) (23715887404499 / 25000) := by
  exact
    packedTile32768 948613376 948678912 13 3147 30799 30 _ _ (41341 / 2000) (2067053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948678912 :
    ThetaLowerSegment 948678912 948744448 (23715887404499 / 25000) (1897400059399 / 2000) := by
  exact
    packedTile32768 948678912 948744448 13 3122 30800 30 _ _ (2067057 / 100000) (103353 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948744448 :
    ThetaLowerSegment 948744448 948809984 (1897400059399 / 2000) (47438305686779 / 50000) := by
  exact
    packedTile32768 948744448 948809984 13 3197 30801 30 _ _ (258383 / 12500) (2067067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948809984 :
    ThetaLowerSegment 948809984 948875520 (47438305686779 / 50000) (47441635736549 / 50000) := by
  exact
    packedTile32768 948809984 948875520 13 3222 30802 30 _ _ (206707 / 10000) (2067073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948875520 :
    ThetaLowerSegment 948875520 948941056 (47441635736549 / 50000) (18977948698237 / 20000) := by
  exact
    packedTile32768 948875520 948941056 13 3131 30803 30 _ _ (2067077 / 100000) (51677 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell948941056 :
    ThetaLowerSegment 948941056 949006592 (18977948698237 / 20000) (94896323019557 / 100000) := by
  exact
    packedTile32768 948941056 949006592 13 3183 30804 30 _ _ (516771 / 25000) (2067087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949006592 :
    ThetaLowerSegment 949006592 949072128 (94896323019557 / 100000) (94902826087843 / 100000) := by
  exact
    packedTile32768 949006592 949072128 13 3146 30805 30 _ _ (2067091 / 100000) (1033547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949072128 :
    ThetaLowerSegment 949072128 949137664 (94902826087843 / 100000) (94909440801443 / 100000) := by
  exact
    packedTile32768 949072128 949137664 13 3200 30807 30 _ _ (1033549 / 50000) (2067101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949137664 :
    ThetaLowerSegment 949137664 949203200 (94909440801443 / 100000) (47458018466749 / 50000) := by
  exact
    packedTile32768 949137664 949203200 13 3191 30808 30 _ _ (413421 / 20000) (516777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949203200 :
    ThetaLowerSegment 949203200 949268736 (47458018466749 / 50000) (47461251429917 / 50000) := by
  exact
    packedTile32768 949203200 949268736 13 3128 30809 30 _ _ (258389 / 12500) (413423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949268736 :
    ThetaLowerSegment 949268736 949334272 (47461251429917 / 50000) (11866119550669 / 12500) := by
  exact
    packedTile32768 949268736 949334272 13 3122 30810 30 _ _ (2067119 / 100000) (1033561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949334272 :
    ThetaLowerSegment 949334272 949399808 (11866119550669 / 12500) (47467765966579 / 50000) := by
  exact
    packedTile32768 949334272 949399808 13 3181 30811 30 _ _ (1033563 / 50000) (2067129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949399808 :
    ThetaLowerSegment 949399808 949465344 (47467765966579 / 50000) (94942128154561 / 100000) := by
  exact
    packedTile32768 949399808 949465344 13 3191 30812 30 _ _ (2067133 / 100000) (64598 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949465344 :
    ThetaLowerSegment 949465344 949530880 (94942128154561 / 100000) (94948742999361 / 100000) := by
  exact
    packedTile32768 949465344 949530880 13 3200 30813 30 _ _ (2067139 / 100000) (1033571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949530880 :
    ThetaLowerSegment 949530880 949596416 (94948742999361 / 100000) (94955233837801 / 100000) := by
  exact
    packedTile32768 949530880 949596416 13 3140 30814 30 _ _ (1033573 / 50000) (2067149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949596416 :
    ThetaLowerSegment 949596416 949661952 (94955233837801 / 100000) (2967560292074 / 3125) := by
  exact
    packedTile32768 949596416 949661952 13 3239 30815 30 _ _ (2067153 / 100000) (516789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949661952 :
    ThetaLowerSegment 949661952 949727488 (2967560292074 / 3125) (11871053303781 / 12500) := by
  exact
    packedTile32768 949661952 949727488 13 3143 30816 30 _ _ (51679 / 2500) (2067163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949727488 :
    ThetaLowerSegment 949727488 949793024 (11871053303781 / 12500) (18994975611691 / 20000) := by
  exact
    packedTile32768 949727488 949793024 13 3121 30817 30 _ _ (2067167 / 100000) (206717 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949793024 :
    ThetaLowerSegment 949793024 949858560 (18994975611691 / 20000) (94981428932861 / 100000) := by
  exact
    packedTile32768 949793024 949858560 13 3169 30818 30 _ _ (1033587 / 50000) (2067177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949858560 :
    ThetaLowerSegment 949858560 949924096 (94981428932861 / 100000) (23746987722229 / 25000) := by
  exact
    packedTile32768 949858560 949924096 13 3155 30819 30 _ _ (2067181 / 100000) (129199 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949924096 :
    ThetaLowerSegment 949924096 949989632 (23746987722229 / 25000) (2968581153073 / 3125) := by
  exact
    packedTile32768 949924096 949989632 13 3215 30820 30 _ _ (516797 / 25000) (2067191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell949989632 :
    ThetaLowerSegment 949989632 950055168 (2968581153073 / 3125) (95001110629781 / 100000) := by
  exact
    packedTile32768 949989632 950055168 13 3151 30821 30 _ _ (413439 / 20000) (1033599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950055168 :
    ThetaLowerSegment 950055168 950120704 (95001110629781 / 100000) (95007609912869 / 100000) := by
  exact
    packedTile32768 950055168 950120704 13 3144 30822 30 _ _ (1033601 / 50000) (413441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950120704 :
    ThetaLowerSegment 950120704 950186240 (95007609912869 / 100000) (95014142290149 / 100000) := by
  exact
    packedTile32768 950120704 950186240 13 3160 30824 30 _ _ (258401 / 12500) (2067211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950186240 :
    ThetaLowerSegment 950186240 950251776 (95014142290149 / 100000) (95020687092839 / 100000) := by
  exact
    packedTile32768 950186240 950251776 13 3166 30825 30 _ _ (413443 / 20000) (1033609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950251776 :
    ThetaLowerSegment 950251776 950317312 (95020687092839 / 100000) (95027180237141 / 100000) := by
  exact
    packedTile32768 950251776 950317312 13 3141 30826 30 _ _ (1033611 / 50000) (82689 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950317312 :
    ThetaLowerSegment 950317312 950382848 (95027180237141 / 100000) (95033778832109 / 100000) := by
  exact
    packedTile32768 950317312 950382848 13 3192 30827 30 _ _ (2067229 / 100000) (64601 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950382848 :
    ThetaLowerSegment 950382848 950448384 (95033778832109 / 100000) (95040238944609 / 100000) := by
  exact
    packedTile32768 950382848 950448384 13 3125 30828 30 _ _ (516809 / 25000) (2067239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950448384 :
    ThetaLowerSegment 950448384 950513920 (95040238944609 / 100000) (95046730087629 / 100000) := by
  exact
    packedTile32768 950448384 950513920 13 3140 30829 30 _ _ (2067243 / 100000) (1033623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950513920 :
    ThetaLowerSegment 950513920 950579456 (95046730087629 / 100000) (95053260530379 / 100000) := by
  exact
    packedTile32768 950513920 950579456 13 3159 30830 30 _ _ (8269 / 400) (2067253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950579456 :
    ThetaLowerSegment 950579456 950644992 (95053260530379 / 100000) (95059896425349 / 100000) := by
  exact
    packedTile32768 950579456 950644992 13 3210 30831 30 _ _ (2067257 / 100000) (103363 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950644992 :
    ThetaLowerSegment 950644992 950710528 (95059896425349 / 100000) (95066441383173 / 100000) := by
  exact
    packedTile32768 950644992 950710528 13 3166 30832 30 _ _ (64602 / 3125) (2067267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950710528 :
    ThetaLowerSegment 950710528 950776064 (95066441383173 / 100000) (23768235737617 / 25000) := by
  exact
    packedTile32768 950710528 950776064 13 3145 30833 30 _ _ (2067271 / 100000) (1033637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950776064 :
    ThetaLowerSegment 950776064 950841600 (23768235737617 / 25000) (95079473478511 / 100000) := by
  exact
    packedTile32768 950776064 950841600 13 3159 30834 30 _ _ (2067277 / 100000) (25841 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950841600 :
    ThetaLowerSegment 950841600 950907136 (95079473478511 / 100000) (95086146671263 / 100000) := by
  exact
    packedTile32768 950841600 950907136 13 3228 30835 30 _ _ (516821 / 25000) (2067287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950907136 :
    ThetaLowerSegment 950907136 950972672 (95086146671263 / 100000) (47546344823639 / 50000) := by
  exact
    packedTile32768 950907136 950972672 13 3165 30836 30 _ _ (2067291 / 100000) (1033647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell950972672 :
    ThetaLowerSegment 950972672 951038208 (47546344823639 / 50000) (1901986678861 / 2000) := by
  exact
    packedTile32768 950972672 951038208 13 3214 30837 30 _ _ (1033649 / 50000) (2067301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951038208 :
    ThetaLowerSegment 951038208 951103744 (1901986678861 / 2000) (9510585835763 / 10000) := by
  exact
    packedTile32768 951038208 951103744 13 3156 30838 30 _ _ (413461 / 20000) (516827 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951103744 :
    ThetaLowerSegment 951103744 951169280 (9510585835763 / 10000) (9511227736139 / 10000) := by
  exact
    packedTile32768 951103744 951169280 13 3105 30839 30 _ _ (129207 / 6250) (413463 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951169280 :
    ThetaLowerSegment 951169280 951234816 (9511227736139 / 10000) (47559475333561 / 50000) := by
  exact
    packedTile32768 951169280 951234816 13 3228 30841 30 _ _ (2067319 / 100000) (1033661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951234816 :
    ThetaLowerSegment 951234816 951300352 (47559475333561 / 50000) (23781343462251 / 25000) := by
  exact
    packedTile32768 951234816 951300352 13 3107 30842 30 _ _ (1033663 / 50000) (2067329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951300352 :
    ThetaLowerSegment 951300352 951365888 (23781343462251 / 25000) (3805270228239 / 4000) := by
  exact
    packedTile32768 951300352 951365888 13 3087 30843 30 _ _ (2067333 / 100000) (258417 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951365888 :
    ThetaLowerSegment 951365888 951431424 (3805270228239 / 4000) (19027661834121 / 20000) := by
  exact
    packedTile32768 951365888 951431424 13 3170 30844 30 _ _ (2067339 / 100000) (1033671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951431424 :
    ThetaLowerSegment 951431424 951496960 (19027661834121 / 20000) (95145025977759 / 100000) := by
  exact
    packedTile32768 951431424 951496960 13 3249 30845 30 _ _ (1033673 / 50000) (2067349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951496960 :
    ThetaLowerSegment 951496960 951562496 (95145025977759 / 100000) (95151550543827 / 100000) := by
  exact
    packedTile32768 951496960 951562496 13 3156 30846 30 _ _ (2067353 / 100000) (516839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951562496 :
    ThetaLowerSegment 951562496 951628032 (95151550543827 / 100000) (95158161961107 / 100000) := by
  exact
    packedTile32768 951562496 951628032 13 3198 30847 30 _ _ (12921 / 625) (2067363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951628032 :
    ThetaLowerSegment 951628032 951693568 (95158161961107 / 100000) (95164616280881 / 100000) := by
  exact
    packedTile32768 951628032 951693568 13 3122 30848 30 _ _ (2067367 / 100000) (206737 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951693568 :
    ThetaLowerSegment 951693568 951759104 (95164616280881 / 100000) (95171126441607 / 100000) := by
  exact
    packedTile32768 951693568 951759104 13 3149 30849 30 _ _ (1033687 / 50000) (2067377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951759104 :
    ThetaLowerSegment 951759104 951824640 (95171126441607 / 100000) (95177733791283 / 100000) := by
  exact
    packedTile32768 951759104 951824640 13 3196 30850 30 _ _ (2067381 / 100000) (258423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951824640 :
    ThetaLowerSegment 951824640 951890176 (95177733791283 / 100000) (95184270872139 / 100000) := by
  exact
    packedTile32768 951824640 951890176 13 3162 30851 30 _ _ (516847 / 25000) (2067391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951890176 :
    ThetaLowerSegment 951890176 951955712 (95184270872139 / 100000) (47595427762607 / 50000) := by
  exact
    packedTile32768 951890176 951955712 13 3185 30852 30 _ _ (413479 / 20000) (1033699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell951955712 :
    ThetaLowerSegment 951955712 952021248 (47595427762607 / 50000) (95197527028241 / 100000) := by
  exact
    packedTile32768 951955712 952021248 13 3227 30853 30 _ _ (2067401 / 100000) (516851 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952021248 :
    ThetaLowerSegment 952021248 952086784 (95197527028241 / 100000) (19040813247949 / 20000) := by
  exact
    packedTile32768 952021248 952086784 13 3163 30854 30 _ _ (129213 / 6250) (2067411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952086784 :
    ThetaLowerSegment 952086784 952152320 (19040813247949 / 20000) (952105930689 / 1000) := by
  exact
    packedTile32768 952086784 952152320 13 3157 30855 30 _ _ (413483 / 20000) (1033709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952152320 :
    ThetaLowerSegment 952152320 952217856 (952105930689 / 1000) (2975539972239 / 3125) := by
  exact
    packedTile32768 952152320 952217856 13 3234 30856 30 _ _ (1033711 / 50000) (82697 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952217856 :
    ThetaLowerSegment 952217856 952283392 (2975539972239 / 3125) (47611879217067 / 50000) := by
  exact
    packedTile32768 952217856 952283392 13 3134 30858 30 _ _ (2067429 / 100000) (258429 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952283392 :
    ThetaLowerSegment 952283392 952348928 (47611879217067 / 50000) (47615153001973 / 50000) := by
  exact
    packedTile32768 952283392 952348928 13 3167 30859 30 _ _ (516859 / 25000) (2067439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952348928 :
    ThetaLowerSegment 952348928 952414464 (47615153001973 / 50000) (19047360795459 / 20000) := by
  exact
    packedTile32768 952348928 952414464 13 3143 30860 30 _ _ (2067443 / 100000) (1033723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952414464 :
    ThetaLowerSegment 952414464 952480000 (19047360795459 / 20000) (19048658740569 / 20000) := by
  exact
    packedTile32768 952414464 952480000 13 3139 30861 30 _ _ (41349 / 2000) (2067453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952480000 :
    ThetaLowerSegment 952480000 952545536 (19048658740569 / 20000) (19049975710041 / 20000) := by
  exact
    packedTile32768 952480000 952545536 13 3185 30862 30 _ _ (64608 / 3125) (2067459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952545536 :
    ThetaLowerSegment 952545536 952611072 (19049975710041 / 20000) (11907040354047 / 12500) := by
  exact
    packedTile32768 952545536 952611072 13 3117 30863 30 _ _ (2067463 / 100000) (1033733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952611072 :
    ThetaLowerSegment 952611072 952676608 (11907040354047 / 12500) (47631402175413 / 50000) := by
  exact
    packedTile32768 952611072 952676608 13 3135 30864 30 _ _ (206747 / 10000) (2067473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952676608 :
    ThetaLowerSegment 952676608 952742144 (47631402175413 / 50000) (9526948643649 / 10000) := by
  exact
    packedTile32768 952676608 952742144 13 3232 30865 30 _ _ (2067477 / 100000) (51687 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952742144 :
    ThetaLowerSegment 952742144 952807680 (9526948643649 / 10000) (47638033619031 / 50000) := by
  exact
    packedTile32768 952742144 952807680 13 3183 30866 30 _ _ (516871 / 25000) (2067487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952807680 :
    ThetaLowerSegment 952807680 952873216 (47638033619031 / 50000) (19056517207437 / 20000) := by
  exact
    packedTile32768 952807680 952873216 13 3153 30867 30 _ _ (2067491 / 100000) (1033747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952873216 :
    ThetaLowerSegment 952873216 952938752 (19056517207437 / 20000) (95289113128371 / 100000) := by
  exact
    packedTile32768 952873216 952938752 13 3157 30868 30 _ _ (1033749 / 50000) (2067501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell952938752 :
    ThetaLowerSegment 952938752 953004288 (95289113128371 / 100000) (95295733279381 / 100000) := by
  exact
    packedTile32768 952938752 953004288 13 3202 30869 30 _ _ (413501 / 20000) (516877 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953004288 :
    ThetaLowerSegment 953004288 953069824 (95295733279381 / 100000) (95302307964361 / 100000) := by
  exact
    packedTile32768 953004288 953069824 13 3180 30870 30 _ _ (2067511 / 100000) (1033757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953069824 :
    ThetaLowerSegment 953069824 953135360 (95302307964361 / 100000) (95308915751889 / 100000) := by
  exact
    packedTile32768 953069824 953135360 13 3196 30871 30 _ _ (1033759 / 50000) (2067521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953135360 :
    ThetaLowerSegment 953135360 953200896 (95308915751889 / 100000) (95315453265939 / 100000) := by
  exact
    packedTile32768 953135360 953200896 13 3162 30872 30 _ _ (82701 / 4000) (258441 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953200896 :
    ThetaLowerSegment 953200896 953266432 (95315453265939 / 100000) (95322090043659 / 100000) := by
  exact
    packedTile32768 953200896 953266432 13 3210 30873 30 _ _ (516883 / 25000) (413507 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953266432 :
    ThetaLowerSegment 953266432 953331968 (95322090043659 / 100000) (95328648277367 / 100000) := by
  exact
    packedTile32768 953266432 953331968 13 3172 30875 30 _ _ (2067539 / 100000) (1033771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953331968 :
    ThetaLowerSegment 953331968 953397504 (95328648277367 / 100000) (95335194128003 / 100000) := by
  exact
    packedTile32768 953331968 953397504 13 3166 30876 30 _ _ (1033773 / 50000) (2067549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953397504 :
    ThetaLowerSegment 953397504 953463040 (95335194128003 / 100000) (95341764811437 / 100000) := by
  exact
    packedTile32768 953397504 953463040 13 3178 30877 30 _ _ (2067553 / 100000) (516889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953463040 :
    ThetaLowerSegment 953463040 953528576 (95341764811437 / 100000) (95348376868317 / 100000) := by
  exact
    packedTile32768 953463040 953528576 13 3198 30878 30 _ _ (51689 / 2500) (2067563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953528576 :
    ThetaLowerSegment 953528576 953594112 (95348376868317 / 100000) (19070964707821 / 20000) := by
  exact
    packedTile32768 953528576 953594112 13 3118 30879 30 _ _ (1033783 / 50000) (2067569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953594112 :
    ThetaLowerSegment 953594112 953659648 (19070964707821 / 20000) (3814456763879 / 4000) := by
  exact
    packedTile32768 953594112 953659648 13 3190 30880 30 _ _ (2067573 / 100000) (258447 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953659648 :
    ThetaLowerSegment 953659648 953725184 (3814456763879 / 4000) (19073599213791 / 20000) := by
  exact
    packedTile32768 953659648 953725184 13 3181 30881 30 _ _ (103379 / 5000) (2067583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953725184 :
    ThetaLowerSegment 953725184 953790720 (19073599213791 / 20000) (95374417994177 / 100000) := by
  exact
    packedTile32768 953725184 953790720 13 3106 30882 30 _ _ (2067587 / 100000) (206759 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953790720 :
    ThetaLowerSegment 953790720 953856256 (95374417994177 / 100000) (95380992943097 / 100000) := by
  exact
    packedTile32768 953790720 953856256 13 3180 30883 30 _ _ (1033797 / 50000) (2067597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953856256 :
    ThetaLowerSegment 953856256 953921792 (95380992943097 / 100000) (47693847018969 / 50000) := by
  exact
    packedTile32768 953856256 953921792 13 3241 30884 30 _ _ (2067601 / 100000) (516901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953921792 :
    ThetaLowerSegment 953921792 953987328 (47693847018969 / 50000) (47697110738197 / 50000) := by
  exact
    packedTile32768 953921792 953987328 13 3157 30885 30 _ _ (258451 / 12500) (2067611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell953987328 :
    ThetaLowerSegment 953987328 954052864 (47697110738197 / 50000) (95400802694939 / 100000) := by
  exact
    packedTile32768 953987328 954052864 13 3183 30886 30 _ _ (413523 / 20000) (1033809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954052864 :
    ThetaLowerSegment 954052864 954118400 (95400802694939 / 100000) (19081473891847 / 20000) := by
  exact
    packedTile32768 954052864 954118400 13 3176 30887 30 _ _ (2067621 / 100000) (258453 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954118400 :
    ThetaLowerSegment 954118400 954183936 (19081473891847 / 20000) (95413998274603 / 100000) := by
  exact
    packedTile32768 954118400 954183936 13 3206 30888 30 _ _ (516907 / 25000) (2067631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954183936 :
    ThetaLowerSegment 954183936 954249472 (95413998274603 / 100000) (11927568309331 / 12500) := by
  exact
    packedTile32768 954183936 954249472 13 3167 30889 30 _ _ (413527 / 20000) (1033819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954249472 :
    ThetaLowerSegment 954249472 954315008 (11927568309331 / 12500) (47713601107123 / 50000) := by
  exact
    packedTile32768 954249472 954315008 13 3219 30890 30 _ _ (1033821 / 50000) (413529 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954315008 :
    ThetaLowerSegment 954315008 954380544 (47713601107123 / 50000) (47716839045457 / 50000) := by
  exact
    packedTile32768 954315008 954380544 13 3132 30891 30 _ _ (2067649 / 100000) (516913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954380544 :
    ThetaLowerSegment 954380544 954446080 (47716839045457 / 50000) (47720094569829 / 50000) := by
  exact
    packedTile32768 954380544 954446080 13 3149 30893 30 _ _ (258457 / 12500) (2067659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954446080 :
    ThetaLowerSegment 954446080 954511616 (47720094569829 / 50000) (95446671263163 / 100000) := by
  exact
    packedTile32768 954446080 954511616 13 3135 30894 30 _ _ (2067663 / 100000) (1033833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954511616 :
    ThetaLowerSegment 954511616 954577152 (95446671263163 / 100000) (95453240250753 / 100000) := by
  exact
    packedTile32768 954511616 954577152 13 3177 30895 30 _ _ (206767 / 10000) (2067673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954577152 :
    ThetaLowerSegment 954577152 954642688 (95453240250753 / 100000) (95459774106913 / 100000) := by
  exact
    packedTile32768 954577152 954642688 13 3160 30896 30 _ _ (516919 / 25000) (2067679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954642688 :
    ThetaLowerSegment 954642688 954708224 (95459774106913 / 100000) (19093275657283 / 20000) := by
  exact
    packedTile32768 954642688 954708224 13 3194 30897 30 _ _ (2067683 / 100000) (1033843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954708224 :
    ThetaLowerSegment 954708224 954773760 (19093275657283 / 20000) (19094610144409 / 20000) := by
  exact
    packedTile32768 954708224 954773760 13 3227 30898 30 _ _ (206769 / 10000) (2067693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954773760 :
    ThetaLowerSegment 954773760 954839296 (19094610144409 / 20000) (19095921064307 / 20000) := by
  exact
    packedTile32768 954773760 954839296 13 3170 30899 30 _ _ (2067697 / 100000) (20677 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954839296 :
    ThetaLowerSegment 954839296 954904832 (19095921064307 / 20000) (95486102047503 / 100000) := by
  exact
    packedTile32768 954839296 954904832 13 3142 30900 30 _ _ (258463 / 12500) (2067707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954904832 :
    ThetaLowerSegment 954904832 954970368 (95486102047503 / 100000) (23873168825193 / 25000) := by
  exact
    packedTile32768 954904832 954970368 13 3179 30901 30 _ _ (2067711 / 100000) (1033857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell954970368 :
    ThetaLowerSegment 954970368 955035904 (23873168825193 / 25000) (4774962118657 / 5000) := by
  exact
    packedTile32768 954970368 955035904 13 3176 30902 30 _ _ (1033859 / 50000) (2067721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955035904 :
    ThetaLowerSegment 955035904 955101440 (4774962118657 / 5000) (11938234195501 / 12500) := by
  exact
    packedTile32768 955035904 955101440 13 3207 30903 30 _ _ (516931 / 25000) (2067727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955101440 :
    ThetaLowerSegment 955101440 955166976 (11938234195501 / 12500) (95512409661699 / 100000) := by
  exact
    packedTile32768 955101440 955166976 13 3161 30904 30 _ _ (2067731 / 100000) (1033867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955166976 :
    ThetaLowerSegment 955166976 955232512 (95512409661699 / 100000) (95518929239613 / 100000) := by
  exact
    packedTile32768 955166976 955232512 13 3153 30905 30 _ _ (1033869 / 50000) (2067741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955232512 :
    ThetaLowerSegment 955232512 955298048 (95518929239613 / 100000) (23881369447007 / 25000) := by
  exact
    packedTile32768 955232512 955298048 13 3167 30906 30 _ _ (413549 / 20000) (516937 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955298048 :
    ThetaLowerSegment 955298048 955363584 (23881369447007 / 25000) (23883043292251 / 25000) := by
  exact
    packedTile32768 955298048 955363584 13 3238 30907 30 _ _ (258469 / 12500) (413551 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955363584 :
    ThetaLowerSegment 955363584 955429120 (23883043292251 / 25000) (95538672135541 / 100000) := by
  exact
    packedTile32768 955363584 955429120 13 3143 30908 30 _ _ (2067759 / 100000) (1033881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955429120 :
    ThetaLowerSegment 955429120 955494656 (95538672135541 / 100000) (95545264173549 / 100000) := by
  exact
    packedTile32768 955429120 955494656 13 3188 30910 30 _ _ (1033883 / 50000) (2067769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955494656 :
    ThetaLowerSegment 955494656 955560192 (95545264173549 / 100000) (95551806604157 / 100000) := by
  exact
    packedTile32768 955494656 955560192 13 3164 30911 30 _ _ (516943 / 25000) (82711 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955560192 :
    ThetaLowerSegment 955560192 955625728 (95551806604157 / 100000) (95558266345753 / 100000) := by
  exact
    packedTile32768 955560192 955625728 13 3124 30912 30 _ _ (2067779 / 100000) (1033891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955625728 :
    ThetaLowerSegment 955625728 955691264 (95558266345753 / 100000) (95564769532723 / 100000) := by
  exact
    packedTile32768 955625728 955691264 13 3145 30913 30 _ _ (1033893 / 50000) (2067789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955691264 :
    ThetaLowerSegment 955691264 955756800 (95564769532723 / 100000) (764569669121 / 800) := by
  exact
    packedTile32768 955691264 955756800 13 3114 30914 30 _ _ (2067793 / 100000) (516949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955756800 :
    ThetaLowerSegment 955756800 955822336 (764569669121 / 800) (3823111700613 / 4000) := by
  exact
    packedTile32768 955756800 955822336 13 3184 30915 30 _ _ (10339 / 500) (2067803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955822336 :
    ThetaLowerSegment 955822336 955887872 (3823111700613 / 4000) (597402107028 / 625) := by
  exact
    packedTile32768 955822336 955887872 13 3165 30916 30 _ _ (2067807 / 100000) (206781 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955887872 :
    ThetaLowerSegment 955887872 955953408 (597402107028 / 625) (47795364368777 / 50000) := by
  exact
    packedTile32768 955887872 955953408 13 3091 30917 30 _ _ (1033907 / 50000) (2067817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell955953408 :
    ThetaLowerSegment 955953408 956018944 (47795364368777 / 50000) (47798670812957 / 50000) := by
  exact
    packedTile32768 955953408 956018944 13 3198 30918 30 _ _ (103391 / 5000) (2067823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956018944 :
    ThetaLowerSegment 956018944 956084480 (47798670812957 / 50000) (47801917301347 / 50000) := by
  exact
    packedTile32768 956018944 956084480 13 3140 30919 30 _ _ (2067827 / 100000) (206783 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956084480 :
    ThetaLowerSegment 956084480 956150016 (47801917301347 / 50000) (47805153461557 / 50000) := by
  exact
    packedTile32768 956084480 956150016 13 3130 30920 30 _ _ (1033917 / 50000) (2067837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956150016 :
    ThetaLowerSegment 956150016 956215552 (47805153461557 / 50000) (95616917810791 / 100000) := by
  exact
    packedTile32768 956150016 956215552 13 3197 30921 30 _ _ (2067841 / 100000) (516961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956215552 :
    ThetaLowerSegment 956215552 956281088 (95616917810791 / 100000) (95623553535023 / 100000) := by
  exact
    packedTile32768 956215552 956281088 13 3209 30922 30 _ _ (258481 / 12500) (2067851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956281088 :
    ThetaLowerSegment 956281088 956346624 (95623553535023 / 100000) (23907515268677 / 25000) := by
  exact
    packedTile32768 956281088 956346624 13 3147 30923 30 _ _ (413571 / 20000) (1033929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956346624 :
    ThetaLowerSegment 956346624 956412160 (23907515268677 / 25000) (478183039629 / 500) := by
  exact
    packedTile32768 956346624 956412160 13 3166 30924 30 _ _ (1033931 / 50000) (413573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956412160 :
    ThetaLowerSegment 956412160 956477696 (478183039629 / 500) (23910766469391 / 25000) := by
  exact
    packedTile32768 956412160 956477696 13 3123 30925 30 _ _ (516967 / 25000) (2067871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956477696 :
    ThetaLowerSegment 956477696 956543232 (23910766469391 / 25000) (47824831199407 / 50000) := by
  exact
    packedTile32768 956477696 956543232 13 3190 30926 30 _ _ (16543 / 800) (1033939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956543232 :
    ThetaLowerSegment 956543232 956608768 (47824831199407 / 50000) (47828092249321 / 50000) := by
  exact
    packedTile32768 956543232 956608768 13 3154 30928 30 _ _ (1033941 / 50000) (413577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956608768 :
    ThetaLowerSegment 956608768 956674304 (47828092249321 / 50000) (95662861712223 / 100000) := by
  exact
    packedTile32768 956608768 956674304 13 3229 30929 30 _ _ (2067889 / 100000) (516973 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956674304 :
    ThetaLowerSegment 956674304 956739840 (95662861712223 / 100000) (95669396263583 / 100000) := by
  exact
    packedTile32768 956674304 956739840 13 3160 30930 30 _ _ (258487 / 12500) (2067899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956739840 :
    ThetaLowerSegment 956739840 956805376 (95669396263583 / 100000) (5979748649927 / 6250) := by
  exact
    packedTile32768 956739840 956805376 13 3183 30931 30 _ _ (2067903 / 100000) (1033953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956805376 :
    ThetaLowerSegment 956805376 956870912 (5979748649927 / 6250) (47841255463261 / 50000) := by
  exact
    packedTile32768 956805376 956870912 13 3159 30932 30 _ _ (206791 / 10000) (2067913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956870912 :
    ThetaLowerSegment 956870912 956936448 (47841255463261 / 50000) (9568922751769 / 10000) := by
  exact
    packedTile32768 956870912 956936448 13 3248 30933 30 _ _ (516979 / 25000) (2067919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell956936448 :
    ThetaLowerSegment 956936448 957001984 (9568922751769 / 10000) (95695789037369 / 100000) := by
  exact
    packedTile32768 956936448 957001984 13 3173 30934 30 _ _ (2067923 / 100000) (1033963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957001984 :
    ThetaLowerSegment 957001984 957067520 (95695789037369 / 100000) (95702156193839 / 100000) := by
  exact
    packedTile32768 957001984 957067520 13 3079 30935 30 _ _ (206793 / 10000) (2067933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957067520 :
    ThetaLowerSegment 957067520 957133056 (95702156193839 / 100000) (95708785999861 / 100000) := by
  exact
    packedTile32768 957067520 957133056 13 3206 30936 30 _ _ (2067937 / 100000) (103397 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957133056 :
    ThetaLowerSegment 957133056 957198592 (95708785999861 / 100000) (3828616633133 / 4000) := by
  exact
    packedTile32768 957133056 957198592 13 3206 30937 30 _ _ (258493 / 12500) (2067947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957198592 :
    ThetaLowerSegment 957198592 957264128 (3828616633133 / 4000) (47861028009493 / 50000) := by
  exact
    packedTile32768 957198592 957264128 13 3211 30938 30 _ _ (2067951 / 100000) (1033977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957264128 :
    ThetaLowerSegment 957264128 957329664 (47861028009493 / 50000) (95728659005687 / 100000) := by
  exact
    packedTile32768 957264128 957329664 13 3193 30939 30 _ _ (2067957 / 100000) (51699 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957329664 :
    ThetaLowerSegment 957329664 957395200 (95728659005687 / 100000) (19147056125283 / 20000) := by
  exact
    packedTile32768 957329664 957395200 13 3202 30940 30 _ _ (516991 / 25000) (2067967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957395200 :
    ThetaLowerSegment 957395200 957460736 (19147056125283 / 20000) (1914837342281 / 2000) := by
  exact
    packedTile32768 957395200 957460736 13 3185 30941 30 _ _ (2067971 / 100000) (1033987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957460736 :
    ThetaLowerSegment 957460736 957526272 (1914837342281 / 2000) (23937088590259 / 25000) := by
  exact
    packedTile32768 957460736 957526272 13 3137 30942 30 _ _ (1033989 / 50000) (2067981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957526272 :
    ThetaLowerSegment 957526272 957591808 (23937088590259 / 25000) (47877504568383 / 50000) := by
  exact
    packedTile32768 957526272 957591808 13 3218 30943 30 _ _ (413597 / 20000) (516997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957591808 :
    ThetaLowerSegment 957591808 957657344 (47877504568383 / 50000) (47880767859759 / 50000) := by
  exact
    packedTile32768 957591808 957657344 13 3156 30944 30 _ _ (258499 / 12500) (413599 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957657344 :
    ThetaLowerSegment 957657344 957722880 (47880767859759 / 50000) (95768109888339 / 100000) := by
  exact
    packedTile32768 957657344 957722880 13 3179 30946 30 _ _ (2067999 / 100000) (1034001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957722880 :
    ThetaLowerSegment 957722880 957788416 (95768109888339 / 100000) (95774624104089 / 100000) := by
  exact
    packedTile32768 957722880 957788416 13 3150 30947 30 _ _ (413601 / 20000) (258501 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957788416 :
    ThetaLowerSegment 957788416 957853952 (95774624104089 / 100000) (95781221062369 / 100000) := by
  exact
    packedTile32768 957788416 957853952 13 3190 30948 30 _ _ (517003 / 25000) (413603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957853952 :
    ThetaLowerSegment 957853952 957919488 (95781221062369 / 100000) (95787896627701 / 100000) := by
  exact
    packedTile32768 957853952 957919488 13 3228 30949 30 _ _ (2068019 / 100000) (1034011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957919488 :
    ThetaLowerSegment 957919488 957985024 (95787896627701 / 100000) (95794324052509 / 100000) := by
  exact
    packedTile32768 957919488 957985024 13 3108 30950 30 _ _ (1034013 / 50000) (2068029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell957985024 :
    ThetaLowerSegment 957985024 958050560 (95794324052509 / 100000) (47900422280279 / 50000) := by
  exact
    packedTile32768 957985024 958050560 13 3153 30951 30 _ _ (2068033 / 100000) (517009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958050560 :
    ThetaLowerSegment 958050560 958116096 (47900422280279 / 50000) (47903715633979 / 50000) := by
  exact
    packedTile32768 958050560 958116096 13 3185 30952 30 _ _ (51701 / 2500) (2068043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958116096 :
    ThetaLowerSegment 958116096 958181632 (47903715633979 / 50000) (47906950057923 / 50000) := by
  exact
    packedTile32768 958116096 958181632 13 3128 30953 30 _ _ (1034023 / 50000) (2068049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958181632 :
    ThetaLowerSegment 958181632 958247168 (47906950057923 / 50000) (3832816000257 / 4000) := by
  exact
    packedTile32768 958181632 958247168 13 3143 30954 30 _ _ (2068053 / 100000) (258507 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958247168 :
    ThetaLowerSegment 958247168 958312704 (3832816000257 / 4000) (3833076989429 / 4000) := by
  exact
    packedTile32768 958247168 958312704 13 3155 30955 30 _ _ (103403 / 5000) (2068063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958312704 :
    ThetaLowerSegment 958312704 958378240 (3833076989429 / 4000) (95833517733321 / 100000) := by
  exact
    packedTile32768 958312704 958378240 13 3188 30956 30 _ _ (2068067 / 100000) (206807 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958378240 :
    ThetaLowerSegment 958378240 958443776 (95833517733321 / 100000) (95840059051383 / 100000) := by
  exact
    packedTile32768 958378240 958443776 13 3163 30957 30 _ _ (1034037 / 50000) (2068077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958443776 :
    ThetaLowerSegment 958443776 958509312 (95840059051383 / 100000) (95846788586957 / 100000) := by
  exact
    packedTile32768 958443776 958509312 13 3254 30958 30 _ _ (2068081 / 100000) (517021 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958509312 :
    ThetaLowerSegment 958509312 958574848 (95846788586957 / 100000) (47926656700721 / 50000) := by
  exact
    packedTile32768 958509312 958574848 13 3155 30959 30 _ _ (2068087 / 100000) (206809 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958574848 :
    ThetaLowerSegment 958574848 958640384 (47926656700721 / 50000) (9585993543843 / 10000) := by
  exact
    packedTile32768 958574848 958640384 13 3202 30960 30 _ _ (1034047 / 50000) (2068097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958640384 :
    ThetaLowerSegment 958640384 958705920 (9585993543843 / 10000) (479332456593 / 500) := by
  exact
    packedTile32768 958640384 958705920 13 3170 30961 30 _ _ (2068101 / 100000) (258513 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958705920 :
    ThetaLowerSegment 958705920 958771456 (479332456593 / 500) (4793654946183 / 5000) := by
  exact
    packedTile32768 958705920 958771456 13 3195 30962 30 _ _ (517027 / 25000) (2068111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958771456 :
    ThetaLowerSegment 958771456 958836992 (4793654946183 / 5000) (2396988165627 / 2500) := by
  exact
    packedTile32768 958771456 958836992 13 3108 30964 30 _ _ (413623 / 20000) (1034059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958836992 :
    ThetaLowerSegment 958836992 958902528 (2396988165627 / 2500) (47943050592459 / 50000) := by
  exact
    packedTile32768 958836992 958902528 13 3179 30965 30 _ _ (1034061 / 50000) (3309 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958902528 :
    ThetaLowerSegment 958902528 958968064 (47943050592459 / 50000) (47946294451227 / 50000) := by
  exact
    packedTile32768 958902528 958968064 13 3137 30966 30 _ _ (64629 / 3125) (2068131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell958968064 :
    ThetaLowerSegment 958968064 959033600 (47946294451227 / 50000) (11987404486043 / 12500) := by
  exact
    packedTile32768 958968064 959033600 13 3214 30967 30 _ _ (413627 / 20000) (1034069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959033600 :
    ThetaLowerSegment 959033600 959099136 (11987404486043 / 12500) (2997057677193 / 3125) := by
  exact
    packedTile32768 959033600 959099136 13 3196 30968 30 _ _ (1034071 / 50000) (413629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959099136 :
    ThetaLowerSegment 959099136 959164672 (2997057677193 / 3125) (95912478224019 / 100000) := by
  exact
    packedTile32768 959099136 959164672 13 3207 30969 30 _ _ (2068149 / 100000) (258519 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959164672 :
    ThetaLowerSegment 959164672 959230208 (95912478224019 / 100000) (19183796928559 / 20000) := by
  exact
    packedTile32768 959164672 959230208 13 3146 30970 30 _ _ (517039 / 25000) (2068159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959230208 :
    ThetaLowerSegment 959230208 959295744 (19183796928559 / 20000) (95925681354589 / 100000) := by
  exact
    packedTile32768 959230208 959295744 13 3238 30971 30 _ _ (2068163 / 100000) (1034083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959295744 :
    ThetaLowerSegment 959295744 959361280 (95925681354589 / 100000) (47966142509103 / 50000) := by
  exact
    packedTile32768 959295744 959361280 13 3193 30972 30 _ _ (2068169 / 100000) (517043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959361280 :
    ThetaLowerSegment 959361280 959426816 (47966142509103 / 50000) (47969412295359 / 50000) := by
  exact
    packedTile32768 959361280 959426816 13 3162 30973 30 _ _ (129261 / 6250) (2068179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959426816 :
    ThetaLowerSegment 959426816 959492352 (47969412295359 / 50000) (95945395208109 / 100000) := by
  exact
    packedTile32768 959426816 959492352 13 3177 30974 30 _ _ (2068183 / 100000) (1034093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959492352 :
    ThetaLowerSegment 959492352 959557888 (95945395208109 / 100000) (95951852097289 / 100000) := by
  exact
    packedTile32768 959492352 959557888 13 3122 30975 30 _ _ (206819 / 10000) (2068193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959557888 :
    ThetaLowerSegment 959557888 959623424 (95951852097289 / 100000) (95958358645051 / 100000) := by
  exact
    packedTile32768 959557888 959623424 13 3146 30976 30 _ _ (2068197 / 100000) (10341 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959623424 :
    ThetaLowerSegment 959623424 959688960 (95958358645051 / 100000) (95964964488627 / 100000) := by
  exact
    packedTile32768 959623424 959688960 13 3194 30977 30 _ _ (517051 / 25000) (2068207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959688960 :
    ThetaLowerSegment 959688960 959754496 (95964964488627 / 100000) (95971560010317 / 100000) := by
  exact
    packedTile32768 959688960 959754496 13 3189 30978 30 _ _ (206821 / 10000) (2068213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959754496 :
    ThetaLowerSegment 959754496 959820032 (95971560010317 / 100000) (95978033529527 / 100000) := by
  exact
    packedTile32768 959754496 959820032 13 3130 30979 30 _ _ (2068217 / 100000) (103411 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959820032 :
    ThetaLowerSegment 959820032 959885568 (95978033529527 / 100000) (95984678733239 / 100000) := by
  exact
    packedTile32768 959820032 959885568 13 3213 30980 30 _ _ (64632 / 3125) (2068227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959885568 :
    ThetaLowerSegment 959885568 959951104 (95984678733239 / 100000) (95991235025509 / 100000) := by
  exact
    packedTile32768 959885568 959951104 13 3170 30982 30 _ _ (2068231 / 100000) (1034117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell959951104 :
    ThetaLowerSegment 959951104 960016640 (95991235025509 / 100000) (95997747906971 / 100000) := by
  exact
    packedTile32768 959951104 960016640 13 3149 30983 30 _ _ (1034119 / 50000) (2068241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960016640 :
    ThetaLowerSegment 960016640 960082176 (95997747906971 / 100000) (96004291834151 / 100000) := by
  exact
    packedTile32768 960016640 960082176 13 3164 30984 30 _ _ (413649 / 20000) (258531 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960082176 :
    ThetaLowerSegment 960082176 960147712 (96004291834151 / 100000) (96010976421383 / 100000) := by
  exact
    packedTile32768 960082176 960147712 13 3232 30985 30 _ _ (2068251 / 100000) (1034127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960147712 :
    ThetaLowerSegment 960147712 960213248 (96010976421383 / 100000) (96017584505693 / 100000) := by
  exact
    packedTile32768 960147712 960213248 13 3195 30986 30 _ _ (1034129 / 50000) (2068261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960213248 :
    ThetaLowerSegment 960213248 960278784 (96017584505693 / 100000) (48012065282209 / 50000) := by
  exact
    packedTile32768 960213248 960278784 13 3165 30987 30 _ _ (413653 / 20000) (517067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960278784 :
    ThetaLowerSegment 960278784 960344320 (48012065282209 / 50000) (48015368312593 / 50000) := by
  exact
    packedTile32768 960278784 960344320 13 3194 30988 30 _ _ (129267 / 6250) (82731 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960344320 :
    ThetaLowerSegment 960344320 960409856 (48015368312593 / 50000) (48018661012761 / 50000) := by
  exact
    packedTile32768 960344320 960409856 13 3184 30989 30 _ _ (2068279 / 100000) (1034141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960409856 :
    ThetaLowerSegment 960409856 960475392 (48018661012761 / 50000) (48021986816649 / 50000) := by
  exact
    packedTile32768 960409856 960475392 13 3216 30990 30 _ _ (1034143 / 50000) (2068289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960475392 :
    ThetaLowerSegment 960475392 960540928 (48021986816649 / 50000) (48025309527747 / 50000) := by
  exact
    packedTile32768 960475392 960540928 13 3213 30991 30 _ _ (517073 / 25000) (413659 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960540928 :
    ThetaLowerSegment 960540928 960606464 (48025309527747 / 50000) (48028515391197 / 50000) := by
  exact
    packedTile32768 960540928 960606464 13 3100 30992 30 _ _ (2068299 / 100000) (1034151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960606464 :
    ThetaLowerSegment 960606464 960672000 (48028515391197 / 50000) (24015890106109 / 25000) := by
  exact
    packedTile32768 960606464 960672000 13 3157 30993 30 _ _ (1034153 / 50000) (2068309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960672000 :
    ThetaLowerSegment 960672000 960737536 (24015890106109 / 25000) (3002191801868 / 3125) := by
  exact
    packedTile32768 960672000 960737536 13 3180 30994 30 _ _ (2068313 / 100000) (517079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960737536 :
    ThetaLowerSegment 960737536 960803072 (3002191801868 / 3125) (3002396888723 / 3125) := by
  exact
    packedTile32768 960737536 960803072 13 3173 30995 30 _ _ (12927 / 625) (2068323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960803072 :
    ThetaLowerSegment 960803072 960868608 (3002396888723 / 3125) (48041587151323 / 50000) := by
  exact
    packedTile32768 960803072 960868608 13 3130 30996 30 _ _ (2068327 / 100000) (206833 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960868608 :
    ThetaLowerSegment 960868608 960934144 (48041587151323 / 50000) (96089749533253 / 100000) := by
  exact
    packedTile32768 960868608 960934144 13 3179 30997 30 _ _ (2068333 / 100000) (129271 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960934144 :
    ThetaLowerSegment 960934144 960999680 (96089749533253 / 100000) (96096320649433 / 100000) := by
  exact
    packedTile32768 960934144 960999680 13 3177 30998 30 _ _ (103417 / 5000) (2068343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell960999680 :
    ThetaLowerSegment 960999680 961065216 (96096320649433 / 100000) (24025731220351 / 25000) := by
  exact
    packedTile32768 960999680 961065216 13 3193 30999 30 _ _ (2068347 / 100000) (41367 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961065216 :
    ThetaLowerSegment 961065216 961130752 (24025731220351 / 25000) (12013677956209 / 12500) := by
  exact
    packedTile32768 961065216 961130752 13 3142 31001 30 _ _ (1034177 / 50000) (2068357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961130752 :
    ThetaLowerSegment 961130752 961196288 (12013677956209 / 12500) (96116061020121 / 100000) := by
  exact
    packedTile32768 961130752 961196288 13 3209 31002 30 _ _ (2068361 / 100000) (517091 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961196288 :
    ThetaLowerSegment 961196288 961261824 (96116061020121 / 100000) (96122654974117 / 100000) := by
  exact
    packedTile32768 961196288 961261824 13 3188 31003 30 _ _ (2068367 / 100000) (206837 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961261824 :
    ThetaLowerSegment 961261824 961327360 (96122654974117 / 100000) (96129203446201 / 100000) := by
  exact
    packedTile32768 961261824 961327360 13 3166 31004 30 _ _ (1034187 / 50000) (2068377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961327360 :
    ThetaLowerSegment 961327360 961392896 (96129203446201 / 100000) (48067870799271 / 50000) := by
  exact
    packedTile32768 961327360 961392896 13 3161 31005 30 _ _ (2068381 / 100000) (64637 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961392896 :
    ThetaLowerSegment 961392896 961458432 (48067870799271 / 50000) (48071171946519 / 50000) := by
  exact
    packedTile32768 961392896 961458432 13 3192 31006 30 _ _ (517097 / 25000) (2068391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961458432 :
    ThetaLowerSegment 961458432 961523968 (48071171946519 / 50000) (48074489652099 / 50000) := by
  exact
    packedTile32768 961458432 961523968 13 3208 31007 30 _ _ (413679 / 20000) (1034199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961523968 :
    ThetaLowerSegment 961523968 961589504 (48074489652099 / 50000) (48077695675199 / 50000) := by
  exact
    packedTile32768 961523968 961589504 13 3100 31008 30 _ _ (1034201 / 50000) (413681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961589504 :
    ThetaLowerSegment 961589504 961655040 (48077695675199 / 50000) (48080945144167 / 50000) := by
  exact
    packedTile32768 961589504 961655040 13 3142 31009 30 _ _ (258551 / 12500) (2068411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961655040 :
    ThetaLowerSegment 961655040 961720576 (48080945144167 / 50000) (48084167734737 / 50000) := by
  exact
    packedTile32768 961655040 961720576 13 3116 31010 30 _ _ (413683 / 20000) (1034209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961720576 :
    ThetaLowerSegment 961720576 961786112 (48084167734737 / 50000) (3005464546179 / 3125) := by
  exact
    packedTile32768 961720576 961786112 13 3157 31011 30 _ _ (1034211 / 50000) (82737 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961786112 :
    ThetaLowerSegment 961786112 961851648 (3005464546179 / 3125) (19236285720589 / 20000) := by
  exact
    packedTile32768 961786112 961851648 13 3173 31012 30 _ _ (2068429 / 100000) (129277 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961851648 :
    ThetaLowerSegment 961851648 961917184 (19236285720589 / 20000) (96187877986393 / 100000) := by
  exact
    packedTile32768 961851648 961917184 13 3118 31013 30 _ _ (517109 / 25000) (2068439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961917184 :
    ThetaLowerSegment 961917184 961982720 (96187877986393 / 100000) (19238895676963 / 20000) := by
  exact
    packedTile32768 961917184 961982720 13 3191 31014 30 _ _ (1034221 / 50000) (413689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell961982720 :
    ThetaLowerSegment 961982720 962048256 (19238895676963 / 20000) (96200985725369 / 100000) := by
  exact
    packedTile32768 961982720 962048256 13 3146 31015 30 _ _ (2068449 / 100000) (517113 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962048256 :
    ThetaLowerSegment 962048256 962113792 (96200985725369 / 100000) (96207519977873 / 100000) := by
  exact
    packedTile32768 962048256 962113792 13 3159 31016 30 _ _ (258557 / 12500) (2068459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962113792 :
    ThetaLowerSegment 962113792 962179328 (96207519977873 / 100000) (48107022989319 / 50000) := by
  exact
    packedTile32768 962113792 962179328 13 3155 31017 30 _ _ (2068463 / 100000) (1034233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962179328 :
    ThetaLowerSegment 962179328 962244864 (48107022989319 / 50000) (48110264281809 / 50000) := by
  exact
    packedTile32768 962179328 962244864 13 3134 31019 30 _ _ (206847 / 10000) (2068473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962244864 :
    ThetaLowerSegment 962244864 962310400 (48110264281809 / 50000) (9622712079663 / 10000) := by
  exact
    packedTile32768 962244864 962310400 13 3187 31020 30 _ _ (517119 / 25000) (2068479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962310400 :
    ThetaLowerSegment 962310400 962375936 (9622712079663 / 10000) (96233572395107 / 100000) := by
  exact
    packedTile32768 962310400 962375936 13 3119 31021 30 _ _ (2068483 / 100000) (1034243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962375936 :
    ThetaLowerSegment 962375936 962441472 (96233572395107 / 100000) (96240328083447 / 100000) := by
  exact
    packedTile32768 962375936 962441472 13 3266 31022 30 _ _ (206849 / 10000) (2068493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962441472 :
    ThetaLowerSegment 962441472 962507008 (96240328083447 / 100000) (9624690383541 / 10000) := by
  exact
    packedTile32768 962441472 962507008 13 3179 31023 30 _ _ (2068497 / 100000) (4137 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962507008 :
    ThetaLowerSegment 962507008 962572544 (9624690383541 / 10000) (48126791517413 / 50000) := by
  exact
    packedTile32768 962507008 962572544 13 3229 31024 30 _ _ (258563 / 12500) (2068507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962572544 :
    ThetaLowerSegment 962572544 962638080 (48126791517413 / 50000) (48130096996393 / 50000) := by
  exact
    packedTile32768 962572544 962638080 13 3196 31025 30 _ _ (206851 / 10000) (2068513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962638080 :
    ThetaLowerSegment 962638080 962703616 (48130096996393 / 50000) (19253344860191 / 20000) := by
  exact
    packedTile32768 962638080 962703616 13 3157 31026 30 _ _ (2068517 / 100000) (51713 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962703616 :
    ThetaLowerSegment 962703616 962769152 (19253344860191 / 20000) (96273204986647 / 100000) := by
  exact
    packedTile32768 962703616 962769152 13 3133 31027 30 _ _ (517131 / 25000) (2068527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962769152 :
    ThetaLowerSegment 962769152 962834688 (96273204986647 / 100000) (19255964029757 / 20000) := by
  exact
    packedTile32768 962769152 962834688 13 3198 31028 30 _ _ (2068531 / 100000) (1034267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962834688 :
    ThetaLowerSegment 962834688 962900224 (19255964029757 / 20000) (96286381551321 / 100000) := by
  exact
    packedTile32768 962834688 962900224 13 3172 31029 30 _ _ (1034269 / 50000) (2068541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962900224 :
    ThetaLowerSegment 962900224 962965760 (96286381551321 / 100000) (96292963661511 / 100000) := by
  exact
    packedTile32768 962900224 962965760 13 3182 31030 30 _ _ (413709 / 20000) (517137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell962965760 :
    ThetaLowerSegment 962965760 963031296 (96292963661511 / 100000) (96299533379487 / 100000) := by
  exact
    packedTile32768 962965760 963031296 13 3176 31031 30 _ _ (2068551 / 100000) (1034277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963031296 :
    ThetaLowerSegment 963031296 963096832 (96299533379487 / 100000) (96306125873833 / 100000) := by
  exact
    packedTile32768 963031296 963096832 13 3187 31032 30 _ _ (1034279 / 50000) (2068561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963096832 :
    ThetaLowerSegment 963096832 963162368 (96306125873833 / 100000) (96312670813493 / 100000) := by
  exact
    packedTile32768 963096832 963162368 13 3164 31033 30 _ _ (413713 / 20000) (258571 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963162368 :
    ThetaLowerSegment 963162368 963227904 (96312670813493 / 100000) (96319246803881 / 100000) := by
  exact
    packedTile32768 963162368 963227904 13 3179 31034 30 _ _ (517143 / 25000) (82743 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963227904 :
    ThetaLowerSegment 963227904 963293440 (96319246803881 / 100000) (3010181058013 / 3125) := by
  exact
    packedTile32768 963227904 963293440 13 3165 31035 30 _ _ (2068579 / 100000) (1034291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963293440 :
    ThetaLowerSegment 963293440 963358976 (3010181058013 / 3125) (96332237498691 / 100000) := by
  exact
    packedTile32768 963293440 963358976 13 3115 31036 30 _ _ (413717 / 20000) (517147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963358976 :
    ThetaLowerSegment 963358976 963424512 (96332237498691 / 100000) (96338772180819 / 100000) := by
  exact
    packedTile32768 963358976 963424512 13 3159 31038 30 _ _ (129287 / 6250) (413719 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963424512 :
    ThetaLowerSegment 963424512 963490048 (96338772180819 / 100000) (48172651373931 / 50000) := by
  exact
    packedTile32768 963424512 963490048 13 3157 31039 30 _ _ (2068599 / 100000) (1034301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963490048 :
    ThetaLowerSegment 963490048 963555584 (48172651373931 / 50000) (48175950800501 / 50000) := by
  exact
    packedTile32768 963490048 963555584 13 3190 31040 30 _ _ (1034303 / 50000) (2068609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963555584 :
    ThetaLowerSegment 963555584 963621120 (48175950800501 / 50000) (96358432212243 / 100000) := by
  exact
    packedTile32768 963555584 963621120 13 3157 31041 30 _ _ (2068613 / 100000) (258577 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963621120 :
    ThetaLowerSegment 963621120 963686656 (96358432212243 / 100000) (12045618803839 / 12500) := by
  exact
    packedTile32768 963621120 963686656 13 3151 31042 30 _ _ (2068619 / 100000) (1034311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963686656 :
    ThetaLowerSegment 963686656 963752192 (12045618803839 / 12500) (9637161761231 / 10000) := by
  exact
    packedTile32768 963686656 963752192 13 3223 31043 30 _ _ (1034313 / 50000) (2068629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963752192 :
    ThetaLowerSegment 963752192 963817728 (9637161761231 / 10000) (96378222757479 / 100000) := by
  exact
    packedTile32768 963752192 963817728 13 3193 31044 30 _ _ (2068633 / 100000) (517159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963817728 :
    ThetaLowerSegment 963817728 963883264 (96378222757479 / 100000) (96384819650439 / 100000) := by
  exact
    packedTile32768 963817728 963883264 13 3189 31045 30 _ _ (12929 / 625) (2068643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963883264 :
    ThetaLowerSegment 963883264 963948800 (96384819650439 / 100000) (963913627809 / 1000) := by
  exact
    packedTile32768 963883264 963948800 13 3163 31046 30 _ _ (2068647 / 100000) (41373 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell963948800 :
    ThetaLowerSegment 963948800 964014336 (963913627809 / 1000) (19279602700059 / 20000) := by
  exact
    packedTile32768 963948800 964014336 13 3215 31047 30 _ _ (2068653 / 100000) (129291 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964014336 :
    ThetaLowerSegment 964014336 964079872 (19279602700059 / 20000) (19280917954087 / 20000) := by
  exact
    packedTile32768 964014336 964079872 13 3179 31048 30 _ _ (103433 / 5000) (2068663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964079872 :
    ThetaLowerSegment 964079872 964145408 (19280917954087 / 20000) (96411015050137 / 100000) := by
  exact
    packedTile32768 964079872 964145408 13 3106 31049 30 _ _ (2068667 / 100000) (206867 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964145408 :
    ThetaLowerSegment 964145408 964210944 (96411015050137 / 100000) (96417605845501 / 100000) := by
  exact
    packedTile32768 964145408 964210944 13 3186 31050 30 _ _ (1034337 / 50000) (2068677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964210944 :
    ThetaLowerSegment 964210944 964276480 (96417605845501 / 100000) (96424184251081 / 100000) := by
  exact
    packedTile32768 964210944 964276480 13 3180 31051 30 _ _ (2068681 / 100000) (517171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964276480 :
    ThetaLowerSegment 964276480 964342016 (96424184251081 / 100000) (96430696477757 / 100000) := by
  exact
    packedTile32768 964276480 964342016 13 3148 31052 30 _ _ (2068687 / 100000) (206869 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964342016 :
    ThetaLowerSegment 964342016 964407552 (96430696477757 / 100000) (96437256306431 / 100000) := by
  exact
    packedTile32768 964342016 964407552 13 3171 31053 30 _ _ (1034347 / 50000) (2068697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964407552 :
    ThetaLowerSegment 964407552 964473088 (96437256306431 / 100000) (96443747890169 / 100000) := by
  exact
    packedTile32768 964407552 964473088 13 3138 31054 30 _ _ (2068701 / 100000) (64647 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964473088 :
    ThetaLowerSegment 964473088 964538624 (96443747890169 / 100000) (19290059897681 / 20000) := by
  exact
    packedTile32768 964473088 964538624 13 3167 31055 30 _ _ (517177 / 25000) (2068711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964538624 :
    ThetaLowerSegment 964538624 964604160 (19290059897681 / 20000) (964568635211 / 1000) := by
  exact
    packedTile32768 964538624 964604160 13 3173 31057 30 _ _ (413743 / 20000) (1034359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964604160 :
    ThetaLowerSegment 964604160 964669696 (964568635211 / 1000) (96463468947253 / 100000) := by
  exact
    packedTile32768 964604160 964669696 13 3193 31058 30 _ _ (2068721 / 100000) (517181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964669696 :
    ThetaLowerSegment 964669696 964735232 (96463468947253 / 100000) (96469923378613 / 100000) := by
  exact
    packedTile32768 964669696 964735232 13 3120 31059 30 _ _ (258591 / 12500) (2068731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964735232 :
    ThetaLowerSegment 964735232 964800768 (96469923378613 / 100000) (12059558865611 / 12500) := by
  exact
    packedTile32768 964735232 964800768 13 3165 31060 30 _ _ (413747 / 20000) (1034369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964800768 :
    ThetaLowerSegment 964800768 964866304 (12059558865611 / 12500) (24120738590579 / 25000) := by
  exact
    packedTile32768 964800768 964866304 13 3134 31061 30 _ _ (1034371 / 50000) (413749 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964866304 :
    ThetaLowerSegment 964866304 964931840 (24120738590579 / 25000) (48244768560817 / 50000) := by
  exact
    packedTile32768 964866304 964931840 13 3182 31062 30 _ _ (2068749 / 100000) (129297 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964931840 :
    ThetaLowerSegment 964931840 964997376 (48244768560817 / 50000) (12062007746863 / 12500) := by
  exact
    packedTile32768 964931840 964997376 13 3154 31063 30 _ _ (413751 / 20000) (1034379 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell964997376 :
    ThetaLowerSegment 964997376 965062912 (12062007746863 / 12500) (48251306872079 / 50000) := by
  exact
    packedTile32768 964997376 965062912 13 3167 31064 30 _ _ (1034381 / 50000) (413753 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965062912 :
    ThetaLowerSegment 965062912 965128448 (48251306872079 / 50000) (96509144847891 / 100000) := by
  exact
    packedTile32768 965062912 965128448 13 3157 31065 30 _ _ (2068769 / 100000) (517193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965128448 :
    ThetaLowerSegment 965128448 965193984 (96509144847891 / 100000) (96515661492291 / 100000) := by
  exact
    packedTile32768 965128448 965193984 13 3150 31066 30 _ _ (258597 / 12500) (2068779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965193984 :
    ThetaLowerSegment 965193984 965259520 (96515661492291 / 100000) (96522289869819 / 100000) := by
  exact
    packedTile32768 965193984 965259520 13 3204 31067 30 _ _ (1034391 / 50000) (413757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965259520 :
    ThetaLowerSegment 965259520 965325056 (96522289869819 / 100000) (96528930682509 / 100000) := by
  exact
    packedTile32768 965259520 965325056 13 3210 31068 30 _ _ (2068789 / 100000) (258599 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965325056 :
    ThetaLowerSegment 965325056 965390592 (96528930682509 / 100000) (96535492903421 / 100000) := by
  exact
    packedTile32768 965325056 965390592 13 3172 31069 30 _ _ (517199 / 25000) (2068799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965390592 :
    ThetaLowerSegment 965390592 965456128 (96535492903421 / 100000) (96542038596113 / 100000) := by
  exact
    packedTile32768 965390592 965456128 13 3164 31070 30 _ _ (2068803 / 100000) (1034403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965456128 :
    ThetaLowerSegment 965456128 965521664 (96542038596113 / 100000) (96548573966903 / 100000) := by
  exact
    packedTile32768 965456128 965521664 13 3159 31071 30 _ _ (206881 / 10000) (2068813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965521664 :
    ThetaLowerSegment 965521664 965587200 (96548573966903 / 100000) (96555210728631 / 100000) := by
  exact
    packedTile32768 965521664 965587200 13 3208 31072 30 _ _ (129301 / 6250) (2068819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965587200 :
    ThetaLowerSegment 965587200 965652736 (96555210728631 / 100000) (24140434466299 / 25000) := by
  exact
    packedTile32768 965587200 965652736 13 3155 31073 30 _ _ (2068823 / 100000) (1034413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965652736 :
    ThetaLowerSegment 965652736 965718272 (24140434466299 / 25000) (48284115961283 / 50000) := by
  exact
    packedTile32768 965652736 965718272 13 3139 31074 30 _ _ (206883 / 10000) (2068833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965718272 :
    ThetaLowerSegment 965718272 965783808 (48284115961283 / 50000) (6035924383491 / 6250) := by
  exact
    packedTile32768 965718272 965783808 13 3170 31076 30 _ _ (2068837 / 100000) (51721 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965783808 :
    ThetaLowerSegment 965783808 965849344 (6035924383491 / 6250) (24145300370853 / 25000) := by
  exact
    packedTile32768 965783808 965849344 13 3099 31077 30 _ _ (517211 / 25000) (2068847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965849344 :
    ThetaLowerSegment 965849344 965914880 (24145300370853 / 25000) (48293891247631 / 50000) := by
  exact
    packedTile32768 965849344 965914880 13 3181 31078 30 _ _ (41377 / 2000) (2068853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965914880 :
    ThetaLowerSegment 965914880 965980416 (48293891247631 / 50000) (96594284912813 / 100000) := by
  exact
    packedTile32768 965914880 965980416 13 3143 31079 30 _ _ (2068857 / 100000) (103443 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell965980416 :
    ThetaLowerSegment 965980416 966045952 (96594284912813 / 100000) (96600743906221 / 100000) := by
  exact
    packedTile32768 965980416 966045952 13 3122 31080 30 _ _ (64652 / 3125) (2068867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966045952 :
    ThetaLowerSegment 966045952 966111488 (96600743906221 / 100000) (19321449687329 / 20000) := by
  exact
    packedTile32768 966045952 966111488 13 3144 31081 30 _ _ (2068871 / 100000) (1034437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966111488 :
    ThetaLowerSegment 966111488 966177024 (19321449687329 / 20000) (24153427384879 / 25000) := by
  exact
    packedTile32768 966111488 966177024 13 3123 31082 30 _ _ (2068877 / 100000) (25861 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966177024 :
    ThetaLowerSegment 966177024 966242560 (24153427384879 / 25000) (12077552366291 / 12500) := by
  exact
    packedTile32768 966177024 966242560 13 3243 31083 30 _ _ (517221 / 25000) (2068887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966242560 :
    ThetaLowerSegment 966242560 966308096 (12077552366291 / 12500) (4831349072629 / 5000) := by
  exact
    packedTile32768 966242560 966308096 13 3172 31084 30 _ _ (2068891 / 100000) (1034447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966308096 :
    ThetaLowerSegment 966308096 966373632 (4831349072629 / 5000) (24158404619341 / 25000) := by
  exact
    packedTile32768 966308096 966373632 13 3208 31085 30 _ _ (1034449 / 50000) (2068901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966373632 :
    ThetaLowerSegment 966373632 966439168 (24158404619341 / 25000) (48320071901867 / 50000) := by
  exact
    packedTile32768 966373632 966439168 13 3154 31086 30 _ _ (413781 / 20000) (517227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966439168 :
    ThetaLowerSegment 966439168 966504704 (48320071901867 / 50000) (48323291127383 / 50000) := by
  exact
    packedTile32768 966439168 966504704 13 3112 31087 30 _ _ (2068911 / 100000) (1034457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966504704 :
    ThetaLowerSegment 966504704 966570240 (48323291127383 / 50000) (6040821424609 / 6250) := by
  exact
    packedTile32768 966504704 966570240 13 3171 31088 30 _ _ (1034459 / 50000) (2068921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966570240 :
    ThetaLowerSegment 966570240 966635776 (6040821424609 / 6250) (96659744733419 / 100000) := by
  exact
    packedTile32768 966570240 966635776 13 3191 31089 30 _ _ (82757 / 4000) (64654 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966635776 :
    ThetaLowerSegment 966635776 966701312 (96659744733419 / 100000) (96666276351743 / 100000) := by
  exact
    packedTile32768 966635776 966701312 13 3157 31090 30 _ _ (517233 / 25000) (413787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966701312 :
    ThetaLowerSegment 966701312 966766848 (96666276351743 / 100000) (96672921783811 / 100000) := by
  exact
    packedTile32768 966701312 966766848 13 3212 31091 30 _ _ (2068939 / 100000) (1034471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966766848 :
    ThetaLowerSegment 966766848 966832384 (96672921783811 / 100000) (12084927542507 / 12500) := by
  exact
    packedTile32768 966766848 966832384 13 3141 31092 30 _ _ (413789 / 20000) (517237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966832384 :
    ThetaLowerSegment 966832384 966897920 (12084927542507 / 12500) (483429915279 / 500) := by
  exact
    packedTile32768 966832384 966897920 13 3172 31093 30 _ _ (258619 / 12500) (413791 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966897920 :
    ThetaLowerSegment 966897920 966963456 (483429915279 / 500) (96692585103969 / 100000) := by
  exact
    packedTile32768 966897920 966963456 13 3191 31094 30 _ _ (2068959 / 100000) (1034481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell966963456 :
    ThetaLowerSegment 966963456 967028992 (96692585103969 / 100000) (96699116829631 / 100000) := by
  exact
    packedTile32768 966963456 967028992 13 3157 31096 30 _ _ (1034483 / 50000) (2068969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967028992 :
    ThetaLowerSegment 967028992 967094528 (96699116829631 / 100000) (96705667194983 / 100000) := by
  exact
    packedTile32768 967028992 967094528 13 3166 31097 30 _ _ (517243 / 25000) (82759 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967094528 :
    ThetaLowerSegment 967094528 967160064 (96705667194983 / 100000) (96712176202917 / 100000) := by
  exact
    packedTile32768 967094528 967160064 13 3146 31098 30 _ _ (2068979 / 100000) (1034491 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967160064 :
    ThetaLowerSegment 967160064 967225600 (96712176202917 / 100000) (96718743164481 / 100000) := by
  exact
    packedTile32768 967160064 967225600 13 3174 31099 30 _ _ (1034493 / 50000) (2068989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967225600 :
    ThetaLowerSegment 967225600 967291136 (96718743164481 / 100000) (96725181870697 / 100000) := by
  exact
    packedTile32768 967225600 967291136 13 3112 31100 30 _ _ (2068993 / 100000) (517249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967291136 :
    ThetaLowerSegment 967291136 967356672 (96725181870697 / 100000) (96731744738697 / 100000) := by
  exact
    packedTile32768 967291136 967356672 13 3172 31101 30 _ _ (2069 / 100) (2069003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967356672 :
    ThetaLowerSegment 967356672 967422208 (96731744738697 / 100000) (96738260038591 / 100000) := by
  exact
    packedTile32768 967356672 967422208 13 3149 31102 30 _ _ (1034503 / 50000) (2069009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967422208 :
    ThetaLowerSegment 967422208 967487744 (96738260038591 / 100000) (96744864328087 / 100000) := by
  exact
    packedTile32768 967422208 967487744 13 3192 31103 30 _ _ (2069013 / 100000) (258627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967487744 :
    ThetaLowerSegment 967487744 967553280 (96744864328087 / 100000) (96751344498727 / 100000) := by
  exact
    packedTile32768 967487744 967553280 13 3132 31104 30 _ _ (103451 / 5000) (2069023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967553280 :
    ThetaLowerSegment 967553280 967618816 (96751344498727 / 100000) (4837894027751 / 5000) := by
  exact
    packedTile32768 967553280 967618816 13 3159 31105 30 _ _ (2069027 / 100000) (206903 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967618816 :
    ThetaLowerSegment 967618816 967684352 (4837894027751 / 5000) (2419111501999 / 2500) := by
  exact
    packedTile32768 967618816 967684352 13 3180 31106 30 _ _ (2069033 / 100000) (517259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967684352 :
    ThetaLowerSegment 967684352 967749888 (2419111501999 / 2500) (2419278007993 / 2500) := by
  exact
    packedTile32768 967684352 967749888 13 3219 31107 30 _ _ (25863 / 1250) (2069043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967749888 :
    ThetaLowerSegment 967749888 967815424 (2419278007993 / 2500) (96777826101047 / 100000) := by
  exact
    packedTile32768 967749888 967815424 13 3241 31108 30 _ _ (2069047 / 100000) (41381 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967815424 :
    ThetaLowerSegment 967815424 967880960 (96777826101047 / 100000) (19356852999419 / 20000) := by
  exact
    packedTile32768 967815424 967880960 13 3112 31109 30 _ _ (1034527 / 50000) (2069057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967880960 :
    ThetaLowerSegment 967880960 967946496 (19356852999419 / 20000) (19358158162467 / 20000) := by
  exact
    packedTile32768 967880960 967946496 13 3154 31110 30 _ _ (103453 / 5000) (2069063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell967946496 :
    ThetaLowerSegment 967946496 968012032 (19358158162467 / 20000) (3024920348094 / 3125) := by
  exact
    packedTile32768 967946496 968012032 13 3219 31111 30 _ _ (2069067 / 100000) (206907 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968012032 :
    ThetaLowerSegment 968012032 968077568 (3024920348094 / 3125) (6050251407377 / 6250) := by
  exact
    packedTile32768 968012032 968077568 13 3176 31112 30 _ _ (1034537 / 50000) (2069077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968077568 :
    ThetaLowerSegment 968077568 968143104 (6050251407377 / 6250) (24202625719931 / 25000) := by
  exact
    packedTile32768 968077568 968143104 13 3132 31113 30 _ _ (2069081 / 100000) (517271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968143104 :
    ThetaLowerSegment 968143104 968208640 (24202625719931 / 25000) (24204264954899 / 25000) := by
  exact
    packedTile32768 968143104 968208640 13 3169 31114 30 _ _ (64659 / 3125) (2069091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968208640 :
    ThetaLowerSegment 968208640 968274176 (24204264954899 / 25000) (3025738864897 / 3125) := by
  exact
    packedTile32768 968208640 968274176 13 3182 31116 30 _ _ (1034547 / 50000) (2069097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968274176 :
    ThetaLowerSegment 968274176 968339712 (3025738864897 / 3125) (96830258592601 / 100000) := by
  exact
    packedTile32768 968274176 968339712 13 3197 31117 30 _ _ (2069101 / 100000) (129319 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968339712 :
    ThetaLowerSegment 968339712 968405248 (96830258592601 / 100000) (96836799042989 / 100000) := by
  exact
    packedTile32768 968339712 968405248 13 3161 31118 30 _ _ (517277 / 25000) (2069111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968405248 :
    ThetaLowerSegment 968405248 968470784 (96836799042989 / 100000) (96843329169929 / 100000) := by
  exact
    packedTile32768 968405248 968470784 13 3156 31119 30 _ _ (413823 / 20000) (1034559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968470784 :
    ThetaLowerSegment 968470784 968536320 (96843329169929 / 100000) (96849913112951 / 100000) := by
  exact
    packedTile32768 968470784 968536320 13 3182 31120 30 _ _ (2069121 / 100000) (517281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968536320 :
    ThetaLowerSegment 968536320 968601856 (96849913112951 / 100000) (96856528115167 / 100000) := by
  exact
    packedTile32768 968536320 968601856 13 3197 31121 30 _ _ (258641 / 12500) (2069131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968601856 :
    ThetaLowerSegment 968601856 968667392 (96856528115167 / 100000) (24215722676323 / 25000) := by
  exact
    packedTile32768 968601856 968667392 13 3075 31122 30 _ _ (413827 / 20000) (1034569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968667392 :
    ThetaLowerSegment 968667392 968732928 (24215722676323 / 25000) (9686948919913 / 10000) := by
  exact
    packedTile32768 968667392 968732928 13 3189 31123 30 _ _ (1034571 / 50000) (413829 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968732928 :
    ThetaLowerSegment 968732928 968798464 (9686948919913 / 10000) (48438014887979 / 50000) := by
  exact
    packedTile32768 968732928 968798464 13 3161 31124 30 _ _ (517287 / 25000) (2069151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968798464 :
    ThetaLowerSegment 968798464 968864000 (48438014887979 / 50000) (96882595204773 / 100000) := by
  exact
    packedTile32768 968798464 968864000 13 3173 31125 30 _ _ (413831 / 20000) (1034579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968864000 :
    ThetaLowerSegment 968864000 968929536 (96882595204773 / 100000) (96889057197699 / 100000) := by
  exact
    packedTile32768 968864000 968929536 13 3123 31126 30 _ _ (1034581 / 50000) (413833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968929536 :
    ThetaLowerSegment 968929536 968995072 (96889057197699 / 100000) (48447854788017 / 50000) := by
  exact
    packedTile32768 968929536 968995072 13 3215 31127 30 _ _ (2069169 / 100000) (517293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell968995072 :
    ThetaLowerSegment 968995072 969060608 (48447854788017 / 50000) (48451128224449 / 50000) := by
  exact
    packedTile32768 968995072 969060608 13 3164 31128 30 _ _ (258647 / 12500) (2069179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969060608 :
    ThetaLowerSegment 969060608 969126144 (48451128224449 / 50000) (3028399393117 / 3125) := by
  exact
    packedTile32768 969060608 969126144 13 3153 31129 30 _ _ (1034591 / 50000) (413837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969126144 :
    ThetaLowerSegment 969126144 969191680 (3028399393117 / 3125) (96915404053733 / 100000) := by
  exact
    packedTile32768 969126144 969191680 13 3201 31130 30 _ _ (2069189 / 100000) (258649 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969191680 :
    ThetaLowerSegment 969191680 969257216 (96915404053733 / 100000) (96922089626009 / 100000) := by
  exact
    packedTile32768 969191680 969257216 13 3231 31131 30 _ _ (517299 / 25000) (2069199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969257216 :
    ThetaLowerSegment 969257216 969322752 (96922089626009 / 100000) (12116081900891 / 12500) := by
  exact
    packedTile32768 969257216 969322752 13 3173 31132 30 _ _ (2069203 / 100000) (1034603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969322752 :
    ThetaLowerSegment 969322752 969339136 (12116081900891 / 12500) (3029070653541 / 3125) := by
  exact
    packedTile32768 969322752 969339136 11 776 31133 30 _ _ (2069209 / 100000) (517303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell969339136 :
    ThetaLowerSegment 969339136 969341184 (3029070653541 / 3125) (12116309513907 / 12500) := by
  exact
    packedTile32768 969339136 969341184 8 104 31134 30 _ _ (2069211 / 100000) (1034607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_937341184_969341184 :
    ThetaLowerSegment 937341184 969341184 (46864982813727 / 50000) (12116309513907 / 12500) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell937341184 cell937406720)
                    (ThetaLowerSegment.join cell937472256 cell937537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell937603328 cell937668864)
                    (ThetaLowerSegment.join cell937734400 cell937799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell937865472 cell937931008)
                    (ThetaLowerSegment.join cell937996544 cell938062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell938127616 cell938193152)
                    (ThetaLowerSegment.join cell938258688 cell938324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell938389760 cell938455296)
                    (ThetaLowerSegment.join cell938520832 cell938586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell938651904 cell938717440)
                    (ThetaLowerSegment.join cell938782976 cell938848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell938914048 cell938979584)
                    (ThetaLowerSegment.join cell939045120 cell939110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell939176192 cell939241728)
                    (ThetaLowerSegment.join cell939307264 cell939372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell939438336 cell939503872)
                    (ThetaLowerSegment.join cell939569408 cell939634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell939700480 cell939766016)
                    (ThetaLowerSegment.join cell939831552 cell939897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell939962624 cell940028160)
                    (ThetaLowerSegment.join cell940093696 cell940159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell940224768 cell940290304)
                    (ThetaLowerSegment.join cell940355840 cell940421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell940486912 cell940552448)
                    (ThetaLowerSegment.join cell940617984 cell940683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell940749056 cell940814592)
                    (ThetaLowerSegment.join cell940880128 cell940945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell941011200 cell941076736)
                    (ThetaLowerSegment.join cell941142272 cell941207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell941273344 cell941338880)
                    (ThetaLowerSegment.join cell941404416 cell941469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell941535488 cell941601024)
                    (ThetaLowerSegment.join cell941666560 cell941732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell941797632 cell941863168)
                    (ThetaLowerSegment.join cell941928704 cell941994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell942059776 cell942125312)
                    (ThetaLowerSegment.join cell942190848 cell942256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell942321920 cell942387456)
                    (ThetaLowerSegment.join cell942452992 cell942518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell942584064 cell942649600)
                    (ThetaLowerSegment.join cell942715136 cell942780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell942846208 cell942911744)
                    (ThetaLowerSegment.join cell942977280 cell943042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell943108352 cell943173888)
                    (ThetaLowerSegment.join cell943239424 cell943304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell943370496 cell943436032)
                    (ThetaLowerSegment.join cell943501568 cell943567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell943632640 cell943698176)
                    (ThetaLowerSegment.join cell943763712 cell943829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell943894784 cell943960320)
                    (ThetaLowerSegment.join cell944025856 cell944091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell944156928 cell944222464)
                    (ThetaLowerSegment.join cell944288000 cell944353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell944419072 cell944484608)
                    (ThetaLowerSegment.join cell944550144 cell944615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell944681216 cell944746752)
                    (ThetaLowerSegment.join cell944812288 cell944877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell944943360 cell945008896)
                    (ThetaLowerSegment.join cell945074432 cell945139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell945205504 cell945271040)
                    (ThetaLowerSegment.join cell945336576 cell945402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell945467648 cell945533184)
                    (ThetaLowerSegment.join cell945598720 cell945664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell945729792 cell945795328)
                    (ThetaLowerSegment.join cell945860864 cell945926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell945991936 cell946057472)
                    (ThetaLowerSegment.join cell946123008 cell946188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell946254080 cell946319616)
                    (ThetaLowerSegment.join cell946385152 cell946450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell946516224 cell946581760)
                    (ThetaLowerSegment.join cell946647296 cell946712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell946778368 cell946843904)
                    (ThetaLowerSegment.join cell946909440 cell946974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell947040512 cell947106048)
                    (ThetaLowerSegment.join cell947171584 cell947237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell947302656 cell947368192)
                    (ThetaLowerSegment.join cell947433728 cell947499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell947564800 cell947630336)
                    (ThetaLowerSegment.join cell947695872 cell947761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell947826944 cell947892480)
                    (ThetaLowerSegment.join cell947958016 cell948023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell948089088 cell948154624)
                    (ThetaLowerSegment.join cell948220160 cell948285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell948351232 cell948416768)
                    (ThetaLowerSegment.join cell948482304 cell948547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell948613376 cell948678912)
                    (ThetaLowerSegment.join cell948744448 cell948809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell948875520 cell948941056)
                    (ThetaLowerSegment.join cell949006592 cell949072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell949137664 cell949203200)
                    (ThetaLowerSegment.join cell949268736 cell949334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell949399808 cell949465344)
                    (ThetaLowerSegment.join cell949530880 cell949596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell949661952 cell949727488)
                    (ThetaLowerSegment.join cell949793024 cell949858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell949924096 cell949989632)
                    (ThetaLowerSegment.join cell950055168 cell950120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell950186240 cell950251776)
                    (ThetaLowerSegment.join cell950317312 cell950382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell950448384 cell950513920)
                    (ThetaLowerSegment.join cell950579456 cell950644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell950710528 cell950776064)
                    (ThetaLowerSegment.join cell950841600 cell950907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell950972672 cell951038208)
                    (ThetaLowerSegment.join cell951103744 cell951169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell951234816 cell951300352)
                    (ThetaLowerSegment.join cell951365888 cell951431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell951496960 cell951562496)
                    (ThetaLowerSegment.join cell951628032 cell951693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell951759104 cell951824640)
                    (ThetaLowerSegment.join cell951890176 cell951955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell952021248 cell952086784)
                    (ThetaLowerSegment.join cell952152320 cell952217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell952283392 cell952348928)
                    (ThetaLowerSegment.join cell952414464 cell952480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell952545536 cell952611072)
                    (ThetaLowerSegment.join cell952676608 cell952742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell952807680 cell952873216)
                    (ThetaLowerSegment.join cell952938752 cell953004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell953069824 cell953135360)
                    (ThetaLowerSegment.join cell953200896 cell953266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell953331968 cell953397504)
                    (ThetaLowerSegment.join cell953463040 cell953528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell953594112 cell953659648)
                    (ThetaLowerSegment.join cell953725184 cell953790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell953856256 cell953921792)
                    (ThetaLowerSegment.join cell953987328 cell954052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell954118400 cell954183936)
                    (ThetaLowerSegment.join cell954249472 cell954315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell954380544 cell954446080)
                    (ThetaLowerSegment.join cell954511616 cell954577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell954642688 cell954708224)
                    (ThetaLowerSegment.join cell954773760 cell954839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell954904832 cell954970368)
                    (ThetaLowerSegment.join cell955035904 cell955101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell955166976 cell955232512)
                    (ThetaLowerSegment.join cell955298048 cell955363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell955429120 cell955494656)
                    (ThetaLowerSegment.join cell955560192 cell955625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell955691264 cell955756800)
                    (ThetaLowerSegment.join cell955822336 cell955887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell955953408 cell956018944)
                    (ThetaLowerSegment.join cell956084480 cell956150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell956215552 cell956281088)
                    (ThetaLowerSegment.join cell956346624 cell956412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell956477696 cell956543232)
                    (ThetaLowerSegment.join cell956608768 cell956674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell956739840 cell956805376)
                    (ThetaLowerSegment.join cell956870912 cell956936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell957001984 cell957067520)
                    (ThetaLowerSegment.join cell957133056 cell957198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell957264128 cell957329664)
                    (ThetaLowerSegment.join cell957395200 cell957460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell957526272 cell957591808)
                    (ThetaLowerSegment.join cell957657344 cell957722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell957788416 cell957853952)
                    (ThetaLowerSegment.join cell957919488 cell957985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell958050560 cell958116096)
                    (ThetaLowerSegment.join cell958181632 cell958247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell958312704 cell958378240)
                    (ThetaLowerSegment.join cell958443776 cell958509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell958574848 cell958640384)
                    (ThetaLowerSegment.join cell958705920 cell958771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell958836992 cell958902528)
                    (ThetaLowerSegment.join cell958968064 cell959033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell959099136 cell959164672)
                    (ThetaLowerSegment.join cell959230208 cell959295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell959361280 cell959426816)
                    (ThetaLowerSegment.join cell959492352 cell959557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell959623424 cell959688960)
                    (ThetaLowerSegment.join cell959754496 cell959820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell959885568 cell959951104)
                    (ThetaLowerSegment.join cell960016640 cell960082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell960147712 cell960213248)
                    (ThetaLowerSegment.join cell960278784 cell960344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell960409856 cell960475392)
                    (ThetaLowerSegment.join cell960540928 cell960606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell960672000 cell960737536)
                    (ThetaLowerSegment.join cell960803072 cell960868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell960934144 cell960999680)
                    (ThetaLowerSegment.join cell961065216 cell961130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell961196288 cell961261824)
                    (ThetaLowerSegment.join cell961327360 cell961392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell961458432 cell961523968)
                    (ThetaLowerSegment.join cell961589504 cell961655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell961720576 cell961786112)
                    (ThetaLowerSegment.join cell961851648 cell961917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell961982720 cell962048256)
                    (ThetaLowerSegment.join cell962113792 cell962179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell962244864 cell962310400)
                    (ThetaLowerSegment.join cell962375936 cell962441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell962507008 cell962572544)
                    (ThetaLowerSegment.join cell962638080 cell962703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell962769152 cell962834688)
                    (ThetaLowerSegment.join cell962900224 cell962965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell963031296 cell963096832)
                    (ThetaLowerSegment.join cell963162368 cell963227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell963293440 cell963358976)
                    (ThetaLowerSegment.join cell963424512 cell963490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell963555584 cell963621120)
                    (ThetaLowerSegment.join cell963686656 cell963752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell963817728 cell963883264)
                    (ThetaLowerSegment.join cell963948800 cell964014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell964079872 cell964145408)
                    (ThetaLowerSegment.join cell964210944 cell964276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell964342016 cell964407552)
                    (ThetaLowerSegment.join cell964473088 cell964538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell964604160 cell964669696)
                    (ThetaLowerSegment.join cell964735232 cell964800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell964866304 cell964931840)
                    (ThetaLowerSegment.join cell964997376 cell965062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell965128448 cell965193984)
                    (ThetaLowerSegment.join cell965259520 cell965325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell965390592 cell965456128)
                    (ThetaLowerSegment.join cell965521664 cell965587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell965652736 cell965718272)
                    (ThetaLowerSegment.join cell965783808 cell965849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell965914880 cell965980416)
                    (ThetaLowerSegment.join cell966045952 cell966111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell966177024 cell966242560)
                    (ThetaLowerSegment.join cell966308096 cell966373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell966439168 cell966504704)
                    (ThetaLowerSegment.join cell966570240 cell966635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell966701312 cell966766848)
                    (ThetaLowerSegment.join cell966832384 cell966897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell966963456 cell967028992)
                    (ThetaLowerSegment.join cell967094528 cell967160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell967225600 cell967291136)
                    (ThetaLowerSegment.join cell967356672 cell967422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell967487744 cell967553280)
                    (ThetaLowerSegment.join cell967618816 cell967684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell967749888 cell967815424)
                    (ThetaLowerSegment.join cell967880960 cell967946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell968012032 cell968077568)
                    (ThetaLowerSegment.join cell968143104 cell968208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell968274176 cell968339712)
                    (ThetaLowerSegment.join cell968405248 cell968470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell968536320 cell968601856)
                    (ThetaLowerSegment.join cell968667392 cell968732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell968798464 cell968864000)
                  (ThetaLowerSegment.join cell968929536 cell968995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell969060608 cell969126144)
                  (ThetaLowerSegment.join cell969191680 cell969257216)))
              (ThetaLowerSegment.join cell969322752 cell969339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
