/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 873341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell841341184 :
    ThetaLowerSegment 841341184 841406720 (42065498884063 / 50000) (84137444456839 / 100000) := by
  exact
    packedTile32768 841341184 841406720 13 3137 29005 30 _ _ (2055049 / 100000) (513763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841406720 :
    ThetaLowerSegment 841406720 841472256 (84137444456839 / 100000) (84143905556047 / 100000) := by
  exact
    packedTile32768 841406720 841472256 13 3144 29007 30 _ _ (2055057 / 100000) (102753 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841472256 :
    ThetaLowerSegment 841472256 841537792 (84143905556047 / 100000) (42075285065921 / 50000) := by
  exact
    packedTile32768 841472256 841537792 13 3243 29008 30 _ _ (411013 / 20000) (513767 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841537792 :
    ThetaLowerSegment 841537792 841603328 (42075285065921 / 50000) (42078573182721 / 50000) := by
  exact
    packedTile32768 841537792 841603328 13 3200 29009 30 _ _ (2055073 / 100000) (513769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841603328 :
    ThetaLowerSegment 841603328 841668864 (42078573182721 / 50000) (42081890081841 / 50000) := by
  exact
    packedTile32768 841603328 841668864 13 3228 29010 30 _ _ (51377 / 2500) (2055083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841668864 :
    ThetaLowerSegment 841668864 841734400 (42081890081841 / 50000) (42085203911241 / 50000) := by
  exact
    packedTile32768 841668864 841734400 13 3225 29011 30 _ _ (128443 / 6250) (2055091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841734400 :
    ThetaLowerSegment 841734400 841799936 (42085203911241 / 50000) (42088502340321 / 50000) := by
  exact
    packedTile32768 841734400 841799936 13 3210 29012 30 _ _ (256887 / 12500) (2055099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841799936 :
    ThetaLowerSegment 841799936 841865472 (42088502340321 / 50000) (42091806947553 / 50000) := by
  exact
    packedTile32768 841799936 841865472 13 3216 29013 30 _ _ (64222 / 3125) (2055107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841865472 :
    ThetaLowerSegment 841865472 841931008 (42091806947553 / 50000) (42095121843209 / 50000) := by
  exact
    packedTile32768 841865472 841931008 13 3226 29014 30 _ _ (256889 / 12500) (411023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841931008 :
    ThetaLowerSegment 841931008 841996544 (42095121843209 / 50000) (42098323718611 / 50000) := by
  exact
    packedTile32768 841931008 841996544 13 3116 29016 30 _ _ (2055119 / 100000) (1027561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell841996544 :
    ThetaLowerSegment 841996544 842062080 (42098323718611 / 50000) (21050819319231 / 25000) := by
  exact
    packedTile32768 841996544 842062080 13 3226 29017 30 _ _ (2055127 / 100000) (205513 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842062080 :
    ThetaLowerSegment 842062080 842127616 (21050819319231 / 25000) (2631557671512 / 3125) := by
  exact
    packedTile32768 842062080 842127616 13 3196 29018 30 _ _ (411027 / 20000) (1027569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842127616 :
    ThetaLowerSegment 842127616 842193152 (2631557671512 / 3125) (8421646715913 / 10000) := by
  exact
    packedTile32768 842127616 842193152 13 3222 29019 30 _ _ (2055143 / 100000) (1027573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842193152 :
    ThetaLowerSegment 842193152 842258688 (8421646715913 / 10000) (8422301075673 / 10000) := by
  exact
    packedTile32768 842193152 842258688 13 3184 29020 30 _ _ (41103 / 2000) (2055153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842258688 :
    ThetaLowerSegment 842258688 842324224 (8422301075673 / 10000) (421147576659 / 500) := by
  exact
    packedTile32768 842258688 842324224 13 3165 29021 30 _ _ (1027579 / 50000) (2055161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842324224 :
    ThetaLowerSegment 842324224 842389760 (421147576659 / 500) (42118034628087 / 50000) := by
  exact
    packedTile32768 842324224 842389760 13 3189 29022 30 _ _ (1027583 / 50000) (2055169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842389760 :
    ThetaLowerSegment 842389760 842455296 (42118034628087 / 50000) (21060641415297 / 25000) := by
  exact
    packedTile32768 842389760 842455296 13 3161 29023 30 _ _ (1027587 / 50000) (2055177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842455296 :
    ThetaLowerSegment 842455296 842520832 (21060641415297 / 25000) (10531131990743 / 12500) := by
  exact
    packedTile32768 842455296 842520832 13 3158 29025 30 _ _ (1027591 / 50000) (411037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842520832 :
    ThetaLowerSegment 842520832 842586368 (10531131990743 / 12500) (84255655137823 / 100000) := by
  exact
    packedTile32768 842520832 842586368 13 3211 29026 30 _ _ (2055189 / 100000) (256899 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842586368 :
    ThetaLowerSegment 842586368 842651904 (84255655137823 / 100000) (42131110746119 / 50000) := by
  exact
    packedTile32768 842586368 842651904 13 3195 29027 30 _ _ (2055197 / 100000) (2569 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842651904 :
    ThetaLowerSegment 842651904 842717440 (42131110746119 / 50000) (21067219061507 / 25000) := by
  exact
    packedTile32768 842651904 842717440 13 3238 29028 30 _ _ (411041 / 20000) (256901 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842717440 :
    ThetaLowerSegment 842717440 842782976 (21067219061507 / 25000) (526721632178 / 625) := by
  exact
    packedTile32768 842717440 842782976 13 3204 29029 30 _ _ (2055213 / 100000) (128451 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842782976 :
    ThetaLowerSegment 842782976 842848512 (526721632178 / 625) (21070536181793 / 25000) := by
  exact
    packedTile32768 842782976 842848512 13 3252 29030 30 _ _ (2055221 / 100000) (256903 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842848512 :
    ThetaLowerSegment 842848512 842914048 (21070536181793 / 25000) (21072191667947 / 25000) := by
  exact
    packedTile32768 842848512 842914048 13 3222 29031 30 _ _ (513807 / 25000) (2055231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842914048 :
    ThetaLowerSegment 842914048 842979584 (21072191667947 / 25000) (21073820442477 / 25000) := by
  exact
    packedTile32768 842914048 842979584 13 3170 29032 30 _ _ (513809 / 25000) (2055239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell842979584 :
    ThetaLowerSegment 842979584 843045120 (21073820442477 / 25000) (21075439974749 / 25000) := by
  exact
    packedTile32768 842979584 843045120 13 3152 29034 30 _ _ (513811 / 25000) (2055247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843045120 :
    ThetaLowerSegment 843045120 843110656 (21075439974749 / 25000) (2634637513069 / 3125) := by
  exact
    packedTile32768 843045120 843110656 13 3231 29035 30 _ _ (513813 / 25000) (411051 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843110656 :
    ThetaLowerSegment 843110656 843176192 (2634637513069 / 3125) (674520031723 / 800) := by
  exact
    packedTile32768 843110656 843176192 13 3213 29036 30 _ _ (2055259 / 100000) (1027631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843176192 :
    ThetaLowerSegment 843176192 843241728 (674520031723 / 800) (84321527382833 / 100000) := by
  exact
    packedTile32768 843176192 843241728 13 3174 29037 30 _ _ (2055267 / 100000) (205527 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843241728 :
    ThetaLowerSegment 843241728 843307264 (84321527382833 / 100000) (84328190584383 / 100000) := by
  exact
    packedTile32768 843241728 843307264 13 3242 29038 30 _ _ (82211 / 4000) (1027639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843307264 :
    ThetaLowerSegment 843307264 843372800 (84328190584383 / 100000) (84334783932247 / 100000) := by
  exact
    packedTile32768 843307264 843372800 13 3208 29039 30 _ _ (2055283 / 100000) (1027643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843372800 :
    ThetaLowerSegment 843372800 843438336 (84334783932247 / 100000) (84341418408367 / 100000) := by
  exact
    packedTile32768 843372800 843438336 13 3228 29040 30 _ _ (205529 / 10000) (2055293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843438336 :
    ThetaLowerSegment 843438336 843503872 (84341418408367 / 100000) (84347921371239 / 100000) := by
  exact
    packedTile32768 843438336 843503872 13 3164 29042 30 _ _ (1027649 / 50000) (2055301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843503872 :
    ThetaLowerSegment 843503872 843569408 (84347921371239 / 100000) (16870900081149 / 20000) := by
  exact
    packedTile32768 843503872 843569408 13 3201 29043 30 _ _ (1027653 / 50000) (2055309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843569408 :
    ThetaLowerSegment 843569408 843634944 (16870900081149 / 20000) (84361081521173 / 100000) := by
  exact
    packedTile32768 843569408 843634944 13 3202 29044 30 _ _ (1027657 / 50000) (2055317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843634944 :
    ThetaLowerSegment 843634944 843700480 (84361081521173 / 100000) (84367596891913 / 100000) := by
  exact
    packedTile32768 843634944 843700480 13 3170 29045 30 _ _ (1027661 / 50000) (82213 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843700480 :
    ThetaLowerSegment 843700480 843766016 (84367596891913 / 100000) (42187067446731 / 50000) := by
  exact
    packedTile32768 843700480 843766016 13 3181 29046 30 _ _ (2055329 / 100000) (513833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843766016 :
    ThetaLowerSegment 843766016 843831552 (42187067446731 / 50000) (16876146093979 / 20000) := by
  exact
    packedTile32768 843766016 843831552 13 3209 29047 30 _ _ (2055337 / 100000) (102767 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843831552 :
    ThetaLowerSegment 843831552 843897088 (16876146093979 / 20000) (8438716575509 / 10000) := by
  exact
    packedTile32768 843831552 843897088 13 3131 29048 30 _ _ (411069 / 20000) (513837 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843897088 :
    ThetaLowerSegment 843897088 843962624 (8438716575509 / 10000) (21098444970261 / 25000) := by
  exact
    packedTile32768 843897088 843962624 13 3218 29049 30 _ _ (2055353 / 100000) (513839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell843962624 :
    ThetaLowerSegment 843962624 844028160 (21098444970261 / 25000) (21100057400181 / 25000) := by
  exact
    packedTile32768 843962624 844028160 13 3138 29051 30 _ _ (12846 / 625) (2055363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844028160 :
    ThetaLowerSegment 844028160 844093696 (21100057400181 / 25000) (844067697817 / 1000) := by
  exact
    packedTile32768 844028160 844093696 13 3182 29052 30 _ _ (256921 / 12500) (2055371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844093696 :
    ThetaLowerSegment 844093696 844159232 (844067697817 / 1000) (21103336232381 / 25000) := by
  exact
    packedTile32768 844093696 844159232 13 3199 29053 30 _ _ (128461 / 6250) (2055379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844159232 :
    ThetaLowerSegment 844159232 844224768 (21103336232381 / 25000) (4220988811303 / 5000) := by
  exact
    packedTile32768 844159232 844224768 13 3129 29054 30 _ _ (256923 / 12500) (2055387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844224768 :
    ThetaLowerSegment 844224768 844290304 (4220988811303 / 5000) (84426388418907 / 100000) := by
  exact
    packedTile32768 844224768 844290304 13 3217 29055 30 _ _ (2055391 / 100000) (1027697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844290304 :
    ThetaLowerSegment 844290304 844355840 (84426388418907 / 100000) (21108212134491 / 25000) := by
  exact
    packedTile32768 844290304 844355840 13 3143 29056 30 _ _ (2055399 / 100000) (1027701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844355840 :
    ThetaLowerSegment 844355840 844421376 (21108212134491 / 25000) (84439423784957 / 100000) := by
  exact
    packedTile32768 844355840 844421376 13 3199 29057 30 _ _ (2055407 / 100000) (205541 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844421376 :
    ThetaLowerSegment 844421376 844486912 (84439423784957 / 100000) (84446001112957 / 100000) := by
  exact
    packedTile32768 844421376 844486912 13 3200 29058 30 _ _ (411083 / 20000) (1027709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844486912 :
    ThetaLowerSegment 844486912 844552448 (84446001112957 / 100000) (84452444860927 / 100000) := by
  exact
    packedTile32768 844486912 844552448 13 3135 29060 30 _ _ (1027711 / 50000) (82217 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844552448 :
    ThetaLowerSegment 844552448 844617984 (84452444860927 / 100000) (84458979072897 / 100000) := by
  exact
    packedTile32768 844552448 844617984 13 3179 29061 30 _ _ (205543 / 10000) (2055433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844617984 :
    ThetaLowerSegment 844617984 844683520 (84458979072897 / 100000) (16893089096169 / 20000) := by
  exact
    packedTile32768 844617984 844683520 13 3146 29062 30 _ _ (1027719 / 50000) (2055441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844683520 :
    ThetaLowerSegment 844683520 844749056 (16893089096169 / 20000) (84472024963491 / 100000) := by
  exact
    packedTile32768 844683520 844749056 13 3201 29063 30 _ _ (1027723 / 50000) (2055449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844749056 :
    ThetaLowerSegment 844749056 844814592 (84472024963491 / 100000) (84478618859923 / 100000) := by
  exact
    packedTile32768 844749056 844814592 13 3208 29064 30 _ _ (1027727 / 50000) (2055457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844814592 :
    ThetaLowerSegment 844814592 844880128 (84478618859923 / 100000) (84485208667889 / 100000) := by
  exact
    packedTile32768 844814592 844880128 13 3206 29065 30 _ _ (2055461 / 100000) (256933 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844880128 :
    ThetaLowerSegment 844880128 844945664 (84485208667889 / 100000) (84491769724937 / 100000) := by
  exact
    packedTile32768 844880128 844945664 13 3192 29066 30 _ _ (2055469 / 100000) (128467 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell844945664 :
    ThetaLowerSegment 844945664 845011200 (84491769724937 / 100000) (84498343140383 / 100000) := by
  exact
    packedTile32768 844945664 845011200 13 3198 29067 30 _ _ (2055477 / 100000) (51387 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845011200 :
    ThetaLowerSegment 845011200 845076736 (84498343140383 / 100000) (42252459318449 / 50000) := by
  exact
    packedTile32768 845011200 845076736 13 3199 29069 30 _ _ (411097 / 20000) (64234 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845076736 :
    ThetaLowerSegment 845076736 845142272 (42252459318449 / 50000) (42255735772697 / 50000) := by
  exact
    packedTile32768 845076736 845142272 13 3188 29070 30 _ _ (513873 / 25000) (411099 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845142272 :
    ThetaLowerSegment 845142272 845207808 (42255735772697 / 50000) (42259010184197 / 50000) := by
  exact
    packedTile32768 845142272 845207808 13 3186 29071 30 _ _ (4111 / 200) (2055503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845207808 :
    ThetaLowerSegment 845207808 845273344 (42259010184197 / 50000) (42262276386409 / 50000) := by
  exact
    packedTile32768 845207808 845273344 13 3178 29072 30 _ _ (513877 / 25000) (2055511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845273344 :
    ThetaLowerSegment 845273344 845338880 (42262276386409 / 50000) (8453107286957 / 10000) := by
  exact
    packedTile32768 845273344 845338880 13 3172 29073 30 _ _ (513879 / 25000) (2055519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845338880 :
    ThetaLowerSegment 845338880 845404416 (8453107286957 / 10000) (42268780050079 / 50000) := by
  exact
    packedTile32768 845338880 845404416 13 3156 29074 30 _ _ (2055523 / 100000) (1027763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845404416 :
    ThetaLowerSegment 845404416 845469952 (42268780050079 / 50000) (10568000266789 / 12500) := by
  exact
    packedTile32768 845404416 845469952 13 3134 29075 30 _ _ (2055531 / 100000) (1027767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845469952 :
    ThetaLowerSegment 845469952 845535488 (10568000266789 / 12500) (42275279651861 / 50000) := by
  exact
    packedTile32768 845469952 845535488 13 3190 29076 30 _ _ (2055539 / 100000) (1027771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845535488 :
    ThetaLowerSegment 845535488 845601024 (42275279651861 / 50000) (42278626082377 / 50000) := by
  exact
    packedTile32768 845535488 845601024 13 3256 29078 30 _ _ (2055547 / 100000) (41111 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845601024 :
    ThetaLowerSegment 845601024 845666560 (42278626082377 / 50000) (21140933331629 / 25000) := by
  exact
    packedTile32768 845601024 845666560 13 3153 29079 30 _ _ (1027777 / 50000) (2055557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845666560 :
    ThetaLowerSegment 845666560 845732096 (21140933331629 / 25000) (4228514734021 / 5000) := by
  exact
    packedTile32768 845666560 845732096 13 3192 29080 30 _ _ (1027781 / 50000) (411113 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845732096 :
    ThetaLowerSegment 845732096 845797632 (4228514734021 / 5000) (8457696500507 / 10000) := by
  exact
    packedTile32768 845732096 845797632 13 3245 29081 30 _ _ (205557 / 10000) (2055573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845797632 :
    ThetaLowerSegment 845797632 845863168 (8457696500507 / 10000) (4229174573261 / 5000) := by
  exact
    packedTile32768 845797632 845863168 13 3175 29082 30 _ _ (1027789 / 50000) (2055581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845863168 :
    ThetaLowerSegment 845863168 845928704 (4229174573261 / 5000) (16917997011647 / 20000) := by
  exact
    packedTile32768 845863168 845928704 13 3159 29083 30 _ _ (411117 / 20000) (513897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845928704 :
    ThetaLowerSegment 845928704 845994240 (16917997011647 / 20000) (84596653401927 / 100000) := by
  exact
    packedTile32768 845928704 845994240 13 3244 29084 30 _ _ (2055593 / 100000) (513899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell845994240 :
    ThetaLowerSegment 845994240 846059776 (84596653401927 / 100000) (8460315526789 / 10000) := by
  exact
    packedTile32768 845994240 846059776 13 3163 29085 30 _ _ (2055601 / 100000) (513901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846059776 :
    ThetaLowerSegment 846059776 846125312 (8460315526789 / 10000) (42304870719563 / 50000) := by
  exact
    packedTile32768 846059776 846125312 13 3204 29087 30 _ _ (2055609 / 100000) (513903 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846125312 :
    ThetaLowerSegment 846125312 846190848 (42304870719563 / 50000) (42308137093387 / 50000) := by
  exact
    packedTile32768 846125312 846190848 13 3178 29088 30 _ _ (64238 / 3125) (2055619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846190848 :
    ThetaLowerSegment 846190848 846256384 (42308137093387 / 50000) (42311367506503 / 50000) := by
  exact
    packedTile32768 846190848 846256384 13 3143 29089 30 _ _ (256953 / 12500) (2055627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846256384 :
    ThetaLowerSegment 846256384 846321920 (42311367506503 / 50000) (8462935825931 / 10000) := by
  exact
    packedTile32768 846256384 846321920 13 3222 29090 30 _ _ (128477 / 6250) (411127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846321920 :
    ThetaLowerSegment 846321920 846387456 (8462935825931 / 10000) (1692717945003 / 2000) := by
  exact
    packedTile32768 846321920 846387456 13 3181 29091 30 _ _ (51391 / 2500) (2055643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846387456 :
    ThetaLowerSegment 846387456 846452992 (1692717945003 / 2000) (8464243420761 / 10000) := by
  exact
    packedTile32768 846387456 846452992 13 3180 29092 30 _ _ (2055647 / 100000) (41113 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846452992 :
    ThetaLowerSegment 846452992 846518528 (8464243420761 / 10000) (8464899585837 / 10000) := by
  exact
    packedTile32768 846452992 846518528 13 3192 29093 30 _ _ (411131 / 20000) (1027829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846518528 :
    ThetaLowerSegment 846518528 846584064 (8464899585837 / 10000) (42327819880593 / 50000) := by
  exact
    packedTile32768 846518528 846584064 13 3232 29094 30 _ _ (2055663 / 100000) (1027833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846584064 :
    ThetaLowerSegment 846584064 846649600 (42327819880593 / 50000) (42331022616011 / 50000) := by
  exact
    packedTile32768 846584064 846649600 13 3116 29096 30 _ _ (2055671 / 100000) (1027837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846649600 :
    ThetaLowerSegment 846649600 846715136 (42331022616011 / 50000) (42334274698607 / 50000) := by
  exact
    packedTile32768 846649600 846715136 13 3164 29097 30 _ _ (1027839 / 50000) (2055681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846715136 :
    ThetaLowerSegment 846715136 846780672 (42334274698607 / 50000) (42337510348371 / 50000) := by
  exact
    packedTile32768 846715136 846780672 13 3148 29098 30 _ _ (1027843 / 50000) (2055689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846780672 :
    ThetaLowerSegment 846780672 846846208 (42337510348371 / 50000) (8468158247199 / 10000) := by
  exact
    packedTile32768 846780672 846846208 13 3192 29099 30 _ _ (1027847 / 50000) (2055697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846846208 :
    ThetaLowerSegment 846846208 846911744 (8468158247199 / 10000) (42344063911987 / 50000) := by
  exact
    packedTile32768 846846208 846911744 13 3184 29100 30 _ _ (2055701 / 100000) (256963 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846911744 :
    ThetaLowerSegment 846911744 846977280 (42344063911987 / 50000) (84694671145721 / 100000) := by
  exact
    packedTile32768 846911744 846977280 13 3183 29101 30 _ _ (2055709 / 100000) (64241 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell846977280 :
    ThetaLowerSegment 846977280 847042816 (84694671145721 / 100000) (4235063191507 / 5000) := by
  exact
    packedTile32768 846977280 847042816 13 3207 29102 30 _ _ (2055717 / 100000) (51393 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847042816 :
    ThetaLowerSegment 847042816 847108352 (4235063191507 / 5000) (16941542527893 / 20000) := by
  exact
    packedTile32768 847042816 847108352 13 3137 29104 30 _ _ (82229 / 4000) (128483 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847108352 :
    ThetaLowerSegment 847108352 847173888 (16941542527893 / 20000) (84714272480277 / 100000) := by
  exact
    packedTile32768 847108352 847173888 13 3191 29105 30 _ _ (513933 / 25000) (411147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847173888 :
    ThetaLowerSegment 847173888 847239424 (84714272480277 / 100000) (84720838513837 / 100000) := by
  exact
    packedTile32768 847173888 847239424 13 3194 29106 30 _ _ (102787 / 5000) (2055743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847239424 :
    ThetaLowerSegment 847239424 847304960 (84720838513837 / 100000) (16945467346653 / 20000) := by
  exact
    packedTile32768 847239424 847304960 13 3161 29107 30 _ _ (513937 / 25000) (2055751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847304960 :
    ThetaLowerSegment 847304960 847370496 (16945467346653 / 20000) (16946764528689 / 20000) := by
  exact
    packedTile32768 847304960 847370496 13 3155 29108 30 _ _ (513939 / 25000) (2055759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847370496 :
    ThetaLowerSegment 847370496 847436032 (16946764528689 / 20000) (8474043192149 / 10000) := by
  exact
    packedTile32768 847370496 847436032 13 3215 29109 30 _ _ (2055763 / 100000) (1027883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847436032 :
    ThetaLowerSegment 847436032 847501568 (8474043192149 / 10000) (42373468190467 / 50000) := by
  exact
    packedTile32768 847436032 847501568 13 3164 29110 30 _ _ (2055771 / 100000) (1027887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847501568 :
    ThetaLowerSegment 847501568 847567104 (42373468190467 / 50000) (10594186789493 / 12500) := by
  exact
    packedTile32768 847501568 847567104 13 3190 29111 30 _ _ (2055779 / 100000) (1027891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847567104 :
    ThetaLowerSegment 847567104 847632640 (10594186789493 / 12500) (10595013215867 / 12500) := by
  exact
    packedTile32768 847567104 847632640 13 3216 29113 30 _ _ (2055787 / 100000) (205579 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847632640 :
    ThetaLowerSegment 847632640 847698176 (10595013215867 / 12500) (2119165873217 / 2500) := by
  exact
    packedTile32768 847632640 847698176 13 3176 29114 30 _ _ (1027897 / 50000) (2055797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847698176 :
    ThetaLowerSegment 847698176 847763712 (2119165873217 / 2500) (42386589273223 / 50000) := by
  exact
    packedTile32768 847698176 847763712 13 3183 29115 30 _ _ (1027901 / 50000) (411161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847763712 :
    ThetaLowerSegment 847763712 847829248 (42386589273223 / 50000) (21194918212559 / 25000) := by
  exact
    packedTile32768 847763712 847829248 13 3159 29116 30 _ _ (205581 / 10000) (2055813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847829248 :
    ThetaLowerSegment 847829248 847894784 (21194918212559 / 25000) (5299139174677 / 6250) := by
  exact
    packedTile32768 847829248 847894784 13 3188 29117 30 _ _ (2055817 / 100000) (102791 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847894784 :
    ThetaLowerSegment 847894784 847960320 (5299139174677 / 6250) (84792770485807 / 100000) := by
  exact
    packedTile32768 847894784 847960320 13 3183 29118 30 _ _ (82233 / 4000) (513957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell847960320 :
    ThetaLowerSegment 847960320 848025856 (84792770485807 / 100000) (21199819299313 / 25000) := by
  exact
    packedTile32768 847960320 848025856 13 3165 29119 30 _ _ (2055833 / 100000) (513959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848025856 :
    ThetaLowerSegment 848025856 848091392 (21199819299313 / 25000) (84805775710653 / 100000) := by
  exact
    packedTile32768 848025856 848091392 13 3161 29120 30 _ _ (2055841 / 100000) (513961 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848091392 :
    ThetaLowerSegment 848091392 848156928 (84805775710653 / 100000) (84812319474837 / 100000) := by
  exact
    packedTile32768 848091392 848156928 13 3183 29122 30 _ _ (256981 / 12500) (2055851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848156928 :
    ThetaLowerSegment 848156928 848222464 (84812319474837 / 100000) (16963780876321 / 20000) := by
  exact
    packedTile32768 848156928 848222464 13 3203 29123 30 _ _ (128491 / 6250) (2055859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848222464 :
    ThetaLowerSegment 848222464 848288000 (16963780876321 / 20000) (84825341291789 / 100000) := by
  exact
    packedTile32768 848222464 848288000 13 3131 29124 30 _ _ (256983 / 12500) (2055867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848288000 :
    ThetaLowerSegment 848288000 848353536 (84825341291789 / 100000) (84831955032013 / 100000) := by
  exact
    packedTile32768 848288000 848353536 13 3217 29125 30 _ _ (64246 / 3125) (16447 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848353536 :
    ThetaLowerSegment 848353536 848419072 (84831955032013 / 100000) (84838505062507 / 100000) := by
  exact
    packedTile32768 848353536 848419072 13 3186 29126 30 _ _ (2055879 / 100000) (1027941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848419072 :
    ThetaLowerSegment 848419072 848484608 (84838505062507 / 100000) (16969034871987 / 20000) := by
  exact
    packedTile32768 848419072 848484608 13 3244 29127 30 _ _ (2055887 / 100000) (205589 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848484608 :
    ThetaLowerSegment 848484608 848550144 (16969034871987 / 20000) (106064709519 / 125) := by
  exact
    packedTile32768 848484608 848550144 13 3207 29128 30 _ _ (411179 / 20000) (1027949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848550144 :
    ThetaLowerSegment 848550144 848615680 (106064709519 / 125) (21214606156469 / 25000) := by
  exact
    packedTile32768 848550144 848615680 13 3238 29129 30 _ _ (1027951 / 50000) (411181 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848615680 :
    ThetaLowerSegment 848615680 848681216 (21214606156469 / 25000) (42432504852803 / 50000) := by
  exact
    packedTile32768 848615680 848681216 13 3203 29131 30 _ _ (205591 / 10000) (2055913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848681216 :
    ThetaLowerSegment 848681216 848746752 (42432504852803 / 50000) (21217947016813 / 25000) := by
  exact
    packedTile32768 848681216 848746752 13 3297 29132 30 _ _ (1027959 / 50000) (2055921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848746752 :
    ThetaLowerSegment 848746752 848812288 (21217947016813 / 25000) (21219597925391 / 25000) := by
  exact
    packedTile32768 848746752 848812288 13 3212 29133 30 _ _ (1027963 / 50000) (2055929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848812288 :
    ThetaLowerSegment 848812288 848877824 (21219597925391 / 25000) (42442475063917 / 50000) := by
  exact
    packedTile32768 848812288 848877824 13 3190 29134 30 _ _ (2055933 / 100000) (64248 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848877824 :
    ThetaLowerSegment 848877824 848943360 (42442475063917 / 50000) (42445711115051 / 50000) := by
  exact
    packedTile32768 848877824 848943360 13 3148 29135 30 _ _ (2055941 / 100000) (256993 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell848943360 :
    ThetaLowerSegment 848943360 849008896 (42445711115051 / 50000) (42449049976227 / 50000) := by
  exact
    packedTile32768 848943360 849008896 13 3248 29136 30 _ _ (2055949 / 100000) (128497 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849008896 :
    ThetaLowerSegment 849008896 849074432 (42449049976227 / 50000) (84904656399327 / 100000) := by
  exact
    packedTile32768 849008896 849074432 13 3189 29137 30 _ _ (2055957 / 100000) (51399 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849074432 :
    ThetaLowerSegment 849074432 849139968 (84904656399327 / 100000) (84911237540091 / 100000) := by
  exact
    packedTile32768 849074432 849139968 13 3201 29138 30 _ _ (513991 / 25000) (2055967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849139968 :
    ThetaLowerSegment 849139968 849205504 (84911237540091 / 100000) (84917732355639 / 100000) := by
  exact
    packedTile32768 849139968 849205504 13 3159 29140 30 _ _ (513993 / 25000) (82239 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849205504 :
    ThetaLowerSegment 849205504 849271040 (84917732355639 / 100000) (84924173740979 / 100000) := by
  exact
    packedTile32768 849205504 849271040 13 3133 29141 30 _ _ (102799 / 5000) (2055983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849271040 :
    ThetaLowerSegment 849271040 849336576 (84924173740979 / 100000) (42465356917813 / 50000) := by
  exact
    packedTile32768 849271040 849336576 13 3181 29142 30 _ _ (2055987 / 100000) (205599 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849336576 :
    ThetaLowerSegment 849336576 849402112 (42465356917813 / 50000) (84937262179701 / 100000) := by
  exact
    packedTile32768 849336576 849402112 13 3185 29143 30 _ _ (411199 / 20000) (1027999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849402112 :
    ThetaLowerSegment 849402112 849467648 (84937262179701 / 100000) (84943681021067 / 100000) := by
  exact
    packedTile32768 849402112 849467648 13 3122 29144 30 _ _ (2056003 / 100000) (1028003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849467648 :
    ThetaLowerSegment 849467648 849533184 (84943681021067 / 100000) (42475176388381 / 50000) := by
  exact
    packedTile32768 849467648 849533184 13 3245 29145 30 _ _ (2056011 / 100000) (1028007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849533184 :
    ThetaLowerSegment 849533184 849598720 (42475176388381 / 50000) (21239210906397 / 25000) := by
  exact
    packedTile32768 849533184 849598720 13 3157 29146 30 _ _ (1028009 / 50000) (2056021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849598720 :
    ThetaLowerSegment 849598720 849664256 (21239210906397 / 25000) (10620426321579 / 12500) := by
  exact
    packedTile32768 849598720 849664256 13 3194 29147 30 _ _ (1028013 / 50000) (2056029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849664256 :
    ThetaLowerSegment 849664256 849729792 (10620426321579 / 12500) (21242492330273 / 25000) := by
  exact
    packedTile32768 849664256 849729792 13 3190 29149 30 _ _ (1028017 / 50000) (2056037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849729792 :
    ThetaLowerSegment 849729792 849795328 (21242492330273 / 25000) (84976715191613 / 100000) := by
  exact
    packedTile32768 849729792 849795328 13 3281 29150 30 _ _ (2056041 / 100000) (514011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849795328 :
    ThetaLowerSegment 849795328 849860864 (84976715191613 / 100000) (42491672974819 / 50000) := by
  exact
    packedTile32768 849795328 849860864 13 3225 29151 30 _ _ (2056049 / 100000) (514013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849860864 :
    ThetaLowerSegment 849860864 849926400 (42491672974819 / 50000) (42494962666019 / 50000) := by
  exact
    packedTile32768 849860864 849926400 13 3200 29152 30 _ _ (2056057 / 100000) (102803 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849926400 :
    ThetaLowerSegment 849926400 849991936 (42494962666019 / 50000) (84996453338413 / 100000) := by
  exact
    packedTile32768 849926400 849991936 13 3175 29153 30 _ _ (411213 / 20000) (514017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell849991936 :
    ThetaLowerSegment 849991936 850057472 (84996453338413 / 100000) (85002989591301 / 100000) := by
  exact
    packedTile32768 849991936 850057472 13 3179 29154 30 _ _ (257009 / 12500) (82243 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850057472 :
    ThetaLowerSegment 850057472 850123008 (85002989591301 / 100000) (85009554654741 / 100000) := by
  exact
    packedTile32768 850057472 850123008 13 3193 29155 30 _ _ (25701 / 1250) (2056083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850123008 :
    ThetaLowerSegment 850123008 850188544 (85009554654741 / 100000) (85016103295021 / 100000) := by
  exact
    packedTile32768 850123008 850188544 13 3185 29156 30 _ _ (257011 / 12500) (2056091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850188544 :
    ThetaLowerSegment 850188544 850254080 (85016103295021 / 100000) (85022534760181 / 100000) := by
  exact
    packedTile32768 850188544 850254080 13 3128 29157 30 _ _ (411219 / 20000) (1028049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850254080 :
    ThetaLowerSegment 850254080 850319616 (85022534760181 / 100000) (8502907933603 / 10000) := by
  exact
    packedTile32768 850254080 850319616 13 3183 29159 30 _ _ (2056103 / 100000) (1028053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850319616 :
    ThetaLowerSegment 850319616 850385152 (8502907933603 / 10000) (4251775748173 / 5000) := by
  exact
    packedTile32768 850319616 850385152 13 3130 29160 30 _ _ (2056111 / 100000) (1028057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850385152 :
    ThetaLowerSegment 850385152 850450688 (4251775748173 / 5000) (2126051849497 / 2500) := by
  exact
    packedTile32768 850385152 850450688 13 3190 29161 30 _ _ (1028059 / 50000) (2056121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850450688 :
    ThetaLowerSegment 850450688 850516224 (2126051849497 / 2500) (42524358661493 / 50000) := by
  exact
    packedTile32768 850450688 850516224 13 3231 29162 30 _ _ (1028063 / 50000) (2056129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850516224 :
    ThetaLowerSegment 850516224 850581760 (42524358661493 / 50000) (2657976551897 / 3125) := by
  exact
    packedTile32768 850516224 850581760 13 3177 29163 30 _ _ (1028067 / 50000) (2056137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850581760 :
    ThetaLowerSegment 850581760 850647296 (2657976551897 / 3125) (21265437795427 / 25000) := by
  exact
    packedTile32768 850581760 850647296 13 3162 29164 30 _ _ (1028071 / 50000) (411229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850647296 :
    ThetaLowerSegment 850647296 850712832 (21265437795427 / 25000) (85068238331803 / 100000) := by
  exact
    packedTile32768 850647296 850712832 13 3155 29165 30 _ _ (2056149 / 100000) (257019 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850712832 :
    ThetaLowerSegment 850712832 850778368 (85068238331803 / 100000) (8507484065193 / 10000) := by
  exact
    packedTile32768 850712832 850778368 13 3211 29166 30 _ _ (2056157 / 100000) (12851 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850778368 :
    ThetaLowerSegment 850778368 850843904 (8507484065193 / 10000) (4254075336943 / 5000) := by
  exact
    packedTile32768 850778368 850843904 13 3242 29168 30 _ _ (411233 / 20000) (257021 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850843904 :
    ThetaLowerSegment 850843904 850909440 (4254075336943 / 5000) (4254395071689 / 5000) := by
  exact
    packedTile32768 850843904 850909440 13 3110 29169 30 _ _ (514043 / 25000) (82247 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850909440 :
    ThetaLowerSegment 850909440 850974976 (4254395071689 / 5000) (4254723649253 / 5000) := by
  exact
    packedTile32768 850909440 850974976 13 3196 29170 30 _ _ (102809 / 5000) (2056183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell850974976 :
    ThetaLowerSegment 850974976 851040512 (4254723649253 / 5000) (10637633397497 / 12500) := by
  exact
    packedTile32768 850974976 851040512 13 3207 29171 30 _ _ (514047 / 25000) (2056191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851040512 :
    ThetaLowerSegment 851040512 851106048 (10637633397497 / 12500) (10638447651113 / 12500) := by
  exact
    packedTile32768 851040512 851106048 13 3168 29172 30 _ _ (514049 / 25000) (2056199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851106048 :
    ThetaLowerSegment 851106048 851171584 (10638447651113 / 12500) (85114220688391 / 100000) := by
  exact
    packedTile32768 851106048 851171584 13 3229 29173 30 _ _ (2056203 / 100000) (1028103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851171584 :
    ThetaLowerSegment 851171584 851237120 (85114220688391 / 100000) (21280183177157 / 25000) := by
  exact
    packedTile32768 851171584 851237120 13 3167 29174 30 _ _ (2056211 / 100000) (1028107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851237120 :
    ThetaLowerSegment 851237120 851302656 (21280183177157 / 25000) (85127273541267 / 100000) := by
  exact
    packedTile32768 851237120 851302656 13 3181 29175 30 _ _ (2056219 / 100000) (1028111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851302656 :
    ThetaLowerSegment 851302656 851368192 (85127273541267 / 100000) (85133830845981 / 100000) := by
  exact
    packedTile32768 851302656 851368192 13 3189 29177 30 _ _ (1028113 / 50000) (2056229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851368192 :
    ThetaLowerSegment 851368192 851433728 (85133830845981 / 100000) (85140375838803 / 100000) := by
  exact
    packedTile32768 851368192 851433728 13 3183 29178 30 _ _ (1028117 / 50000) (2056237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851433728 :
    ThetaLowerSegment 851433728 851499264 (85140375838803 / 100000) (85147116200079 / 100000) := by
  exact
    packedTile32768 851433728 851499264 13 3278 29179 30 _ _ (1028121 / 50000) (411249 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851499264 :
    ThetaLowerSegment 851499264 851564800 (85147116200079 / 100000) (2128840811329 / 2500) := by
  exact
    packedTile32768 851499264 851564800 13 3169 29180 30 _ _ (2056249 / 100000) (514063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851564800 :
    ThetaLowerSegment 851564800 851630336 (2128840811329 / 2500) (17032032213827 / 20000) := by
  exact
    packedTile32768 851564800 851630336 13 3175 29181 30 _ _ (2056257 / 100000) (102813 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851630336 :
    ThetaLowerSegment 851630336 851695872 (17032032213827 / 20000) (2129166111817 / 2500) := by
  exact
    packedTile32768 851630336 851695872 13 3153 29182 30 _ _ (411253 / 20000) (514067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851695872 :
    ThetaLowerSegment 851695872 851761408 (2129166111817 / 2500) (85173107338719 / 100000) := by
  exact
    packedTile32768 851695872 851761408 13 3143 29183 30 _ _ (2056273 / 100000) (514069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851761408 :
    ThetaLowerSegment 851761408 851826944 (85173107338719 / 100000) (85179654534239 / 100000) := by
  exact
    packedTile32768 851761408 851826944 13 3184 29184 30 _ _ (51407 / 2500) (2056283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851826944 :
    ThetaLowerSegment 851826944 851892480 (85179654534239 / 100000) (85186098940831 / 100000) := by
  exact
    packedTile32768 851826944 851892480 13 3134 29186 30 _ _ (64259 / 3125) (2056291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851892480 :
    ThetaLowerSegment 851892480 851958016 (85186098940831 / 100000) (85192695538399 / 100000) := by
  exact
    packedTile32768 851892480 851958016 13 3208 29187 30 _ _ (257037 / 12500) (2056299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell851958016 :
    ThetaLowerSegment 851958016 852023552 (85192695538399 / 100000) (85199193455879 / 100000) := by
  exact
    packedTile32768 851958016 852023552 13 3160 29188 30 _ _ (2056303 / 100000) (1028153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852023552 :
    ThetaLowerSegment 852023552 852089088 (85199193455879 / 100000) (17041144859923 / 20000) := by
  exact
    packedTile32768 852023552 852089088 13 3176 29189 30 _ _ (2056311 / 100000) (1028157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852089088 :
    ThetaLowerSegment 852089088 852154624 (17041144859923 / 20000) (85212370322623 / 100000) := by
  exact
    packedTile32768 852089088 852154624 13 3232 29190 30 _ _ (2056319 / 100000) (1028161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852154624 :
    ThetaLowerSegment 852154624 852220160 (85212370322623 / 100000) (85218977298061 / 100000) := by
  exact
    packedTile32768 852154624 852220160 13 3213 29191 30 _ _ (1028163 / 50000) (2056329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852220160 :
    ThetaLowerSegment 852220160 852285696 (85218977298061 / 100000) (17045101642969 / 20000) := by
  exact
    packedTile32768 852220160 852285696 13 3176 29192 30 _ _ (1028167 / 50000) (2056337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852285696 :
    ThetaLowerSegment 852285696 852351232 (17045101642969 / 20000) (85231998030197 / 100000) := by
  exact
    packedTile32768 852285696 852351232 13 3156 29193 30 _ _ (1028171 / 50000) (411269 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852351232 :
    ThetaLowerSegment 852351232 852416768 (85231998030197 / 100000) (10654817923633 / 12500) := by
  exact
    packedTile32768 852351232 852416768 13 3183 29195 30 _ _ (2056349 / 100000) (64261 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852416768 :
    ThetaLowerSegment 852416768 852482304 (10654817923633 / 12500) (85245105224251 / 100000) := by
  exact
    packedTile32768 852416768 852482304 13 3191 29196 30 _ _ (2056357 / 100000) (51409 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852482304 :
    ThetaLowerSegment 852482304 852547840 (85245105224251 / 100000) (42625837655213 / 50000) := by
  exact
    packedTile32768 852482304 852547840 13 3195 29197 30 _ _ (411273 / 20000) (128523 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852547840 :
    ThetaLowerSegment 852547840 852613376 (42625837655213 / 50000) (42629137104087 / 50000) := by
  exact
    packedTile32768 852547840 852613376 13 3209 29198 30 _ _ (514093 / 25000) (16451 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852613376 :
    ThetaLowerSegment 852613376 852678912 (42629137104087 / 50000) (42632362536117 / 50000) := by
  exact
    packedTile32768 852613376 852678912 13 3137 29199 30 _ _ (102819 / 5000) (2056383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852678912 :
    ThetaLowerSegment 852678912 852744448 (42632362536117 / 50000) (42635627052067 / 50000) := by
  exact
    packedTile32768 852678912 852744448 13 3175 29200 30 _ _ (514097 / 25000) (2056391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852744448 :
    ThetaLowerSegment 852744448 852809984 (42635627052067 / 50000) (42638899806301 / 50000) := by
  exact
    packedTile32768 852744448 852809984 13 3183 29201 30 _ _ (514099 / 25000) (2056399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852809984 :
    ThetaLowerSegment 852809984 852875520 (42638899806301 / 50000) (85284378045799 / 100000) := by
  exact
    packedTile32768 852809984 852875520 13 3199 29202 30 _ _ (2056403 / 100000) (1028203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852875520 :
    ThetaLowerSegment 852875520 852941056 (85284378045799 / 100000) (85290966786643 / 100000) := by
  exact
    packedTile32768 852875520 852941056 13 3204 29204 30 _ _ (2056411 / 100000) (1028207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell852941056 :
    ThetaLowerSegment 852941056 853006592 (85290966786643 / 100000) (85297485634873 / 100000) := by
  exact
    packedTile32768 852941056 853006592 13 3170 29205 30 _ _ (2056419 / 100000) (1028211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853006592 :
    ThetaLowerSegment 853006592 853072128 (85297485634873 / 100000) (85304016843849 / 100000) := by
  exact
    packedTile32768 853006592 853072128 13 3176 29206 30 _ _ (1028213 / 50000) (2056429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853072128 :
    ThetaLowerSegment 853072128 853137664 (85304016843849 / 100000) (85310496667383 / 100000) := by
  exact
    packedTile32768 853072128 853137664 13 3151 29207 30 _ _ (1028217 / 50000) (2056437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853137664 :
    ThetaLowerSegment 853137664 853203200 (85310496667383 / 100000) (85317062886689 / 100000) := by
  exact
    packedTile32768 853137664 853203200 13 3193 29208 30 _ _ (1028221 / 50000) (411289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853203200 :
    ThetaLowerSegment 853203200 853268736 (85317062886689 / 100000) (3412946892551 / 4000) := by
  exact
    packedTile32768 853203200 853268736 13 3214 29209 30 _ _ (2056449 / 100000) (514113 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853268736 :
    ThetaLowerSegment 853268736 853334272 (3412946892551 / 4000) (85330269427831 / 100000) := by
  exact
    packedTile32768 853268736 853334272 13 3208 29210 30 _ _ (2056457 / 100000) (102823 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853334272 :
    ThetaLowerSegment 853334272 853399808 (85330269427831 / 100000) (2666778172733 / 3125) := by
  exact
    packedTile32768 853334272 853399808 13 3225 29211 30 _ _ (411293 / 20000) (514117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853399808 :
    ThetaLowerSegment 853399808 853465344 (2666778172733 / 3125) (10667935022673 / 12500) := by
  exact
    packedTile32768 853399808 853465344 13 3199 29213 30 _ _ (257059 / 12500) (82259 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853465344 :
    ThetaLowerSegment 853465344 853530880 (10667935022673 / 12500) (10668753758773 / 12500) := by
  exact
    packedTile32768 853465344 853530880 13 3185 29214 30 _ _ (12853 / 625) (2056483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853530880 :
    ThetaLowerSegment 853530880 853596416 (10668753758773 / 12500) (533479164731 / 625) := by
  exact
    packedTile32768 853530880 853596416 13 3227 29215 30 _ _ (257061 / 12500) (2056491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853596416 :
    ThetaLowerSegment 853596416 853661952 (533479164731 / 625) (4268161945749 / 5000) := by
  exact
    packedTile32768 853596416 853661952 13 3196 29216 30 _ _ (411299 / 20000) (1028249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853661952 :
    ThetaLowerSegment 853661952 853727488 (4268161945749 / 5000) (17073957775407 / 20000) := by
  exact
    packedTile32768 853661952 853727488 13 3185 29217 30 _ _ (2056503 / 100000) (1028253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853727488 :
    ThetaLowerSegment 853727488 853793024 (17073957775407 / 20000) (42688198223439 / 50000) := by
  exact
    packedTile32768 853727488 853793024 13 3213 29218 30 _ _ (2056511 / 100000) (1028257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853793024 :
    ThetaLowerSegment 853793024 853858560 (42688198223439 / 50000) (42691470143577 / 50000) := by
  exact
    packedTile32768 853793024 853858560 13 3182 29219 30 _ _ (1028259 / 50000) (2056521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853858560 :
    ThetaLowerSegment 853858560 853924096 (42691470143577 / 50000) (21347367439301 / 25000) := by
  exact
    packedTile32768 853858560 853924096 13 3175 29220 30 _ _ (1028263 / 50000) (2056529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853924096 :
    ThetaLowerSegment 853924096 853989632 (21347367439301 / 25000) (21348985931559 / 25000) := by
  exact
    packedTile32768 853924096 853989632 13 3148 29221 30 _ _ (1028267 / 50000) (2056537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell853989632 :
    ThetaLowerSegment 853989632 854055168 (21348985931559 / 25000) (4270132813803 / 5000) := by
  exact
    packedTile32768 853989632 854055168 13 3264 29223 30 _ _ (2056541 / 100000) (64267 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854055168 :
    ThetaLowerSegment 854055168 854120704 (4270132813803 / 5000) (85409148801253 / 100000) := by
  exact
    packedTile32768 854055168 854120704 13 3157 29224 30 _ _ (2056549 / 100000) (257069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854120704 :
    ThetaLowerSegment 854120704 854186240 (85409148801253 / 100000) (42707874146333 / 50000) := by
  exact
    packedTile32768 854120704 854186240 13 3209 29225 30 _ _ (2056557 / 100000) (25707 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854186240 :
    ThetaLowerSegment 854186240 854251776 (42707874146333 / 50000) (8542232107121 / 10000) := by
  exact
    packedTile32768 854186240 854251776 13 3196 29226 30 _ _ (514141 / 25000) (2056567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854251776 :
    ThetaLowerSegment 854251776 854317312 (8542232107121 / 10000) (8542880955587 / 10000) := by
  exact
    packedTile32768 854251776 854317312 13 3155 29227 30 _ _ (514143 / 25000) (82263 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854317312 :
    ThetaLowerSegment 854317312 854382848 (8542880955587 / 10000) (1708706413763 / 2000) := by
  exact
    packedTile32768 854317312 854382848 13 3166 29228 30 _ _ (102829 / 5000) (2056583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854382848 :
    ThetaLowerSegment 854382848 854448384 (1708706413763 / 2000) (10680231036911 / 12500) := by
  exact
    packedTile32768 854382848 854448384 13 3174 29229 30 _ _ (2056587 / 100000) (205659 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854448384 :
    ThetaLowerSegment 854448384 854513920 (10680231036911 / 12500) (85448398550363 / 100000) := by
  exact
    packedTile32768 854448384 854513920 13 3185 29230 30 _ _ (411319 / 20000) (1028299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854513920 :
    ThetaLowerSegment 854513920 854579456 (85448398550363 / 100000) (85454819264929 / 100000) := by
  exact
    packedTile32768 854513920 854579456 13 3122 29232 30 _ _ (2056603 / 100000) (1028303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854579456 :
    ThetaLowerSegment 854579456 854644992 (85454819264929 / 100000) (42730682728871 / 50000) := by
  exact
    packedTile32768 854579456 854644992 13 3183 29233 30 _ _ (2056611 / 100000) (1028307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854644992 :
    ThetaLowerSegment 854644992 854710528 (42730682728871 / 50000) (42733985657379 / 50000) := by
  exact
    packedTile32768 854644992 854710528 13 3212 29234 30 _ _ (1028309 / 50000) (2056621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854710528 :
    ThetaLowerSegment 854710528 854776064 (42733985657379 / 50000) (42737292711987 / 50000) := by
  exact
    packedTile32768 854710528 854776064 13 3216 29235 30 _ _ (1028313 / 50000) (2056629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854776064 :
    ThetaLowerSegment 854776064 854841600 (42737292711987 / 50000) (10685151230261 / 12500) := by
  exact
    packedTile32768 854776064 854841600 13 3221 29236 30 _ _ (1028317 / 50000) (2056637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854841600 :
    ThetaLowerSegment 854841600 854907136 (10685151230261 / 12500) (85487817829621 / 100000) := by
  exact
    packedTile32768 854841600 854907136 13 3213 29237 30 _ _ (2056641 / 100000) (514161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854907136 :
    ThetaLowerSegment 854907136 854972672 (85487817829621 / 100000) (21373619828933 / 25000) := by
  exact
    packedTile32768 854907136 854972672 13 3239 29238 30 _ _ (2056649 / 100000) (514163 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell854972672 :
    ThetaLowerSegment 854972672 855038208 (21373619828933 / 25000) (10687617152339 / 12500) := by
  exact
    packedTile32768 854972672 855038208 13 3140 29239 30 _ _ (2056657 / 100000) (102833 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855038208 :
    ThetaLowerSegment 855038208 855103744 (10687617152339 / 12500) (10688429534619 / 12500) := by
  exact
    packedTile32768 855038208 855103744 13 3160 29241 30 _ _ (257083 / 12500) (2056667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855103744 :
    ThetaLowerSegment 855103744 855169280 (10688429534619 / 12500) (10689252203419 / 12500) := by
  exact
    packedTile32768 855103744 855169280 13 3200 29242 30 _ _ (64271 / 3125) (82267 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855169280 :
    ThetaLowerSegment 855169280 855234816 (10689252203419 / 12500) (21380143580001 / 25000) := by
  exact
    packedTile32768 855169280 855234816 13 3188 29243 30 _ _ (2056679 / 100000) (1028341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855234816 :
    ThetaLowerSegment 855234816 855300352 (21380143580001 / 25000) (42763542895523 / 50000) := by
  exact
    packedTile32768 855234816 855300352 13 3166 29244 30 _ _ (2056687 / 100000) (205669 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855300352 :
    ThetaLowerSegment 855300352 855365888 (42763542895523 / 50000) (85533603457501 / 100000) := by
  exact
    packedTile32768 855300352 855365888 13 3169 29245 30 _ _ (411339 / 20000) (1028349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855365888 :
    ThetaLowerSegment 855365888 855431424 (85533603457501 / 100000) (17108037803461 / 20000) := by
  exact
    packedTile32768 855365888 855431424 13 3202 29246 30 _ _ (1028351 / 50000) (411341 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855431424 :
    ThetaLowerSegment 855431424 855496960 (17108037803461 / 20000) (3421870572767 / 4000) := by
  exact
    packedTile32768 855431424 855496960 13 3197 29247 30 _ _ (205671 / 10000) (2056713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855496960 :
    ThetaLowerSegment 855496960 855562496 (3421870572767 / 4000) (85553415745187 / 100000) := by
  exact
    packedTile32768 855496960 855562496 13 3234 29248 30 _ _ (1028359 / 50000) (2056721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855562496 :
    ThetaLowerSegment 855562496 855628032 (85553415745187 / 100000) (85559943790337 / 100000) := by
  exact
    packedTile32768 855562496 855628032 13 3174 29249 30 _ _ (82269 / 4000) (257091 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855628032 :
    ThetaLowerSegment 855628032 855693568 (85559943790337 / 100000) (85566471860879 / 100000) := by
  exact
    packedTile32768 855628032 855693568 13 3174 29251 30 _ _ (2056733 / 100000) (64273 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855693568 :
    ThetaLowerSegment 855693568 855759104 (85566471860879 / 100000) (42786488666331 / 50000) := by
  exact
    packedTile32768 855693568 855759104 13 3163 29252 30 _ _ (2056741 / 100000) (257093 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855759104 :
    ThetaLowerSegment 855759104 855824640 (42786488666331 / 50000) (42789810314351 / 50000) := by
  exact
    packedTile32768 855759104 855824640 13 3230 29253 30 _ _ (514187 / 25000) (2056751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855824640 :
    ThetaLowerSegment 855824640 855890176 (42789810314351 / 50000) (8558623926951 / 10000) := by
  exact
    packedTile32768 855824640 855890176 13 3218 29254 30 _ _ (514189 / 25000) (2056759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855890176 :
    ThetaLowerSegment 855890176 855955712 (8558623926951 / 10000) (42796424854503 / 50000) := by
  exact
    packedTile32768 855890176 855955712 13 3214 29255 30 _ _ (514191 / 25000) (2056767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell855955712 :
    ThetaLowerSegment 855955712 856021248 (42796424854503 / 50000) (85599371729847 / 100000) := by
  exact
    packedTile32768 855955712 856021248 13 3171 29256 30 _ _ (2056771 / 100000) (1028387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856021248 :
    ThetaLowerSegment 856021248 856086784 (85599371729847 / 100000) (10700753176239 / 12500) := by
  exact
    packedTile32768 856021248 856086784 13 3235 29257 30 _ _ (2056779 / 100000) (1028391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856086784 :
    ThetaLowerSegment 856086784 856152320 (10700753176239 / 12500) (17122496332861 / 20000) := by
  exact
    packedTile32768 856086784 856152320 13 3139 29258 30 _ _ (2056787 / 100000) (205679 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856152320 :
    ThetaLowerSegment 856152320 856217856 (17122496332861 / 20000) (17123790056287 / 20000) := by
  exact
    packedTile32768 856152320 856217856 13 3145 29260 30 _ _ (1028397 / 50000) (2056797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856217856 :
    ThetaLowerSegment 856217856 856283392 (17123790056287 / 20000) (3425020870553 / 4000) := by
  exact
    packedTile32768 856217856 856283392 13 3195 29261 30 _ _ (1028401 / 50000) (411361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856283392 :
    ThetaLowerSegment 856283392 856348928 (3425020870553 / 4000) (17126405490771 / 20000) := by
  exact
    packedTile32768 856283392 856348928 13 3163 29262 30 _ _ (205681 / 10000) (2056813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856348928 :
    ThetaLowerSegment 856348928 856414464 (17126405490771 / 20000) (85638592813719 / 100000) := by
  exact
    packedTile32768 856348928 856414464 13 3192 29263 30 _ _ (2056817 / 100000) (102841 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856414464 :
    ThetaLowerSegment 856414464 856480000 (85638592813719 / 100000) (85645038903269 / 100000) := by
  exact
    packedTile32768 856414464 856480000 13 3134 29264 30 _ _ (82273 / 4000) (514207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856480000 :
    ThetaLowerSegment 856480000 856545536 (85645038903269 / 100000) (2676612827647 / 3125) := by
  exact
    packedTile32768 856480000 856545536 13 3195 29265 30 _ _ (2056833 / 100000) (514209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856545536 :
    ThetaLowerSegment 856545536 856611072 (2676612827647 / 3125) (10707274817903 / 12500) := by
  exact
    packedTile32768 856545536 856611072 13 3203 29266 30 _ _ (51421 / 2500) (2056843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856611072 :
    ThetaLowerSegment 856611072 856676608 (10707274817903 / 12500) (10708094728937 / 12500) := by
  exact
    packedTile32768 856611072 856676608 13 3189 29267 30 _ _ (128553 / 6250) (2056851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856676608 :
    ThetaLowerSegment 856676608 856742144 (10708094728937 / 12500) (2677227118148 / 3125) := by
  exact
    packedTile32768 856676608 856742144 13 3165 29269 30 _ _ (257107 / 12500) (2056859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856742144 :
    ThetaLowerSegment 856742144 856807680 (2677227118148 / 3125) (3427114236517 / 4000) := by
  exact
    packedTile32768 856742144 856807680 13 3203 29270 30 _ _ (2056863 / 100000) (1028433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856807680 :
    ThetaLowerSegment 856807680 856873216 (3427114236517 / 4000) (85684409103931 / 100000) := by
  exact
    packedTile32768 856807680 856873216 13 3186 29271 30 _ _ (2056871 / 100000) (1028437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856873216 :
    ThetaLowerSegment 856873216 856938752 (85684409103931 / 100000) (2142273286681 / 2500) := by
  exact
    packedTile32768 856873216 856938752 13 3171 29272 30 _ _ (2056879 / 100000) (1028441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell856938752 :
    ThetaLowerSegment 856938752 857004288 (2142273286681 / 2500) (42848724869487 / 50000) := by
  exact
    packedTile32768 856938752 857004288 13 3169 29273 30 _ _ (1028443 / 50000) (2056889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857004288 :
    ThetaLowerSegment 857004288 857069824 (42848724869487 / 50000) (21425994065909 / 25000) := by
  exact
    packedTile32768 857004288 857069824 13 3173 29274 30 _ _ (1028447 / 50000) (2056897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857069824 :
    ThetaLowerSegment 857069824 857135360 (21425994065909 / 25000) (85710465786291 / 100000) := by
  exact
    packedTile32768 857069824 857135360 13 3155 29275 30 _ _ (2056901 / 100000) (257113 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857135360 :
    ThetaLowerSegment 857135360 857200896 (85710465786291 / 100000) (85716953277277 / 100000) := by
  exact
    packedTile32768 857135360 857200896 13 3154 29276 30 _ _ (2056909 / 100000) (128557 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857200896 :
    ThetaLowerSegment 857200896 857266432 (85716953277277 / 100000) (85723510728673 / 100000) := by
  exact
    packedTile32768 857200896 857266432 13 3188 29277 30 _ _ (2056917 / 100000) (51423 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857266432 :
    ThetaLowerSegment 857266432 857331968 (85723510728673 / 100000) (85730107283941 / 100000) := by
  exact
    packedTile32768 857266432 857331968 13 3207 29279 30 _ _ (514231 / 25000) (2056927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857331968 :
    ThetaLowerSegment 857331968 857397504 (85730107283941 / 100000) (17147344886837 / 20000) := by
  exact
    packedTile32768 857331968 857397504 13 3217 29280 30 _ _ (514233 / 25000) (411387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857397504 :
    ThetaLowerSegment 857397504 857463040 (17147344886837 / 20000) (3429725765757 / 4000) := by
  exact
    packedTile32768 857397504 857463040 13 3121 29281 30 _ _ (102847 / 5000) (2056943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857463040 :
    ThetaLowerSegment 857463040 857528576 (3429725765757 / 4000) (42874866272583 / 50000) := by
  exact
    packedTile32768 857463040 857528576 13 3203 29282 30 _ _ (2056947 / 100000) (41139 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857528576 :
    ThetaLowerSegment 857528576 857594112 (42874866272583 / 50000) (42878095691933 / 50000) := by
  exact
    packedTile32768 857528576 857594112 13 3140 29283 30 _ _ (411391 / 20000) (1028479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857594112 :
    ThetaLowerSegment 857594112 857659648 (42878095691933 / 50000) (10720345165461 / 12500) := by
  exact
    packedTile32768 857594112 857659648 13 3194 29284 30 _ _ (2056963 / 100000) (1028483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857659648 :
    ThetaLowerSegment 857659648 857725184 (10720345165461 / 12500) (5360586547943 / 6250) := by
  exact
    packedTile32768 857659648 857725184 13 3220 29285 30 _ _ (205697 / 10000) (2056973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857725184 :
    ThetaLowerSegment 857725184 857790720 (5360586547943 / 6250) (21443992802661 / 25000) := by
  exact
    packedTile32768 857725184 857790720 13 3202 29286 30 _ _ (1028489 / 50000) (2056981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857790720 :
    ThetaLowerSegment 857790720 857856256 (21443992802661 / 25000) (4289129323881 / 5000) := by
  exact
    packedTile32768 857790720 857856256 13 3216 29288 30 _ _ (1028493 / 50000) (2056989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857856256 :
    ThetaLowerSegment 857856256 857921792 (4289129323881 / 5000) (3431569633999 / 4000) := by
  exact
    packedTile32768 857856256 857921792 13 3235 29289 30 _ _ (2056993 / 100000) (514249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857921792 :
    ThetaLowerSegment 857921792 857987328 (3431569633999 / 4000) (42897869458067 / 50000) := by
  exact
    packedTile32768 857921792 857987328 13 3159 29290 30 _ _ (2057001 / 100000) (514251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell857987328 :
    ThetaLowerSegment 857987328 858052864 (42897869458067 / 50000) (8580233574079 / 10000) := by
  exact
    packedTile32768 857987328 858052864 13 3207 29291 30 _ _ (128563 / 6250) (2057011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858052864 :
    ThetaLowerSegment 858052864 858118400 (8580233574079 / 10000) (42904388128943 / 50000) := by
  exact
    packedTile32768 858052864 858118400 13 3131 29292 30 _ _ (257127 / 12500) (2057019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858118400 :
    ThetaLowerSegment 858118400 858183936 (42904388128943 / 50000) (42907730792943 / 50000) := by
  exact
    packedTile32768 858118400 858183936 13 3250 29293 30 _ _ (64282 / 3125) (2057027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858183936 :
    ThetaLowerSegment 858183936 858249472 (42907730792943 / 50000) (85821926834319 / 100000) := by
  exact
    packedTile32768 858183936 858249472 13 3143 29294 30 _ _ (2057031 / 100000) (1028517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858249472 :
    ThetaLowerSegment 858249472 858315008 (85821926834319 / 100000) (4291427422143 / 5000) := by
  exact
    packedTile32768 858249472 858315008 13 3219 29295 30 _ _ (2057039 / 100000) (1028521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858315008 :
    ThetaLowerSegment 858315008 858380544 (4291427422143 / 5000) (42917497614079 / 50000) := by
  exact
    packedTile32768 858315008 858380544 13 3134 29297 30 _ _ (2057047 / 100000) (41141 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858380544 :
    ThetaLowerSegment 858380544 858446080 (42917497614079 / 50000) (2146041656357 / 2500) := by
  exact
    packedTile32768 858380544 858446080 13 3243 29298 30 _ _ (1028527 / 50000) (2057057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858446080 :
    ThetaLowerSegment 858446080 858511616 (2146041656357 / 2500) (42924080199507 / 50000) := by
  exact
    packedTile32768 858446080 858511616 13 3157 29299 30 _ _ (1028531 / 50000) (411413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858511616 :
    ThetaLowerSegment 858511616 858577152 (42924080199507 / 50000) (10731836449533 / 12500) := by
  exact
    packedTile32768 858511616 858577152 13 3175 29300 30 _ _ (205707 / 10000) (2057073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858577152 :
    ThetaLowerSegment 858577152 858642688 (10731836449533 / 12500) (21465324731897 / 25000) := by
  exact
    packedTile32768 858577152 858642688 13 3212 29301 30 _ _ (2057077 / 100000) (51427 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858642688 :
    ThetaLowerSegment 858642688 858708224 (21465324731897 / 25000) (21466978628237 / 25000) := by
  exact
    packedTile32768 858642688 858708224 13 3216 29302 30 _ _ (411417 / 20000) (64284 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858708224 :
    ThetaLowerSegment 858708224 858773760 (21466978628237 / 25000) (21468660300947 / 25000) := by
  exact
    packedTile32768 858708224 858773760 13 3270 29303 30 _ _ (514273 / 25000) (411419 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858773760 :
    ThetaLowerSegment 858773760 858839296 (21468660300947 / 25000) (21470260724747 / 25000) := by
  exact
    packedTile32768 858773760 858839296 13 3112 29304 30 _ _ (20571 / 1000) (2057103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858839296 :
    ThetaLowerSegment 858839296 858904832 (21470260724747 / 25000) (4294385807867 / 5000) := by
  exact
    packedTile32768 858839296 858904832 13 3244 29305 30 _ _ (514277 / 25000) (2057111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858904832 :
    ThetaLowerSegment 858904832 858970368 (4294385807867 / 5000) (17178823168421 / 20000) := by
  exact
    packedTile32768 858904832 858970368 13 3111 29307 30 _ _ (411423 / 20000) (1028559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell858970368 :
    ThetaLowerSegment 858970368 859035904 (17178823168421 / 20000) (4295033388943 / 5000) := by
  exact
    packedTile32768 858970368 859035904 13 3185 29308 30 _ _ (2057123 / 100000) (1028563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859035904 :
    ThetaLowerSegment 859035904 859101440 (4295033388943 / 5000) (85907203284047 / 100000) := by
  exact
    packedTile32768 859035904 859101440 13 3177 29309 30 _ _ (2057131 / 100000) (1028567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859101440 :
    ThetaLowerSegment 859101440 859166976 (85907203284047 / 100000) (85913498126327 / 100000) := by
  exact
    packedTile32768 859101440 859166976 13 3060 29310 30 _ _ (1028569 / 50000) (2057141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859166976 :
    ThetaLowerSegment 859166976 859232512 (85913498126327 / 100000) (85920070707797 / 100000) := by
  exact
    packedTile32768 859166976 859232512 13 3195 29311 30 _ _ (1028573 / 50000) (2057149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859232512 :
    ThetaLowerSegment 859232512 859298048 (85920070707797 / 100000) (85926744115373 / 100000) := by
  exact
    packedTile32768 859232512 859298048 13 3244 29312 30 _ _ (1028577 / 50000) (2057157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859298048 :
    ThetaLowerSegment 859298048 859363584 (85926744115373 / 100000) (85933199486591 / 100000) := by
  exact
    packedTile32768 859298048 859363584 13 3138 29313 30 _ _ (2057161 / 100000) (514291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859363584 :
    ThetaLowerSegment 859363584 859429120 (85933199486591 / 100000) (2685615179389 / 3125) := by
  exact
    packedTile32768 859363584 859429120 13 3153 29314 30 _ _ (2057169 / 100000) (514293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859429120 :
    ThetaLowerSegment 859429120 859494656 (2685615179389 / 3125) (2685818839813 / 3125) := by
  exact
    packedTile32768 859429120 859494656 13 3168 29316 30 _ _ (257147 / 12500) (2057179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859494656 :
    ThetaLowerSegment 859494656 859560192 (2685818839813 / 3125) (2686024236778 / 3125) := by
  exact
    packedTile32768 859494656 859560192 13 3195 29317 30 _ _ (64287 / 3125) (2057187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859560192 :
    ThetaLowerSegment 859560192 859625728 (2686024236778 / 3125) (10744889737479 / 12500) := by
  exact
    packedTile32768 859560192 859625728 13 3083 29318 30 _ _ (257149 / 12500) (411439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859625728 :
    ThetaLowerSegment 859625728 859691264 (10744889737479 / 12500) (21491435520153 / 25000) := by
  exact
    packedTile32768 859625728 859691264 13 3220 29319 30 _ _ (2057199 / 100000) (1028601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859691264 :
    ThetaLowerSegment 859691264 859756800 (21491435520153 / 25000) (42986098798089 / 50000) := by
  exact
    packedTile32768 859691264 859756800 13 3138 29320 30 _ _ (2057207 / 100000) (205721 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859756800 :
    ThetaLowerSegment 859756800 859822336 (42986098798089 / 50000) (2686838053564 / 3125) := by
  exact
    packedTile32768 859756800 859822336 13 3218 29321 30 _ _ (411443 / 20000) (1028609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859822336 :
    ThetaLowerSegment 859822336 859887872 (2686838053564 / 3125) (42992656181951 / 50000) := by
  exact
    packedTile32768 859822336 859887872 13 3157 29322 30 _ _ (1028611 / 50000) (82289 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859887872 :
    ThetaLowerSegment 859887872 859953408 (42992656181951 / 50000) (2687248213006 / 3125) := by
  exact
    packedTile32768 859887872 859953408 13 3223 29323 30 _ _ (205723 / 10000) (2057233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell859953408 :
    ThetaLowerSegment 859953408 860018944 (2687248213006 / 3125) (17199692440049 / 20000) := by
  exact
    packedTile32768 859953408 860018944 13 3169 29324 30 _ _ (2057237 / 100000) (51431 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860018944 :
    ThetaLowerSegment 860018944 860084480 (17199692440049 / 20000) (537531212207 / 625) := by
  exact
    packedTile32768 860018944 860084480 13 3175 29326 30 _ _ (411449 / 20000) (64289 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860084480 :
    ThetaLowerSegment 860084480 860150016 (537531212207 / 625) (86011575105467 / 100000) := by
  exact
    packedTile32768 860084480 860150016 13 3199 29327 30 _ _ (2057253 / 100000) (257157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860150016 :
    ThetaLowerSegment 860150016 860215552 (86011575105467 / 100000) (86018145993907 / 100000) := by
  exact
    packedTile32768 860150016 860215552 13 3194 29328 30 _ _ (102863 / 5000) (2057263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860215552 :
    ThetaLowerSegment 860215552 860281088 (86018145993907 / 100000) (17204911288199 / 20000) := by
  exact
    packedTile32768 860215552 860281088 13 3116 29329 30 _ _ (514317 / 25000) (2057271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860281088 :
    ThetaLowerSegment 860281088 860346624 (17204911288199 / 20000) (8603096896717 / 10000) := by
  exact
    packedTile32768 860281088 860346624 13 3117 29330 30 _ _ (82291 / 4000) (1028639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860346624 :
    ThetaLowerSegment 860346624 860412160 (8603096896717 / 10000) (10754702777549 / 12500) := by
  exact
    packedTile32768 860346624 860412160 13 3234 29331 30 _ _ (2057283 / 100000) (1028643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860412160 :
    ThetaLowerSegment 860412160 860477696 (10754702777549 / 12500) (43022125405997 / 50000) := by
  exact
    packedTile32768 860412160 860477696 13 3222 29332 30 _ _ (2057291 / 100000) (1028647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860477696 :
    ThetaLowerSegment 860477696 860543232 (43022125405997 / 50000) (43025425311989 / 50000) := by
  exact
    packedTile32768 860477696 860543232 13 3208 29333 30 _ _ (1028649 / 50000) (2057301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860543232 :
    ThetaLowerSegment 860543232 860608768 (43025425311989 / 50000) (43028679970081 / 50000) := by
  exact
    packedTile32768 860543232 860608768 13 3164 29335 30 _ _ (1028653 / 50000) (2057309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860608768 :
    ThetaLowerSegment 860608768 860674304 (43028679970081 / 50000) (5378991187193 / 6250) := by
  exact
    packedTile32768 860608768 860674304 13 3159 29336 30 _ _ (1028657 / 50000) (2057317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860674304 :
    ThetaLowerSegment 860674304 860739840 (5378991187193 / 6250) (2689696182394 / 3125) := by
  exact
    packedTile32768 860674304 860739840 13 3120 29337 30 _ _ (2057321 / 100000) (514331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860739840 :
    ThetaLowerSegment 860739840 860805376 (2689696182394 / 3125) (86076879805369 / 100000) := by
  exact
    packedTile32768 860739840 860805376 13 3209 29338 30 _ _ (2057329 / 100000) (514333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860805376 :
    ThetaLowerSegment 860805376 860870912 (86076879805369 / 100000) (86083313095041 / 100000) := by
  exact
    packedTile32768 860805376 860870912 13 3127 29339 30 _ _ (257167 / 12500) (2057339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860870912 :
    ThetaLowerSegment 860870912 860936448 (86083313095041 / 100000) (86089923341313 / 100000) := by
  exact
    packedTile32768 860870912 860936448 13 3213 29340 30 _ _ (64292 / 3125) (2057347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell860936448 :
    ThetaLowerSegment 860936448 861001984 (86089923341313 / 100000) (86096525383881 / 100000) := by
  exact
    packedTile32768 860936448 861001984 13 3209 29341 30 _ _ (257169 / 12500) (411471 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861001984 :
    ThetaLowerSegment 861001984 861067520 (86096525383881 / 100000) (17220620140649 / 20000) := by
  exact
    packedTile32768 861001984 861067520 13 3196 29342 30 _ _ (2057359 / 100000) (1028681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861067520 :
    ThetaLowerSegment 861067520 861133056 (17220620140649 / 20000) (21527425698487 / 25000) := by
  exact
    packedTile32768 861067520 861133056 13 3209 29343 30 _ _ (2057367 / 100000) (205737 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861133056 :
    ThetaLowerSegment 861133056 861198592 (21527425698487 / 25000) (8611614854669 / 10000) := by
  exact
    packedTile32768 861133056 861198592 13 3133 29345 30 _ _ (1028687 / 50000) (2057377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861198592 :
    ThetaLowerSegment 861198592 861264128 (8611614854669 / 10000) (21530674298399 / 25000) := by
  exact
    packedTile32768 861198592 861264128 13 3183 29346 30 _ _ (1028691 / 50000) (411477 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861264128 :
    ThetaLowerSegment 861264128 861329664 (21530674298399 / 25000) (43064555039113 / 50000) := by
  exact
    packedTile32768 861264128 861329664 13 3117 29347 30 _ _ (205739 / 10000) (2057393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861329664 :
    ThetaLowerSegment 861329664 861395200 (43064555039113 / 50000) (21533916236267 / 25000) := by
  exact
    packedTile32768 861329664 861395200 13 3186 29348 30 _ _ (2057397 / 100000) (10287 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861395200 :
    ThetaLowerSegment 861395200 861460736 (21533916236267 / 25000) (43071134607559 / 50000) := by
  exact
    packedTile32768 861395200 861460736 13 3210 29349 30 _ _ (411481 / 20000) (64294 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861460736 :
    ThetaLowerSegment 861460736 861526272 (43071134607559 / 50000) (2153723072219 / 2500) := by
  exact
    packedTile32768 861460736 861526272 13 3234 29350 30 _ _ (2057413 / 100000) (257177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861526272 :
    ThetaLowerSegment 861526272 861591808 (2153723072219 / 2500) (2153885814141 / 2500) := by
  exact
    packedTile32768 861526272 861591808 13 3164 29351 30 _ _ (102871 / 5000) (2057423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861591808 :
    ThetaLowerSegment 861591808 861657344 (2153885814141 / 2500) (5385135536557 / 6250) := by
  exact
    packedTile32768 861591808 861657344 13 3274 29352 30 _ _ (514357 / 25000) (2057431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861657344 :
    ThetaLowerSegment 861657344 861722880 (5385135536557 / 6250) (86168709170777 / 100000) := by
  exact
    packedTile32768 861657344 861722880 13 3179 29354 30 _ _ (411487 / 20000) (1028719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861722880 :
    ThetaLowerSegment 861722880 861788416 (86168709170777 / 100000) (86175194231113 / 100000) := by
  exact
    packedTile32768 861722880 861788416 13 3152 29355 30 _ _ (2057443 / 100000) (1028723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861788416 :
    ThetaLowerSegment 861788416 861853952 (86175194231113 / 100000) (21545424458431 / 25000) := by
  exact
    packedTile32768 861788416 861853952 13 3161 29356 30 _ _ (2057451 / 100000) (1028727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861853952 :
    ThetaLowerSegment 861853952 861919488 (21545424458431 / 25000) (21547033390587 / 25000) := by
  exact
    packedTile32768 861853952 861919488 13 3128 29357 30 _ _ (1028729 / 50000) (2057461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861919488 :
    ThetaLowerSegment 861919488 861985024 (21547033390587 / 25000) (43097361812973 / 50000) := by
  exact
    packedTile32768 861919488 861985024 13 3203 29358 30 _ _ (1028733 / 50000) (2057469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell861985024 :
    ThetaLowerSegment 861985024 862050560 (43097361812973 / 50000) (3448054194457 / 4000) := by
  exact
    packedTile32768 861985024 862050560 13 3223 29359 30 _ _ (2057473 / 100000) (514369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862050560 :
    ThetaLowerSegment 862050560 862116096 (3448054194457 / 4000) (86207885306119 / 100000) := by
  exact
    packedTile32768 862050560 862116096 13 3174 29360 30 _ _ (2057481 / 100000) (514371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862116096 :
    ThetaLowerSegment 862116096 862181632 (86207885306119 / 100000) (21553603429679 / 25000) := by
  exact
    packedTile32768 862116096 862181632 13 3173 29361 30 _ _ (2057489 / 100000) (514373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862181632 :
    ThetaLowerSegment 862181632 862247168 (21553603429679 / 25000) (862210059359 / 1000) := by
  exact
    packedTile32768 862181632 862247168 13 3204 29362 30 _ _ (257187 / 12500) (2057499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862247168 :
    ThetaLowerSegment 862247168 862312704 (862210059359 / 1000) (21556885656527 / 25000) := by
  exact
    packedTile32768 862247168 862312704 13 3177 29364 30 _ _ (64297 / 3125) (2057507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862312704 :
    ThetaLowerSegment 862312704 862378240 (21556885656527 / 25000) (43117131228517 / 50000) := by
  exact
    packedTile32768 862312704 862378240 13 3266 29365 30 _ _ (2057511 / 100000) (1028757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862378240 :
    ThetaLowerSegment 862378240 862443776 (43117131228517 / 50000) (21560173565357 / 25000) := by
  exact
    packedTile32768 862378240 862443776 13 3126 29366 30 _ _ (2057519 / 100000) (1028761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862443776 :
    ThetaLowerSegment 862443776 862509312 (21560173565357 / 25000) (21561790781579 / 25000) := by
  exact
    packedTile32768 862443776 862509312 13 3144 29367 30 _ _ (2057527 / 100000) (205753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862509312 :
    ThetaLowerSegment 862509312 862574848 (21561790781579 / 25000) (8625370814197 / 10000) := by
  exact
    packedTile32768 862509312 862574848 13 3181 29368 30 _ _ (1028767 / 50000) (2057537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862574848 :
    ThetaLowerSegment 862574848 862640384 (8625370814197 / 10000) (10782540906823 / 12500) := by
  exact
    packedTile32768 862574848 862640384 13 3217 29369 30 _ _ (1028771 / 50000) (411509 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862640384 :
    ThetaLowerSegment 862640384 862705920 (10782540906823 / 12500) (86266880548149 / 100000) := by
  exact
    packedTile32768 862640384 862705920 13 3185 29370 30 _ _ (2057549 / 100000) (128597 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862705920 :
    ThetaLowerSegment 862705920 862771456 (86266880548149 / 100000) (1725469006553 / 2000) := by
  exact
    packedTile32768 862705920 862771456 13 3193 29371 30 _ _ (2057557 / 100000) (51439 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862771456 :
    ThetaLowerSegment 862771456 862836992 (1725469006553 / 2000) (17256014725877 / 20000) := by
  exact
    packedTile32768 862771456 862836992 13 3219 29372 30 _ _ (411513 / 20000) (64299 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862836992 :
    ThetaLowerSegment 862836992 862902528 (17256014725877 / 20000) (86286509714601 / 100000) := by
  exact
    packedTile32768 862836992 862902528 13 3128 29374 30 _ _ (514393 / 25000) (82303 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862902528 :
    ThetaLowerSegment 862902528 862968064 (86286509714601 / 100000) (86293096028181 / 100000) := by
  exact
    packedTile32768 862902528 862968064 13 3201 29375 30 _ _ (102879 / 5000) (2057583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell862968064 :
    ThetaLowerSegment 862968064 863033600 (86293096028181 / 100000) (539372706138 / 625) := by
  exact
    packedTile32768 862968064 863033600 13 3177 29376 30 _ _ (2057587 / 100000) (205759 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863033600 :
    ThetaLowerSegment 863033600 863099136 (539372706138 / 625) (17261237284431 / 20000) := by
  exact
    packedTile32768 863033600 863099136 13 3185 29377 30 _ _ (411519 / 20000) (1028799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863099136 :
    ThetaLowerSegment 863099136 863164672 (17261237284431 / 20000) (86312795442991 / 100000) := by
  exact
    packedTile32768 863099136 863164672 13 3212 29378 30 _ _ (2057603 / 100000) (1028803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863164672 :
    ThetaLowerSegment 863164672 863230208 (86312795442991 / 100000) (86319336585181 / 100000) := by
  exact
    packedTile32768 863164672 863230208 13 3179 29379 30 _ _ (205761 / 10000) (2057613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863230208 :
    ThetaLowerSegment 863230208 863295744 (86319336585181 / 100000) (86325838658061 / 100000) := by
  exact
    packedTile32768 863230208 863295744 13 3160 29380 30 _ _ (1028809 / 50000) (2057621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863295744 :
    ThetaLowerSegment 863295744 863361280 (86325838658061 / 100000) (86332217295561 / 100000) := by
  exact
    packedTile32768 863295744 863361280 13 3100 29381 30 _ _ (16461 / 800) (514407 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863361280 :
    ThetaLowerSegment 863361280 863426816 (86332217295561 / 100000) (5396180123053 / 6250) := by
  exact
    packedTile32768 863361280 863426816 13 3239 29383 30 _ _ (2057633 / 100000) (514409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863426816 :
    ThetaLowerSegment 863426816 863492352 (5396180123053 / 6250) (10793179958441 / 12500) := by
  exact
    packedTile32768 863426816 863492352 13 3187 29384 30 _ _ (51441 / 2500) (2057643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863492352 :
    ThetaLowerSegment 863492352 863557888 (10793179958441 / 12500) (10794008933379 / 12500) := by
  exact
    packedTile32768 863492352 863557888 13 3223 29385 30 _ _ (128603 / 6250) (2057651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863557888 :
    ThetaLowerSegment 863557888 863623424 (10794008933379 / 12500) (10794829423709 / 12500) := by
  exact
    packedTile32768 863557888 863623424 13 3190 29386 30 _ _ (257207 / 12500) (2057659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863623424 :
    ThetaLowerSegment 863623424 863688960 (10794829423709 / 12500) (21591278228199 / 25000) := by
  exact
    packedTile32768 863623424 863688960 13 3148 29387 30 _ _ (2057663 / 100000) (1028833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863688960 :
    ThetaLowerSegment 863688960 863754496 (21591278228199 / 25000) (17274322619097 / 20000) := by
  exact
    packedTile32768 863688960 863754496 13 3159 29388 30 _ _ (2057671 / 100000) (1028837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863754496 :
    ThetaLowerSegment 863754496 863820032 (17274322619097 / 20000) (86378226472577 / 100000) := by
  exact
    packedTile32768 863754496 863820032 13 3214 29389 30 _ _ (1028839 / 50000) (2057681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863820032 :
    ThetaLowerSegment 863820032 863885568 (86378226472577 / 100000) (86384885144473 / 100000) := by
  exact
    packedTile32768 863820032 863885568 13 3236 29390 30 _ _ (1028843 / 50000) (2057689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863885568 :
    ThetaLowerSegment 863885568 863951104 (86384885144473 / 100000) (86391436842169 / 100000) := by
  exact
    packedTile32768 863885568 863951104 13 3184 29391 30 _ _ (1028847 / 50000) (2057697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell863951104 :
    ThetaLowerSegment 863951104 864016640 (86391436842169 / 100000) (43199003540731 / 50000) := by
  exact
    packedTile32768 863951104 864016640 13 3193 29393 30 _ _ (2057701 / 100000) (257213 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864016640 :
    ThetaLowerSegment 864016640 864082176 (43199003540731 / 50000) (86404396267907 / 100000) := by
  exact
    packedTile32768 864016640 864082176 13 3105 29394 30 _ _ (2057709 / 100000) (128607 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864082176 :
    ThetaLowerSegment 864082176 864147712 (86404396267907 / 100000) (86411042690587 / 100000) := by
  exact
    packedTile32768 864082176 864147712 13 3230 29395 30 _ _ (514429 / 25000) (2057719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864147712 :
    ThetaLowerSegment 864147712 864213248 (86411042690587 / 100000) (86417680908211 / 100000) := by
  exact
    packedTile32768 864147712 864213248 13 3226 29396 30 _ _ (514431 / 25000) (2057727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864213248 :
    ThetaLowerSegment 864213248 864278784 (86417680908211 / 100000) (86424294458859 / 100000) := by
  exact
    packedTile32768 864213248 864278784 13 3214 29397 30 _ _ (514433 / 25000) (411547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864278784 :
    ThetaLowerSegment 864278784 864344320 (86424294458859 / 100000) (86430759874797 / 100000) := by
  exact
    packedTile32768 864278784 864344320 13 3142 29398 30 _ _ (2057739 / 100000) (1028871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864344320 :
    ThetaLowerSegment 864344320 864409856 (86430759874797 / 100000) (86437336434209 / 100000) := by
  exact
    packedTile32768 864344320 864409856 13 3196 29399 30 _ _ (2057747 / 100000) (8231 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864409856 :
    ThetaLowerSegment 864409856 864475392 (86437336434209 / 100000) (86444087925083 / 100000) := by
  exact
    packedTile32768 864409856 864475392 13 3281 29400 30 _ _ (1028877 / 50000) (2057757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864475392 :
    ThetaLowerSegment 864475392 864540928 (86444087925083 / 100000) (86450668647959 / 100000) := by
  exact
    packedTile32768 864475392 864540928 13 3198 29401 30 _ _ (1028881 / 50000) (411553 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864540928 :
    ThetaLowerSegment 864540928 864606464 (86450668647959 / 100000) (21614303602787 / 25000) := by
  exact
    packedTile32768 864540928 864606464 13 3181 29403 30 _ _ (2057769 / 100000) (514443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864606464 :
    ThetaLowerSegment 864606464 864672000 (21614303602787 / 25000) (86463957746377 / 100000) := by
  exact
    packedTile32768 864606464 864672000 13 3277 29404 30 _ _ (2057777 / 100000) (102889 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864672000 :
    ThetaLowerSegment 864672000 864737536 (86463957746377 / 100000) (86470448000267 / 100000) := by
  exact
    packedTile32768 864672000 864737536 13 3154 29405 30 _ _ (411557 / 20000) (514447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864737536 :
    ThetaLowerSegment 864737536 864803072 (86470448000267 / 100000) (86476890947019 / 100000) := by
  exact
    packedTile32768 864737536 864803072 13 3131 29406 30 _ _ (64306 / 3125) (411559 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864803072 :
    ThetaLowerSegment 864803072 864868608 (86476890947019 / 100000) (86483438866619 / 100000) := by
  exact
    packedTile32768 864803072 864868608 13 3182 29407 30 _ _ (10289 / 500) (2057803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864868608 :
    ThetaLowerSegment 864868608 864934144 (86483438866619 / 100000) (43244971797273 / 50000) := by
  exact
    packedTile32768 864868608 864934144 13 3161 29408 30 _ _ (2057807 / 100000) (205781 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864934144 :
    ThetaLowerSegment 864934144 864999680 (43244971797273 / 50000) (10812056300697 / 12500) := by
  exact
    packedTile32768 864934144 864999680 13 3162 29409 30 _ _ (411563 / 20000) (1028909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell864999680 :
    ThetaLowerSegment 864999680 865065216 (10812056300697 / 12500) (43251502284323 / 50000) := by
  exact
    packedTile32768 864999680 865065216 13 3185 29410 30 _ _ (1028911 / 50000) (82313 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865065216 :
    ThetaLowerSegment 865065216 865130752 (43251502284323 / 50000) (21627414383259 / 25000) := by
  exact
    packedTile32768 865065216 865130752 13 3233 29411 30 _ _ (205783 / 10000) (2057833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865130752 :
    ThetaLowerSegment 865130752 865196288 (21627414383259 / 25000) (43258075005963 / 50000) := by
  exact
    packedTile32768 865130752 865196288 13 3155 29413 30 _ _ (1028919 / 50000) (2057841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865196288 :
    ThetaLowerSegment 865196288 865261824 (43258075005963 / 50000) (86522761867911 / 100000) := by
  exact
    packedTile32768 865196288 865261824 13 3213 29414 30 _ _ (411569 / 20000) (257231 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865261824 :
    ThetaLowerSegment 865261824 865327360 (86522761867911 / 100000) (86529355228923 / 100000) := by
  exact
    packedTile32768 865261824 865327360 13 3204 29415 30 _ _ (2057853 / 100000) (64308 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865327360 :
    ThetaLowerSegment 865327360 865392896 (86529355228923 / 100000) (86536053563223 / 100000) := by
  exact
    packedTile32768 865327360 865392896 13 3255 29416 30 _ _ (102893 / 5000) (2057863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865392896 :
    ThetaLowerSegment 865392896 865458432 (86536053563223 / 100000) (86542581120519 / 100000) := by
  exact
    packedTile32768 865392896 865458432 13 3172 29417 30 _ _ (514467 / 25000) (2057871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865458432 :
    ThetaLowerSegment 865458432 865523968 (86542581120519 / 100000) (86549182783519 / 100000) := by
  exact
    packedTile32768 865458432 865523968 13 3208 29418 30 _ _ (16463 / 800) (1028939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865523968 :
    ThetaLowerSegment 865523968 865589504 (86549182783519 / 100000) (17311142077679 / 20000) := by
  exact
    packedTile32768 865523968 865589504 13 3172 29419 30 _ _ (2057883 / 100000) (1028943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865589504 :
    ThetaLowerSegment 865589504 865655040 (17311142077679 / 20000) (86562287408031 / 100000) := by
  exact
    packedTile32768 865589504 865655040 13 3196 29420 30 _ _ (2057891 / 100000) (1028947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865655040 :
    ThetaLowerSegment 865655040 865720576 (86562287408031 / 100000) (86568720397179 / 100000) := by
  exact
    packedTile32768 865655040 865720576 13 3126 29422 30 _ _ (1028949 / 50000) (2057901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865720576 :
    ThetaLowerSegment 865720576 865786112 (86568720397179 / 100000) (86575281001507 / 100000) := by
  exact
    packedTile32768 865720576 865786112 13 3188 29423 30 _ _ (1028953 / 50000) (2057909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865786112 :
    ThetaLowerSegment 865786112 865851648 (86575281001507 / 100000) (43290890974337 / 50000) := by
  exact
    packedTile32768 865786112 865851648 13 3159 29424 30 _ _ (2057913 / 100000) (514479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865851648 :
    ThetaLowerSegment 865851648 865917184 (43290890974337 / 50000) (86588212951799 / 100000) := by
  exact
    packedTile32768 865851648 865917184 13 3125 29425 30 _ _ (2057921 / 100000) (514481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865917184 :
    ThetaLowerSegment 865917184 865982720 (86588212951799 / 100000) (86594775684191 / 100000) := by
  exact
    packedTile32768 865917184 865982720 13 3189 29426 30 _ _ (257241 / 12500) (2057931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell865982720 :
    ThetaLowerSegment 865982720 866048256 (86594775684191 / 100000) (86601223197679 / 100000) := by
  exact
    packedTile32768 865982720 866048256 13 3133 29427 30 _ _ (128621 / 6250) (2057939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866048256 :
    ThetaLowerSegment 866048256 866113792 (86601223197679 / 100000) (86607798328759 / 100000) := by
  exact
    packedTile32768 866048256 866113792 13 3195 29428 30 _ _ (257243 / 12500) (2057947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866113792 :
    ThetaLowerSegment 866113792 866179328 (86607798328759 / 100000) (692914510413 / 800) := by
  exact
    packedTile32768 866113792 866179328 13 3166 29429 30 _ _ (2057951 / 100000) (1028977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866179328 :
    ThetaLowerSegment 866179328 866244864 (692914510413 / 800) (86620825183901 / 100000) := by
  exact
    packedTile32768 866179328 866244864 13 3164 29430 30 _ _ (2057959 / 100000) (1028981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866244864 :
    ThetaLowerSegment 866244864 866310400 (86620825183901 / 100000) (86627348936121 / 100000) := by
  exact
    packedTile32768 866244864 866310400 13 3170 29432 30 _ _ (1028983 / 50000) (2057969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866310400 :
    ThetaLowerSegment 866310400 866375936 (86627348936121 / 100000) (86633856249909 / 100000) := by
  exact
    packedTile32768 866310400 866375936 13 3162 29433 30 _ _ (1028987 / 50000) (2057977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866375936 :
    ThetaLowerSegment 866375936 866441472 (86633856249909 / 100000) (43320205459697 / 50000) := by
  exact
    packedTile32768 866375936 866441472 13 3185 29434 30 _ _ (2057981 / 100000) (64312 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866441472 :
    ThetaLowerSegment 866441472 866507008 (43320205459697 / 50000) (43323469430251 / 50000) := by
  exact
    packedTile32768 866441472 866507008 13 3172 29435 30 _ _ (2057989 / 100000) (257249 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866507008 :
    ThetaLowerSegment 866507008 866572544 (43323469430251 / 50000) (10831684896871 / 12500) := by
  exact
    packedTile32768 866507008 866572544 13 3178 29436 30 _ _ (2057997 / 100000) (1029 / 50)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866572544 :
    ThetaLowerSegment 866572544 866638080 (10831684896871 / 12500) (5416249675977 / 6250) := by
  exact
    packedTile32768 866572544 866638080 13 3166 29437 30 _ _ (514501 / 25000) (2058007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866638080 :
    ThetaLowerSegment 866638080 866703616 (5416249675977 / 6250) (10833327187281 / 12500) := by
  exact
    packedTile32768 866638080 866703616 13 3218 29438 30 _ _ (514503 / 25000) (411603 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866703616 :
    ThetaLowerSegment 866703616 866769152 (10833327187281 / 12500) (86673192868953 / 100000) := by
  exact
    packedTile32768 866703616 866769152 13 3195 29439 30 _ _ (2058019 / 100000) (1029011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866769152 :
    ThetaLowerSegment 866769152 866834688 (86673192868953 / 100000) (86679819715893 / 100000) := by
  exact
    packedTile32768 866769152 866834688 13 3220 29440 30 _ _ (2058027 / 100000) (205803 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866834688 :
    ThetaLowerSegment 866834688 866900224 (86679819715893 / 100000) (86686417772897 / 100000) := by
  exact
    packedTile32768 866834688 866900224 13 3206 29442 30 _ _ (1029017 / 50000) (2058037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866900224 :
    ThetaLowerSegment 866900224 866965760 (86686417772897 / 100000) (17338581767473 / 20000) := by
  exact
    packedTile32768 866900224 866965760 13 3154 29443 30 _ _ (1029021 / 50000) (411609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell866965760 :
    ThetaLowerSegment 866965760 867031296 (17338581767473 / 20000) (17339895626593 / 20000) := by
  exact
    packedTile32768 866965760 867031296 13 3192 29444 30 _ _ (41161 / 2000) (2058053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867031296 :
    ThetaLowerSegment 867031296 867096832 (17339895626593 / 20000) (10838260819249 / 12500) := by
  exact
    packedTile32768 867031296 867096832 13 3211 29445 30 _ _ (2058057 / 100000) (102903 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867096832 :
    ThetaLowerSegment 867096832 867162368 (10838260819249 / 12500) (21678186613083 / 25000) := by
  exact
    packedTile32768 867096832 867162368 13 3236 29446 30 _ _ (411613 / 20000) (514517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867162368 :
    ThetaLowerSegment 867162368 867227904 (21678186613083 / 25000) (4335964453161 / 5000) := by
  exact
    packedTile32768 867162368 867227904 13 3179 29447 30 _ _ (257259 / 12500) (82323 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867227904 :
    ThetaLowerSegment 867227904 867293440 (4335964453161 / 5000) (4336291482073 / 5000) := by
  exact
    packedTile32768 867227904 867293440 13 3178 29448 30 _ _ (12863 / 625) (2058083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867293440 :
    ThetaLowerSegment 867293440 867358976 (4336291482073 / 5000) (43366230398887 / 50000) := by
  exact
    packedTile32768 867293440 867358976 13 3222 29449 30 _ _ (2058087 / 100000) (205809 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867358976 :
    ThetaLowerSegment 867358976 867424512 (43366230398887 / 50000) (86739094037959 / 100000) := by
  exact
    packedTile32768 867358976 867424512 13 3223 29450 30 _ _ (411619 / 20000) (1029049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867424512 :
    ThetaLowerSegment 867424512 867490048 (86739094037959 / 100000) (86745725242603 / 100000) := by
  exact
    packedTile32768 867424512 867490048 13 3222 29452 30 _ _ (1029051 / 50000) (411621 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867490048 :
    ThetaLowerSegment 867490048 867555584 (86745725242603 / 100000) (86752346182473 / 100000) := by
  exact
    packedTile32768 867490048 867555584 13 3217 29453 30 _ _ (205811 / 10000) (2058113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867555584 :
    ThetaLowerSegment 867555584 867621120 (86752346182473 / 100000) (86758942450663 / 100000) := by
  exact
    packedTile32768 867555584 867621120 13 3205 29454 30 _ _ (1029059 / 50000) (2058121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867621120 :
    ThetaLowerSegment 867621120 867686656 (86758942450663 / 100000) (86765306173163 / 100000) := by
  exact
    packedTile32768 867621120 867686656 13 3092 29455 30 _ _ (3293 / 160) (128633 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867686656 :
    ThetaLowerSegment 867686656 867752192 (86765306173163 / 100000) (21692996203687 / 25000) := by
  exact
    packedTile32768 867686656 867752192 13 3245 29456 30 _ _ (2058133 / 100000) (257267 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867752192 :
    ThetaLowerSegment 867752192 867817728 (21692996203687 / 25000) (21694595378467 / 25000) := by
  exact
    packedTile32768 867752192 867817728 13 3108 29457 30 _ _ (102907 / 5000) (2058143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867817728 :
    ThetaLowerSegment 867817728 867883264 (21694595378467 / 25000) (21696251158533 / 25000) := by
  exact
    packedTile32768 867817728 867883264 13 3218 29458 30 _ _ (514537 / 25000) (2058151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867883264 :
    ThetaLowerSegment 867883264 867948800 (21696251158533 / 25000) (86791592788287 / 100000) := by
  exact
    packedTile32768 867883264 867948800 13 3201 29459 30 _ _ (411631 / 20000) (1029079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell867948800 :
    ThetaLowerSegment 867948800 868014336 (86791592788287 / 100000) (86798158328257 / 100000) := by
  exact
    packedTile32768 867948800 868014336 13 3190 29460 30 _ _ (2058163 / 100000) (1029083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868014336 :
    ThetaLowerSegment 868014336 868079872 (86798158328257 / 100000) (86804773286637 / 100000) := by
  exact
    packedTile32768 868014336 868079872 13 3214 29462 30 _ _ (205817 / 10000) (2058173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868079872 :
    ThetaLowerSegment 868079872 868145408 (86804773286637 / 100000) (86811316234499 / 100000) := by
  exact
    packedTile32768 868079872 868145408 13 3179 29463 30 _ _ (1029089 / 50000) (2058181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868145408 :
    ThetaLowerSegment 868145408 868210944 (86811316234499 / 100000) (43408892554977 / 50000) := by
  exact
    packedTile32768 868145408 868210944 13 3143 29464 30 _ _ (411637 / 20000) (514547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868210944 :
    ThetaLowerSegment 868210944 868276480 (43408892554977 / 50000) (43412148616303 / 50000) := by
  exact
    packedTile32768 868210944 868276480 13 3164 29465 30 _ _ (2058193 / 100000) (514549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868276480 :
    ThetaLowerSegment 868276480 868342016 (43412148616303 / 50000) (86830762041947 / 100000) := by
  exact
    packedTile32768 868276480 868342016 13 3141 29466 30 _ _ (2058201 / 100000) (514551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868342016 :
    ThetaLowerSegment 868342016 868407552 (86830762041947 / 100000) (86837265979227 / 100000) := by
  exact
    packedTile32768 868342016 868407552 13 3160 29467 30 _ _ (64319 / 3125) (2058211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868407552 :
    ThetaLowerSegment 868407552 868473088 (86837265979227 / 100000) (86843874910803 / 100000) := by
  exact
    packedTile32768 868407552 868473088 13 3211 29468 30 _ _ (257277 / 12500) (2058219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868473088 :
    ThetaLowerSegment 868473088 868538624 (86843874910803 / 100000) (86850527087539 / 100000) := by
  exact
    packedTile32768 868473088 868538624 13 3232 29469 30 _ _ (2058223 / 100000) (1029113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868538624 :
    ThetaLowerSegment 868538624 868604160 (86850527087539 / 100000) (86856932302411 / 100000) := by
  exact
    packedTile32768 868538624 868604160 13 3112 29470 30 _ _ (2058231 / 100000) (1029117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868604160 :
    ThetaLowerSegment 868604160 868669696 (86856932302411 / 100000) (86863543362867 / 100000) := by
  exact
    packedTile32768 868604160 868669696 13 3212 29472 30 _ _ (1029119 / 50000) (2058241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868669696 :
    ThetaLowerSegment 868669696 868735232 (86863543362867 / 100000) (86870113284099 / 100000) := by
  exact
    packedTile32768 868669696 868735232 13 3192 29473 30 _ _ (1029123 / 50000) (2058249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868735232 :
    ThetaLowerSegment 868735232 868800768 (86870113284099 / 100000) (86876687344181 / 100000) := by
  exact
    packedTile32768 868735232 868800768 13 3194 29474 30 _ _ (2058253 / 100000) (128641 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868800768 :
    ThetaLowerSegment 868800768 868866304 (86876687344181 / 100000) (2715100183024 / 3125) := by
  exact
    packedTile32768 868800768 868866304 13 3167 29475 30 _ _ (2058261 / 100000) (257283 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868866304 :
    ThetaLowerSegment 868866304 868931840 (2715100183024 / 3125) (21722489758519 / 25000) := by
  exact
    packedTile32768 868866304 868931840 13 3281 29476 30 _ _ (514567 / 25000) (2058271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868931840 :
    ThetaLowerSegment 868931840 868997376 (21722489758519 / 25000) (21724120942249 / 25000) := by
  exact
    packedTile32768 868931840 868997376 13 3170 29477 30 _ _ (514569 / 25000) (2058279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell868997376 :
    ThetaLowerSegment 868997376 869062912 (21724120942249 / 25000) (869029797133 / 1000) := by
  exact
    packedTile32768 868997376 869062912 13 3156 29478 30 _ _ (514571 / 25000) (2058287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869062912 :
    ThetaLowerSegment 869062912 869128448 (869029797133 / 1000) (21727358628469 / 25000) := by
  exact
    packedTile32768 869062912 869128448 13 3136 29479 30 _ _ (2058291 / 100000) (1029147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869128448 :
    ThetaLowerSegment 869128448 869193984 (21727358628469 / 25000) (86915953146809 / 100000) := by
  exact
    packedTile32768 869128448 869193984 13 3167 29480 30 _ _ (2058299 / 100000) (1029151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869193984 :
    ThetaLowerSegment 869193984 869259520 (86915953146809 / 100000) (86922589125353 / 100000) := by
  exact
    packedTile32768 869193984 869259520 13 3224 29482 30 _ _ (1029153 / 50000) (2058309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869259520 :
    ThetaLowerSegment 869259520 869325056 (86922589125353 / 100000) (3477162747913 / 4000) := by
  exact
    packedTile32768 869259520 869325056 13 3148 29483 30 _ _ (1029157 / 50000) (2058317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869325056 :
    ThetaLowerSegment 869325056 869390592 (3477162747913 / 4000) (86935667674951 / 100000) := by
  exact
    packedTile32768 869325056 869390592 13 3206 29484 30 _ _ (2058321 / 100000) (514581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869390592 :
    ThetaLowerSegment 869390592 869456128 (86935667674951 / 100000) (43471101434763 / 50000) := by
  exact
    packedTile32768 869390592 869456128 13 3175 29485 30 _ _ (2058329 / 100000) (514583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869456128 :
    ThetaLowerSegment 869456128 869521664 (43471101434763 / 50000) (43474350518139 / 50000) := by
  exact
    packedTile32768 869456128 869521664 13 3157 29486 30 _ _ (64323 / 3125) (2058339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869521664 :
    ThetaLowerSegment 869521664 869587200 (43474350518139 / 50000) (43477556388919 / 50000) := by
  exact
    packedTile32768 869521664 869587200 13 3115 29487 30 _ _ (257293 / 12500) (2058347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869587200 :
    ThetaLowerSegment 869587200 869652736 (43477556388919 / 50000) (17392371598813 / 20000) := by
  exact
    packedTile32768 869587200 869652736 13 3277 29488 30 _ _ (2058351 / 100000) (1029177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869652736 :
    ThetaLowerSegment 869652736 869718272 (17392371598813 / 20000) (86968432392711 / 100000) := by
  exact
    packedTile32768 869652736 869718272 13 3194 29489 30 _ _ (2058359 / 100000) (1029181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869718272 :
    ThetaLowerSegment 869718272 869783808 (86968432392711 / 100000) (86975076798159 / 100000) := by
  exact
    packedTile32768 869718272 869783808 13 3228 29490 30 _ _ (1029183 / 50000) (2058369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869783808 :
    ThetaLowerSegment 869783808 869849344 (86975076798159 / 100000) (86981643011219 / 100000) := by
  exact
    packedTile32768 869783808 869849344 13 3190 29492 30 _ _ (1029187 / 50000) (2058377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869849344 :
    ThetaLowerSegment 869849344 869914880 (86981643011219 / 100000) (17397655435281 / 20000) := by
  exact
    packedTile32768 869849344 869914880 13 3223 29493 30 _ _ (1029191 / 50000) (411677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869914880 :
    ThetaLowerSegment 869914880 869980416 (17397655435281 / 20000) (5437172697509 / 6250) := by
  exact
    packedTile32768 869914880 869980416 13 3151 29494 30 _ _ (2058389 / 100000) (257299 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell869980416 :
    ThetaLowerSegment 869980416 870045952 (5437172697509 / 6250) (87001393256881 / 100000) := by
  exact
    packedTile32768 869980416 870045952 13 3221 29495 30 _ _ (2058397 / 100000) (2573 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870045952 :
    ThetaLowerSegment 870045952 870111488 (87001393256881 / 100000) (87007836061401 / 100000) := by
  exact
    packedTile32768 870045952 870111488 13 3130 29496 30 _ _ (514601 / 25000) (2058407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870111488 :
    ThetaLowerSegment 870111488 870177024 (87007836061401 / 100000) (17402891594561 / 20000) := by
  exact
    packedTile32768 870111488 870177024 13 3217 29497 30 _ _ (514603 / 25000) (411683 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870177024 :
    ThetaLowerSegment 870177024 870242560 (17402891594561 / 20000) (2719407203271 / 3125) := by
  exact
    packedTile32768 870177024 870242560 13 3193 29498 30 _ _ (2058419 / 100000) (1029211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870242560 :
    ThetaLowerSegment 870242560 870308096 (2719407203271 / 3125) (87027566010397 / 100000) := by
  exact
    packedTile32768 870242560 870308096 13 3175 29499 30 _ _ (2058427 / 100000) (205843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870308096 :
    ThetaLowerSegment 870308096 870373632 (87027566010397 / 100000) (87034165349801 / 100000) := by
  exact
    packedTile32768 870308096 870373632 13 3206 29500 30 _ _ (1029217 / 50000) (2058437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870373632 :
    ThetaLowerSegment 870373632 870439168 (87034165349801 / 100000) (87040770890179 / 100000) := by
  exact
    packedTile32768 870373632 870439168 13 3209 29502 30 _ _ (1029221 / 50000) (411689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870439168 :
    ThetaLowerSegment 870439168 870504704 (87040770890179 / 100000) (87047267355223 / 100000) := by
  exact
    packedTile32768 870439168 870504704 13 3156 29503 30 _ _ (2058449 / 100000) (514613 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870504704 :
    ThetaLowerSegment 870504704 870570240 (87047267355223 / 100000) (87053829716139 / 100000) := by
  exact
    packedTile32768 870504704 870570240 13 3188 29504 30 _ _ (2058457 / 100000) (102923 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870570240 :
    ThetaLowerSegment 870570240 870635776 (87053829716139 / 100000) (87060427093259 / 100000) := by
  exact
    packedTile32768 870570240 870635776 13 3205 29505 30 _ _ (64327 / 3125) (2058467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870635776 :
    ThetaLowerSegment 870635776 870701312 (87060427093259 / 100000) (87066900987699 / 100000) := by
  exact
    packedTile32768 870635776 870701312 13 3145 29506 30 _ _ (257309 / 12500) (82339 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870701312 :
    ThetaLowerSegment 870701312 870766848 (87066900987699 / 100000) (87073508705289 / 100000) := by
  exact
    packedTile32768 870701312 870766848 13 3210 29507 30 _ _ (2058479 / 100000) (1029241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870766848 :
    ThetaLowerSegment 870766848 870832384 (87073508705289 / 100000) (87080095863689 / 100000) := by
  exact
    packedTile32768 870766848 870832384 13 3200 29508 30 _ _ (2058487 / 100000) (205849 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870832384 :
    ThetaLowerSegment 870832384 870897920 (87080095863689 / 100000) (21771644516111 / 25000) := by
  exact
    packedTile32768 870832384 870897920 13 3149 29509 30 _ _ (411699 / 20000) (1029249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870897920 :
    ThetaLowerSegment 870897920 870963456 (21771644516111 / 25000) (21773301610221 / 25000) := by
  exact
    packedTile32768 870897920 870963456 13 3220 29510 30 _ _ (1029251 / 50000) (411701 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell870963456 :
    ThetaLowerSegment 870963456 871028992 (21773301610221 / 25000) (21774905189511 / 25000) := by
  exact
    packedTile32768 870963456 871028992 13 3116 29512 30 _ _ (205851 / 10000) (2058513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871028992 :
    ThetaLowerSegment 871028992 871094528 (21774905189511 / 25000) (21776560237179 / 25000) := by
  exact
    packedTile32768 871028992 871094528 13 3216 29513 30 _ _ (2058517 / 100000) (51463 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871094528 :
    ThetaLowerSegment 871094528 871160064 (21776560237179 / 25000) (43556333831883 / 50000) := by
  exact
    packedTile32768 871094528 871160064 13 3122 29514 30 _ _ (82341 / 4000) (64329 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871160064 :
    ThetaLowerSegment 871160064 871225600 (43556333831883 / 50000) (43559577049049 / 50000) := by
  exact
    packedTile32768 871160064 871225600 13 3151 29515 30 _ _ (514633 / 25000) (411707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871225600 :
    ThetaLowerSegment 871225600 871291136 (43559577049049 / 50000) (43562875859399 / 50000) := by
  exact
    packedTile32768 871225600 871291136 13 3205 29516 30 _ _ (102927 / 5000) (2058543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871291136 :
    ThetaLowerSegment 871291136 871356672 (43562875859399 / 50000) (21783048742727 / 25000) := by
  exact
    packedTile32768 871291136 871356672 13 3130 29517 30 _ _ (2058547 / 100000) (41171 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871356672 :
    ThetaLowerSegment 871356672 871422208 (21783048742727 / 25000) (87138702063263 / 100000) := by
  exact
    packedTile32768 871356672 871422208 13 3161 29518 30 _ _ (411711 / 20000) (1029279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871422208 :
    ThetaLowerSegment 871422208 871487744 (87138702063263 / 100000) (17429045952673 / 20000) := by
  exact
    packedTile32768 871422208 871487744 13 3171 29519 30 _ _ (1029281 / 50000) (411713 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871487744 :
    ThetaLowerSegment 871487744 871553280 (17429045952673 / 20000) (697214422219 / 800) := by
  exact
    packedTile32768 871487744 871553280 13 3193 29520 30 _ _ (205857 / 10000) (2058573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871553280 :
    ThetaLowerSegment 871553280 871618816 (697214422219 / 800) (1743166775187 / 2000) := by
  exact
    packedTile32768 871553280 871618816 13 3175 29522 30 _ _ (2058577 / 100000) (102929 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871618816 :
    ThetaLowerSegment 871618816 871684352 (1743166775187 / 2000) (3486597460971 / 4000) := by
  exact
    packedTile32768 871618816 871684352 13 3205 29523 30 _ _ (411717 / 20000) (514647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871684352 :
    ThetaLowerSegment 871684352 871749888 (3486597460971 / 4000) (87171414913299 / 100000) := by
  exact
    packedTile32768 871684352 871749888 13 3147 29524 30 _ _ (64331 / 3125) (411719 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871749888 :
    ThetaLowerSegment 871749888 871815424 (87171414913299 / 100000) (87177915972099 / 100000) := by
  exact
    packedTile32768 871749888 871815424 13 3158 29525 30 _ _ (10293 / 500) (2058603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871815424 :
    ThetaLowerSegment 871815424 871880960 (87177915972099 / 100000) (43592322779191 / 50000) := by
  exact
    packedTile32768 871815424 871880960 13 3269 29526 30 _ _ (2058607 / 100000) (205861 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871880960 :
    ThetaLowerSegment 871880960 871946496 (43592322779191 / 50000) (43595591859811 / 50000) := by
  exact
    packedTile32768 871880960 871946496 13 3176 29527 30 _ _ (411723 / 20000) (1029309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell871946496 :
    ThetaLowerSegment 871946496 872012032 (43595591859811 / 50000) (21799453635271 / 25000) := by
  exact
    packedTile32768 871946496 872012032 13 3221 29528 30 _ _ (1029311 / 50000) (16469 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872012032 :
    ThetaLowerSegment 872012032 872077568 (21799453635271 / 25000) (43602167111147 / 50000) := by
  exact
    packedTile32768 872012032 872077568 13 3167 29529 30 _ _ (205863 / 10000) (2058633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872077568 :
    ThetaLowerSegment 872077568 872143104 (43602167111147 / 50000) (2725340407493 / 3125) := by
  exact
    packedTile32768 872077568 872143104 13 3186 29530 30 _ _ (2058637 / 100000) (25733 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872143104 :
    ThetaLowerSegment 872143104 872208640 (2725340407493 / 3125) (87217466293261 / 100000) := by
  exact
    packedTile32768 872143104 872208640 13 3193 29532 30 _ _ (411729 / 20000) (257331 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872208640 :
    ThetaLowerSegment 872208640 872274176 (87217466293261 / 100000) (87224152794957 / 100000) := by
  exact
    packedTile32768 872208640 872274176 13 3248 29533 30 _ _ (514663 / 25000) (411731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872274176 :
    ThetaLowerSegment 872274176 872339712 (87224152794957 / 100000) (87230557286217 / 100000) := by
  exact
    packedTile32768 872274176 872339712 13 3111 29534 30 _ _ (102933 / 5000) (2058663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872339712 :
    ThetaLowerSegment 872339712 872405248 (87230557286217 / 100000) (21809282652487 / 25000) := by
  exact
    packedTile32768 872339712 872405248 13 3193 29535 30 _ _ (2058667 / 100000) (205867 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872405248 :
    ThetaLowerSegment 872405248 872470784 (21809282652487 / 25000) (87243547499923 / 100000) := by
  exact
    packedTile32768 872405248 872470784 13 3117 29536 30 _ _ (82347 / 4000) (1029339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872470784 :
    ThetaLowerSegment 872470784 872536320 (87243547499923 / 100000) (87250015878767 / 100000) := by
  exact
    packedTile32768 872470784 872536320 13 3142 29537 30 _ _ (1029341 / 50000) (411737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872536320 :
    ThetaLowerSegment 872536320 872601856 (87250015878767 / 100000) (87256556336897 / 100000) := by
  exact
    packedTile32768 872536320 872601856 13 3177 29538 30 _ _ (205869 / 10000) (2058693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872601856 :
    ThetaLowerSegment 872601856 872667392 (87256556336897 / 100000) (2726971646871 / 3125) := by
  exact
    packedTile32768 872601856 872667392 13 3175 29539 30 _ _ (2058697 / 100000) (20587 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872667392 :
    ThetaLowerSegment 872667392 872732928 (2726971646871 / 3125) (87269781432417 / 100000) := by
  exact
    packedTile32768 872667392 872732928 13 3249 29540 30 _ _ (411741 / 20000) (514677 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872732928 :
    ThetaLowerSegment 872732928 872798464 (87269781432417 / 100000) (8727628902421 / 10000) := by
  exact
    packedTile32768 872732928 872798464 13 3161 29542 30 _ _ (2058713 / 100000) (514679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872798464 :
    ThetaLowerSegment 872798464 872864000 (8727628902421 / 10000) (8728288310437 / 10000) := by
  exact
    packedTile32768 872798464 872864000 13 3203 29543 30 _ _ (12867 / 625) (2058723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872864000 :
    ThetaLowerSegment 872864000 872929536 (8728288310437 / 10000) (8728957397037 / 10000) := by
  exact
    packedTile32768 872864000 872929536 13 3250 29544 30 _ _ (257341 / 12500) (2058731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872929536 :
    ThetaLowerSegment 872929536 872995072 (8728957397037 / 10000) (3491844253461 / 4000) := by
  exact
    packedTile32768 872929536 872995072 13 3173 29545 30 _ _ (411747 / 20000) (1029369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell872995072 :
    ThetaLowerSegment 872995072 873060608 (3491844253461 / 4000) (43651370832607 / 50000) := by
  exact
    packedTile32768 872995072 873060608 13 3223 29546 30 _ _ (2058743 / 100000) (1029373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873060608 :
    ThetaLowerSegment 873060608 873126144 (43651370832607 / 50000) (2728417517077 / 3125) := by
  exact
    packedTile32768 873060608 873126144 13 3215 29547 30 _ _ (1647 / 80) (2058753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873126144 :
    ThetaLowerSegment 873126144 873191680 (2728417517077 / 3125) (43657942375283 / 50000) := by
  exact
    packedTile32768 873126144 873191680 13 3169 29548 30 _ _ (1029379 / 50000) (2058761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873191680 :
    ThetaLowerSegment 873191680 873257216 (43657942375283 / 50000) (87322429564501 / 100000) := by
  exact
    packedTile32768 873191680 873257216 13 3179 29549 30 _ _ (411753 / 20000) (128673 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873257216 :
    ThetaLowerSegment 873257216 873322752 (87322429564501 / 100000) (87329038225831 / 100000) := by
  exact
    packedTile32768 873257216 873322752 13 3210 29550 30 _ _ (2058773 / 100000) (257347 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873322752 :
    ThetaLowerSegment 873322752 873339136 (87329038225831 / 100000) (87330753189571 / 100000) := by
  exact
    packedTile32768 873322752 873339136 11 833 29552 30 _ _ (102939 / 5000) (2058783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell873339136 :
    ThetaLowerSegment 873339136 873341184 (87330753189571 / 100000) (87330957008989 / 100000) := by
  exact
    packedTile32768 873339136 873341184 8 99 29552 30 _ _ (1029391 / 50000) (411757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_841341184_873341184 :
    ThetaLowerSegment 841341184 873341184 (42065498884063 / 50000) (87330957008989 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell841341184 cell841406720)
                    (ThetaLowerSegment.join cell841472256 cell841537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell841603328 cell841668864)
                    (ThetaLowerSegment.join cell841734400 cell841799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell841865472 cell841931008)
                    (ThetaLowerSegment.join cell841996544 cell842062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell842127616 cell842193152)
                    (ThetaLowerSegment.join cell842258688 cell842324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell842389760 cell842455296)
                    (ThetaLowerSegment.join cell842520832 cell842586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell842651904 cell842717440)
                    (ThetaLowerSegment.join cell842782976 cell842848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell842914048 cell842979584)
                    (ThetaLowerSegment.join cell843045120 cell843110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell843176192 cell843241728)
                    (ThetaLowerSegment.join cell843307264 cell843372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell843438336 cell843503872)
                    (ThetaLowerSegment.join cell843569408 cell843634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell843700480 cell843766016)
                    (ThetaLowerSegment.join cell843831552 cell843897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell843962624 cell844028160)
                    (ThetaLowerSegment.join cell844093696 cell844159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell844224768 cell844290304)
                    (ThetaLowerSegment.join cell844355840 cell844421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell844486912 cell844552448)
                    (ThetaLowerSegment.join cell844617984 cell844683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell844749056 cell844814592)
                    (ThetaLowerSegment.join cell844880128 cell844945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell845011200 cell845076736)
                    (ThetaLowerSegment.join cell845142272 cell845207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell845273344 cell845338880)
                    (ThetaLowerSegment.join cell845404416 cell845469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell845535488 cell845601024)
                    (ThetaLowerSegment.join cell845666560 cell845732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell845797632 cell845863168)
                    (ThetaLowerSegment.join cell845928704 cell845994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell846059776 cell846125312)
                    (ThetaLowerSegment.join cell846190848 cell846256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell846321920 cell846387456)
                    (ThetaLowerSegment.join cell846452992 cell846518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell846584064 cell846649600)
                    (ThetaLowerSegment.join cell846715136 cell846780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell846846208 cell846911744)
                    (ThetaLowerSegment.join cell846977280 cell847042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell847108352 cell847173888)
                    (ThetaLowerSegment.join cell847239424 cell847304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell847370496 cell847436032)
                    (ThetaLowerSegment.join cell847501568 cell847567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell847632640 cell847698176)
                    (ThetaLowerSegment.join cell847763712 cell847829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell847894784 cell847960320)
                    (ThetaLowerSegment.join cell848025856 cell848091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell848156928 cell848222464)
                    (ThetaLowerSegment.join cell848288000 cell848353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell848419072 cell848484608)
                    (ThetaLowerSegment.join cell848550144 cell848615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell848681216 cell848746752)
                    (ThetaLowerSegment.join cell848812288 cell848877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell848943360 cell849008896)
                    (ThetaLowerSegment.join cell849074432 cell849139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell849205504 cell849271040)
                    (ThetaLowerSegment.join cell849336576 cell849402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell849467648 cell849533184)
                    (ThetaLowerSegment.join cell849598720 cell849664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell849729792 cell849795328)
                    (ThetaLowerSegment.join cell849860864 cell849926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell849991936 cell850057472)
                    (ThetaLowerSegment.join cell850123008 cell850188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell850254080 cell850319616)
                    (ThetaLowerSegment.join cell850385152 cell850450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell850516224 cell850581760)
                    (ThetaLowerSegment.join cell850647296 cell850712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell850778368 cell850843904)
                    (ThetaLowerSegment.join cell850909440 cell850974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell851040512 cell851106048)
                    (ThetaLowerSegment.join cell851171584 cell851237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell851302656 cell851368192)
                    (ThetaLowerSegment.join cell851433728 cell851499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell851564800 cell851630336)
                    (ThetaLowerSegment.join cell851695872 cell851761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell851826944 cell851892480)
                    (ThetaLowerSegment.join cell851958016 cell852023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell852089088 cell852154624)
                    (ThetaLowerSegment.join cell852220160 cell852285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell852351232 cell852416768)
                    (ThetaLowerSegment.join cell852482304 cell852547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell852613376 cell852678912)
                    (ThetaLowerSegment.join cell852744448 cell852809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell852875520 cell852941056)
                    (ThetaLowerSegment.join cell853006592 cell853072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell853137664 cell853203200)
                    (ThetaLowerSegment.join cell853268736 cell853334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell853399808 cell853465344)
                    (ThetaLowerSegment.join cell853530880 cell853596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell853661952 cell853727488)
                    (ThetaLowerSegment.join cell853793024 cell853858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell853924096 cell853989632)
                    (ThetaLowerSegment.join cell854055168 cell854120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell854186240 cell854251776)
                    (ThetaLowerSegment.join cell854317312 cell854382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell854448384 cell854513920)
                    (ThetaLowerSegment.join cell854579456 cell854644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell854710528 cell854776064)
                    (ThetaLowerSegment.join cell854841600 cell854907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell854972672 cell855038208)
                    (ThetaLowerSegment.join cell855103744 cell855169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell855234816 cell855300352)
                    (ThetaLowerSegment.join cell855365888 cell855431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell855496960 cell855562496)
                    (ThetaLowerSegment.join cell855628032 cell855693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell855759104 cell855824640)
                    (ThetaLowerSegment.join cell855890176 cell855955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell856021248 cell856086784)
                    (ThetaLowerSegment.join cell856152320 cell856217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell856283392 cell856348928)
                    (ThetaLowerSegment.join cell856414464 cell856480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell856545536 cell856611072)
                    (ThetaLowerSegment.join cell856676608 cell856742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell856807680 cell856873216)
                    (ThetaLowerSegment.join cell856938752 cell857004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell857069824 cell857135360)
                    (ThetaLowerSegment.join cell857200896 cell857266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell857331968 cell857397504)
                    (ThetaLowerSegment.join cell857463040 cell857528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell857594112 cell857659648)
                    (ThetaLowerSegment.join cell857725184 cell857790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell857856256 cell857921792)
                    (ThetaLowerSegment.join cell857987328 cell858052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell858118400 cell858183936)
                    (ThetaLowerSegment.join cell858249472 cell858315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell858380544 cell858446080)
                    (ThetaLowerSegment.join cell858511616 cell858577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell858642688 cell858708224)
                    (ThetaLowerSegment.join cell858773760 cell858839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell858904832 cell858970368)
                    (ThetaLowerSegment.join cell859035904 cell859101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell859166976 cell859232512)
                    (ThetaLowerSegment.join cell859298048 cell859363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell859429120 cell859494656)
                    (ThetaLowerSegment.join cell859560192 cell859625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell859691264 cell859756800)
                    (ThetaLowerSegment.join cell859822336 cell859887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell859953408 cell860018944)
                    (ThetaLowerSegment.join cell860084480 cell860150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell860215552 cell860281088)
                    (ThetaLowerSegment.join cell860346624 cell860412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell860477696 cell860543232)
                    (ThetaLowerSegment.join cell860608768 cell860674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell860739840 cell860805376)
                    (ThetaLowerSegment.join cell860870912 cell860936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell861001984 cell861067520)
                    (ThetaLowerSegment.join cell861133056 cell861198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell861264128 cell861329664)
                    (ThetaLowerSegment.join cell861395200 cell861460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell861526272 cell861591808)
                    (ThetaLowerSegment.join cell861657344 cell861722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell861788416 cell861853952)
                    (ThetaLowerSegment.join cell861919488 cell861985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell862050560 cell862116096)
                    (ThetaLowerSegment.join cell862181632 cell862247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell862312704 cell862378240)
                    (ThetaLowerSegment.join cell862443776 cell862509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell862574848 cell862640384)
                    (ThetaLowerSegment.join cell862705920 cell862771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell862836992 cell862902528)
                    (ThetaLowerSegment.join cell862968064 cell863033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell863099136 cell863164672)
                    (ThetaLowerSegment.join cell863230208 cell863295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell863361280 cell863426816)
                    (ThetaLowerSegment.join cell863492352 cell863557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell863623424 cell863688960)
                    (ThetaLowerSegment.join cell863754496 cell863820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell863885568 cell863951104)
                    (ThetaLowerSegment.join cell864016640 cell864082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell864147712 cell864213248)
                    (ThetaLowerSegment.join cell864278784 cell864344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell864409856 cell864475392)
                    (ThetaLowerSegment.join cell864540928 cell864606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell864672000 cell864737536)
                    (ThetaLowerSegment.join cell864803072 cell864868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell864934144 cell864999680)
                    (ThetaLowerSegment.join cell865065216 cell865130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell865196288 cell865261824)
                    (ThetaLowerSegment.join cell865327360 cell865392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell865458432 cell865523968)
                    (ThetaLowerSegment.join cell865589504 cell865655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell865720576 cell865786112)
                    (ThetaLowerSegment.join cell865851648 cell865917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell865982720 cell866048256)
                    (ThetaLowerSegment.join cell866113792 cell866179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell866244864 cell866310400)
                    (ThetaLowerSegment.join cell866375936 cell866441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell866507008 cell866572544)
                    (ThetaLowerSegment.join cell866638080 cell866703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell866769152 cell866834688)
                    (ThetaLowerSegment.join cell866900224 cell866965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell867031296 cell867096832)
                    (ThetaLowerSegment.join cell867162368 cell867227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell867293440 cell867358976)
                    (ThetaLowerSegment.join cell867424512 cell867490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell867555584 cell867621120)
                    (ThetaLowerSegment.join cell867686656 cell867752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell867817728 cell867883264)
                    (ThetaLowerSegment.join cell867948800 cell868014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell868079872 cell868145408)
                    (ThetaLowerSegment.join cell868210944 cell868276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell868342016 cell868407552)
                    (ThetaLowerSegment.join cell868473088 cell868538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell868604160 cell868669696)
                    (ThetaLowerSegment.join cell868735232 cell868800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell868866304 cell868931840)
                    (ThetaLowerSegment.join cell868997376 cell869062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell869128448 cell869193984)
                    (ThetaLowerSegment.join cell869259520 cell869325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell869390592 cell869456128)
                    (ThetaLowerSegment.join cell869521664 cell869587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell869652736 cell869718272)
                    (ThetaLowerSegment.join cell869783808 cell869849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell869914880 cell869980416)
                    (ThetaLowerSegment.join cell870045952 cell870111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell870177024 cell870242560)
                    (ThetaLowerSegment.join cell870308096 cell870373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell870439168 cell870504704)
                    (ThetaLowerSegment.join cell870570240 cell870635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell870701312 cell870766848)
                    (ThetaLowerSegment.join cell870832384 cell870897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell870963456 cell871028992)
                    (ThetaLowerSegment.join cell871094528 cell871160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell871225600 cell871291136)
                    (ThetaLowerSegment.join cell871356672 cell871422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell871487744 cell871553280)
                    (ThetaLowerSegment.join cell871618816 cell871684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell871749888 cell871815424)
                    (ThetaLowerSegment.join cell871880960 cell871946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell872012032 cell872077568)
                    (ThetaLowerSegment.join cell872143104 cell872208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell872274176 cell872339712)
                    (ThetaLowerSegment.join cell872405248 cell872470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell872536320 cell872601856)
                    (ThetaLowerSegment.join cell872667392 cell872732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell872798464 cell872864000)
                  (ThetaLowerSegment.join cell872929536 cell872995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell873060608 cell873126144)
                  (ThetaLowerSegment.join cell873191680 cell873257216)))
              (ThetaLowerSegment.join cell873322752 cell873339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
