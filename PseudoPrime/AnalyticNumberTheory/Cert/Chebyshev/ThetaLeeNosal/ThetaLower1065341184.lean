/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 1065341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1033341184 :
    ThetaLowerSegment 1033341184 1033406720 (103330508404191 / 100000)
      (103337175247451 / 100000) := by
  exact
    packedTile32768 1033341184 1033406720 13 3212 32145 30 _ _ (415121 / 20000) (259451 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033406720 :
    ThetaLowerSegment 1033406720 1033472256 (103337175247451 / 100000)
      (103343759085543 / 100000) := by
  exact
    packedTile32768 1033406720 1033472256 13 3172 32146 30 _ _ (2075611 / 100000) (1037807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033472256 :
    ThetaLowerSegment 1033472256 1033537792 (103343759085543 / 100000)
      (103350307660333 / 100000) := by
  exact
    packedTile32768 1033472256 1033537792 13 3155 32147 30 _ _ (1037809 / 50000) (2075621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033537792 :
    ThetaLowerSegment 1033537792 1033603328 (103350307660333 / 100000)
      (103356746245981 / 100000) := by
  exact
    packedTile32768 1033537792 1033603328 13 3102 32148 30 _ _ (259453 / 12500) (2075627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033603328 :
    ThetaLowerSegment 1033603328 1033668864 (103356746245981 / 100000)
      (103363288631741 / 100000) := by
  exact
    packedTile32768 1033603328 1033668864 13 3152 32149 30 _ _ (207563 / 10000) (2075633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033668864 :
    ThetaLowerSegment 1033668864 1033734400 (103363288631741 / 100000)
      (51684891649957 / 50000) := by
  exact
    packedTile32768 1033668864 1033734400 13 3129 32150 30 _ _ (2075637 / 100000) (51891 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033734400 :
    ThetaLowerSegment 1033734400 1033799936 (51684891649957 / 50000)
      (103376431584443 / 100000) := by
  exact
    packedTile32768 1033734400 1033799936 13 3203 32151 30 _ _ (2075643 / 100000) (1037823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033799936 :
    ThetaLowerSegment 1033799936 1033865472 (103376431584443 / 100000)
      (103382982332687 / 100000) := by
  exact
    packedTile32768 1033799936 1033865472 13 3156 32152 30 _ _ (2075649 / 100000) (518913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033865472 :
    ThetaLowerSegment 1033865472 1033931008 (103382982332687 / 100000)
      (103389460455063 / 100000) := by
  exact
    packedTile32768 1033865472 1033931008 13 3121 32153 30 _ _ (259457 / 12500) (2075659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033931008 :
    ThetaLowerSegment 1033931008 1033996544 (103389460455063 / 100000)
      (103395892931601 / 100000) := by
  exact
    packedTile32768 1033931008 1033996544 13 3099 32154 30 _ _ (1037831 / 50000) (415133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1033996544 :
    ThetaLowerSegment 1033996544 1034062080 (103395892931601 / 100000)
      (103402481101833 / 100000) := by
  exact
    packedTile32768 1033996544 1034062080 13 3174 32155 30 _ _ (518917 / 25000) (2075671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034062080 :
    ThetaLowerSegment 1034062080 1034127616 (103402481101833 / 100000)
      (51704556441729 / 50000) := by
  exact
    packedTile32768 1034062080 1034127616 13 3195 32156 30 _ _ (83027 / 4000) (1037839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034127616 :
    ThetaLowerSegment 1034127616 1034193152 (51704556441729 / 50000)
      (103415736381529 / 100000) := by
  exact
    packedTile32768 1034127616 1034193152 13 3191 32157 30 _ _ (2075681 / 100000) (518921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034193152 :
    ThetaLowerSegment 1034193152 1034258688 (103415736381529 / 100000)
      (51711167495251 / 50000) := by
  exact
    packedTile32768 1034193152 1034258688 13 3179 32158 30 _ _ (2075687 / 100000) (207569 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034258688 :
    ThetaLowerSegment 1034258688 1034324224 (51711167495251 / 50000) (51714426334831 / 50000) := by
  exact
    packedTile32768 1034258688 1034324224 13 3140 32159 30 _ _ (1037847 / 50000) (2075697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034324224 :
    ThetaLowerSegment 1034324224 1034389760 (51714426334831 / 50000) (51717708016531 / 50000) := by
  exact
    packedTile32768 1034324224 1034389760 13 3162 32160 30 _ _ (20757 / 1000) (2075703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034389760 :
    ThetaLowerSegment 1034389760 1034455296 (51717708016531 / 50000) (25860507827021 / 25000) := by
  exact
    packedTile32768 1034389760 1034455296 13 3187 32161 30 _ _ (1037853 / 50000) (2075709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034455296 :
    ThetaLowerSegment 1034455296 1034520832 (25860507827021 / 25000) (51724284902017 / 50000) := by
  exact
    packedTile32768 1034455296 1034520832 13 3150 32162 30 _ _ (2075713 / 100000) (518929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034520832 :
    ThetaLowerSegment 1034520832 1034586368 (51724284902017 / 50000) (12931870896249 / 12500) := by
  exact
    packedTile32768 1034520832 1034586368 13 3082 32163 30 _ _ (2075719 / 100000) (1037861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034586368 :
    ThetaLowerSegment 1034586368 1034651904 (12931870896249 / 12500)
      (103461545142517 / 100000) := by
  exact
    packedTile32768 1034586368 1034651904 13 3169 32164 30 _ _ (83029 / 4000) (129733 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034651904 :
    ThetaLowerSegment 1034651904 1034717440 (103461545142517 / 100000)
      (103468220696629 / 100000) := by
  exact
    packedTile32768 1034651904 1034717440 13 3216 32166 30 _ _ (518933 / 25000) (415147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034717440 :
    ThetaLowerSegment 1034717440 1034782976 (103468220696629 / 100000) (4138985555141 / 4000) := by
  exact
    packedTile32768 1034717440 1034782976 13 3092 32167 30 _ _ (1037869 / 50000) (2075741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034782976 :
    ThetaLowerSegment 1034782976 1034848512 (4138985555141 / 4000) (103481279183581 / 100000) := by
  exact
    packedTile32768 1034782976 1034848512 13 3199 32168 30 _ _ (64867 / 3125) (2075747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034848512 :
    ThetaLowerSegment 1034848512 1034914048 (103481279183581 / 100000)
      (51743905785989 / 50000) := by
  exact
    packedTile32768 1034848512 1034914048 13 3147 32169 30 _ _ (2075751 / 100000) (1037877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034914048 :
    ThetaLowerSegment 1034914048 1034979584 (51743905785989 / 50000)
      (103494356433799 / 100000) := by
  exact
    packedTile32768 1034914048 1034979584 13 3153 32170 30 _ _ (2075757 / 100000) (25947 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1034979584 :
    ThetaLowerSegment 1034979584 1035045120 (103494356433799 / 100000)
      (103500936602509 / 100000) := by
  exact
    packedTile32768 1034979584 1035045120 13 3170 32171 30 _ _ (2075763 / 100000) (1037883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035045120 :
    ThetaLowerSegment 1035045120 1035110656 (103500936602509 / 100000)
      (103507520944949 / 100000) := by
  exact
    packedTile32768 1035045120 1035110656 13 3172 32172 30 _ _ (207577 / 10000) (2075773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035110656 :
    ThetaLowerSegment 1035110656 1035176192 (103507520944949 / 100000)
      (20702824797681 / 20000) := by
  exact
    packedTile32768 1035110656 1035176192 13 3181 32173 30 _ _ (64868 / 3125) (2075779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035176192 :
    ThetaLowerSegment 1035176192 1035241728 (20702824797681 / 20000)
      (103520635716539 / 100000) := by
  exact
    packedTile32768 1035176192 1035241728 13 3137 32174 30 _ _ (1037891 / 50000) (415157 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035241728 :
    ThetaLowerSegment 1035241728 1035307264 (103520635716539 / 100000)
      (103527282392917 / 100000) := by
  exact
    packedTile32768 1035241728 1035307264 13 3202 32175 30 _ _ (2075789 / 100000) (129737 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035307264 :
    ThetaLowerSegment 1035307264 1035372800 (103527282392917 / 100000)
      (51766857640811 / 50000) := by
  exact
    packedTile32768 1035307264 1035372800 13 3099 32176 30 _ _ (415159 / 20000) (1037899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035372800 :
    ThetaLowerSegment 1035372800 1035438336 (51766857640811 / 50000)
      (103540305949797 / 100000) := by
  exact
    packedTile32768 1035372800 1035438336 13 3175 32177 30 _ _ (2075801 / 100000) (518951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035438336 :
    ThetaLowerSegment 1035438336 1035503872 (103540305949797 / 100000)
      (103546990051557 / 100000) := by
  exact
    packedTile32768 1035438336 1035503872 13 3220 32178 30 _ _ (64869 / 3125) (2075811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035503872 :
    ThetaLowerSegment 1035503872 1035569408 (103546990051557 / 100000)
      (20710698300201 / 20000) := by
  exact
    packedTile32768 1035503872 1035569408 13 3132 32179 30 _ _ (1037907 / 50000) (2075817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035569408 :
    ThetaLowerSegment 1035569408 1035634944 (20710698300201 / 20000) (20711965795893 / 20000) := by
  exact
    packedTile32768 1035569408 1035634944 13 3053 32180 30 _ _ (103791 / 5000) (2075823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035634944 :
    ThetaLowerSegment 1035634944 1035700480 (20711965795893 / 20000) (1294579987149 / 1250) := by
  exact
    packedTile32768 1035634944 1035700480 13 3165 32181 30 _ _ (2075827 / 100000) (207583 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035700480 :
    ThetaLowerSegment 1035700480 1035766016 (1294579987149 / 1250) (51786497984597 / 50000) := by
  exact
    packedTile32768 1035700480 1035766016 13 3178 32182 30 _ _ (2075833 / 100000) (518959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035766016 :
    ThetaLowerSegment 1035766016 1035831552 (51786497984597 / 50000) (51789732141759 / 50000) := by
  exact
    packedTile32768 1035766016 1035831552 13 3116 32183 30 _ _ (2075839 / 100000) (1037921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035831552 :
    ThetaLowerSegment 1035831552 1035897088 (51789732141759 / 50000) (51793041040283 / 50000) := by
  exact
    packedTile32768 1035831552 1035897088 13 3188 32184 30 _ _ (1037923 / 50000) (2075849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035897088 :
    ThetaLowerSegment 1035897088 1035962624 (51793041040283 / 50000) (10359257326977 / 10000) := by
  exact
    packedTile32768 1035897088 1035962624 13 3127 32185 30 _ _ (518963 / 25000) (415171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1035962624 :
    ThetaLowerSegment 1035962624 1036028160 (10359257326977 / 10000) (25899800371091 / 25000) := by
  exact
    packedTile32768 1035962624 1036028160 13 3193 32186 30 _ _ (1037929 / 50000) (2075861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036028160 :
    ThetaLowerSegment 1036028160 1036093696 (25899800371091 / 25000)
      (103605696865949 / 100000) := by
  exact
    packedTile32768 1036028160 1036093696 13 3129 32187 30 _ _ (415173 / 20000) (518967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036093696 :
    ThetaLowerSegment 1036093696 1036159232 (103605696865949 / 100000) (6475764611483 / 6250) := by
  exact
    packedTile32768 1036093696 1036159232 13 3149 32188 30 _ _ (2075871 / 100000) (1037937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036159232 :
    ThetaLowerSegment 1036159232 1036224768 (6475764611483 / 6250) (12952345042627 / 12500) := by
  exact
    packedTile32768 1036159232 1036224768 13 3144 32189 30 _ _ (2075877 / 100000) (51897 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036224768 :
    ThetaLowerSegment 1036224768 1036290304 (12952345042627 / 12500)
      (103625359573073 / 100000) := by
  exact
    packedTile32768 1036224768 1036290304 13 3179 32190 30 _ _ (2075883 / 100000) (1037943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036290304 :
    ThetaLowerSegment 1036290304 1036355840 (103625359573073 / 100000)
      (103631855032883 / 100000) := by
  exact
    packedTile32768 1036290304 1036355840 13 3129 32191 30 _ _ (207589 / 10000) (2075893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036355840 :
    ThetaLowerSegment 1036355840 1036421376 (103631855032883 / 100000)
      (103638308993547 / 100000) := by
  exact
    packedTile32768 1036355840 1036421376 13 3109 32192 30 _ _ (259487 / 12500) (2075899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036421376 :
    ThetaLowerSegment 1036421376 1036486912 (103638308993547 / 100000)
      (20729008643927 / 20000) := by
  exact
    packedTile32768 1036421376 1036486912 13 3244 32193 30 _ _ (1037951 / 50000) (415181 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036486912 :
    ThetaLowerSegment 1036486912 1036552448 (20729008643927 / 20000) (51825866937171 / 50000) := by
  exact
    packedTile32768 1036486912 1036552448 13 3223 32194 30 _ _ (2075909 / 100000) (259489 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036552448 :
    ThetaLowerSegment 1036552448 1036617984 (51825866937171 / 50000) (51829180097511 / 50000) := by
  exact
    packedTile32768 1036552448 1036617984 13 3192 32195 30 _ _ (415183 / 20000) (1037959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036617984 :
    ThetaLowerSegment 1036617984 1036683520 (51829180097511 / 50000) (6479050500353 / 6250) := by
  exact
    packedTile32768 1036617984 1036683520 13 3106 32196 30 _ _ (2075921 / 100000) (518981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036683520 :
    ThetaLowerSegment 1036683520 1036749056 (6479050500353 / 6250) (3239731934758 / 3125) := by
  exact
    packedTile32768 1036683520 1036749056 13 3186 32197 30 _ _ (259491 / 12500) (2075931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036749056 :
    ThetaLowerSegment 1036749056 1036814592 (3239731934758 / 3125) (3239934338323 / 3125) := by
  exact
    packedTile32768 1036749056 1036814592 13 3120 32198 30 _ _ (1037967 / 50000) (2075937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036814592 :
    ThetaLowerSegment 1036814592 1036880128 (3239934338323 / 3125) (12960570324217 / 12500) := by
  exact
    packedTile32768 1036814592 1036880128 13 3210 32199 30 _ _ (103797 / 5000) (2075943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036880128 :
    ThetaLowerSegment 1036880128 1036945664 (12960570324217 / 12500)
      (103691216003871 / 100000) := by
  exact
    packedTile32768 1036880128 1036945664 13 3205 32200 30 _ _ (2075947 / 100000) (41519 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1036945664 :
    ThetaLowerSegment 1036945664 1037011200 (103691216003871 / 100000) (5184885998231 / 5000) := by
  exact
    packedTile32768 1036945664 1037011200 13 3133 32201 30 _ _ (2075953 / 100000) (518989 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037011200 :
    ThetaLowerSegment 1037011200 1037076736 (5184885998231 / 5000) (103704257159511 / 100000) := by
  exact
    packedTile32768 1037011200 1037076736 13 3149 32202 30 _ _ (2075959 / 100000) (1037981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037076736 :
    ThetaLowerSegment 1037076736 1037142272 (103704257159511 / 100000)
      (20742148495459 / 20000) := by
  exact
    packedTile32768 1037076736 1037142272 13 3124 32203 30 _ _ (1037983 / 50000) (2075969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037142272 :
    ThetaLowerSegment 1037142272 1037207808 (20742148495459 / 20000) (20743460509763 / 20000) := by
  exact
    packedTile32768 1037142272 1037207808 13 3160 32204 30 _ _ (518993 / 25000) (83039 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037207808 :
    ThetaLowerSegment 1037207808 1037273344 (20743460509763 / 20000)
      (103723825271691 / 100000) := by
  exact
    packedTile32768 1037207808 1037273344 13 3142 32205 30 _ _ (1037989 / 50000) (2075981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037273344 :
    ThetaLowerSegment 1037273344 1037338880 (103723825271691 / 100000)
      (103730310648831 / 100000) := by
  exact
    packedTile32768 1037273344 1037338880 13 3124 32206 30 _ _ (415197 / 20000) (518997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037338880 :
    ThetaLowerSegment 1037338880 1037404416 (103730310648831 / 100000)
      (103736820956607 / 100000) := by
  exact
    packedTile32768 1037338880 1037404416 13 3136 32207 30 _ _ (2075991 / 100000) (1037997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037404416 :
    ThetaLowerSegment 1037404416 1037469952 (103736820956607 / 100000)
      (25935845795781 / 25000) := by
  exact
    packedTile32768 1037404416 1037469952 13 3161 32208 30 _ _ (2075997 / 100000) (519 / 25)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037469952 :
    ThetaLowerSegment 1037469952 1037535488 (25935845795781 / 25000) (3242186443494 / 3125) := by
  exact
    packedTile32768 1037469952 1037535488 13 3171 32209 30 _ _ (519001 / 25000) (2076007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037535488 :
    ThetaLowerSegment 1037535488 1037601024 (3242186443494 / 3125) (51878276685769 / 50000) := by
  exact
    packedTile32768 1037535488 1037601024 13 3173 32210 30 _ _ (207601 / 10000) (2076013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037601024 :
    ThetaLowerSegment 1037601024 1037666560 (51878276685769 / 50000) (10376316963453 / 10000) := by
  exact
    packedTile32768 1037601024 1037666560 13 3187 32211 30 _ _ (129751 / 6250) (2076019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037666560 :
    ThetaLowerSegment 1037666560 1037732096 (10376316963453 / 10000) (51884819261099 / 50000) := by
  exact
    packedTile32768 1037666560 1037732096 13 3116 32212 30 _ _ (2076023 / 100000) (1038013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037732096 :
    ThetaLowerSegment 1037732096 1037797632 (51884819261099 / 50000) (12972037821911 / 12500) := by
  exact
    packedTile32768 1037732096 1037797632 13 3210 32213 30 _ _ (2076029 / 100000) (64876 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037797632 :
    ThetaLowerSegment 1037797632 1037863168 (12972037821911 / 12500) (51891371217929 / 50000) := by
  exact
    packedTile32768 1037797632 1037863168 13 3102 32214 30 _ _ (415207 / 20000) (1038019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037863168 :
    ThetaLowerSegment 1037863168 1037928704 (51891371217929 / 50000)
      (103789304801459 / 100000) := by
  exact
    packedTile32768 1037863168 1037928704 13 3161 32215 30 _ _ (2076041 / 100000) (519011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037928704 :
    ThetaLowerSegment 1037928704 1037994240 (103789304801459 / 100000)
      (103795840200563 / 100000) := by
  exact
    packedTile32768 1037928704 1037994240 13 3148 32216 30 _ _ (129753 / 6250) (2076051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1037994240 :
    ThetaLowerSegment 1037994240 1038059776 (103795840200563 / 100000)
      (103802466964931 / 100000) := by
  exact
    packedTile32768 1037994240 1038059776 13 3192 32217 30 _ _ (1038027 / 50000) (2076057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038059776 :
    ThetaLowerSegment 1038059776 1038125312 (103802466964931 / 100000)
      (103809164334491 / 100000) := by
  exact
    packedTile32768 1038059776 1038125312 13 3226 32218 30 _ _ (103803 / 5000) (2076063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038125312 :
    ThetaLowerSegment 1038125312 1038190848 (103809164334491 / 100000)
      (25953941037871 / 25000) := by
  exact
    packedTile32768 1038125312 1038190848 13 3179 32219 30 _ _ (2076067 / 100000) (207607 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038190848 :
    ThetaLowerSegment 1038190848 1038256384 (25953941037871 / 25000) (25955589439833 / 25000) := by
  exact
    packedTile32768 1038190848 1038256384 13 3176 32220 30 _ _ (2076073 / 100000) (519019 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038256384 :
    ThetaLowerSegment 1038256384 1038321920 (25955589439833 / 25000)
      (103828920245051 / 100000) := by
  exact
    packedTile32768 1038256384 1038321920 13 3161 32221 30 _ _ (2076079 / 100000) (1038041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038321920 :
    ThetaLowerSegment 1038321920 1038387456 (103828920245051 / 100000)
      (20767089491887 / 20000) := by
  exact
    packedTile32768 1038321920 1038387456 13 3144 32223 30 _ _ (1038043 / 50000) (2076089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038387456 :
    ThetaLowerSegment 1038387456 1038452992 (20767089491887 / 20000)
      (103841918638199 / 100000) := by
  exact
    packedTile32768 1038387456 1038452992 13 3117 32224 30 _ _ (519023 / 25000) (415219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038452992 :
    ThetaLowerSegment 1038452992 1038518528 (103841918638199 / 100000)
      (103848572532289 / 100000) := by
  exact
    packedTile32768 1038452992 1038518528 13 3205 32225 30 _ _ (1038049 / 50000) (2076101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038518528 :
    ThetaLowerSegment 1038518528 1038584064 (103848572532289 / 100000)
      (103855095654199 / 100000) := by
  exact
    packedTile32768 1038518528 1038584064 13 3142 32226 30 _ _ (415221 / 20000) (519027 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038584064 :
    ThetaLowerSegment 1038584064 1038649600 (103855095654199 / 100000)
      (103861577272741 / 100000) := by
  exact
    packedTile32768 1038584064 1038649600 13 3122 32227 30 _ _ (2076111 / 100000) (1038057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038649600 :
    ThetaLowerSegment 1038649600 1038715136 (103861577272741 / 100000)
      (51934082395991 / 50000) := by
  exact
    packedTile32768 1038649600 1038715136 13 3173 32228 30 _ _ (2076117 / 100000) (51903 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038715136 :
    ThetaLowerSegment 1038715136 1038780672 (51934082395991 / 50000) (10387476063793 / 10000) := by
  exact
    packedTile32768 1038715136 1038780672 13 3177 32229 30 _ _ (519031 / 25000) (2076127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038780672 :
    ThetaLowerSegment 1038780672 1038846208 (10387476063793 / 10000) (10388133781777 / 10000) := by
  exact
    packedTile32768 1038780672 1038846208 13 3168 32230 30 _ _ (207613 / 10000) (2076133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038846208 :
    ThetaLowerSegment 1038846208 1038911744 (10388133781777 / 10000) (51943967888989 / 50000) := by
  exact
    packedTile32768 1038846208 1038911744 13 3178 32231 30 _ _ (259517 / 12500) (2076139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038911744 :
    ThetaLowerSegment 1038911744 1038977280 (51943967888989 / 50000) (25973600740077 / 25000) := by
  exact
    packedTile32768 1038911744 1038977280 13 3115 32232 30 _ _ (1038071 / 50000) (415229 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1038977280 :
    ThetaLowerSegment 1038977280 1039042816 (25973600740077 / 25000)
      (103901027951767 / 100000) := by
  exact
    packedTile32768 1038977280 1039042816 13 3191 32233 30 _ _ (2076149 / 100000) (259519 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039042816 :
    ThetaLowerSegment 1039042816 1039108352 (103901027951767 / 100000)
      (103907567840017 / 100000) := by
  exact
    packedTile32768 1039042816 1039108352 13 3150 32234 30 _ _ (415231 / 20000) (1038079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039108352 :
    ThetaLowerSegment 1039108352 1039173888 (103907567840017 / 100000)
      (25978521227349 / 25000) := by
  exact
    packedTile32768 1039108352 1039173888 13 3139 32235 30 _ _ (2076161 / 100000) (519041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039173888 :
    ThetaLowerSegment 1039173888 1039239424 (25978521227349 / 25000) (25980173857077 / 25000) := by
  exact
    packedTile32768 1039173888 1039239424 13 3184 32236 30 _ _ (259521 / 12500) (2076171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039239424 :
    ThetaLowerSegment 1039239424 1039304960 (25980173857077 / 25000) (51963627030987 / 50000) := by
  exact
    packedTile32768 1039239424 1039304960 13 3159 32237 30 _ _ (1038087 / 50000) (2076177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039304960 :
    ThetaLowerSegment 1039304960 1039370496 (51963627030987 / 50000) (51966892862127 / 50000) := by
  exact
    packedTile32768 1039304960 1039370496 13 3146 32238 30 _ _ (103809 / 5000) (2076183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039370496 :
    ThetaLowerSegment 1039370496 1039436032 (51966892862127 / 50000)
      (103940398379849 / 100000) := by
  exact
    packedTile32768 1039370496 1039436032 13 3185 32239 30 _ _ (2076187 / 100000) (207619 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039436032 :
    ThetaLowerSegment 1039436032 1039501568 (103940398379849 / 100000)
      (51973389260469 / 50000) := by
  exact
    packedTile32768 1039436032 1039501568 13 3073 32240 30 _ _ (2076193 / 100000) (519049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039501568 :
    ThetaLowerSegment 1039501568 1039567104 (51973389260469 / 50000) (51976731940859 / 50000) := by
  exact
    packedTile32768 1039501568 1039567104 13 3220 32241 30 _ _ (2076199 / 100000) (1038101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039567104 :
    ThetaLowerSegment 1039567104 1039632640 (51976731940859 / 50000) (51979954212571 / 50000) := by
  exact
    packedTile32768 1039567104 1039632640 13 3104 32242 30 _ _ (1038103 / 50000) (2076209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039632640 :
    ThetaLowerSegment 1039632640 1039698176 (51979954212571 / 50000) (51983242932379 / 50000) := by
  exact
    packedTile32768 1039632640 1039698176 13 3168 32243 30 _ _ (519053 / 25000) (415243 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039698176 :
    ThetaLowerSegment 1039698176 1039763712 (51983242932379 / 50000) (51986531661691 / 50000) := by
  exact
    packedTile32768 1039698176 1039763712 13 3168 32244 30 _ _ (1038109 / 50000) (2076221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039763712 :
    ThetaLowerSegment 1039763712 1039829248 (51986531661691 / 50000) (51989864001211 / 50000) := by
  exact
    packedTile32768 1039763712 1039829248 13 3210 32245 30 _ _ (64882 / 3125) (2076227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039829248 :
    ThetaLowerSegment 1039829248 1039894784 (51989864001211 / 50000)
      (103986415542473 / 100000) := by
  exact
    packedTile32768 1039829248 1039894784 13 3221 32246 30 _ _ (2076231 / 100000) (1038117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039894784 :
    ThetaLowerSegment 1039894784 1039960320 (103986415542473 / 100000)
      (25998231136367 / 25000) := by
  exact
    packedTile32768 1039894784 1039960320 13 3135 32247 30 _ _ (2076237 / 100000) (25953 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1039960320 :
    ThetaLowerSegment 1039960320 1040025856 (25998231136367 / 25000) (51999773880319 / 50000) := by
  exact
    packedTile32768 1039960320 1040025856 13 3190 32248 30 _ _ (2076243 / 100000) (1038123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040025856 :
    ThetaLowerSegment 1040025856 1040091392 (51999773880319 / 50000) (52003041897819 / 50000) := by
  exact
    packedTile32768 1040025856 1040091392 13 3148 32249 30 _ _ (1661 / 80) (2076253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040091392 :
    ThetaLowerSegment 1040091392 1040156928 (52003041897819 / 50000) (52006313039147 / 50000) := by
  exact
    packedTile32768 1040091392 1040156928 13 3151 32250 30 _ _ (64883 / 3125) (2076259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040156928 :
    ThetaLowerSegment 1040156928 1040222464 (52006313039147 / 50000) (26004815971977 / 25000) := by
  exact
    packedTile32768 1040156928 1040222464 13 3197 32251 30 _ _ (1038131 / 50000) (415253 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040222464 :
    ThetaLowerSegment 1040222464 1040353536 (26004815971977 / 25000) (20806515800201 / 20000) := by
  exact
    packedTile32768 1040222464 1040353536 14 6413 32252 30 _ _ (2076269 / 100000) (129767 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040353536 :
    ThetaLowerSegment 1040353536 1040484608 (20806515800201 / 20000) (20809094541203 / 20000) := by
  exact
    packedTile32768 1040353536 1040484608 14 6210 32254 30 _ _ (2076281 / 100000) (519071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040484608 :
    ThetaLowerSegment 1040484608 1040615680 (20809094541203 / 20000) (20811708595349 / 20000) := by
  exact
    packedTile32768 1040484608 1040615680 14 6295 32256 30 _ _ (1038147 / 50000) (2076297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040615680 :
    ThetaLowerSegment 1040615680 1040681216 (20811708595349 / 20000)
      (104065006517323 / 100000) := by
  exact
    packedTile32768 1040615680 1040681216 13 3113 32258 30 _ _ (1038153 / 50000) (2076309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040681216 :
    ThetaLowerSegment 1040681216 1040746752 (104065006517323 / 100000)
      (52035795252923 / 50000) := by
  exact
    packedTile32768 1040681216 1040746752 13 3171 32259 30 _ _ (2076313 / 100000) (519079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040746752 :
    ThetaLowerSegment 1040746752 1040812288 (52035795252923 / 50000)
      (104078170360757 / 100000) := by
  exact
    packedTile32768 1040746752 1040812288 13 3169 32260 30 _ _ (2076319 / 100000) (1038161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040812288 :
    ThetaLowerSegment 1040812288 1040877824 (104078170360757 / 100000)
      (104084777226907 / 100000) := by
  exact
    packedTile32768 1040812288 1040877824 13 3182 32261 30 _ _ (83053 / 4000) (259541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1040877824 :
    ThetaLowerSegment 1040877824 1041008896 (104084777226907 / 100000) (4163914241687 / 4000) := by
  exact
    packedTile32768 1040877824 1041008896 14 6299 32262 30 _ _ (519083 / 25000) (415267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041008896 :
    ThetaLowerSegment 1041008896 1041074432 (4163914241687 / 4000) (104104346693519 / 100000) := by
  exact
    packedTile32768 1041008896 1041074432 13 3126 32264 30 _ _ (259543 / 12500) (2076347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041074432 :
    ThetaLowerSegment 1041074432 1041139968 (104104346693519 / 100000)
      (104110887196019 / 100000) := by
  exact
    packedTile32768 1041074432 1041139968 13 3150 32265 30 _ _ (41527 / 2000) (2076353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041139968 :
    ThetaLowerSegment 1041139968 1041205504 (104110887196019 / 100000)
      (104117328055433 / 100000) := by
  exact
    packedTile32768 1041139968 1041205504 13 3102 32266 30 _ _ (2076357 / 100000) (51909 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041205504 :
    ThetaLowerSegment 1041205504 1041271040 (104117328055433 / 100000)
      (104123947500677 / 100000) := by
  exact
    packedTile32768 1041205504 1041271040 13 3188 32267 30 _ _ (2076363 / 100000) (1038183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041271040 :
    ThetaLowerSegment 1041271040 1041336576 (104123947500677 / 100000)
      (52065238840591 / 50000) := by
  exact
    packedTile32768 1041271040 1041336576 13 3145 32268 30 _ _ (2076369 / 100000) (519093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041336576 :
    ThetaLowerSegment 1041336576 1041402112 (52065238840591 / 50000) (52068494598159 / 50000) := by
  exact
    packedTile32768 1041336576 1041402112 13 3136 32269 30 _ _ (259547 / 12500) (2076379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041402112 :
    ThetaLowerSegment 1041402112 1041467648 (52068494598159 / 50000) (2082873752093 / 2000) := by
  exact
    packedTile32768 1041402112 1041467648 13 3226 32270 30 _ _ (1038191 / 50000) (415277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041467648 :
    ThetaLowerSegment 1041467648 1041533184 (2082873752093 / 2000) (52075122418977 / 50000) := by
  exact
    packedTile32768 1041467648 1041533184 13 3158 32271 30 _ _ (519097 / 25000) (2076391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041533184 :
    ThetaLowerSegment 1041533184 1041598720 (52075122418977 / 50000) (13019602597219 / 12500) := by
  exact
    packedTile32768 1041533184 1041598720 13 3167 32272 30 _ _ (1038197 / 50000) (2076397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041598720 :
    ThetaLowerSegment 1041598720 1041664256 (13019602597219 / 12500) (52081755470887 / 50000) := by
  exact
    packedTile32768 1041598720 1041664256 13 3222 32273 30 _ _ (2076401 / 100000) (519101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041664256 :
    ThetaLowerSegment 1041664256 1041795328 (52081755470887 / 50000)
      (104176698202631 / 100000) := by
  exact
    packedTile32768 1041664256 1041795328 14 6351 32274 30 _ _ (2076407 / 100000) (207641 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041795328 :
    ThetaLowerSegment 1041795328 1041926400 (104176698202631 / 100000)
      (104189871011111 / 100000) := by
  exact
    packedTile32768 1041795328 1041926400 14 6344 32276 30 _ _ (103821 / 5000) (2076423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1041926400 :
    ThetaLowerSegment 1041926400 1042057472 (104189871011111 / 100000)
      (104202844558247 / 100000) := by
  exact
    packedTile32768 1041926400 1042057472 14 6248 32278 30 _ _ (129777 / 6250) (415287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1042057472 :
    ThetaLowerSegment 1042057472 1042188544 (104202844558247 / 100000)
      (104215851409727 / 100000) := by
  exact
    packedTile32768 1042057472 1042188544 14 6264 32280 30 _ _ (415289 / 20000) (64889 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1042188544 :
    ThetaLowerSegment 1042188544 1042319616 (104215851409727 / 100000)
      (104228928935913 / 100000) := by
  exact
    packedTile32768 1042188544 1042319616 14 6298 32282 30 _ _ (2076457 / 100000) (103823 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1042319616 :
    ThetaLowerSegment 1042319616 1042450688 (104228928935913 / 100000)
      (104242164355693 / 100000) := by
  exact
    packedTile32768 1042319616 1042450688 14 6374 32284 30 _ _ (207647 / 10000) (2076473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1042450688 :
    ThetaLowerSegment 1042450688 1042581760 (104242164355693 / 100000)
      (52127700967409 / 50000) := by
  exact
    packedTile32768 1042450688 1042581760 14 6375 32287 30 _ _ (2076483 / 100000) (1038243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1042581760 :
    ThetaLowerSegment 1042581760 1042712832 (52127700967409 / 50000) (6516791401993 / 6250) := by
  exact
    packedTile32768 1042581760 1042712832 14 6386 32289 30 _ _ (415299 / 20000) (1038249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1042712832 :
    ThetaLowerSegment 1042712832 1042843904 (6516791401993 / 6250) (26070443894977 / 25000) := by
  exact
    packedTile32768 1042712832 1042843904 14 6315 32291 30 _ _ (519127 / 25000) (2076511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1042843904 :
    ThetaLowerSegment 1042843904 1042974976 (26070443894977 / 25000) (26073688976607 / 25000) := by
  exact
    packedTile32768 1042843904 1042974976 14 6251 32293 30 _ _ (51913 / 2500) (2076523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1042974976 :
    ThetaLowerSegment 1042974976 1043106048 (26073688976607 / 25000) (20861567197559 / 20000) := by
  exact
    packedTile32768 1042974976 1043106048 14 6299 32295 30 _ _ (2076533 / 100000) (259567 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1043106048 :
    ThetaLowerSegment 1043106048 1043237120 (20861567197559 / 20000) (20864180321787 / 20000) := by
  exact
    packedTile32768 1043106048 1043237120 14 6292 32297 30 _ _ (415309 / 20000) (519137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1043237120 :
    ThetaLowerSegment 1043237120 1043368192 (20864180321787 / 20000)
      (104333832335601 / 100000) := by
  exact
    packedTile32768 1043237120 1043368192 14 6227 32299 30 _ _ (1038279 / 50000) (2076561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1043368192 :
    ThetaLowerSegment 1043368192 1043499264 (104333832335601 / 100000)
      (104347049703651 / 100000) := by
  exact
    packedTile32768 1043368192 1043499264 14 6365 32301 30 _ _ (207657 / 10000) (2076573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1043499264 :
    ThetaLowerSegment 1043499264 1043630336 (104347049703651 / 100000)
      (52180129424057 / 50000) := by
  exact
    packedTile32768 1043499264 1043630336 14 6361 32303 30 _ _ (2076583 / 100000) (1038293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1043630336 :
    ThetaLowerSegment 1043630336 1043761408 (52180129424057 / 50000) (10437338501143 / 10000) := by
  exact
    packedTile32768 1043630336 1043761408 14 6321 32305 30 _ _ (519149 / 25000) (2076599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1043761408 :
    ThetaLowerSegment 1043761408 1043892480 (10437338501143 / 10000) (10438658185527 / 10000) := by
  exact
    packedTile32768 1043761408 1043892480 14 6355 32307 30 _ _ (64894 / 3125) (2076611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1043892480 :
    ThetaLowerSegment 1043892480 1044023552 (10438658185527 / 10000)
      (104399704023369 / 100000) := by
  exact
    packedTile32768 1043892480 1044023552 14 6319 32309 30 _ _ (2076621 / 100000) (129789 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1044023552 :
    ThetaLowerSegment 1044023552 1044154624 (104399704023369 / 100000)
      (104412670519821 / 100000) := by
  exact
    packedTile32768 1044023552 1044154624 14 6244 32311 30 _ _ (2076633 / 100000) (519159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1044154624 :
    ThetaLowerSegment 1044154624 1044285696 (104412670519821 / 100000)
      (20885146109303 / 20000) := by
  exact
    packedTile32768 1044154624 1044285696 14 6289 32313 30 _ _ (1038323 / 50000) (2076649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1044285696 :
    ThetaLowerSegment 1044285696 1044416768 (20885146109303 / 20000)
      (104438809338599 / 100000) := by
  exact
    packedTile32768 1044285696 1044416768 14 6298 32315 30 _ _ (1038329 / 50000) (2076661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1044416768 :
    ThetaLowerSegment 1044416768 1044547840 (104438809338599 / 100000)
      (13056483171147 / 12500) := by
  exact
    packedTile32768 1044416768 1044547840 14 6287 32317 30 _ _ (2076671 / 100000) (1038337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1044547840 :
    ThetaLowerSegment 1044547840 1044678912 (13056483171147 / 12500)
      (104465012849249 / 100000) := by
  exact
    packedTile32768 1044547840 1044678912 14 6331 32319 30 _ _ (2076683 / 100000) (1038343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1044678912 :
    ThetaLowerSegment 1044678912 1044809984 (104465012849249 / 100000)
      (104478131337881 / 100000) := by
  exact
    packedTile32768 1044678912 1044809984 14 6317 32321 30 _ _ (259587 / 12500) (2076699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1044809984 :
    ThetaLowerSegment 1044809984 1044941056 (104478131337881 / 100000)
      (52245583420137 / 50000) := by
  exact
    packedTile32768 1044809984 1044941056 14 6277 32323 30 _ _ (2076709 / 100000) (259589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1044941056 :
    ThetaLowerSegment 1044941056 1045072128 (52245583420137 / 50000) (20900829684649 / 20000) := by
  exact
    packedTile32768 1044941056 1045072128 14 6251 32325 30 _ _ (2076721 / 100000) (519181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045072128 :
    ThetaLowerSegment 1045072128 1045137664 (20900829684649 / 20000)
      (104510663137803 / 100000) := by
  exact
    packedTile32768 1045072128 1045137664 13 3137 32327 30 _ _ (1038367 / 50000) (2076737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045137664 :
    ThetaLowerSegment 1045137664 1045203200 (104510663137803 / 100000)
      (104517252633823 / 100000) := by
  exact
    packedTile32768 1045137664 1045203200 13 3173 32328 30 _ _ (103837 / 5000) (2076743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045203200 :
    ThetaLowerSegment 1045203200 1045268736 (104517252633823 / 100000)
      (104523636551027 / 100000) := by
  exact
    packedTile32768 1045203200 1045268736 13 3074 32329 30 _ _ (1038373 / 50000) (2076749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045268736 :
    ThetaLowerSegment 1045268736 1045334272 (104523636551027 / 100000)
      (104530190780339 / 100000) := by
  exact
    packedTile32768 1045268736 1045334272 13 3156 32330 30 _ _ (129797 / 6250) (415351 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045334272 :
    ThetaLowerSegment 1045334272 1045399808 (104530190780339 / 100000)
      (104536861330247 / 100000) := by
  exact
    packedTile32768 1045334272 1045399808 13 3212 32331 30 _ _ (2076759 / 100000) (1038381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045399808 :
    ThetaLowerSegment 1045399808 1045465344 (104536861330247 / 100000)
      (104543415600587 / 100000) := by
  exact
    packedTile32768 1045399808 1045465344 13 3156 32332 30 _ _ (415353 / 20000) (64899 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045465344 :
    ThetaLowerSegment 1045465344 1045530880 (104543415600587 / 100000) (6534369353969 / 6250) := by
  exact
    packedTile32768 1045465344 1045530880 13 3127 32333 30 _ _ (2076771 / 100000) (1038387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045530880 :
    ThetaLowerSegment 1045530880 1045596416 (6534369353969 / 6250) (52278226795491 / 50000) := by
  exact
    packedTile32768 1045530880 1045596416 13 3151 32334 30 _ _ (1038389 / 50000) (2076781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045596416 :
    ThetaLowerSegment 1045596416 1045661952 (52278226795491 / 50000) (10456296846239 / 10000) := by
  exact
    packedTile32768 1045596416 1045661952 13 3137 32335 30 _ _ (129799 / 6250) (2076787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045661952 :
    ThetaLowerSegment 1045661952 1045727488 (10456296846239 / 10000) (10456954773311 / 10000) := by
  exact
    packedTile32768 1045661952 1045727488 13 3168 32336 30 _ _ (207679 / 10000) (2076793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045727488 :
    ThetaLowerSegment 1045727488 1045793024 (10456954773311 / 10000) (52288083240981 / 50000) := by
  exact
    packedTile32768 1045727488 1045793024 13 3187 32337 30 _ _ (519199 / 25000) (2076799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045793024 :
    ThetaLowerSegment 1045793024 1045858560 (52288083240981 / 50000)
      (104582598340853 / 100000) := by
  exact
    packedTile32768 1045793024 1045858560 13 3097 32338 30 _ _ (2076803 / 100000) (1038403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045858560 :
    ThetaLowerSegment 1045858560 1045924096 (104582598340853 / 100000)
      (52294598181523 / 50000) := by
  exact
    packedTile32768 1045858560 1045924096 13 3177 32339 30 _ _ (2076809 / 100000) (519203 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045924096 :
    ThetaLowerSegment 1045924096 1045989632 (52294598181523 / 50000) (3268618380433 / 3125) := by
  exact
    packedTile32768 1045924096 1045989632 13 3174 32340 30 _ _ (415363 / 20000) (1038409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1045989632 :
    ThetaLowerSegment 1045989632 1046055168 (3268618380433 / 3125) (104602394541457 / 100000) := by
  exact
    packedTile32768 1045989632 1046055168 13 3181 32341 30 _ _ (2076821 / 100000) (259603 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046055168 :
    ThetaLowerSegment 1046055168 1046120704 (104602394541457 / 100000)
      (104609036237401 / 100000) := by
  exact
    packedTile32768 1046055168 1046120704 13 3198 32342 30 _ _ (519207 / 25000) (2076831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046120704 :
    ThetaLowerSegment 1046120704 1046251776 (104609036237401 / 100000)
      (104622068370751 / 100000) := by
  exact
    packedTile32768 1046120704 1046251776 14 6275 32343 30 _ _ (1038417 / 50000) (2076837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046251776 :
    ThetaLowerSegment 1046251776 1046317312 (104622068370751 / 100000)
      (104628662356801 / 100000) := by
  exact
    packedTile32768 1046251776 1046317312 13 3175 32345 30 _ _ (1038423 / 50000) (2076849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046317312 :
    ThetaLowerSegment 1046317312 1046382848 (104628662356801 / 100000)
      (104635258441929 / 100000) := by
  exact
    packedTile32768 1046317312 1046382848 13 3176 32346 30 _ _ (2076853 / 100000) (259607 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046382848 :
    ThetaLowerSegment 1046382848 1046513920 (104635258441929 / 100000)
      (52324145366077 / 50000) := by
  exact
    packedTile32768 1046382848 1046513920 14 6275 32347 30 _ _ (2076859 / 100000) (1038431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046513920 :
    ThetaLowerSegment 1046513920 1046579456 (52324145366077 / 50000) (10465493256881 / 10000) := by
  exact
    packedTile32768 1046513920 1046579456 13 3198 32349 30 _ _ (259609 / 12500) (3323 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046579456 :
    ThetaLowerSegment 1046579456 1046710528 (10465493256881 / 10000) (26166985013931 / 25000) := by
  exact
    packedTile32768 1046579456 1046710528 14 6263 32350 30 _ _ (1038439 / 50000) (2076881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046710528 :
    ThetaLowerSegment 1046710528 1046776064 (26166985013931 / 25000) (13084314436183 / 12500) := by
  exact
    packedTile32768 1046710528 1046776064 13 3166 32352 30 _ _ (207689 / 10000) (2076893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046776064 :
    ThetaLowerSegment 1046776064 1046841600 (13084314436183 / 12500)
      (104681072253293 / 100000) := by
  exact
    packedTile32768 1046776064 1046841600 13 3157 32353 30 _ _ (2076897 / 100000) (20769 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046841600 :
    ThetaLowerSegment 1046841600 1046907136 (104681072253293 / 100000) (5234378544139 / 5000) := by
  exact
    packedTile32768 1046841600 1046907136 13 3129 32354 30 _ _ (2076903 / 100000) (1038453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046907136 :
    ThetaLowerSegment 1046907136 1046972672 (5234378544139 / 5000) (2617350232517 / 2500) := by
  exact
    packedTile32768 1046907136 1046972672 13 3100 32355 30 _ _ (2076909 / 100000) (129807 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1046972672 :
    ThetaLowerSegment 1046972672 1047038208 (2617350232517 / 2500) (26175168011 / 25) := by
  exact
    packedTile32768 1046972672 1047038208 13 3208 32356 30 _ _ (415383 / 20000) (1038459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047038208 :
    ThetaLowerSegment 1047038208 1047103744 (26175168011 / 25) (10470722473291 / 10000) := by
  exact
    packedTile32768 1047038208 1047103744 13 3155 32357 30 _ _ (1038461 / 50000) (83077 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047103744 :
    ThetaLowerSegment 1047103744 1047169280 (10470722473291 / 10000) (10471373590219 / 10000) := by
  exact
    packedTile32768 1047103744 1047169280 13 3135 32358 30 _ _ (64904 / 3125) (2076931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047169280 :
    ThetaLowerSegment 1047169280 1047234816 (10471373590219 / 10000) (52360058121719 / 50000) := by
  exact
    packedTile32768 1047169280 1047234816 13 3072 32359 30 _ _ (1038467 / 50000) (2076937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047234816 :
    ThetaLowerSegment 1047234816 1047300352 (52360058121719 / 50000) (52363318917519 / 50000) := by
  exact
    packedTile32768 1047234816 1047300352 13 3140 32361 30 _ _ (103847 / 5000) (2076943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047300352 :
    ThetaLowerSegment 1047300352 1047365888 (52363318917519 / 50000)
      (104733215526187 / 100000) := by
  exact
    packedTile32768 1047300352 1047365888 13 3167 32362 30 _ _ (2076947 / 100000) (41539 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047365888 :
    ThetaLowerSegment 1047365888 1047431424 (104733215526187 / 100000) (3273122562732 / 3125) := by
  exact
    packedTile32768 1047365888 1047431424 13 3229 32363 30 _ _ (2076953 / 100000) (519239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047431424 :
    ThetaLowerSegment 1047431424 1047496960 (3273122562732 / 3125) (26186590145081 / 25000) := by
  exact
    packedTile32768 1047431424 1047496960 13 3100 32364 30 _ _ (2076959 / 100000) (1038481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047496960 :
    ThetaLowerSegment 1047496960 1047562496 (26186590145081 / 25000) (52376468125757 / 50000) := by
  exact
    packedTile32768 1047496960 1047562496 13 3166 32365 30 _ _ (415393 / 20000) (259621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047562496 :
    ThetaLowerSegment 1047562496 1047628032 (52376468125757 / 50000) (52379691586301 / 50000) := by
  exact
    packedTile32768 1047562496 1047628032 13 3104 32366 30 _ _ (519243 / 25000) (83079 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047628032 :
    ThetaLowerSegment 1047628032 1047693568 (52379691586301 / 50000) (52382929595003 / 50000) := by
  exact
    packedTile32768 1047628032 1047693568 13 3118 32367 30 _ _ (1038489 / 50000) (2076981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047693568 :
    ThetaLowerSegment 1047693568 1047759104 (52382929595003 / 50000) (52386256923371 / 50000) := by
  exact
    packedTile32768 1047693568 1047759104 13 3204 32368 30 _ _ (259623 / 12500) (2076987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047759104 :
    ThetaLowerSegment 1047759104 1047824640 (52386256923371 / 50000) (3274345316696 / 3125) := by
  exact
    packedTile32768 1047759104 1047824640 13 3147 32369 30 _ _ (207699 / 10000) (2076993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047824640 :
    ThetaLowerSegment 1047824640 1047890176 (3274345316696 / 3125) (52392775567441 / 50000) := by
  exact
    packedTile32768 1047824640 1047890176 13 3130 32370 30 _ _ (2076997 / 100000) (2077 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047890176 :
    ThetaLowerSegment 1047890176 1047955712 (52392775567441 / 50000) (20958406692249 / 20000) := by
  exact
    packedTile32768 1047890176 1047955712 13 3121 32371 30 _ _ (2077003 / 100000) (1038503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1047955712 :
    ThetaLowerSegment 1047955712 1048021248 (20958406692249 / 20000) (26199652837187 / 25000) := by
  exact
    packedTile32768 1047955712 1048021248 13 3167 32372 30 _ _ (2077009 / 100000) (519253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048021248 :
    ThetaLowerSegment 1048021248 1048086784 (26199652837187 / 25000) (6550323939013 / 6250) := by
  exact
    packedTile32768 1048021248 1048086784 13 3164 32373 30 _ _ (415403 / 20000) (1038509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048086784 :
    ThetaLowerSegment 1048086784 1048152320 (6550323939013 / 6250) (419246993963 / 400) := by
  exact
    packedTile32768 1048086784 1048152320 13 3161 32374 30 _ _ (1038511 / 50000) (83081 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048152320 :
    ThetaLowerSegment 1048152320 1048217856 (419246993963 / 400) (52409191259091 / 50000) := by
  exact
    packedTile32768 1048152320 1048217856 13 3194 32375 30 _ _ (519257 / 25000) (2077031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048217856 :
    ThetaLowerSegment 1048217856 1048283392 (52409191259091 / 50000) (52412489589083 / 50000) := by
  exact
    packedTile32768 1048217856 1048283392 13 3176 32376 30 _ _ (1038517 / 50000) (2077037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048283392 :
    ThetaLowerSegment 1048283392 1048348928 (52412489589083 / 50000) (52415765081163 / 50000) := by
  exact
    packedTile32768 1048283392 1048348928 13 3154 32377 30 _ _ (25963 / 1250) (2077043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048348928 :
    ThetaLowerSegment 1048348928 1048414464 (52415765081163 / 50000)
      (104837979393261 / 100000) := by
  exact
    packedTile32768 1048348928 1048414464 13 3105 32378 30 _ _ (2077047 / 100000) (41541 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048414464 :
    ThetaLowerSegment 1048414464 1048480000 (104837979393261 / 100000)
      (26211112353339 / 25000) := by
  exact
    packedTile32768 1048414464 1048480000 13 3115 32379 30 _ _ (2077053 / 100000) (64908 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048480000 :
    ThetaLowerSegment 1048480000 1048545536 (26211112353339 / 25000)
      (104851010842737 / 100000) := by
  exact
    packedTile32768 1048480000 1048545536 13 3159 32380 30 _ _ (2077059 / 100000) (1038531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048545536 :
    ThetaLowerSegment 1048545536 1048611072 (104851010842737 / 100000)
      (52428796530861 / 50000) := by
  exact
    packedTile32768 1048545536 1048611072 13 3169 32381 30 _ _ (415413 / 20000) (519267 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048611072 :
    ThetaLowerSegment 1048611072 1048676608 (52428796530861 / 50000) (52432081420229 / 50000) := by
  exact
    packedTile32768 1048611072 1048676608 13 3163 32382 30 _ _ (129817 / 6250) (83083 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048676608 :
    ThetaLowerSegment 1048676608 1048742144 (52432081420229 / 50000) (52435340355611 / 50000) := by
  exact
    packedTile32768 1048676608 1048742144 13 3138 32383 30 _ _ (1038539 / 50000) (2077081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048742144 :
    ThetaLowerSegment 1048742144 1048807680 (52435340355611 / 50000) (10487713421121 / 10000) := by
  exact
    packedTile32768 1048742144 1048807680 13 3107 32384 30 _ _ (519271 / 25000) (2077087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048807680 :
    ThetaLowerSegment 1048807680 1048873216 (10487713421121 / 10000) (5244184579217 / 5000) := by
  exact
    packedTile32768 1048807680 1048873216 13 3157 32385 30 _ _ (207709 / 10000) (2077093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048873216 :
    ThetaLowerSegment 1048873216 1048938752 (5244184579217 / 5000) (2622255341723 / 2500) := by
  exact
    packedTile32768 1048873216 1048938752 13 3140 32386 30 _ _ (2077097 / 100000) (20771 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1048938752 :
    ThetaLowerSegment 1048938752 1049004288 (2622255341723 / 2500) (52448353346449 / 50000) := by
  exact
    packedTile32768 1048938752 1049004288 13 3126 32387 30 _ _ (2077103 / 100000) (1038553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049004288 :
    ThetaLowerSegment 1049004288 1049069824 (52448353346449 / 50000)
      (104903143653689 / 100000) := by
  exact
    packedTile32768 1049004288 1049069824 13 3099 32388 30 _ _ (2077109 / 100000) (259639 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049069824 :
    ThetaLowerSegment 1049069824 1049135360 (104903143653689 / 100000)
      (13113714715333 / 12500) := by
  exact
    packedTile32768 1049069824 1049135360 13 3165 32389 30 _ _ (415423 / 20000) (1038559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049135360 :
    ThetaLowerSegment 1049135360 1049200896 (13113714715333 / 12500) (52458089824603 / 50000) := by
  exact
    packedTile32768 1049135360 1049200896 13 3111 32390 30 _ _ (1038561 / 50000) (16617 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049200896 :
    ThetaLowerSegment 1049200896 1049266432 (52458089824603 / 50000) (52461406998019 / 50000) := by
  exact
    packedTile32768 1049200896 1049266432 13 3194 32391 30 _ _ (259641 / 12500) (2077131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049266432 :
    ThetaLowerSegment 1049266432 1049331968 (52461406998019 / 50000) (13116190651999 / 12500) := by
  exact
    packedTile32768 1049266432 1049331968 13 3231 32392 30 _ _ (1038567 / 50000) (2077137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049331968 :
    ThetaLowerSegment 1049331968 1049397504 (13116190651999 / 12500) (26233985375363 / 25000) := by
  exact
    packedTile32768 1049331968 1049397504 13 3089 32393 30 _ _ (103857 / 5000) (2077143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049397504 :
    ThetaLowerSegment 1049397504 1049463040 (26233985375363 / 25000) (52471296263073 / 50000) := by
  exact
    packedTile32768 1049397504 1049463040 13 3202 32394 30 _ _ (2077147 / 100000) (41543 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049463040 :
    ThetaLowerSegment 1049463040 1049528576 (52471296263073 / 50000) (52474569856201 / 50000) := by
  exact
    packedTile32768 1049463040 1049528576 13 3152 32395 30 _ _ (2077153 / 100000) (519289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049528576 :
    ThetaLowerSegment 1049528576 1049594112 (52474569856201 / 50000) (52477855921739 / 50000) := by
  exact
    packedTile32768 1049528576 1049594112 13 3164 32396 30 _ _ (2077159 / 100000) (1038581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049594112 :
    ThetaLowerSegment 1049594112 1049659648 (52477855921739 / 50000) (26240538802327 / 25000) := by
  exact
    packedTile32768 1049594112 1049659648 13 3102 32397 30 _ _ (415433 / 20000) (129823 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049659648 :
    ThetaLowerSegment 1049659648 1049725184 (26240538802327 / 25000) (13121096894559 / 12500) := by
  exact
    packedTile32768 1049659648 1049725184 13 3187 32398 30 _ _ (519293 / 25000) (83087 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049725184 :
    ThetaLowerSegment 1049725184 1049790720 (13121096894559 / 12500) (52487653940641 / 50000) := by
  exact
    packedTile32768 1049725184 1049790720 13 3145 32399 30 _ _ (1038589 / 50000) (2077181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049790720 :
    ThetaLowerSegment 1049790720 1049856256 (52487653940641 / 50000) (52490959778977 / 50000) := by
  exact
    packedTile32768 1049790720 1049856256 13 3183 32400 30 _ _ (64912 / 3125) (2077187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049856256 :
    ThetaLowerSegment 1049856256 1049921792 (52490959778977 / 50000) (52494231353227 / 50000) := by
  exact
    packedTile32768 1049856256 1049921792 13 3150 32401 30 _ _ (207719 / 10000) (2077193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049921792 :
    ThetaLowerSegment 1049921792 1049987328 (52494231353227 / 50000) (2624872446569 / 2500) := by
  exact
    packedTile32768 1049921792 1049987328 13 3098 32402 30 _ _ (2077197 / 100000) (5193 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1049987328 :
    ThetaLowerSegment 1049987328 1050052864 (2624872446569 / 2500) (52500745452541 / 50000) := by
  exact
    packedTile32768 1049987328 1050052864 13 3174 32403 30 _ _ (2077203 / 100000) (1038603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050052864 :
    ThetaLowerSegment 1050052864 1050118400 (52500745452541 / 50000) (52504010825089 / 50000) := by
  exact
    packedTile32768 1050052864 1050118400 13 3144 32404 30 _ _ (2077209 / 100000) (519303 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050118400 :
    ThetaLowerSegment 1050118400 1050183936 (52504010825089 / 50000) (26253645373787 / 25000) := by
  exact
    packedTile32768 1050118400 1050183936 13 3158 32405 30 _ _ (415443 / 20000) (1038609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050183936 :
    ThetaLowerSegment 1050183936 1050249472 (26253645373787 / 25000) (52510519789173 / 50000) := by
  exact
    packedTile32768 1050183936 1050249472 13 3109 32406 30 _ _ (1038611 / 50000) (83089 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050249472 :
    ThetaLowerSegment 1050249472 1050315008 (52510519789173 / 50000) (52513802848027 / 50000) := by
  exact
    packedTile32768 1050249472 1050315008 13 3161 32407 30 _ _ (519307 / 25000) (2077231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050315008 :
    ThetaLowerSegment 1050315008 1050380544 (52513802848027 / 50000) (26258548151267 / 25000) := by
  exact
    packedTile32768 1050315008 1050380544 13 3171 32408 30 _ _ (1038617 / 50000) (2077237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050380544 :
    ThetaLowerSegment 1050380544 1050446080 (26258548151267 / 25000) (26260229157737 / 25000) := by
  exact
    packedTile32768 1050380544 1050446080 13 3237 32409 30 _ _ (51931 / 2500) (2077243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050446080 :
    ThetaLowerSegment 1050446080 1050511616 (26260229157737 / 25000) (21009496561743 / 20000) := by
  exact
    packedTile32768 1050446080 1050511616 13 3161 32410 30 _ _ (2077247 / 100000) (8309 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050511616 :
    ThetaLowerSegment 1050511616 1050577152 (21009496561743 / 20000) (21010788613109 / 20000) := by
  exact
    packedTile32768 1050511616 1050577152 13 3110 32411 30 _ _ (2077253 / 100000) (259657 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050577152 :
    ThetaLowerSegment 1050577152 1050642688 (21010788613109 / 20000) (21012113904351 / 20000) := by
  exact
    packedTile32768 1050577152 1050642688 13 3190 32412 30 _ _ (2077259 / 100000) (1038631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050642688 :
    ThetaLowerSegment 1050642688 1050708224 (21012113904351 / 20000) (21013418426771 / 20000) := by
  exact
    packedTile32768 1050642688 1050708224 13 3140 32413 30 _ _ (415453 / 20000) (519317 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050708224 :
    ThetaLowerSegment 1050708224 1050773760 (21013418426771 / 20000)
      (105073639695199 / 100000) := by
  exact
    packedTile32768 1050708224 1050773760 13 3152 32414 30 _ _ (259659 / 12500) (83091 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050773760 :
    ThetaLowerSegment 1050773760 1050839296 (105073639695199 / 100000)
      (105080255825629 / 100000) := by
  exact
    packedTile32768 1050773760 1050839296 13 3185 32415 30 _ _ (1038639 / 50000) (2077281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050839296 :
    ThetaLowerSegment 1050839296 1050904832 (105080255825629 / 100000)
      (105086788883809 / 100000) := by
  exact
    packedTile32768 1050839296 1050904832 13 3145 32416 30 _ _ (519321 / 25000) (2077287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050904832 :
    ThetaLowerSegment 1050904832 1050970368 (105086788883809 / 100000)
      (105093257564869 / 100000) := by
  exact
    packedTile32768 1050904832 1050970368 13 3114 32417 30 _ _ (207729 / 10000) (2077293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1050970368 :
    ThetaLowerSegment 1050970368 1051035904 (105093257564869 / 100000)
      (105099873752629 / 100000) := by
  exact
    packedTile32768 1050970368 1051035904 13 3185 32418 30 _ _ (129831 / 6250) (2077299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051035904 :
    ThetaLowerSegment 1051035904 1051101440 (105099873752629 / 100000)
      (105106346628777 / 100000) := by
  exact
    packedTile32768 1051035904 1051101440 13 3116 32419 30 _ _ (2077303 / 100000) (1038653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051101440 :
    ThetaLowerSegment 1051101440 1051166976 (105106346628777 / 100000) (2102259755713 / 2000) := by
  exact
    packedTile32768 1051101440 1051166976 13 3197 32420 30 _ _ (2077309 / 100000) (64916 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051166976 :
    ThetaLowerSegment 1051166976 1051232512 (2102259755713 / 2000) (21023914159377 / 20000) := by
  exact
    packedTile32768 1051166976 1051232512 13 3169 32421 30 _ _ (415463 / 20000) (1038659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051232512 :
    ThetaLowerSegment 1051232512 1051298048 (21023914159377 / 20000)
      (105126226533369 / 100000) := by
  exact
    packedTile32768 1051232512 1051298048 13 3204 32422 30 _ _ (2077321 / 100000) (519331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051298048 :
    ThetaLowerSegment 1051298048 1051363584 (105126226533369 / 100000)
      (105132792967177 / 100000) := by
  exact
    packedTile32768 1051298048 1051363584 13 3161 32423 30 _ _ (129833 / 6250) (2077331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051363584 :
    ThetaLowerSegment 1051363584 1051429120 (105132792967177 / 100000)
      (21027863990121 / 20000) := by
  exact
    packedTile32768 1051363584 1051429120 13 3142 32424 30 _ _ (1038667 / 50000) (2077337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051429120 :
    ThetaLowerSegment 1051429120 1051494656 (21027863990121 / 20000) (21029180608213 / 20000) := by
  exact
    packedTile32768 1051429120 1051494656 13 3169 32425 30 _ _ (103867 / 5000) (2077343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051494656 :
    ThetaLowerSegment 1051494656 1051560192 (21029180608213 / 20000)
      (105152392669969 / 100000) := by
  exact
    packedTile32768 1051494656 1051560192 13 3124 32426 30 _ _ (1038673 / 50000) (2077349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051560192 :
    ThetaLowerSegment 1051560192 1051625728 (105152392669969 / 100000)
      (10515895087339 / 10000) := by
  exact
    packedTile32768 1051560192 1051625728 13 3157 32427 30 _ _ (2077353 / 100000) (519339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051625728 :
    ThetaLowerSegment 1051625728 1051691264 (10515895087339 / 10000)
      (105165430156111 / 100000) := by
  exact
    packedTile32768 1051625728 1051691264 13 3119 32428 30 _ _ (2077359 / 100000) (1038681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051691264 :
    ThetaLowerSegment 1051691264 1051756800 (105165430156111 / 100000)
      (52586062751753 / 50000) := by
  exact
    packedTile32768 1051691264 1051756800 13 3223 32429 30 _ _ (415473 / 20000) (259671 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051756800 :
    ThetaLowerSegment 1051756800 1051822336 (52586062751753 / 50000) (26294646531829 / 25000) := by
  exact
    packedTile32768 1051756800 1051822336 13 3110 32430 30 _ _ (2077371 / 100000) (1038687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051822336 :
    ThetaLowerSegment 1051822336 1051887872 (26294646531829 / 25000) (52592607520257 / 50000) := by
  exact
    packedTile32768 1051822336 1051887872 13 3191 32431 30 _ _ (1038689 / 50000) (2077381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051887872 :
    ThetaLowerSegment 1051887872 1051953408 (52592607520257 / 50000) (10519175672273 / 10000) := by
  exact
    packedTile32768 1051887872 1051953408 13 3149 32432 30 _ _ (259673 / 12500) (2077387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1051953408 :
    ThetaLowerSegment 1051953408 1052018944 (10519175672273 / 10000) (2629954344511 / 2500) := by
  exact
    packedTile32768 1051953408 1052018944 13 3089 32433 30 _ _ (207739 / 10000) (2077393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052018944 :
    ThetaLowerSegment 1052018944 1052084480 (2629954344511 / 2500) (26301184068601 / 25000) := by
  exact
    packedTile32768 1052018944 1052084480 13 3159 32434 30 _ _ (519349 / 25000) (2077399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052084480 :
    ThetaLowerSegment 1052084480 1052150016 (26301184068601 / 25000) (52605645238857 / 50000) := by
  exact
    packedTile32768 1052084480 1052150016 13 3155 32435 30 _ _ (1038701 / 50000) (415481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052150016 :
    ThetaLowerSegment 1052150016 1052215552 (52605645238857 / 50000)
      (105217736677841 / 100000) := by
  exact
    packedTile32768 1052150016 1052215552 13 3103 32436 30 _ _ (2077409 / 100000) (519353 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052215552 :
    ThetaLowerSegment 1052215552 1052281088 (105217736677841 / 100000)
      (52612124686933 / 50000) := by
  exact
    packedTile32768 1052215552 1052281088 13 3135 32437 30 _ _ (415483 / 20000) (1038709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052281088 :
    ThetaLowerSegment 1052281088 1052346624 (52612124686933 / 50000)
      (105230824411331 / 100000) := by
  exact
    packedTile32768 1052281088 1052346624 13 3165 32438 30 _ _ (2077421 / 100000) (129839 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052346624 :
    ThetaLowerSegment 1052346624 1052412160 (105230824411331 / 100000)
      (105237555274811 / 100000) := by
  exact
    packedTile32768 1052346624 1052412160 13 3240 32439 30 _ _ (2077427 / 100000) (207743 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052412160 :
    ThetaLowerSegment 1052412160 1052477696 (105237555274811 / 100000)
      (105244103346779 / 100000) := by
  exact
    packedTile32768 1052412160 1052477696 13 3152 32440 30 _ _ (1038717 / 50000) (2077437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052477696 :
    ThetaLowerSegment 1052477696 1052543232 (105244103346779 / 100000)
      (105250665979739 / 100000) := by
  exact
    packedTile32768 1052477696 1052543232 13 3159 32441 30 _ _ (12984 / 625) (2077443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052543232 :
    ThetaLowerSegment 1052543232 1052608768 (105250665979739 / 100000)
      (105257322116723 / 100000) := by
  exact
    packedTile32768 1052543232 1052608768 13 3204 32442 30 _ _ (1038723 / 50000) (2077449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052608768 :
    ThetaLowerSegment 1052608768 1052674304 (105257322116723 / 100000)
      (105264032286683 / 100000) := by
  exact
    packedTile32768 1052608768 1052674304 13 3230 32443 30 _ _ (519363 / 25000) (415491 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052674304 :
    ThetaLowerSegment 1052674304 1052739840 (105264032286683 / 100000)
      (105270638603123 / 100000) := by
  exact
    packedTile32768 1052674304 1052739840 13 3180 32444 30 _ _ (1038729 / 50000) (2077461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052739840 :
    ThetaLowerSegment 1052739840 1052805376 (105270638603123 / 100000)
      (105277087054483 / 100000) := by
  exact
    packedTile32768 1052739840 1052805376 13 3104 32445 30 _ _ (415493 / 20000) (519367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052805376 :
    ThetaLowerSegment 1052805376 1052870912 (105277087054483 / 100000)
      (26320908291401 / 25000) := by
  exact
    packedTile32768 1052805376 1052870912 13 3151 32446 30 _ _ (2077471 / 100000) (1038737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052870912 :
    ThetaLowerSegment 1052870912 1052936448 (26320908291401 / 25000)
      (105290154365907 / 100000) := by
  exact
    packedTile32768 1052870912 1052936448 13 3139 32447 30 _ _ (2077477 / 100000) (51937 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1052936448 :
    ThetaLowerSegment 1052936448 1053001984 (105290154365907 / 100000)
      (105296694282391 / 100000) := by
  exact
    packedTile32768 1052936448 1053001984 13 3148 32448 30 _ _ (2077483 / 100000) (1038743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053001984 :
    ThetaLowerSegment 1053001984 1053067520 (105296694282391 / 100000)
      (105303117881471 / 100000) := by
  exact
    packedTile32768 1053001984 1053067520 13 3092 32449 30 _ _ (207749 / 10000) (2077493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053067520 :
    ThetaLowerSegment 1053067520 1053133056 (105303117881471 / 100000)
      (21061956913227 / 20000) := by
  exact
    packedTile32768 1053067520 1053133056 13 3209 32451 30 _ _ (259687 / 12500) (2077499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053133056 :
    ThetaLowerSegment 1053133056 1053198592 (21061956913227 / 20000)
      (105316376479981 / 100000) := by
  exact
    packedTile32768 1053133056 1053198592 13 3173 32452 30 _ _ (1038751 / 50000) (415501 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053198592 :
    ThetaLowerSegment 1053198592 1053264128 (105316376479981 / 100000)
      (21064606147621 / 20000) := by
  exact
    packedTile32768 1053198592 1053264128 13 3203 32453 30 _ _ (519377 / 25000) (2077511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053264128 :
    ThetaLowerSegment 1053264128 1053329664 (21064606147621 / 20000) (4213183411791 / 4000) := by
  exact
    packedTile32768 1053264128 1053329664 13 3155 32454 30 _ _ (1038757 / 50000) (2077517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053329664 :
    ThetaLowerSegment 1053329664 1053395200 (4213183411791 / 4000) (52668094867017 / 50000) := by
  exact
    packedTile32768 1053329664 1053395200 13 3179 32455 30 _ _ (2077521 / 100000) (519381 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053395200 :
    ThetaLowerSegment 1053395200 1053460736 (52668094867017 / 50000) (26335675175913 / 25000) := by
  exact
    packedTile32768 1053395200 1053460736 13 3134 32456 30 _ _ (2077527 / 100000) (207753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053460736 :
    ThetaLowerSegment 1053460736 1053526272 (26335675175913 / 25000) (6584321315997 / 6250) := by
  exact
    packedTile32768 1053460736 1053526272 13 3100 32457 30 _ _ (2077533 / 100000) (64923 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053526272 :
    ThetaLowerSegment 1053526272 1053591808 (6584321315997 / 6250) (52677796946043 / 50000) := by
  exact
    packedTile32768 1053526272 1053591808 13 3106 32458 30 _ _ (2077539 / 100000) (1038771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053591808 :
    ThetaLowerSegment 1053591808 1053657344 (52677796946043 / 50000) (10536214647217 / 10000) := by
  exact
    packedTile32768 1053591808 1053657344 13 3154 32459 30 _ _ (1038773 / 50000) (2077549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053657344 :
    ThetaLowerSegment 1053657344 1053722880 (10536214647217 / 10000) (52684217611037 / 50000) := by
  exact
    packedTile32768 1053657344 1053722880 13 3027 32460 30 _ _ (129847 / 6250) (415511 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053722880 :
    ThetaLowerSegment 1053722880 1053788416 (52684217611037 / 50000) (52687541703837 / 50000) := by
  exact
    packedTile32768 1053722880 1053788416 13 3200 32461 30 _ _ (1038779 / 50000) (2077561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053788416 :
    ThetaLowerSegment 1053788416 1053853952 (52687541703837 / 50000) (52690865806237 / 50000) := by
  exact
    packedTile32768 1053788416 1053853952 13 3200 32462 30 _ _ (519391 / 25000) (2077567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053853952 :
    ThetaLowerSegment 1053853952 1053919488 (52690865806237 / 50000) (52694090194877 / 50000) := by
  exact
    packedTile32768 1053853952 1053919488 13 3104 32463 30 _ _ (207757 / 10000) (2077573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053919488 :
    ThetaLowerSegment 1053919488 1053985024 (52694090194877 / 50000)
      (105394768386421 / 100000) := by
  exact
    packedTile32768 1053919488 1053985024 13 3171 32464 30 _ _ (2077577 / 100000) (103879 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1053985024 :
    ThetaLowerSegment 1053985024 1054050560 (105394768386421 / 100000)
      (105401200583389 / 100000) := by
  exact
    packedTile32768 1053985024 1054050560 13 3096 32465 30 _ _ (2077583 / 100000) (1038793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054050560 :
    ThetaLowerSegment 1054050560 1054116096 (105401200583389 / 100000)
      (105407786540519 / 100000) := by
  exact
    packedTile32768 1054050560 1054116096 13 3170 32466 30 _ _ (2077589 / 100000) (259699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054116096 :
    ThetaLowerSegment 1054116096 1054181632 (105407786540519 / 100000)
      (105414480551609 / 100000) := by
  exact
    packedTile32768 1054116096 1054181632 13 3222 32467 30 _ _ (415519 / 20000) (1038799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054181632 :
    ThetaLowerSegment 1054181632 1054247168 (105414480551609 / 100000)
      (105421162119641 / 100000) := by
  exact
    packedTile32768 1054181632 1054247168 13 3216 32468 30 _ _ (1038801 / 50000) (415521 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054247168 :
    ThetaLowerSegment 1054247168 1054312704 (105421162119641 / 100000)
      (21085525942669 / 20000) := by
  exact
    packedTile32768 1054247168 1054312704 13 3113 32469 30 _ _ (259701 / 12500) (2077611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054312704 :
    ThetaLowerSegment 1054312704 1054378240 (21085525942669 / 20000) (21086836917103 / 20000) := by
  exact
    packedTile32768 1054312704 1054378240 13 3155 32470 30 _ _ (1038807 / 50000) (2077617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054378240 :
    ThetaLowerSegment 1054378240 1054443776 (21086836917103 / 20000) (4217630243903 / 4000) := by
  exact
    packedTile32768 1054378240 1054443776 13 3163 32471 30 _ _ (103881 / 5000) (2077623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054443776 :
    ThetaLowerSegment 1054443776 1054509312 (4217630243903 / 4000) (21089499598789 / 20000) := by
  exact
    packedTile32768 1054443776 1054509312 13 3245 32472 30 _ _ (1038813 / 50000) (2077629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054509312 :
    ThetaLowerSegment 1054509312 1054574848 (21089499598789 / 20000) (3295438374827 / 3125) := by
  exact
    packedTile32768 1054509312 1054574848 13 3143 32473 30 _ _ (2077633 / 100000) (519409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054574848 :
    ThetaLowerSegment 1054574848 1054640384 (3295438374827 / 3125) (105460474908281 / 100000) := by
  exact
    packedTile32768 1054574848 1054640384 13 3103 32474 30 _ _ (2077639 / 100000) (1038821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054640384 :
    ThetaLowerSegment 1054640384 1054705920 (105460474908281 / 100000)
      (105467023645321 / 100000) := by
  exact
    packedTile32768 1054640384 1054705920 13 3152 32475 30 _ _ (415529 / 20000) (129853 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054705920 :
    ThetaLowerSegment 1054705920 1054771456 (105467023645321 / 100000)
      (52736805938321 / 50000) := by
  exact
    packedTile32768 1054705920 1054771456 13 3171 32476 30 _ _ (2077651 / 100000) (1038827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054771456 :
    ThetaLowerSegment 1054771456 1054836992 (52736805938321 / 50000) (21096026728393 / 20000) := by
  exact
    packedTile32768 1054771456 1054836992 13 3139 32477 30 _ _ (2077657 / 100000) (103883 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054836992 :
    ThetaLowerSegment 1054836992 1054902528 (21096026728393 / 20000)
      (105486618031309 / 100000) := by
  exact
    packedTile32768 1054836992 1054902528 13 3121 32478 30 _ _ (64927 / 3125) (2077667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054902528 :
    ThetaLowerSegment 1054902528 1054968064 (105486618031309 / 100000)
      (105493042186949 / 100000) := by
  exact
    packedTile32768 1054902528 1054968064 13 3092 32479 30 _ _ (207767 / 10000) (2077673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1054968064 :
    ThetaLowerSegment 1054968064 1055033600 (105493042186949 / 100000)
      (105499545312829 / 100000) := by
  exact
    packedTile32768 1054968064 1055033600 13 3130 32480 30 _ _ (519419 / 25000) (2077679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055033600 :
    ThetaLowerSegment 1055033600 1055099136 (105499545312829 / 100000)
      (105506206361321 / 100000) := by
  exact
    packedTile32768 1055033600 1055099136 13 3206 32481 30 _ _ (1038841 / 50000) (415537 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055099136 :
    ThetaLowerSegment 1055099136 1055164672 (105506206361321 / 100000)
      (105512663818733 / 100000) := by
  exact
    packedTile32768 1055099136 1055164672 13 3108 32482 30 _ _ (2077689 / 100000) (519423 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055164672 :
    ThetaLowerSegment 1055164672 1055230208 (105512663818733 / 100000)
      (105519216868763 / 100000) := by
  exact
    packedTile32768 1055164672 1055230208 13 3154 32483 30 _ _ (415539 / 20000) (1038849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055230208 :
    ThetaLowerSegment 1055230208 1055295744 (105519216868763 / 100000)
      (52762873541503 / 50000) := by
  exact
    packedTile32768 1055230208 1055295744 13 3143 32484 30 _ _ (2077701 / 100000) (259713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055295744 :
    ThetaLowerSegment 1055295744 1055361280 (52762873541503 / 50000) (10553229601547 / 10000) := by
  exact
    packedTile32768 1055295744 1055361280 13 3152 32485 30 _ _ (2077707 / 100000) (207771 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055361280 :
    ThetaLowerSegment 1055361280 1055426816 (10553229601547 / 10000) (52769480659387 / 50000) := by
  exact
    packedTile32768 1055361280 1055426816 13 3208 32486 30 _ _ (2077713 / 100000) (519429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055426816 :
    ThetaLowerSegment 1055426816 1055492352 (52769480659387 / 50000) (52772783195327 / 50000) := by
  exact
    packedTile32768 1055426816 1055492352 13 3179 32487 30 _ _ (51943 / 2500) (2077723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055492352 :
    ThetaLowerSegment 1055492352 1055557888 (52772783195327 / 50000) (52775995359723 / 50000) := by
  exact
    packedTile32768 1055492352 1055557888 13 3092 32488 30 _ _ (1038863 / 50000) (2077729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055557888 :
    ThetaLowerSegment 1055557888 1055623424 (52775995359723 / 50000) (52779255321231 / 50000) := by
  exact
    packedTile32768 1055557888 1055623424 13 3138 32489 30 _ _ (519433 / 25000) (415547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055623424 :
    ThetaLowerSegment 1055623424 1055688960 (52779255321231 / 50000) (52782459193227 / 50000) := by
  exact
    packedTile32768 1055623424 1055688960 13 3084 32490 30 _ _ (1038869 / 50000) (2077741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055688960 :
    ThetaLowerSegment 1055688960 1055754496 (52782459193227 / 50000) (10557147159103 / 10000) := by
  exact
    packedTile32768 1055688960 1055754496 13 3154 32491 30 _ _ (129859 / 6250) (2077747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055754496 :
    ThetaLowerSegment 1055754496 1055820032 (10557147159103 / 10000) (52789010331091 / 50000) := by
  exact
    packedTile32768 1055754496 1055820032 13 3152 32492 30 _ _ (2077751 / 100000) (1038877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055820032 :
    ThetaLowerSegment 1055820032 1055885568 (52789010331091 / 50000) (52792309809207 / 50000) := by
  exact
    packedTile32768 1055820032 1055885568 13 3176 32493 30 _ _ (2077757 / 100000) (12986 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055885568 :
    ThetaLowerSegment 1055885568 1055951104 (52792309809207 / 50000) (52795555275013 / 50000) := by
  exact
    packedTile32768 1055885568 1055951104 13 3124 32494 30 _ _ (2077763 / 100000) (1038883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1055951104 :
    ThetaLowerSegment 1055951104 1056016640 (52795555275013 / 50000)
      (105597562022771 / 100000) := by
  exact
    packedTile32768 1055951104 1056016640 13 3105 32495 30 _ _ (2077769 / 100000) (519443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056016640 :
    ThetaLowerSegment 1056016640 1056082176 (105597562022771 / 100000)
      (105604102858471 / 100000) := by
  exact
    packedTile32768 1056016640 1056082176 13 3148 32496 30 _ _ (83111 / 4000) (1038889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056082176 :
    ThetaLowerSegment 1056082176 1056147712 (105604102858471 / 100000)
      (105610733060833 / 100000) := by
  exact
    packedTile32768 1056082176 1056147712 13 3191 32497 30 _ _ (1038891 / 50000) (415557 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056147712 :
    ThetaLowerSegment 1056147712 1056213248 (105610733060833 / 100000)
      (105617253159577 / 100000) := by
  exact
    packedTile32768 1056147712 1056213248 13 3138 32498 30 _ _ (519447 / 25000) (2077791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056213248 :
    ThetaLowerSegment 1056213248 1056278784 (105617253159577 / 100000)
      (105623814833029 / 100000) := by
  exact
    packedTile32768 1056213248 1056278784 13 3158 32499 30 _ _ (1038897 / 50000) (2077797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056278784 :
    ThetaLowerSegment 1056278784 1056344320 (105623814833029 / 100000)
      (105630332891629 / 100000) := by
  exact
    packedTile32768 1056278784 1056344320 13 3137 32500 30 _ _ (10389 / 500) (2077803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056344320 :
    ThetaLowerSegment 1056344320 1056409856 (105630332891629 / 100000)
      (21127399699297 / 20000) := by
  exact
    packedTile32768 1056344320 1056409856 13 3208 32501 30 _ _ (2077807 / 100000) (207781 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056409856 :
    ThetaLowerSegment 1056409856 1056475392 (21127399699297 / 20000) (26410892654751 / 25000) := by
  exact
    packedTile32768 1056409856 1056475392 13 3163 32502 30 _ _ (2077813 / 100000) (259727 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056475392 :
    ThetaLowerSegment 1056475392 1056540928 (26410892654751 / 25000) (5282501008459 / 5000) := by
  exact
    packedTile32768 1056475392 1056540928 13 3104 32503 30 _ _ (2077819 / 100000) (1038911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056540928 :
    ThetaLowerSegment 1056540928 1056606464 (5282501008459 / 5000) (5282822655769 / 5000) := by
  exact
    packedTile32768 1056540928 1056606464 13 3096 32504 30 _ _ (83113 / 4000) (519457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056606464 :
    ThetaLowerSegment 1056606464 1056672000 (5282822655769 / 5000) (21132601734437 / 20000) := by
  exact
    packedTile32768 1056606464 1056672000 13 3155 32505 30 _ _ (2077831 / 100000) (1038917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056672000 :
    ThetaLowerSegment 1056672000 1056737536 (21132601734437 / 20000)
      (105669578795941 / 100000) := by
  exact
    packedTile32768 1056672000 1056737536 13 3162 32506 30 _ _ (1038919 / 50000) (2077841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056737536 :
    ThetaLowerSegment 1056737536 1056803072 (105669578795941 / 100000)
      (105676236208117 / 100000) := by
  exact
    packedTile32768 1056737536 1056803072 13 3204 32507 30 _ _ (519461 / 25000) (2077847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056803072 :
    ThetaLowerSegment 1056803072 1056868608 (105676236208117 / 100000)
      (105682777279917 / 100000) := by
  exact
    packedTile32768 1056803072 1056868608 13 3148 32508 30 _ _ (41557 / 2000) (2077853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056868608 :
    ThetaLowerSegment 1056868608 1056934144 (105682777279917 / 100000)
      (105689393173421 / 100000) := by
  exact
    packedTile32768 1056868608 1056934144 13 3184 32509 30 _ _ (64933 / 3125) (2077859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056934144 :
    ThetaLowerSegment 1056934144 1056999680 (105689393173421 / 100000)
      (21139196830337 / 20000) := by
  exact
    packedTile32768 1056934144 1056999680 13 3172 32510 30 _ _ (1038931 / 50000) (415573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1056999680 :
    ThetaLowerSegment 1056999680 1057065216 (21139196830337 / 20000) (21140505887807 / 20000) := by
  exact
    packedTile32768 1056999680 1057065216 13 3150 32511 30 _ _ (2077869 / 100000) (129867 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057065216 :
    ThetaLowerSegment 1057065216 1057130752 (21140505887807 / 20000) (21141805806407 / 20000) := by
  exact
    packedTile32768 1057065216 1057130752 13 3128 32512 30 _ _ (16623 / 800) (1038939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057130752 :
    ThetaLowerSegment 1057130752 1057196288 (21141805806407 / 20000) (52857746659913 / 50000) := by
  exact
    packedTile32768 1057130752 1057196288 13 3111 32513 30 _ _ (2077881 / 100000) (519471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057196288 :
    ThetaLowerSegment 1057196288 1057261824 (52857746659913 / 50000)
      (105721953470509 / 100000) := by
  exact
    packedTile32768 1057196288 1057261824 13 3109 32514 30 _ _ (2077887 / 100000) (207789 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057261824 :
    ThetaLowerSegment 1057261824 1057327360 (105721953470509 / 100000)
      (26432118994159 / 25000) := by
  exact
    packedTile32768 1057261824 1057327360 13 3139 32515 30 _ _ (2077893 / 100000) (259737 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057327360 :
    ThetaLowerSegment 1057327360 1057392896 (26432118994159 / 25000) (26433793781559 / 25000) := by
  exact
    packedTile32768 1057327360 1057392896 13 3224 32516 30 _ _ (20779 / 1000) (2077903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057392896 :
    ThetaLowerSegment 1057392896 1057458432 (26433793781559 / 25000) (13217725455797 / 12500) := by
  exact
    packedTile32768 1057392896 1057458432 13 3190 32517 30 _ _ (1038953 / 50000) (2077909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057458432 :
    ThetaLowerSegment 1057458432 1057523968 (13217725455797 / 12500) (264370753193 / 250) := by
  exact
    packedTile32768 1057458432 1057523968 13 3127 32518 30 _ _ (259739 / 12500) (415583 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057523968 :
    ThetaLowerSegment 1057523968 1057589504 (264370753193 / 250) (52877382840049 / 50000) := by
  exact
    packedTile32768 1057523968 1057589504 13 3111 32519 30 _ _ (1038959 / 50000) (2077921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057589504 :
    ThetaLowerSegment 1057589504 1057655040 (52877382840049 / 50000) (52880659726197 / 50000) := by
  exact
    packedTile32768 1057589504 1057655040 13 3154 32520 30 _ _ (519481 / 25000) (2077927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057655040 :
    ThetaLowerSegment 1057655040 1057720576 (52880659726197 / 50000) (26441949610313 / 25000) := by
  exact
    packedTile32768 1057655040 1057720576 13 3118 32521 30 _ _ (2077931 / 100000) (1038967 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057720576 :
    ThetaLowerSegment 1057720576 1057786112 (26441949610313 / 25000) (52887201062519 / 50000) := by
  exact
    packedTile32768 1057720576 1057786112 13 3178 32522 30 _ _ (2077937 / 100000) (103897 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057786112 :
    ThetaLowerSegment 1057786112 1057851648 (52887201062519 / 50000) (132226142998 / 125) := by
  exact
    packedTile32768 1057786112 1057851648 13 3134 32523 30 _ _ (2077943 / 100000) (1038973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057851648 :
    ThetaLowerSegment 1057851648 1057917184 (132226142998 / 125) (26446843165973 / 25000) := by
  exact
    packedTile32768 1057851648 1057917184 13 3108 32524 30 _ _ (2077949 / 100000) (64936 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057917184 :
    ThetaLowerSegment 1057917184 1057982720 (26446843165973 / 25000)
      (105794003418297 / 100000) := by
  exact
    packedTile32768 1057917184 1057982720 13 3191 32525 30 _ _ (415591 / 20000) (1038979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1057982720 :
    ThetaLowerSegment 1057982720 1058048256 (105794003418297 / 100000)
      (21160133903437 / 20000) := by
  exact
    packedTile32768 1057982720 1058048256 13 3208 32526 30 _ _ (2077961 / 100000) (519491 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058048256 :
    ThetaLowerSegment 1058048256 1058113792 (21160133903437 / 20000)
      (105807283689329 / 100000) := by
  exact
    packedTile32768 1058048256 1058113792 13 3183 32527 30 _ _ (129873 / 6250) (2077971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058113792 :
    ThetaLowerSegment 1058113792 1058179328 (105807283689329 / 100000)
      (105813783592001 / 100000) := by
  exact
    packedTile32768 1058113792 1058179328 13 3128 32528 30 _ _ (1038987 / 50000) (2077977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058179328 :
    ThetaLowerSegment 1058179328 1058244864 (105813783592001 / 100000)
      (105820360398701 / 100000) := by
  exact
    packedTile32768 1058179328 1058244864 13 3165 32529 30 _ _ (103899 / 5000) (2077983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058244864 :
    ThetaLowerSegment 1058244864 1058310400 (105820360398701 / 100000)
      (21165357937477 / 20000) := by
  exact
    packedTile32768 1058244864 1058310400 13 3094 32530 30 _ _ (1038993 / 50000) (2077989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058310400 :
    ThetaLowerSegment 1058310400 1058375936 (21165357937477 / 20000)
      (105833472509657 / 100000) := by
  exact
    packedTile32768 1058310400 1058375936 13 3216 32531 30 _ _ (259749 / 12500) (415599 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058375936 :
    ThetaLowerSegment 1058375936 1058441472 (105833472509657 / 100000)
      (52920030922243 / 50000) := by
  exact
    packedTile32768 1058375936 1058441472 13 3171 32532 30 _ _ (2077999 / 100000) (1039001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058441472 :
    ThetaLowerSegment 1058441472 1058507008 (52920030922243 / 50000) (13230833218047 / 12500) := by
  exact
    packedTile32768 1058441472 1058507008 13 3178 32533 30 _ _ (415601 / 20000) (259751 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058507008 :
    ThetaLowerSegment 1058507008 1058572544 (13230833218047 / 12500)
      (105853221869081 / 100000) := by
  exact
    packedTile32768 1058507008 1058572544 13 3155 32534 30 _ _ (2078011 / 100000) (1039007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058572544 :
    ThetaLowerSegment 1058572544 1058638080 (105853221869081 / 100000)
      (105859780090733 / 100000) := by
  exact
    packedTile32768 1058572544 1058638080 13 3156 32535 30 _ _ (2078017 / 100000) (103901 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058638080 :
    ThetaLowerSegment 1058638080 1058703616 (105859780090733 / 100000)
      (21173258522963 / 20000) := by
  exact
    packedTile32768 1058638080 1058703616 13 3134 32536 30 _ _ (2078023 / 100000) (1039013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058703616 :
    ThetaLowerSegment 1058703616 1058769152 (21173258522963 / 20000) (4234920352311 / 4000) := by
  exact
    packedTile32768 1058703616 1058769152 13 3232 32537 30 _ _ (207803 / 10000) (2078033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058769152 :
    ThetaLowerSegment 1058769152 1058834688 (4234920352311 / 4000) (105879496436167 / 100000) := by
  exact
    packedTile32768 1058769152 1058834688 13 3122 32538 30 _ _ (519509 / 25000) (2078039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058834688 :
    ThetaLowerSegment 1058834688 1058900224 (105879496436167 / 100000)
      (105886002785669 / 100000) := by
  exact
    packedTile32768 1058834688 1058900224 13 3131 32539 30 _ _ (1039021 / 50000) (415609 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058900224 :
    ThetaLowerSegment 1058900224 1058965760 (105886002785669 / 100000)
      (105892627602693 / 100000) := by
  exact
    packedTile32768 1058900224 1058965760 13 3188 32540 30 _ _ (64939 / 3125) (2078051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1058965760 :
    ThetaLowerSegment 1058965760 1059031296 (105892627602693 / 100000) (4235967603889 / 4000) := by
  exact
    packedTile32768 1058965760 1059031296 13 3158 32541 30 _ _ (1039027 / 50000) (2078057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059031296 :
    ThetaLowerSegment 1059031296 1059096832 (4235967603889 / 4000) (26476422048493 / 25000) := by
  exact
    packedTile32768 1059031296 1059096832 13 3127 32542 30 _ _ (2078061 / 100000) (129879 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059096832 :
    ThetaLowerSegment 1059096832 1059162368 (26476422048493 / 25000) (52956129520913 / 50000) := by
  exact
    packedTile32768 1059096832 1059162368 13 3162 32543 30 _ _ (2078067 / 100000) (207807 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059162368 :
    ThetaLowerSegment 1059162368 1059227904 (52956129520913 / 50000)
      (105918761332243 / 100000) := by
  exact
    packedTile32768 1059162368 1059227904 13 3129 32544 30 _ _ (2078073 / 100000) (519519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059227904 :
    ThetaLowerSegment 1059227904 1059293440 (105918761332243 / 100000)
      (105925265719513 / 100000) := by
  exact
    packedTile32768 1059227904 1059293440 13 3130 32545 30 _ _ (2078079 / 100000) (1039041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059293440 :
    ThetaLowerSegment 1059293440 1059358976 (105925265719513 / 100000)
      (105931919747683 / 100000) := by
  exact
    packedTile32768 1059293440 1059358976 13 3202 32546 30 _ _ (415617 / 20000) (259761 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059358976 :
    ThetaLowerSegment 1059358976 1059424512 (105931919747683 / 100000)
      (105938420016331 / 100000) := by
  exact
    packedTile32768 1059358976 1059424512 13 3128 32547 30 _ _ (2078091 / 100000) (1039047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059424512 :
    ThetaLowerSegment 1059424512 1059490048 (105938420016331 / 100000)
      (105944924463071 / 100000) := by
  exact
    packedTile32768 1059424512 1059490048 13 3130 32548 30 _ _ (1039049 / 50000) (2078101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059490048 :
    ThetaLowerSegment 1059490048 1059555584 (105944924463071 / 100000)
      (105951516208959 / 100000) := by
  exact
    packedTile32768 1059490048 1059555584 13 3172 32549 30 _ _ (259763 / 12500) (2078107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059555584 :
    ThetaLowerSegment 1059555584 1059621120 (105951516208959 / 100000)
      (105958213957489 / 100000) := by
  exact
    packedTile32768 1059555584 1059621120 13 3223 32550 30 _ _ (207811 / 10000) (2078113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059621120 :
    ThetaLowerSegment 1059621120 1059686656 (105958213957489 / 100000)
      (105964618711001 / 100000) := by
  exact
    packedTile32768 1059621120 1059686656 13 3082 32551 30 _ _ (519529 / 25000) (2078119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059686656 :
    ThetaLowerSegment 1059686656 1059752192 (105964618711001 / 100000)
      (105971289482621 / 100000) := by
  exact
    packedTile32768 1059686656 1059752192 13 3210 32552 30 _ _ (1039061 / 50000) (665 / 32)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059752192 :
    ThetaLowerSegment 1059752192 1059817728 (105971289482621 / 100000) (1324723490371 / 1250) := by
  exact
    packedTile32768 1059752192 1059817728 13 3171 32553 30 _ _ (2078129 / 100000) (519533 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059817728 :
    ThetaLowerSegment 1059817728 1059883264 (1324723490371 / 1250) (4239375933567 / 4000) := by
  exact
    packedTile32768 1059817728 1059883264 13 3137 32554 30 _ _ (415627 / 20000) (1039069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059883264 :
    ThetaLowerSegment 1059883264 1059948800 (4239375933567 / 4000) (105990807326019 / 100000) := by
  exact
    packedTile32768 1059883264 1059948800 13 3084 32555 30 _ _ (2078141 / 100000) (64942 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1059948800 :
    ThetaLowerSegment 1059948800 1060014336 (105990807326019 / 100000)
      (13249679836637 / 12500) := by
  exact
    packedTile32768 1059948800 1060014336 13 3191 32556 30 _ _ (2078147 / 100000) (41563 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060014336 :
    ThetaLowerSegment 1060014336 1060079872 (13249679836637 / 12500)
      (106003962015363 / 100000) := by
  exact
    packedTile32768 1060014336 1060079872 13 3139 32557 30 _ _ (2078153 / 100000) (519539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060079872 :
    ThetaLowerSegment 1060079872 1060145408 (106003962015363 / 100000)
      (106010479125123 / 100000) := by
  exact
    packedTile32768 1060079872 1060145408 13 3136 32558 30 _ _ (25977 / 1250) (2078163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060145408 :
    ThetaLowerSegment 1060145408 1060210944 (106010479125123 / 100000)
      (106017058598679 / 100000) := by
  exact
    packedTile32768 1060145408 1060210944 13 3166 32559 30 _ _ (1039083 / 50000) (2078169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060210944 :
    ThetaLowerSegment 1060210944 1060276480 (106017058598679 / 100000)
      (106023613153167 / 100000) := by
  exact
    packedTile32768 1060210944 1060276480 13 3154 32560 30 _ _ (519543 / 25000) (83127 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060276480 :
    ThetaLowerSegment 1060276480 1060342016 (106023613153167 / 100000)
      (106030144866621 / 100000) := by
  exact
    packedTile32768 1060276480 1060342016 13 3143 32561 30 _ _ (1039089 / 50000) (2078181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060342016 :
    ThetaLowerSegment 1060342016 1060407552 (106030144866621 / 100000)
      (21207349035801 / 20000) := by
  exact
    packedTile32768 1060342016 1060407552 13 3176 32562 30 _ _ (259773 / 12500) (2078187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060407552 :
    ThetaLowerSegment 1060407552 1060473088 (21207349035801 / 20000) (21208647904551 / 20000) := by
  exact
    packedTile32768 1060407552 1060473088 13 3125 32563 30 _ _ (207819 / 10000) (2078193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060473088 :
    ThetaLowerSegment 1060473088 1060538624 (21208647904551 / 20000) (10604987936217 / 10000) := by
  exact
    packedTile32768 1060473088 1060538624 13 3195 32564 30 _ _ (2078197 / 100000) (10391 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060538624 :
    ThetaLowerSegment 1060538624 1060604160 (10604987936217 / 10000)
      (106056340495297 / 100000) := by
  exact
    packedTile32768 1060538624 1060604160 13 3109 32565 30 _ _ (2078203 / 100000) (1039103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060604160 :
    ThetaLowerSegment 1060604160 1060669696 (106056340495297 / 100000) (3314462161807 / 3125) := by
  exact
    packedTile32768 1060604160 1060669696 13 3103 32566 30 _ _ (2078209 / 100000) (519553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060669696 :
    ThetaLowerSegment 1060669696 1060735232 (3314462161807 / 3125) (106069304381849 / 100000) := by
  exact
    packedTile32768 1060669696 1060735232 13 3135 32567 30 _ _ (415643 / 20000) (1039109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060735232 :
    ThetaLowerSegment 1060735232 1060800768 (106069304381849 / 100000) (4243034529893 / 4000) := by
  exact
    packedTile32768 1060735232 1060800768 13 3156 32568 30 _ _ (2078221 / 100000) (129889 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060800768 :
    ThetaLowerSegment 1060800768 1060866304 (4243034529893 / 4000) (106082467852731 / 100000) := by
  exact
    packedTile32768 1060800768 1060866304 13 3178 32569 30 _ _ (2078227 / 100000) (207823 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060866304 :
    ThetaLowerSegment 1060866304 1060931840 (106082467852731 / 100000) (4243561901663 / 4000) := by
  exact
    packedTile32768 1060866304 1060931840 13 3166 32570 30 _ _ (1039117 / 50000) (2078237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060931840 :
    ThetaLowerSegment 1060931840 1060997376 (4243561901663 / 4000) (21219124202939 / 20000) := by
  exact
    packedTile32768 1060931840 1060997376 13 3163 32571 30 _ _ (12989 / 625) (2078243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1060997376 :
    ThetaLowerSegment 1060997376 1061062912 (21219124202939 / 20000)
      (106102109298707 / 100000) := by
  exact
    packedTile32768 1060997376 1061062912 13 3122 32572 30 _ _ (1039123 / 50000) (2078249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061062912 :
    ThetaLowerSegment 1061062912 1061128448 (106102109298707 / 100000)
      (106108655792507 / 100000) := by
  exact
    packedTile32768 1061062912 1061128448 13 3150 32573 30 _ _ (519563 / 25000) (415651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061128448 :
    ThetaLowerSegment 1061128448 1061193984 (106108655792507 / 100000)
      (106115260496431 / 100000) := by
  exact
    packedTile32768 1061128448 1061193984 13 3178 32574 30 _ _ (1039129 / 50000) (2078261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061193984 :
    ThetaLowerSegment 1061193984 1061259520 (106115260496431 / 100000)
      (106121744683231 / 100000) := by
  exact
    packedTile32768 1061193984 1061259520 13 3120 32575 30 _ _ (415653 / 20000) (519567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061259520 :
    ThetaLowerSegment 1061259520 1061325056 (106121744683231 / 100000) (3316508126963 / 3125) := by
  exact
    packedTile32768 1061259520 1061325056 13 3135 32576 30 _ _ (2078271 / 100000) (1039137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061325056 :
    ThetaLowerSegment 1061325056 1061390592 (3316508126963 / 3125) (106134850279183 / 100000) := by
  exact
    packedTile32768 1061325056 1061390592 13 3171 32577 30 _ _ (2078277 / 100000) (51957 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061390592 :
    ThetaLowerSegment 1061390592 1061456128 (106134850279183 / 100000)
      (21228276880187 / 20000) := by
  exact
    packedTile32768 1061390592 1061456128 13 3144 32578 30 _ _ (2078283 / 100000) (1039143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061456128 :
    ThetaLowerSegment 1061456128 1061521664 (21228276880187 / 20000)
      (106147839566569 / 100000) := by
  exact
    packedTile32768 1061456128 1061521664 13 3106 32579 30 _ _ (2078289 / 100000) (519573 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061521664 :
    ThetaLowerSegment 1061521664 1061587200 (106147839566569 / 100000)
      (106154398665589 / 100000) := by
  exact
    packedTile32768 1061521664 1061587200 13 3156 32581 30 _ _ (415659 / 20000) (1039149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061587200 :
    ThetaLowerSegment 1061587200 1061652736 (106154398665589 / 100000)
      (106160855949903 / 100000) := by
  exact
    packedTile32768 1061587200 1061652736 13 3107 32582 30 _ _ (1039151 / 50000) (415661 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061652736 :
    ThetaLowerSegment 1061652736 1061718272 (106160855949903 / 100000)
      (21233498813131 / 20000) := by
  exact
    packedTile32768 1061652736 1061718272 13 3194 32583 30 _ _ (519577 / 25000) (2078311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061718272 :
    ThetaLowerSegment 1061718272 1061783808 (21233498813131 / 20000)
      (106173980483649 / 100000) := by
  exact
    packedTile32768 1061718272 1061783808 13 3121 32584 30 _ _ (1039157 / 50000) (2078317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061783808 :
    ThetaLowerSegment 1061783808 1061849344 (106173980483649 / 100000)
      (106180566679729 / 100000) := by
  exact
    packedTile32768 1061783808 1061849344 13 3169 32585 30 _ _ (25979 / 1250) (2078323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061849344 :
    ThetaLowerSegment 1061849344 1061914880 (106180566679729 / 100000)
      (106187169521431 / 100000) := by
  exact
    packedTile32768 1061849344 1061914880 13 3177 32586 30 _ _ (1039163 / 50000) (2078329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061914880 :
    ThetaLowerSegment 1061914880 1061980416 (106187169521431 / 100000)
      (21238758633103 / 20000) := by
  exact
    packedTile32768 1061914880 1061980416 13 3187 32587 30 _ _ (519583 / 25000) (415667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1061980416 :
    ThetaLowerSegment 1061980416 1062045952 (21238758633103 / 20000) (53100168927513 / 50000) := by
  exact
    packedTile32768 1061980416 1062045952 13 3149 32588 30 _ _ (2078339 / 100000) (1039171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062045952 :
    ThetaLowerSegment 1062045952 1062111488 (53100168927513 / 50000)
      (106206836839841 / 100000) := by
  exact
    packedTile32768 1062045952 1062111488 13 3127 32589 30 _ _ (415669 / 20000) (519587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062111488 :
    ThetaLowerSegment 1062111488 1062177024 (106206836839841 / 100000)
      (53106734428941 / 50000) := by
  exact
    packedTile32768 1062111488 1062177024 13 3191 32590 30 _ _ (2078351 / 100000) (1039177 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062177024 :
    ThetaLowerSegment 1062177024 1062242560 (53106734428941 / 50000) (3319375490076 / 3125) := by
  exact
    packedTile32768 1062177024 1062242560 13 3150 32591 30 _ _ (2078357 / 100000) (51959 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062242560 :
    ThetaLowerSegment 1062242560 1062308096 (3319375490076 / 3125) (21245342017931 / 20000) := by
  exact
    packedTile32768 1062242560 1062308096 13 3221 32592 30 _ _ (2078363 / 100000) (1039183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062308096 :
    ThetaLowerSegment 1062308096 1062373632 (21245342017931 / 20000)
      (106233315146337 / 100000) := by
  exact
    packedTile32768 1062308096 1062373632 13 3178 32593 30 _ _ (2078369 / 100000) (519593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062373632 :
    ThetaLowerSegment 1062373632 1062439168 (106233315146337 / 100000)
      (106239737328177 / 100000) := by
  exact
    packedTile32768 1062373632 1062439168 13 3090 32594 30 _ _ (259797 / 12500) (2078379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062439168 :
    ThetaLowerSegment 1062439168 1062504704 (106239737328177 / 100000)
      (21249260587383 / 20000) := by
  exact
    packedTile32768 1062439168 1062504704 13 3159 32595 30 _ _ (1039191 / 50000) (415677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062504704 :
    ThetaLowerSegment 1062504704 1062570240 (21249260587383 / 20000)
      (106252793742639 / 100000) := by
  exact
    packedTile32768 1062504704 1062570240 13 3123 32596 30 _ _ (519597 / 25000) (2078391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062570240 :
    ThetaLowerSegment 1062570240 1062635776 (106252793742639 / 100000)
      (21251884348221 / 20000) := by
  exact
    packedTile32768 1062570240 1062635776 13 3189 32597 30 _ _ (1039197 / 50000) (2078397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062635776 :
    ThetaLowerSegment 1062635776 1062701312 (21251884348221 / 20000) (21253192908861 / 20000) := by
  exact
    packedTile32768 1062635776 1062701312 13 3148 32598 30 _ _ (2598 / 125) (2078403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062701312 :
    ThetaLowerSegment 1062701312 1062766848 (21253192908861 / 20000)
      (106272436700589 / 100000) := by
  exact
    packedTile32768 1062701312 1062766848 13 3114 32599 30 _ _ (1039203 / 50000) (2078409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062766848 :
    ThetaLowerSegment 1062766848 1062832384 (106272436700589 / 100000)
      (106278950446931 / 100000) := by
  exact
    packedTile32768 1062766848 1062832384 13 3134 32600 30 _ _ (2078413 / 100000) (129901 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062832384 :
    ThetaLowerSegment 1062832384 1062897920 (106278950446931 / 100000) (4251422060227 / 4000) := by
  exact
    packedTile32768 1062832384 1062897920 13 3176 32601 30 _ _ (2078419 / 100000) (1039211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062897920 :
    ThetaLowerSegment 1062897920 1062963456 (4251422060227 / 4000) (4251677124543 / 4000) := by
  exact
    packedTile32768 1062897920 1062963456 13 3068 32602 30 _ _ (83137 / 4000) (519607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1062963456 :
    ThetaLowerSegment 1062963456 1063028992 (4251677124543 / 4000) (106298545837879 / 100000) := by
  exact
    packedTile32768 1062963456 1063028992 13 3184 32603 30 _ _ (2078431 / 100000) (1039217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063028992 :
    ThetaLowerSegment 1063028992 1063094528 (106298545837879 / 100000)
      (106305072130059 / 100000) := by
  exact
    packedTile32768 1063028992 1063094528 13 3140 32604 30 _ _ (2078437 / 100000) (51961 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063094528 :
    ThetaLowerSegment 1063094528 1063160064 (106305072130059 / 100000)
      (106311569342877 / 100000) := by
  exact
    packedTile32768 1063094528 1063160064 13 3126 32605 30 _ _ (2078443 / 100000) (1039223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063160064 :
    ThetaLowerSegment 1063160064 1063225600 (106311569342877 / 100000)
      (106318118538827 / 100000) := by
  exact
    packedTile32768 1063160064 1063225600 13 3151 32606 30 _ _ (41569 / 2000) (2078453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063225600 :
    ThetaLowerSegment 1063225600 1063291136 (106318118538827 / 100000)
      (106324549281691 / 100000) := by
  exact
    packedTile32768 1063225600 1063291136 13 3094 32607 30 _ _ (259807 / 12500) (2078459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063291136 :
    ThetaLowerSegment 1063291136 1063356672 (106324549281691 / 100000)
      (106331065260061 / 100000) := by
  exact
    packedTile32768 1063291136 1063356672 13 3135 32608 30 _ _ (1039231 / 50000) (415693 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063356672 :
    ThetaLowerSegment 1063356672 1063422208 (106331065260061 / 100000)
      (106337635297409 / 100000) := by
  exact
    packedTile32768 1063356672 1063422208 13 3161 32609 30 _ _ (519617 / 25000) (2078471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063422208 :
    ThetaLowerSegment 1063422208 1063487744 (106337635297409 / 100000)
      (106344145077977 / 100000) := by
  exact
    packedTile32768 1063422208 1063487744 13 3132 32610 30 _ _ (1039237 / 50000) (2078477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063487744 :
    ThetaLowerSegment 1063487744 1063553280 (106344145077977 / 100000)
      (106350804527897 / 100000) := by
  exact
    packedTile32768 1063487744 1063553280 13 3204 32611 30 _ _ (25981 / 1250) (2078483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063553280 :
    ThetaLowerSegment 1063553280 1063618816 (106350804527897 / 100000)
      (21271517741893 / 20000) := by
  exact
    packedTile32768 1063553280 1063618816 13 3264 32612 30 _ _ (2078487 / 100000) (207849 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063618816 :
    ThetaLowerSegment 1063618816 1063684352 (21271517741893 / 20000)
      (106364202474191 / 100000) := by
  exact
    packedTile32768 1063618816 1063684352 13 3182 32613 30 _ _ (2078493 / 100000) (64953 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063684352 :
    ThetaLowerSegment 1063684352 1063749888 (106364202474191 / 100000)
      (53185340577787 / 50000) := by
  exact
    packedTile32768 1063684352 1063749888 13 3117 32614 30 _ _ (2078499 / 100000) (1039251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063749888 :
    ThetaLowerSegment 1063749888 1063815424 (53185340577787 / 50000) (53188620458677 / 50000) := by
  exact
    packedTile32768 1063749888 1063815424 13 3156 32615 30 _ _ (415701 / 20000) (519627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063815424 :
    ThetaLowerSegment 1063815424 1063880960 (53188620458677 / 50000)
      (106383777834449 / 100000) := by
  exact
    packedTile32768 1063815424 1063880960 13 3145 32616 30 _ _ (2078511 / 100000) (1039257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063880960 :
    ThetaLowerSegment 1063880960 1063946496 (106383777834449 / 100000)
      (13298781551863 / 12500) := by
  exact
    packedTile32768 1063880960 1063946496 13 3115 32617 30 _ _ (2078517 / 100000) (51963 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1063946496 :
    ThetaLowerSegment 1063946496 1064012032 (13298781551863 / 12500) (3324897394517 / 3125) := by
  exact
    packedTile32768 1063946496 1064012032 13 3110 32618 30 _ _ (519631 / 25000) (2078527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064012032 :
    ThetaLowerSegment 1064012032 1064077568 (3324897394517 / 3125) (3325101090457 / 3125) := by
  exact
    packedTile32768 1064012032 1064077568 13 3136 32619 30 _ _ (207853 / 10000) (2078533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064077568 :
    ThetaLowerSegment 1064077568 1064143104 (3325101090457 / 3125) (1330124772781 / 1250) := by
  exact
    packedTile32768 1064077568 1064143104 13 3246 32620 30 _ _ (259817 / 12500) (2078539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064143104 :
    ThetaLowerSegment 1064143104 1064208640 (1330124772781 / 1250) (26604144778697 / 25000) := by
  exact
    packedTile32768 1064143104 1064208640 13 3174 32621 30 _ _ (1039271 / 50000) (415709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064208640 :
    ThetaLowerSegment 1064208640 1064274176 (26604144778697 / 25000) (2660582268657 / 2500) := by
  exact
    packedTile32768 1064208640 1064274176 13 3229 32622 30 _ _ (519637 / 25000) (2078551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064274176 :
    ThetaLowerSegment 1064274176 1064339712 (2660582268657 / 2500) (2660748552977 / 2500) := by
  exact
    packedTile32768 1064274176 1064339712 13 3200 32623 30 _ _ (1039277 / 50000) (2078557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064339712 :
    ThetaLowerSegment 1064339712 1064405248 (2660748552977 / 2500) (532182136147 / 500) := by
  exact
    packedTile32768 1064339712 1064405248 13 3120 32624 30 _ _ (2078561 / 100000) (519641 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064405248 :
    ThetaLowerSegment 1064405248 1064470784 (532182136147 / 500) (26610730168177 / 25000) := by
  exact
    packedTile32768 1064405248 1064470784 13 3124 32625 30 _ _ (2078567 / 100000) (207857 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064470784 :
    ThetaLowerSegment 1064470784 1064536320 (26610730168177 / 25000) (53224813074603 / 50000) := by
  exact
    packedTile32768 1064470784 1064536320 13 3226 32626 30 _ _ (2078573 / 100000) (129911 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064536320 :
    ThetaLowerSegment 1064536320 1064601856 (53224813074603 / 50000)
      (106456163280161 / 100000) := by
  exact
    packedTile32768 1064536320 1064601856 13 3145 32627 30 _ _ (2078579 / 100000) (1039291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064601856 :
    ThetaLowerSegment 1064601856 1064667392 (106456163280161 / 100000)
      (106462885424051 / 100000) := by
  exact
    packedTile32768 1064601856 1064667392 13 3234 32628 30 _ _ (415717 / 20000) (519647 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064667392 :
    ThetaLowerSegment 1064667392 1064732928 (106462885424051 / 100000)
      (10646947247893 / 10000) := by
  exact
    packedTile32768 1064667392 1064732928 13 3169 32629 30 _ _ (2078591 / 100000) (1039297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064732928 :
    ThetaLowerSegment 1064732928 1064798464 (10646947247893 / 10000)
      (106476101124763 / 100000) := by
  exact
    packedTile32768 1064732928 1064798464 13 3189 32630 30 _ _ (2078597 / 100000) (10393 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064798464 :
    ThetaLowerSegment 1064798464 1064864000 (106476101124763 / 100000)
      (106482777600811 / 100000) := by
  exact
    packedTile32768 1064798464 1064864000 13 3212 32631 30 _ _ (519651 / 25000) (2078607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064864000 :
    ThetaLowerSegment 1064864000 1064929536 (106482777600811 / 100000)
      (106489294043161 / 100000) := by
  exact
    packedTile32768 1064864000 1064929536 13 3135 32632 30 _ _ (207861 / 10000) (2078613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064929536 :
    ThetaLowerSegment 1064929536 1064995072 (106489294043161 / 100000)
      (106495802189857 / 100000) := by
  exact
    packedTile32768 1064929536 1064995072 13 3131 32633 30 _ _ (259827 / 12500) (2078619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1064995072 :
    ThetaLowerSegment 1064995072 1065060608 (106495802189857 / 100000)
      (106502331141559 / 100000) := by
  exact
    packedTile32768 1064995072 1065060608 13 3141 32634 30 _ _ (1039311 / 50000) (16629 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065060608 :
    ThetaLowerSegment 1065060608 1065126144 (106502331141559 / 100000)
      (106508745787567 / 100000) := by
  exact
    packedTile32768 1065060608 1065126144 13 3086 32635 30 _ _ (519657 / 25000) (2078631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065126144 :
    ThetaLowerSegment 1065126144 1065191680 (106508745787567 / 100000)
      (106515208260673 / 100000) := by
  exact
    packedTile32768 1065126144 1065191680 13 3109 32636 30 _ _ (1039317 / 50000) (2078637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065191680 :
    ThetaLowerSegment 1065191680 1065257216 (106515208260673 / 100000)
      (106521785080797 / 100000) := by
  exact
    packedTile32768 1065191680 1065257216 13 3164 32637 30 _ _ (2078641 / 100000) (519661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065257216 :
    ThetaLowerSegment 1065257216 1065322752 (106521785080797 / 100000)
      (106528353605317 / 100000) := by
  exact
    packedTile32768 1065257216 1065322752 13 3160 32638 30 _ _ (2078647 / 100000) (41573 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065322752 :
    ThetaLowerSegment 1065322752 1065339136 (106528353605317 / 100000)
      (53264996831267 / 50000) := by
  exact
    packedTile32768 1065322752 1065339136 11 789 32639 30 _ _ (2078653 / 100000) (64958 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1065339136 :
    ThetaLowerSegment 1065339136 1065341184 (53264996831267 / 50000) (13316273891833 / 12500) := by
  exact
    packedTile32768 1065339136 1065341184 8 95 32639 30 _ _ (1039327 / 50000) (2078657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1033341184_1065341184 :
    ThetaLowerSegment 1033341184 1065341184 (103330508404191 / 100000)
      (13316273891833 / 12500) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1033341184 cell1033406720)
                    (ThetaLowerSegment.join cell1033472256 cell1033537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1033603328 cell1033668864)
                    (ThetaLowerSegment.join cell1033734400 cell1033799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1033865472 cell1033931008)
                    (ThetaLowerSegment.join cell1033996544 cell1034062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1034127616 cell1034193152)
                    (ThetaLowerSegment.join cell1034258688 cell1034324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1034389760 cell1034455296)
                    (ThetaLowerSegment.join cell1034520832 cell1034586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1034651904 cell1034717440)
                    (ThetaLowerSegment.join cell1034782976 cell1034848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1034914048 cell1034979584)
                    (ThetaLowerSegment.join cell1035045120 cell1035110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1035176192 cell1035241728)
                    (ThetaLowerSegment.join cell1035307264 cell1035372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1035438336 cell1035503872)
                    (ThetaLowerSegment.join cell1035569408 cell1035634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1035700480 cell1035766016)
                    (ThetaLowerSegment.join cell1035831552 cell1035897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1035962624 cell1036028160)
                    (ThetaLowerSegment.join cell1036093696 cell1036159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1036224768 cell1036290304)
                    (ThetaLowerSegment.join cell1036355840 cell1036421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1036486912 cell1036552448)
                    (ThetaLowerSegment.join cell1036617984 cell1036683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1036749056 cell1036814592)
                    (ThetaLowerSegment.join cell1036880128 cell1036945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1037011200 cell1037076736)
                    (ThetaLowerSegment.join cell1037142272 cell1037207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1037273344 cell1037338880)
                    (ThetaLowerSegment.join cell1037404416 cell1037469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1037535488 cell1037601024)
                    (ThetaLowerSegment.join cell1037666560 cell1037732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1037797632 cell1037863168)
                    (ThetaLowerSegment.join cell1037928704 cell1037994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1038059776 cell1038125312)
                    (ThetaLowerSegment.join cell1038190848 cell1038256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1038321920 cell1038387456)
                    (ThetaLowerSegment.join cell1038452992 cell1038518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1038584064 cell1038649600)
                    (ThetaLowerSegment.join cell1038715136 cell1038780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1038846208 cell1038911744)
                    (ThetaLowerSegment.join cell1038977280 cell1039042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1039108352 cell1039173888)
                    (ThetaLowerSegment.join cell1039239424 cell1039304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1039370496 cell1039436032)
                    (ThetaLowerSegment.join cell1039501568 cell1039567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1039632640 cell1039698176)
                    (ThetaLowerSegment.join cell1039763712 cell1039829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1039894784 cell1039960320)
                    (ThetaLowerSegment.join cell1040025856 cell1040091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1040156928 cell1040222464)
                    (ThetaLowerSegment.join cell1040353536 cell1040484608))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1040615680 cell1040681216)
                    (ThetaLowerSegment.join cell1040746752 cell1040812288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1040877824 cell1041008896)
                    (ThetaLowerSegment.join cell1041074432 cell1041139968))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1041205504 cell1041271040)
                    (ThetaLowerSegment.join cell1041336576 cell1041402112)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1041467648 cell1041533184)
                    (ThetaLowerSegment.join cell1041598720 cell1041664256))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1041795328 cell1041926400)
                    (ThetaLowerSegment.join cell1042057472 cell1042188544)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1042319616 cell1042450688)
                    (ThetaLowerSegment.join cell1042581760 cell1042712832))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1042843904 cell1042974976)
                    (ThetaLowerSegment.join cell1043106048 cell1043237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1043368192 cell1043499264)
                    (ThetaLowerSegment.join cell1043630336 cell1043761408))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1043892480 cell1044023552)
                    (ThetaLowerSegment.join cell1044154624 cell1044285696))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1044416768 cell1044547840)
                    (ThetaLowerSegment.join cell1044678912 cell1044809984))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1044941056 cell1045072128)
                    (ThetaLowerSegment.join cell1045137664 cell1045203200)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1045268736 cell1045334272)
                    (ThetaLowerSegment.join cell1045399808 cell1045465344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1045530880 cell1045596416)
                    (ThetaLowerSegment.join cell1045661952 cell1045727488)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1045793024 cell1045858560)
                    (ThetaLowerSegment.join cell1045924096 cell1045989632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1046055168 cell1046120704)
                    (ThetaLowerSegment.join cell1046251776 cell1046317312)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1046382848 cell1046513920)
                    (ThetaLowerSegment.join cell1046579456 cell1046710528))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1046776064 cell1046841600)
                    (ThetaLowerSegment.join cell1046907136 cell1046972672))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1047038208 cell1047103744)
                    (ThetaLowerSegment.join cell1047169280 cell1047234816))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1047300352 cell1047365888)
                    (ThetaLowerSegment.join cell1047431424 cell1047496960)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1047562496 cell1047628032)
                    (ThetaLowerSegment.join cell1047693568 cell1047759104))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1047824640 cell1047890176)
                    (ThetaLowerSegment.join cell1047955712 cell1048021248))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1048086784 cell1048152320)
                    (ThetaLowerSegment.join cell1048217856 cell1048283392))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1048348928 cell1048414464)
                    (ThetaLowerSegment.join cell1048480000 cell1048545536)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1048611072 cell1048676608)
                    (ThetaLowerSegment.join cell1048742144 cell1048807680))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1048873216 cell1048938752)
                    (ThetaLowerSegment.join cell1049004288 cell1049069824))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1049135360 cell1049200896)
                    (ThetaLowerSegment.join cell1049266432 cell1049331968))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1049397504 cell1049463040)
                    (ThetaLowerSegment.join cell1049528576 cell1049594112)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1049659648 cell1049725184)
                    (ThetaLowerSegment.join cell1049790720 cell1049856256))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1049921792 cell1049987328)
                    (ThetaLowerSegment.join cell1050052864 cell1050118400)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1050183936 cell1050249472)
                    (ThetaLowerSegment.join cell1050315008 cell1050380544))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1050446080 cell1050511616)
                    (ThetaLowerSegment.join cell1050577152 cell1050642688)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1050708224 cell1050773760)
                    (ThetaLowerSegment.join cell1050839296 cell1050904832))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1050970368 cell1051035904)
                    (ThetaLowerSegment.join cell1051101440 cell1051166976))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1051232512 cell1051298048)
                    (ThetaLowerSegment.join cell1051363584 cell1051429120))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1051494656 cell1051560192)
                    (ThetaLowerSegment.join cell1051625728 cell1051691264)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1051756800 cell1051822336)
                    (ThetaLowerSegment.join cell1051887872 cell1051953408))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1052018944 cell1052084480)
                    (ThetaLowerSegment.join cell1052150016 cell1052215552))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1052281088 cell1052346624)
                    (ThetaLowerSegment.join cell1052412160 cell1052477696))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1052543232 cell1052608768)
                    (ThetaLowerSegment.join cell1052674304 cell1052739840)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1052805376 cell1052870912)
                    (ThetaLowerSegment.join cell1052936448 cell1053001984))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1053067520 cell1053133056)
                    (ThetaLowerSegment.join cell1053198592 cell1053264128))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1053329664 cell1053395200)
                    (ThetaLowerSegment.join cell1053460736 cell1053526272))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1053591808 cell1053657344)
                    (ThetaLowerSegment.join cell1053722880 cell1053788416)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1053853952 cell1053919488)
                    (ThetaLowerSegment.join cell1053985024 cell1054050560))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1054116096 cell1054181632)
                    (ThetaLowerSegment.join cell1054247168 cell1054312704)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1054378240 cell1054443776)
                    (ThetaLowerSegment.join cell1054509312 cell1054574848))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1054640384 cell1054705920)
                    (ThetaLowerSegment.join cell1054771456 cell1054836992)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1054902528 cell1054968064)
                    (ThetaLowerSegment.join cell1055033600 cell1055099136))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1055164672 cell1055230208)
                    (ThetaLowerSegment.join cell1055295744 cell1055361280))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1055426816 cell1055492352)
                    (ThetaLowerSegment.join cell1055557888 cell1055623424))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1055688960 cell1055754496)
                    (ThetaLowerSegment.join cell1055820032 cell1055885568)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1055951104 cell1056016640)
                    (ThetaLowerSegment.join cell1056082176 cell1056147712))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1056213248 cell1056278784)
                    (ThetaLowerSegment.join cell1056344320 cell1056409856))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1056475392 cell1056540928)
                    (ThetaLowerSegment.join cell1056606464 cell1056672000))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1056737536 cell1056803072)
                    (ThetaLowerSegment.join cell1056868608 cell1056934144)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1056999680 cell1057065216)
                    (ThetaLowerSegment.join cell1057130752 cell1057196288))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1057261824 cell1057327360)
                    (ThetaLowerSegment.join cell1057392896 cell1057458432))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1057523968 cell1057589504)
                    (ThetaLowerSegment.join cell1057655040 cell1057720576))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1057786112 cell1057851648)
                    (ThetaLowerSegment.join cell1057917184 cell1057982720)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1058048256 cell1058113792)
                    (ThetaLowerSegment.join cell1058179328 cell1058244864))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1058310400 cell1058375936)
                    (ThetaLowerSegment.join cell1058441472 cell1058507008)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1058572544 cell1058638080)
                    (ThetaLowerSegment.join cell1058703616 cell1058769152))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1058834688 cell1058900224)
                    (ThetaLowerSegment.join cell1058965760 cell1059031296)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1059096832 cell1059162368)
                    (ThetaLowerSegment.join cell1059227904 cell1059293440))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1059358976 cell1059424512)
                    (ThetaLowerSegment.join cell1059490048 cell1059555584))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1059621120 cell1059686656)
                    (ThetaLowerSegment.join cell1059752192 cell1059817728))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1059883264 cell1059948800)
                    (ThetaLowerSegment.join cell1060014336 cell1060079872)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1060145408 cell1060210944)
                    (ThetaLowerSegment.join cell1060276480 cell1060342016))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1060407552 cell1060473088)
                    (ThetaLowerSegment.join cell1060538624 cell1060604160)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1060669696 cell1060735232)
                    (ThetaLowerSegment.join cell1060800768 cell1060866304))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1060931840 cell1060997376)
                    (ThetaLowerSegment.join cell1061062912 cell1061128448)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1061193984 cell1061259520)
                    (ThetaLowerSegment.join cell1061325056 cell1061390592))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1061456128 cell1061521664)
                    (ThetaLowerSegment.join cell1061587200 cell1061652736))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1061718272 cell1061783808)
                    (ThetaLowerSegment.join cell1061849344 cell1061914880))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1061980416 cell1062045952)
                    (ThetaLowerSegment.join cell1062111488 cell1062177024)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1062242560 cell1062308096)
                    (ThetaLowerSegment.join cell1062373632 cell1062439168))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1062504704 cell1062570240)
                    (ThetaLowerSegment.join cell1062635776 cell1062701312)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1062766848 cell1062832384)
                    (ThetaLowerSegment.join cell1062897920 cell1062963456))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1063028992 cell1063094528)
                    (ThetaLowerSegment.join cell1063160064 cell1063225600)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1063291136 cell1063356672)
                    (ThetaLowerSegment.join cell1063422208 cell1063487744))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1063553280 cell1063618816)
                    (ThetaLowerSegment.join cell1063684352 cell1063749888))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1063815424 cell1063880960)
                    (ThetaLowerSegment.join cell1063946496 cell1064012032))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1064077568 cell1064143104)
                    (ThetaLowerSegment.join cell1064208640 cell1064274176)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1064339712 cell1064405248)
                    (ThetaLowerSegment.join cell1064470784 cell1064536320))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell1064601856 cell1064667392)
                    (ThetaLowerSegment.join cell1064732928 cell1064798464))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1064864000 cell1064929536)
                (ThetaLowerSegment.join cell1064995072 cell1065060608))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1065126144 cell1065191680)
                (ThetaLowerSegment.join cell1065257216 cell1065322752)))
            cell1065339136))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
