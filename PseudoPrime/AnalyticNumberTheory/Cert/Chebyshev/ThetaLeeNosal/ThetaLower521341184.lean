/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 521341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell489341184 :
    ThetaLowerSegment 489341184 489406720 (9786377090559 / 20000) (48938500282731 / 100000) := by
  exact
    packedTile32768 489341184 489406720 13 3306 22121 29 _ _ (250107 / 12500) (2000859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489406720 :
    ThetaLowerSegment 489406720 489472256 (48938500282731 / 100000) (1529535286304 / 3125) := by
  exact
    packedTile32768 489406720 489472256 13 3313 22122 29 _ _ (2000869 / 100000) (250109 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489472256 :
    ThetaLowerSegment 489472256 489537792 (1529535286304 / 3125) (24475851029549 / 50000) := by
  exact
    packedTile32768 489472256 489537792 13 3285 22124 29 _ _ (1000441 / 50000) (400177 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489537792 :
    ThetaLowerSegment 489537792 489603328 (24475851029549 / 50000) (24479033454637 / 50000) := by
  exact
    packedTile32768 489537792 489603328 13 3181 22125 29 _ _ (62528 / 3125) (2000899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489603328 :
    ThetaLowerSegment 489603328 489668864 (24479033454637 / 50000) (24482302939943 / 50000) := by
  exact
    packedTile32768 489603328 489668864 13 3268 22126 29 _ _ (2000909 / 100000) (125057 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489668864 :
    ThetaLowerSegment 489668864 489734400 (24482302939943 / 50000) (3060698681791 / 6250) := by
  exact
    packedTile32768 489668864 489734400 13 3285 22128 29 _ _ (1000461 / 50000) (80037 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489734400 :
    ThetaLowerSegment 489734400 489799936 (3060698681791 / 6250) (6122215996523 / 12500) := by
  exact
    packedTile32768 489734400 489799936 13 3273 22129 29 _ _ (250117 / 12500) (2000939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489799936 :
    ThetaLowerSegment 489799936 489865472 (6122215996523 / 12500) (48984421146589 / 100000) := by
  exact
    packedTile32768 489799936 489865472 13 3345 22131 29 _ _ (2000949 / 100000) (250119 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489865472 :
    ThetaLowerSegment 489865472 489931008 (48984421146589 / 100000) (48990956291747 / 100000) := by
  exact
    packedTile32768 489865472 489931008 13 3266 22132 29 _ _ (2000963 / 100000) (1000483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489931008 :
    ThetaLowerSegment 489931008 489996544 (48990956291747 / 100000) (9799525108951 / 20000) := by
  exact
    packedTile32768 489931008 489996544 13 3333 22134 29 _ _ (125061 / 6250) (2000979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489996544 :
    ThetaLowerSegment 489996544 490062080 (9799525108951 / 20000) (12251053700383 / 25000) := by
  exact
    packedTile32768 489996544 490062080 13 3293 22135 29 _ _ (2000989 / 100000) (62531 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490062080 :
    ThetaLowerSegment 490062080 490127616 (12251053700383 / 25000) (49010752078333 / 100000) := by
  exact
    packedTile32768 490062080 490127616 13 3267 22137 29 _ _ (2001003 / 100000) (1000503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490127616 :
    ThetaLowerSegment 490127616 490193152 (49010752078333 / 100000) (49017357432149 / 100000) := by
  exact
    packedTile32768 490127616 490193152 13 3301 22138 29 _ _ (250127 / 12500) (2001019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490193152 :
    ThetaLowerSegment 490193152 490258688 (49017357432149 / 100000) (49023916808489 / 100000) := by
  exact
    packedTile32768 490193152 490258688 13 3278 22140 29 _ _ (200103 / 10000) (2001033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490258688 :
    ThetaLowerSegment 490258688 490324224 (49023916808489 / 100000) (12257624559729 / 25000) := by
  exact
    packedTile32768 490258688 490324224 13 3289 22141 29 _ _ (2001043 / 100000) (1000523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490324224 :
    ThetaLowerSegment 490324224 490389760 (12257624559729 / 25000) (12259247916409 / 25000) := by
  exact
    packedTile32768 490324224 490389760 13 3245 22143 29 _ _ (62533 / 3125) (2001059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490389760 :
    ThetaLowerSegment 490389760 490455296 (12259247916409 / 25000) (24521702547493 / 50000) := by
  exact
    packedTile32768 490389760 490455296 13 3205 22144 29 _ _ (200107 / 10000) (2001073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490455296 :
    ThetaLowerSegment 490455296 490520832 (24521702547493 / 50000) (245249623117 / 500) := by
  exact
    packedTile32768 490455296 490520832 13 3258 22146 29 _ _ (2001083 / 100000) (1000543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490520832 :
    ThetaLowerSegment 490520832 490586368 (245249623117 / 500) (6132054023449 / 12500) := by
  exact
    packedTile32768 490520832 490586368 13 3252 22147 29 _ _ (250137 / 12500) (2001099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490586368 :
    ThetaLowerSegment 490586368 490651904 (6132054023449 / 12500) (24531548942501 / 50000) := by
  exact
    packedTile32768 490586368 490651904 13 3331 22149 29 _ _ (200111 / 10000) (2001113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490651904 :
    ThetaLowerSegment 490651904 490717440 (24531548942501 / 50000) (392556828287 / 800) := by
  exact
    packedTile32768 490651904 490717440 13 3251 22150 29 _ _ (2001123 / 100000) (1000563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490717440 :
    ThetaLowerSegment 490717440 490782976 (392556828287 / 800) (49076263316483 / 100000) := by
  exact
    packedTile32768 490717440 490782976 13 3328 22152 29 _ _ (125071 / 6250) (2001139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490782976 :
    ThetaLowerSegment 490782976 490848512 (49076263316483 / 100000) (49082817082733 / 100000) := by
  exact
    packedTile32768 490782976 490848512 13 3275 22153 29 _ _ (40023 / 2000) (2001153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490848512 :
    ThetaLowerSegment 490848512 490914048 (49082817082733 / 100000) (49089304853179 / 100000) := by
  exact
    packedTile32768 490848512 490914048 13 3242 22155 29 _ _ (2001163 / 100000) (1000583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490914048 :
    ThetaLowerSegment 490914048 490979584 (49089304853179 / 100000) (9819168138799 / 20000) := by
  exact
    packedTile32768 490914048 490979584 13 3266 22156 29 _ _ (250147 / 12500) (2001179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell490979584 :
    ThetaLowerSegment 490979584 491045120 (9819168138799 / 20000) (9820481319677 / 20000) := by
  exact
    packedTile32768 490979584 491045120 13 3281 22158 29 _ _ (200119 / 10000) (2001193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491045120 :
    ThetaLowerSegment 491045120 491110656 (9820481319677 / 20000) (24554496278729 / 50000) := by
  exact
    packedTile32768 491045120 491110656 13 3291 22159 29 _ _ (2001203 / 100000) (1000603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491110656 :
    ThetaLowerSegment 491110656 491176192 (24554496278729 / 50000) (122789121513 / 250) := by
  exact
    packedTile32768 491110656 491176192 13 3326 22161 29 _ _ (2001217 / 100000) (100061 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491176192 :
    ThetaLowerSegment 491176192 491241728 (122789121513 / 250) (4912214659901 / 10000) := by
  exact
    packedTile32768 491176192 491241728 13 3247 22162 29 _ _ (200123 / 10000) (2001233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491241728 :
    ThetaLowerSegment 491241728 491307264 (4912214659901 / 10000) (24564343330567 / 50000) := by
  exact
    packedTile32768 491241728 491307264 13 3268 22163 29 _ _ (2001243 / 100000) (1000623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491307264 :
    ThetaLowerSegment 491307264 491372800 (24564343330567 / 50000) (49135184742613 / 100000) := by
  exact
    packedTile32768 491307264 491372800 13 3247 22165 29 _ _ (2001257 / 100000) (100063 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491372800 :
    ThetaLowerSegment 491372800 491438336 (49135184742613 / 100000) (49141828959013 / 100000) := by
  exact
    packedTile32768 491372800 491438336 13 3320 22166 29 _ _ (200127 / 10000) (2001273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491438336 :
    ThetaLowerSegment 491438336 491503872 (49141828959013 / 100000) (4914839116597 / 10000) := by
  exact
    packedTile32768 491438336 491503872 13 3279 22168 29 _ _ (2001283 / 100000) (1000643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491503872 :
    ThetaLowerSegment 491503872 491569408 (4914839116597 / 10000) (49154861359171 / 100000) := by
  exact
    packedTile32768 491503872 491569408 13 3233 22169 29 _ _ (2001297 / 100000) (20013 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491569408 :
    ThetaLowerSegment 491569408 491634944 (49154861359171 / 100000) (49161355610121 / 100000) := by
  exact
    packedTile32768 491569408 491634944 13 3245 22171 29 _ _ (200131 / 10000) (2001313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491634944 :
    ThetaLowerSegment 491634944 491700480 (49161355610121 / 100000) (49167939962791 / 100000) := by
  exact
    packedTile32768 491634944 491700480 13 3290 22172 29 _ _ (2001323 / 100000) (1000663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491700480 :
    ThetaLowerSegment 491700480 491766016 (49167939962791 / 100000) (2458724917207 / 5000) := by
  exact
    packedTile32768 491700480 491766016 13 3277 22174 29 _ _ (2001337 / 100000) (100067 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491766016 :
    ThetaLowerSegment 491766016 491831552 (2458724917207 / 5000) (2459047134557 / 5000) := by
  exact
    packedTile32768 491766016 491831552 13 3220 22175 29 _ _ (40027 / 2000) (2001353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491831552 :
    ThetaLowerSegment 491831552 491897088 (2459047134557 / 5000) (49187529176773 / 100000) := by
  exact
    packedTile32768 491831552 491897088 13 3291 22177 29 _ _ (2001363 / 100000) (1000683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491897088 :
    ThetaLowerSegment 491897088 491962624 (49187529176773 / 100000) (1537312113136 / 3125) := by
  exact
    packedTile32768 491897088 491962624 13 3227 22178 29 _ _ (2001377 / 100000) (100069 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell491962624 :
    ThetaLowerSegment 491962624 492028160 (1537312113136 / 3125) (6150072024529 / 12500) := by
  exact
    packedTile32768 491962624 492028160 13 3292 22180 29 _ _ (200139 / 10000) (2001393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492028160 :
    ThetaLowerSegment 492028160 492093696 (6150072024529 / 12500) (49207138796669 / 100000) := by
  exact
    packedTile32768 492028160 492093696 13 3279 22181 29 _ _ (2001403 / 100000) (1000703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492093696 :
    ThetaLowerSegment 492093696 492159232 (49207138796669 / 100000) (49213673419909 / 100000) := by
  exact
    packedTile32768 492093696 492159232 13 3265 22183 29 _ _ (250177 / 12500) (2001419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492159232 :
    ThetaLowerSegment 492159232 492224768 (49213673419909 / 100000) (49220336180379 / 100000) := by
  exact
    packedTile32768 492159232 492224768 13 3329 22184 29 _ _ (200143 / 10000) (2001433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492224768 :
    ThetaLowerSegment 492224768 492290304 (49220336180379 / 100000) (12306762755411 / 25000) := by
  exact
    packedTile32768 492224768 492290304 13 3355 22186 29 _ _ (2001443 / 100000) (1000723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492290304 :
    ThetaLowerSegment 492290304 492355840 (12306762755411 / 25000) (12308372926763 / 25000) := by
  exact
    packedTile32768 492290304 492355840 13 3218 22187 29 _ _ (125091 / 6250) (2001459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492355840 :
    ThetaLowerSegment 492355840 492421376 (12308372926763 / 25000) (24619937197441 / 50000) := by
  exact
    packedTile32768 492355840 492421376 13 3189 22189 29 _ _ (200147 / 10000) (2001473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492421376 :
    ThetaLowerSegment 492421376 492486912 (24619937197441 / 50000) (9849280246189 / 20000) := by
  exact
    packedTile32768 492421376 492486912 13 3261 22190 29 _ _ (2001483 / 100000) (1000743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492486912 :
    ThetaLowerSegment 492486912 492552448 (9849280246189 / 20000) (49252982149793 / 100000) := by
  exact
    packedTile32768 492486912 492552448 13 3288 22192 29 _ _ (250187 / 12500) (2001499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492552448 :
    ThetaLowerSegment 492552448 492617984 (49252982149793 / 100000) (49259555108633 / 100000) := by
  exact
    packedTile32768 492552448 492617984 13 3284 22193 29 _ _ (200151 / 10000) (2001513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492617984 :
    ThetaLowerSegment 492617984 492683520 (49259555108633 / 100000) (24633075063459 / 50000) := by
  exact
    packedTile32768 492617984 492683520 13 3295 22194 29 _ _ (2001523 / 100000) (1000763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492683520 :
    ThetaLowerSegment 492683520 492749056 (24633075063459 / 50000) (24636388606307 / 50000) := by
  exact
    packedTile32768 492683520 492749056 13 3311 22196 29 _ _ (62548 / 3125) (2001539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492749056 :
    ThetaLowerSegment 492749056 492814592 (24636388606307 / 50000) (3079959268829 / 6250) := by
  exact
    packedTile32768 492749056 492814592 13 3283 22197 29 _ _ (40031 / 2000) (2001553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492814592 :
    ThetaLowerSegment 492814592 492880128 (3079959268829 / 6250) (4928575730599 / 10000) := by
  exact
    packedTile32768 492814592 492880128 13 3202 22199 29 _ _ (2001563 / 100000) (1000783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492880128 :
    ThetaLowerSegment 492880128 492945664 (4928575730599 / 10000) (24646205272307 / 50000) := by
  exact
    packedTile32768 492880128 492945664 13 3324 22200 29 _ _ (250197 / 12500) (2001579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell492945664 :
    ThetaLowerSegment 492945664 493011200 (24646205272307 / 50000) (24649463859199 / 50000) := by
  exact
    packedTile32768 492945664 493011200 13 3256 22202 29 _ _ (2001589 / 100000) (250199 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493011200 :
    ThetaLowerSegment 493011200 493076736 (24649463859199 / 50000) (9861098194927 / 20000) := by
  exact
    packedTile32768 493011200 493076736 13 3279 22203 29 _ _ (2001603 / 100000) (1000803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493076736 :
    ThetaLowerSegment 493076736 493142272 (9861098194927 / 20000) (49311920165227 / 100000) := by
  exact
    packedTile32768 493076736 493142272 13 3212 22205 29 _ _ (125101 / 6250) (2001619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493142272 :
    ThetaLowerSegment 493142272 493207808 (49311920165227 / 100000) (49318441472509 / 100000) := by
  exact
    packedTile32768 493142272 493207808 13 3258 22206 29 _ _ (2001629 / 100000) (62551 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493207808 :
    ThetaLowerSegment 493207808 493273344 (49318441472509 / 100000) (24662522446383 / 50000) := by
  exact
    packedTile32768 493207808 493273344 13 3299 22208 29 _ _ (2001643 / 100000) (1000823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493273344 :
    ThetaLowerSegment 493273344 493338880 (24662522446383 / 50000) (24665826179611 / 50000) := by
  exact
    packedTile32768 493273344 493338880 13 3301 22209 29 _ _ (250207 / 12500) (2001659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493338880 :
    ThetaLowerSegment 493338880 493404416 (24665826179611 / 50000) (49338107741747 / 100000) := by
  exact
    packedTile32768 493338880 493404416 13 3225 22211 29 _ _ (2001669 / 100000) (250209 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493404416 :
    ThetaLowerSegment 493404416 493469952 (49338107741747 / 100000) (49344679263753 / 100000) := by
  exact
    packedTile32768 493404416 493469952 13 3283 22212 29 _ _ (1000841 / 50000) (400337 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493469952 :
    ThetaLowerSegment 493469952 493535488 (49344679263753 / 100000) (9870227747349 / 20000) := by
  exact
    packedTile32768 493469952 493535488 13 3227 22214 29 _ _ (62553 / 3125) (2001699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493535488 :
    ThetaLowerSegment 493535488 493601024 (9870227747349 / 20000) (78972455057 / 160) := by
  exact
    packedTile32768 493535488 493601024 13 3320 22215 29 _ _ (2001709 / 100000) (125107 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493601024 :
    ThetaLowerSegment 493601024 493666560 (78972455057 / 160) (49364358065673 / 100000) := by
  exact
    packedTile32768 493601024 493666560 13 3284 22217 29 _ _ (1000861 / 50000) (80069 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493666560 :
    ThetaLowerSegment 493666560 493732096 (49364358065673 / 100000) (9874177545701 / 20000) := by
  exact
    packedTile32768 493666560 493732096 13 3262 22218 29 _ _ (250217 / 12500) (2001739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493732096 :
    ThetaLowerSegment 493732096 493797632 (9874177545701 / 20000) (24688727733487 / 50000) := by
  exact
    packedTile32768 493732096 493797632 13 3281 22220 29 _ _ (2001749 / 100000) (250219 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493797632 :
    ThetaLowerSegment 493797632 493863168 (24688727733487 / 50000) (1543254730027 / 3125) := by
  exact
    packedTile32768 493797632 493863168 13 3345 22221 29 _ _ (1000881 / 50000) (400353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493863168 :
    ThetaLowerSegment 493863168 493928704 (1543254730027 / 3125) (24695376607407 / 50000) := by
  exact
    packedTile32768 493863168 493928704 13 3298 22223 29 _ _ (80071 / 4000) (1000889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493928704 :
    ThetaLowerSegment 493928704 493994240 (24695376607407 / 50000) (6174677396523 / 12500) := by
  exact
    packedTile32768 493928704 493994240 13 3330 22224 29 _ _ (2001789 / 100000) (62556 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell493994240 :
    ThetaLowerSegment 493994240 494059776 (6174677396523 / 12500) (24701967518847 / 50000) := by
  exact
    packedTile32768 493994240 494059776 13 3255 22225 29 _ _ (1000901 / 50000) (400361 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494059776 :
    ThetaLowerSegment 494059776 494125312 (24701967518847 / 50000) (49410406905589 / 100000) := by
  exact
    packedTile32768 494059776 494125312 13 3233 22227 29 _ _ (400363 / 20000) (1000909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494125312 :
    ThetaLowerSegment 494125312 494190848 (49410406905589 / 100000) (49416932864869 / 100000) := by
  exact
    packedTile32768 494125312 494190848 13 3260 22228 29 _ _ (500457 / 25000) (2001831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494190848 :
    ThetaLowerSegment 494190848 494256384 (49416932864869 / 100000) (49423346766637 / 100000) := by
  exact
    packedTile32768 494190848 494256384 13 3204 22230 29 _ _ (1000921 / 50000) (400369 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494256384 :
    ThetaLowerSegment 494256384 494321920 (49423346766637 / 100000) (49430040969757 / 100000) := by
  exact
    packedTile32768 494256384 494321920 13 3344 22231 29 _ _ (400371 / 20000) (1000929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494321920 :
    ThetaLowerSegment 494321920 494387456 (49430040969757 / 100000) (49436611100533 / 100000) := by
  exact
    packedTile32768 494321920 494387456 13 3282 22233 29 _ _ (500467 / 25000) (2001871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494387456 :
    ThetaLowerSegment 494387456 494452992 (49436611100533 / 100000) (49443143241499 / 100000) := by
  exact
    packedTile32768 494387456 494452992 13 3263 22234 29 _ _ (1000941 / 50000) (400377 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494452992 :
    ThetaLowerSegment 494452992 494518528 (49443143241499 / 100000) (24724851725707 / 50000) := by
  exact
    packedTile32768 494452992 494518528 13 3277 22236 29 _ _ (400379 / 20000) (1000949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494518528 :
    ThetaLowerSegment 494518528 494584064 (24724851725707 / 50000) (24728133853873 / 50000) := by
  exact
    packedTile32768 494518528 494584064 13 3279 22237 29 _ _ (500477 / 25000) (2001911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494584064 :
    ThetaLowerSegment 494584064 494649600 (24728133853873 / 50000) (12365701495433 / 25000) := by
  exact
    packedTile32768 494584064 494649600 13 3266 22239 29 _ _ (2001921 / 100000) (500481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494649600 :
    ThetaLowerSegment 494649600 494715136 (12365701495433 / 25000) (24734680158461 / 50000) := by
  exact
    packedTile32768 494649600 494715136 13 3274 22240 29 _ _ (400387 / 20000) (1000969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494715136 :
    ThetaLowerSegment 494715136 494780672 (24734680158461 / 50000) (24737938328831 / 50000) := by
  exact
    packedTile32768 494715136 494780672 13 3255 22242 29 _ _ (500487 / 25000) (2001951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494780672 :
    ThetaLowerSegment 494780672 494846208 (24737938328831 / 50000) (49482413060327 / 100000) := by
  exact
    packedTile32768 494780672 494846208 13 3265 22243 29 _ _ (2001961 / 100000) (500491 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494846208 :
    ThetaLowerSegment 494846208 494911744 (49482413060327 / 100000) (49488999554787 / 100000) := by
  exact
    packedTile32768 494846208 494911744 13 3290 22245 29 _ _ (1000987 / 50000) (2001977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494911744 :
    ThetaLowerSegment 494911744 494977280 (49488999554787 / 100000) (49495451962111 / 100000) := by
  exact
    packedTile32768 494911744 494977280 13 3223 22246 29 _ _ (500497 / 25000) (2001991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell494977280 :
    ThetaLowerSegment 494977280 495042816 (49495451962111 / 100000) (49502110617437 / 100000) := by
  exact
    packedTile32768 494977280 495042816 13 3326 22248 29 _ _ (2002001 / 100000) (500501 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495042816 :
    ThetaLowerSegment 495042816 495108352 (49502110617437 / 100000) (9901728237421 / 20000) := by
  exact
    packedTile32768 495042816 495108352 13 3262 22249 29 _ _ (1001007 / 50000) (2002017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495108352 :
    ThetaLowerSegment 495108352 495173888 (9901728237421 / 20000) (49515259888367 / 100000) := by
  exact
    packedTile32768 495108352 495173888 13 3306 22251 29 _ _ (2002027 / 100000) (200203 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495173888 :
    ThetaLowerSegment 495173888 495239424 (49515259888367 / 100000) (49521886640767 / 100000) := by
  exact
    packedTile32768 495173888 495239424 13 3310 22252 29 _ _ (50051 / 2500) (2002043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495239424 :
    ThetaLowerSegment 495239424 495304960 (49521886640767 / 100000) (1981139896923 / 4000) := by
  exact
    packedTile32768 495239424 495304960 13 3302 22253 29 _ _ (1001027 / 50000) (2002057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495304960 :
    ThetaLowerSegment 495304960 495370496 (1981139896923 / 4000) (9907032861237 / 20000) := by
  exact
    packedTile32768 495304960 495370496 13 3330 22255 29 _ _ (2002067 / 100000) (200207 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495370496 :
    ThetaLowerSegment 495370496 495436032 (9907032861237 / 20000) (9908325003669 / 20000) := by
  exact
    packedTile32768 495370496 495436032 13 3227 22256 29 _ _ (12513 / 625) (2002083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495436032 :
    ThetaLowerSegment 495436032 495501568 (9908325003669 / 20000) (12387079503811 / 25000) := by
  exact
    packedTile32768 495436032 495501568 13 3343 22258 29 _ _ (2002093 / 100000) (125131 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495501568 :
    ThetaLowerSegment 495501568 495567104 (12387079503811 / 25000) (49554762797677 / 100000) := by
  exact
    packedTile32768 495501568 495567104 13 3219 22259 29 _ _ (2002107 / 100000) (200211 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495567104 :
    ThetaLowerSegment 495567104 495632640 (49554762797677 / 100000) (49561283702517 / 100000) := by
  exact
    packedTile32768 495567104 495632640 13 3257 22261 29 _ _ (50053 / 2500) (2002123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495632640 :
    ThetaLowerSegment 495632640 495698176 (49561283702517 / 100000) (49567770613437 / 100000) := by
  exact
    packedTile32768 495632640 495698176 13 3240 22262 29 _ _ (2002133 / 100000) (250267 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495698176 :
    ThetaLowerSegment 495698176 495763712 (49567770613437 / 100000) (49574261570769 / 100000) := by
  exact
    packedTile32768 495698176 495763712 13 3242 22264 29 _ _ (1001073 / 50000) (2002149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495763712 :
    ThetaLowerSegment 495763712 495829248 (49574261570769 / 100000) (24790437350973 / 50000) := by
  exact
    packedTile32768 495763712 495829248 13 3303 22265 29 _ _ (2002159 / 100000) (1001081 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495829248 :
    ThetaLowerSegment 495829248 495894784 (24790437350973 / 50000) (24793736932077 / 50000) := by
  exact
    packedTile32768 495829248 495894784 13 3296 22267 29 _ _ (2002173 / 100000) (62568 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495894784 :
    ThetaLowerSegment 495894784 495960320 (24793736932077 / 50000) (1549817223577 / 3125) := by
  exact
    packedTile32768 495894784 495960320 13 3335 22268 29 _ _ (1001093 / 50000) (2002189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell495960320 :
    ThetaLowerSegment 495960320 496025856 (1549817223577 / 3125) (24800381207781 / 50000) := by
  exact
    packedTile32768 495960320 496025856 13 3302 22270 29 _ _ (2002199 / 100000) (1001101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496025856 :
    ThetaLowerSegment 496025856 496091392 (24800381207781 / 50000) (24803681854263 / 50000) := by
  exact
    packedTile32768 496025856 496091392 13 3297 22271 29 _ _ (500553 / 25000) (400443 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496091392 :
    ThetaLowerSegment 496091392 496156928 (24803681854263 / 50000) (24806921455931 / 50000) := by
  exact
    packedTile32768 496091392 496156928 13 3236 22273 29 _ _ (1001113 / 50000) (2002229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496156928 :
    ThetaLowerSegment 496156928 496222464 (24806921455931 / 50000) (49620376217719 / 100000) := by
  exact
    packedTile32768 496156928 496222464 13 3263 22274 29 _ _ (2002239 / 100000) (1001121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496222464 :
    ThetaLowerSegment 496222464 496288000 (49620376217719 / 100000) (49626855505191 / 100000) := by
  exact
    packedTile32768 496222464 496288000 13 3236 22276 29 _ _ (500563 / 25000) (400451 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496288000 :
    ThetaLowerSegment 496288000 496353536 (49626855505191 / 100000) (12408354231899 / 25000) := by
  exact
    packedTile32768 496288000 496353536 13 3277 22277 29 _ _ (400453 / 20000) (500567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496353536 :
    ThetaLowerSegment 496353536 496419072 (12408354231899 / 25000) (3102495771263 / 6250) := by
  exact
    packedTile32768 496353536 496419072 13 3254 22278 29 _ _ (1001139 / 50000) (2002281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496419072 :
    ThetaLowerSegment 496419072 496484608 (3102495771263 / 6250) (12411639481109 / 25000) := by
  exact
    packedTile32768 496419072 496484608 13 3309 22280 29 _ _ (500573 / 25000) (400459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496484608 :
    ThetaLowerSegment 496484608 496550144 (12411639481109 / 25000) (6206645691367 / 12500) := by
  exact
    packedTile32768 496484608 496550144 13 3300 22281 29 _ _ (400461 / 20000) (500577 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496550144 :
    ThetaLowerSegment 496550144 496615680 (6206645691367 / 12500) (24829845542649 / 50000) := by
  exact
    packedTile32768 496550144 496615680 13 3259 22283 29 _ _ (1001159 / 50000) (2002321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496615680 :
    ThetaLowerSegment 496615680 496681216 (24829845542649 / 50000) (1986653312689 / 4000) := by
  exact
    packedTile32768 496615680 496681216 13 3317 22284 29 _ _ (2002331 / 100000) (1001167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496681216 :
    ThetaLowerSegment 496681216 496746752 (1986653312689 / 4000) (49672764346153 / 100000) := by
  exact
    packedTile32768 496681216 496746752 13 3212 22286 29 _ _ (250293 / 12500) (2002347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496746752 :
    ThetaLowerSegment 496746752 496812288 (49672764346153 / 100000) (49679366120479 / 100000) := by
  exact
    packedTile32768 496746752 496812288 13 3297 22287 29 _ _ (1001179 / 50000) (2002361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496812288 :
    ThetaLowerSegment 496812288 496877824 (49679366120479 / 100000) (6210738483317 / 12500) := by
  exact
    packedTile32768 496812288 496877824 13 3267 22289 29 _ _ (2002371 / 100000) (1001187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496877824 :
    ThetaLowerSegment 496877824 496943360 (6210738483317 / 12500) (6211547696751 / 12500) := by
  exact
    packedTile32768 496877824 496943360 13 3233 22290 29 _ _ (125149 / 6250) (2002387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell496943360 :
    ThetaLowerSegment 496943360 497008896 (6211547696751 / 12500) (49698955443359 / 100000) := by
  exact
    packedTile32768 496943360 497008896 13 3283 22292 29 _ _ (2002397 / 100000) (2503 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497008896 :
    ThetaLowerSegment 497008896 497074432 (49698955443359 / 100000) (49705637485529 / 100000) := by
  exact
    packedTile32768 497008896 497074432 13 3337 22293 29 _ _ (200241 / 10000) (2002413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497074432 :
    ThetaLowerSegment 497074432 497139968 (49705637485529 / 100000) (49712219453217 / 100000) := by
  exact
    packedTile32768 497074432 497139968 13 3287 22295 29 _ _ (250303 / 12500) (2002427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497139968 :
    ThetaLowerSegment 497139968 497205504 (49712219453217 / 100000) (198875382069 / 400) := by
  exact
    packedTile32768 497139968 497205504 13 3309 22296 29 _ _ (2002437 / 100000) (50061 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497205504 :
    ThetaLowerSegment 497205504 497271040 (198875382069 / 400) (994506989497 / 2000) := by
  exact
    packedTile32768 497205504 497271040 13 3248 22298 29 _ _ (40049 / 2000) (2002453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497271040 :
    ThetaLowerSegment 497271040 497336576 (994506989497 / 2000) (49731919555953 / 100000) := by
  exact
    packedTile32768 497271040 497336576 13 3281 22299 29 _ _ (2002463 / 100000) (1001233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497336576 :
    ThetaLowerSegment 497336576 497402112 (49731919555953 / 100000) (49738499692089 / 100000) := by
  exact
    packedTile32768 497336576 497402112 13 3286 22301 29 _ _ (500619 / 25000) (2002479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497402112 :
    ThetaLowerSegment 497402112 497467648 (49738499692089 / 100000) (1989802233643 / 4000) := by
  exact
    packedTile32768 497402112 497467648 13 3274 22302 29 _ _ (2002489 / 100000) (500623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497467648 :
    ThetaLowerSegment 497467648 497533184 (1989802233643 / 4000) (49751588005861 / 100000) := by
  exact
    packedTile32768 497467648 497533184 13 3262 22303 29 _ _ (2002503 / 100000) (1001253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497533184 :
    ThetaLowerSegment 497533184 497598720 (49751588005861 / 100000) (49758182291049 / 100000) := by
  exact
    packedTile32768 497533184 497598720 13 3293 22305 29 _ _ (500629 / 25000) (2002519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497598720 :
    ThetaLowerSegment 497598720 497664256 (49758182291049 / 100000) (24882348258943 / 50000) := by
  exact
    packedTile32768 497598720 497664256 13 3253 22306 29 _ _ (2002529 / 100000) (500633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497664256 :
    ThetaLowerSegment 497664256 497729792 (24882348258943 / 50000) (24885618410029 / 50000) := by
  exact
    packedTile32768 497664256 497729792 13 3266 22308 29 _ _ (1001271 / 50000) (400509 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497729792 :
    ThetaLowerSegment 497729792 497795328 (24885618410029 / 50000) (49777767151913 / 100000) := by
  exact
    packedTile32768 497729792 497795328 13 3261 22309 29 _ _ (400511 / 20000) (1001279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497795328 :
    ThetaLowerSegment 497795328 497860864 (49777767151913 / 100000) (49784251467097 / 100000) := by
  exact
    packedTile32768 497795328 497860864 13 3238 22311 29 _ _ (250321 / 12500) (2002571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497860864 :
    ThetaLowerSegment 497860864 497926400 (49784251467097 / 100000) (49790833954131 / 100000) := by
  exact
    packedTile32768 497860864 497926400 13 3287 22312 29 _ _ (1001291 / 50000) (400517 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497926400 :
    ThetaLowerSegment 497926400 497991936 (49790833954131 / 100000) (24898646161503 / 50000) := by
  exact
    packedTile32768 497926400 497991936 13 3225 22314 29 _ _ (400519 / 20000) (1001299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell497991936 :
    ThetaLowerSegment 497991936 498057472 (24898646161503 / 50000) (24901900399503 / 50000) := by
  exact
    packedTile32768 497991936 498057472 13 3250 22315 29 _ _ (125163 / 6250) (2002611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498057472 :
    ThetaLowerSegment 498057472 498123008 (24901900399503 / 50000) (6226300680383 / 12500) := by
  exact
    packedTile32768 498057472 498123008 13 3298 22317 29 _ _ (2002621 / 100000) (62582 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498123008 :
    ThetaLowerSegment 498123008 498188544 (6226300680383 / 12500) (24908451995197 / 50000) := by
  exact
    packedTile32768 498123008 498188544 13 3245 22318 29 _ _ (1001317 / 50000) (2002637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498188544 :
    ThetaLowerSegment 498188544 498254080 (24908451995197 / 50000) (49823522738729 / 100000) := by
  exact
    packedTile32768 498188544 498254080 13 3305 22320 29 _ _ (2002647 / 100000) (40053 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498254080 :
    ThetaLowerSegment 498254080 498319616 (49823522738729 / 100000) (49830215631791 / 100000) := by
  exact
    packedTile32768 498254080 498319616 13 3342 22321 29 _ _ (2002661 / 100000) (250333 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498319616 :
    ThetaLowerSegment 498319616 498385152 (49830215631791 / 100000) (49836674255441 / 100000) := by
  exact
    packedTile32768 498319616 498385152 13 3225 22323 29 _ _ (1001337 / 50000) (2002677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498385152 :
    ThetaLowerSegment 498385152 498450688 (49836674255441 / 100000) (2492161853037 / 5000) := by
  exact
    packedTile32768 498385152 498450688 13 3277 22324 29 _ _ (2002687 / 100000) (200269 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498450688 :
    ThetaLowerSegment 498450688 498516224 (2492161853037 / 5000) (2492488293137 / 5000) := by
  exact
    packedTile32768 498450688 498516224 13 3260 22326 29 _ _ (20027 / 1000) (2002703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498516224 :
    ThetaLowerSegment 498516224 498581760 (2492488293137 / 5000) (24928185405107 / 50000) := by
  exact
    packedTile32768 498516224 498581760 13 3298 22327 29 _ _ (2002713 / 100000) (500679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498581760 :
    ThetaLowerSegment 498581760 498647296 (24928185405107 / 50000) (4986291171333 / 10000) := by
  exact
    packedTile32768 498581760 498647296 13 3266 22328 29 _ _ (1001363 / 50000) (2002729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498647296 :
    ThetaLowerSegment 498647296 498712832 (4986291171333 / 10000) (49869374552083 / 100000) := by
  exact
    packedTile32768 498647296 498712832 13 3227 22330 29 _ _ (2002739 / 100000) (1001371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498712832 :
    ThetaLowerSegment 498712832 498778368 (49869374552083 / 100000) (12469002418193 / 25000) := by
  exact
    packedTile32768 498712832 498778368 13 3313 22331 29 _ _ (2002753 / 100000) (500689 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498778368 :
    ThetaLowerSegment 498778368 498843904 (12469002418193 / 25000) (3117660420541 / 6250) := by
  exact
    packedTile32768 498778368 498843904 13 3274 22333 29 _ _ (1001383 / 50000) (2002769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498843904 :
    ThetaLowerSegment 498843904 498909440 (3117660420541 / 6250) (9977807541521 / 20000) := by
  exact
    packedTile32768 498843904 498909440 13 3231 22334 29 _ _ (2002779 / 100000) (1001391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498909440 :
    ThetaLowerSegment 498909440 498974976 (9977807541521 / 20000) (49895554792773 / 100000) := by
  exact
    packedTile32768 498909440 498974976 13 3254 22336 29 _ _ (250349 / 12500) (400559 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell498974976 :
    ThetaLowerSegment 498974976 499040512 (49895554792773 / 100000) (49902156038053 / 100000) := by
  exact
    packedTile32768 498974976 499040512 13 3296 22337 29 _ _ (400561 / 20000) (250351 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499040512 :
    ThetaLowerSegment 499040512 499106048 (49902156038053 / 100000) (399268985099 / 800) := by
  exact
    packedTile32768 499040512 499106048 13 3229 22339 29 _ _ (1001409 / 50000) (2002821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499106048 :
    ThetaLowerSegment 499106048 499171584 (399268985099 / 800) (6239384782711 / 12500) := by
  exact
    packedTile32768 499106048 499171584 13 3223 22340 29 _ _ (2002831 / 100000) (1001417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499171584 :
    ThetaLowerSegment 499171584 499237120 (6239384782711 / 12500) (49921721698553 / 100000) := by
  exact
    packedTile32768 499171584 499237120 13 3317 22342 29 _ _ (400569 / 20000) (62589 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499237120 :
    ThetaLowerSegment 499237120 499302656 (49921721698553 / 100000) (49928236995627 / 100000) := by
  exact
    packedTile32768 499237120 499302656 13 3253 22343 29 _ _ (1001429 / 50000) (2002861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499302656 :
    ThetaLowerSegment 499302656 499368192 (49928236995627 / 100000) (12483705108151 / 25000) := by
  exact
    packedTile32768 499302656 499368192 13 3287 22345 29 _ _ (2002871 / 100000) (1001437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499368192 :
    ThetaLowerSegment 499368192 499433728 (12483705108151 / 25000) (12485347473031 / 25000) := by
  exact
    packedTile32768 499368192 499433728 13 3280 22346 29 _ _ (500721 / 25000) (2002887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499433728 :
    ThetaLowerSegment 499433728 499499264 (12485347473031 / 25000) (49947897304477 / 100000) := by
  exact
    packedTile32768 499433728 499499264 13 3249 22348 29 _ _ (2002897 / 100000) (20029 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499499264 :
    ThetaLowerSegment 499499264 499564800 (49947897304477 / 100000) (49954458837637 / 100000) := by
  exact
    packedTile32768 499499264 499564800 13 3276 22349 29 _ _ (200291 / 10000) (2002913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499564800 :
    ThetaLowerSegment 499564800 499630336 (49954458837637 / 100000) (24980533240307 / 50000) := by
  exact
    packedTile32768 499564800 499630336 13 3299 22350 29 _ _ (2002923 / 100000) (1001463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499630336 :
    ThetaLowerSegment 499630336 499695872 (24980533240307 / 50000) (24983840087643 / 50000) := by
  exact
    packedTile32768 499630336 499695872 13 3302 22352 29 _ _ (250367 / 12500) (2002939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499695872 :
    ThetaLowerSegment 499695872 499761408 (24983840087643 / 50000) (12493548942909 / 25000) := by
  exact
    packedTile32768 499695872 499761408 13 3253 22353 29 _ _ (40059 / 2000) (2002953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499761408 :
    ThetaLowerSegment 499761408 499826944 (12493548942909 / 25000) (24990332671063 / 50000) := by
  exact
    packedTile32768 499761408 499826944 13 3230 22355 29 _ _ (2002963 / 100000) (1001483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499826944 :
    ThetaLowerSegment 499826944 499892480 (24990332671063 / 50000) (24993565474327 / 50000) := by
  exact
    packedTile32768 499826944 499892480 13 3228 22356 29 _ _ (62593 / 3125) (2002979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499892480 :
    ThetaLowerSegment 499892480 499958016 (24993565474327 / 50000) (24996862394221 / 50000) := by
  exact
    packedTile32768 499892480 499958016 13 3292 22358 29 _ _ (2002989 / 100000) (125187 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell499958016 :
    ThetaLowerSegment 499958016 500023552 (24996862394221 / 50000) (25000157332511 / 50000) := by
  exact
    packedTile32768 499958016 500023552 13 3290 22359 29 _ _ (1001501 / 50000) (400601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500023552 :
    ThetaLowerSegment 500023552 500089088 (25000157332511 / 50000) (6250850053449 / 12500) := by
  exact
    packedTile32768 500023552 500089088 13 3238 22361 29 _ _ (400603 / 20000) (1001509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500089088 :
    ThetaLowerSegment 500089088 500154624 (6250850053449 / 12500) (12503324061849 / 25000) := by
  exact
    packedTile32768 500089088 500154624 13 3243 22362 29 _ _ (500757 / 25000) (2003031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500154624 :
    ThetaLowerSegment 500154624 500220160 (12503324061849 / 25000) (1250496855851 / 2500) := by
  exact
    packedTile32768 500154624 500220160 13 3284 22364 29 _ _ (2003041 / 100000) (500761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500220160 :
    ThetaLowerSegment 500220160 500285696 (1250496855851 / 2500) (12506608058209 / 25000) := by
  exact
    packedTile32768 500220160 500285696 13 3274 22365 29 _ _ (1001527 / 50000) (2003057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500285696 :
    ThetaLowerSegment 500285696 500351232 (12506608058209 / 25000) (12508270603819 / 25000) := by
  exact
    packedTile32768 500285696 500351232 13 3320 22367 29 _ _ (2003067 / 100000) (200307 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500351232 :
    ThetaLowerSegment 500351232 500416768 (12508270603819 / 25000) (50039622474741 / 100000) := by
  exact
    packedTile32768 500351232 500416768 13 3265 22368 29 _ _ (2003081 / 100000) (500771 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500416768 :
    ThetaLowerSegment 500416768 500482304 (50039622474741 / 100000) (50046300790137 / 100000) := by
  exact
    packedTile32768 500416768 500482304 13 3334 22369 29 _ _ (1001547 / 50000) (2003097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500482304 :
    ThetaLowerSegment 500482304 500547840 (50046300790137 / 100000) (50052830918957 / 100000) := by
  exact
    packedTile32768 500482304 500547840 13 3260 22371 29 _ _ (2003107 / 100000) (200311 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500547840 :
    ThetaLowerSegment 500547840 500613376 (50052830918957 / 100000) (50059339055837 / 100000) := by
  exact
    packedTile32768 500547840 500613376 13 3249 22372 29 _ _ (25039 / 1250) (2003123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500613376 :
    ThetaLowerSegment 500613376 500678912 (50059339055837 / 100000) (25032943648807 / 50000) := by
  exact
    packedTile32768 500613376 500678912 13 3269 22374 29 _ _ (2003133 / 100000) (62598 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500678912 :
    ThetaLowerSegment 500678912 500744448 (25032943648807 / 50000) (25036232814539 / 50000) := by
  exact
    packedTile32768 500678912 500744448 13 3284 22375 29 _ _ (1001573 / 50000) (2003149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500744448 :
    ThetaLowerSegment 500744448 500809984 (25036232814539 / 50000) (12519743973957 / 25000) := by
  exact
    packedTile32768 500744448 500809984 13 3250 22377 29 _ _ (2003159 / 100000) (1001581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500809984 :
    ThetaLowerSegment 500809984 500875520 (12519743973957 / 25000) (3130342512207 / 6250) := by
  exact
    packedTile32768 500809984 500875520 13 3247 22378 29 _ _ (500793 / 25000) (80127 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500875520 :
    ThetaLowerSegment 500875520 500941056 (3130342512207 / 6250) (1565378585751 / 3125) := by
  exact
    packedTile32768 500875520 500941056 13 3312 22380 29 _ _ (400637 / 20000) (500797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell500941056 :
    ThetaLowerSegment 500941056 501006592 (1565378585751 / 3125) (12524660290779 / 25000) := by
  exact
    packedTile32768 500941056 501006592 13 3258 22381 29 _ _ (1001599 / 50000) (2003201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501006592 :
    ThetaLowerSegment 501006592 501072128 (12524660290779 / 25000) (5010511954749 / 10000) := by
  exact
    packedTile32768 501006592 501072128 13 3234 22383 29 _ _ (2003211 / 100000) (1001607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501072128 :
    ThetaLowerSegment 501072128 501137664 (5010511954749 / 10000) (5011169813839 / 10000) := by
  exact
    packedTile32768 501072128 501137664 13 3284 22384 29 _ _ (80129 / 4000) (500807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501137664 :
    ThetaLowerSegment 501137664 501203200 (5011169813839 / 10000) (5011818862951 / 10000) := by
  exact
    packedTile32768 501137664 501203200 13 3240 22386 29 _ _ (1001619 / 50000) (2003241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501203200 :
    ThetaLowerSegment 501203200 501268736 (5011818862951 / 10000) (200498716651 / 400) := by
  exact
    packedTile32768 501203200 501268736 13 3240 22387 29 _ _ (2003251 / 100000) (1001627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501268736 :
    ThetaLowerSegment 501268736 501334272 (200498716651 / 400) (25065572849471 / 50000) := by
  exact
    packedTile32768 501268736 501334272 13 3228 22389 29 _ _ (62602 / 3125) (2003267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501334272 :
    ThetaLowerSegment 501334272 501399808 (25065572849471 / 50000) (6267207043649 / 12500) := by
  exact
    packedTile32768 501334272 501399808 13 3250 22390 29 _ _ (2003277 / 100000) (25041 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501399808 :
    ThetaLowerSegment 501399808 501465344 (6267207043649 / 12500) (25072112568551 / 50000) := by
  exact
    packedTile32768 501399808 501465344 13 3279 22391 29 _ _ (200329 / 10000) (2003293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501465344 :
    ThetaLowerSegment 501465344 501530880 (25072112568551 / 50000) (50150713835519 / 100000) := by
  exact
    packedTile32768 501465344 501530880 13 3239 22393 29 _ _ (2003303 / 100000) (1001653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501530880 :
    ThetaLowerSegment 501530880 501596416 (50150713835519 / 100000) (50157120440087 / 100000) := by
  exact
    packedTile32768 501530880 501596416 13 3198 22394 29 _ _ (500829 / 25000) (2003319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501596416 :
    ThetaLowerSegment 501596416 501661952 (50157120440087 / 100000) (12540905310673 / 25000) := by
  exact
    packedTile32768 501596416 501661952 13 3245 22396 29 _ _ (2003329 / 100000) (500833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501661952 :
    ThetaLowerSegment 501661952 501727488 (12540905310673 / 25000) (12542548051113 / 25000) := by
  exact
    packedTile32768 501661952 501727488 13 3280 22397 29 _ _ (1001671 / 50000) (400669 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501727488 :
    ThetaLowerSegment 501727488 501793024 (12542548051113 / 25000) (25088403641331 / 50000) := by
  exact
    packedTile32768 501727488 501793024 13 3302 22399 29 _ _ (400671 / 20000) (1001679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501793024 :
    ThetaLowerSegment 501793024 501858560 (25088403641331 / 50000) (5018346046779 / 10000) := by
  exact
    packedTile32768 501793024 501858560 13 3321 22400 29 _ _ (250421 / 12500) (2003371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501858560 :
    ThetaLowerSegment 501858560 501924096 (5018346046779 / 10000) (50189977466183 / 100000) := by
  exact
    packedTile32768 501858560 501924096 13 3253 22402 29 _ _ (2003381 / 100000) (250423 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501924096 :
    ThetaLowerSegment 501924096 501989632 (50189977466183 / 100000) (50196558615473 / 100000) := by
  exact
    packedTile32768 501924096 501989632 13 3285 22403 29 _ _ (1001697 / 50000) (2003397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell501989632 :
    ThetaLowerSegment 501989632 502055168 (50196558615473 / 100000) (50203049657393 / 100000) := by
  exact
    packedTile32768 501989632 502055168 13 3240 22405 29 _ _ (125213 / 6250) (2003411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502055168 :
    ThetaLowerSegment 502055168 502120704 (50203049657393 / 100000) (25104799420321 / 50000) := by
  exact
    packedTile32768 502055168 502120704 13 3269 22406 29 _ _ (2003421 / 100000) (62607 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502120704 :
    ThetaLowerSegment 502120704 502186240 (25104799420321 / 50000) (1255402599771 / 2500) := by
  exact
    packedTile32768 502120704 502186240 13 3247 22408 29 _ _ (1001717 / 50000) (2003437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502186240 :
    ThetaLowerSegment 502186240 502251776 (1255402599771 / 2500) (25111311603689 / 50000) := by
  exact
    packedTile32768 502186240 502251776 13 3254 22409 29 _ _ (2003447 / 100000) (40069 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502251776 :
    ThetaLowerSegment 502251776 502317312 (25111311603689 / 50000) (25114558210619 / 50000) := by
  exact
    packedTile32768 502251776 502317312 13 3241 22410 29 _ _ (100173 / 5000) (2003463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502317312 :
    ThetaLowerSegment 502317312 502382848 (25114558210619 / 50000) (50235709850881 / 100000) := by
  exact
    packedTile32768 502317312 502382848 13 3291 22412 29 _ _ (2003473 / 100000) (500869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502382848 :
    ThetaLowerSegment 502382848 502448384 (50235709850881 / 100000) (50242237208269 / 100000) := by
  exact
    packedTile32768 502382848 502448384 13 3258 22413 29 _ _ (1001743 / 50000) (2003489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502448384 :
    ThetaLowerSegment 502448384 502513920 (50242237208269 / 100000) (12562228717609 / 25000) := by
  exact
    packedTile32768 502448384 502513920 13 3333 22415 29 _ _ (2003499 / 100000) (1001751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502513920 :
    ThetaLowerSegment 502513920 502579456 (12562228717609 / 25000) (2512771514573 / 5000) := by
  exact
    packedTile32768 502513920 502579456 13 3252 22416 29 _ _ (250439 / 12500) (400703 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502579456 :
    ThetaLowerSegment 502579456 502644992 (2512771514573 / 5000) (10052378331917 / 20000) := by
  exact
    packedTile32768 502579456 502644992 13 3225 22418 29 _ _ (80141 / 4000) (250441 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502644992 :
    ThetaLowerSegment 502644992 502710528 (10052378331917 / 20000) (50268441225307 / 100000) := by
  exact
    packedTile32768 502644992 502710528 13 3269 22419 29 _ _ (1001769 / 50000) (2003541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502710528 :
    ThetaLowerSegment 502710528 502776064 (50268441225307 / 100000) (1256871464979 / 2500) := by
  exact
    packedTile32768 502710528 502776064 13 3203 22421 29 _ _ (2003551 / 100000) (1001777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502776064 :
    ThetaLowerSegment 502776064 502841600 (1256871464979 / 2500) (12570362080289 / 25000) := by
  exact
    packedTile32768 502776064 502841600 13 3289 22422 29 _ _ (500891 / 25000) (2003567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502841600 :
    ThetaLowerSegment 502841600 502907136 (12570362080289 / 25000) (50287845742517 / 100000) := by
  exact
    packedTile32768 502841600 502907136 13 3193 22424 29 _ _ (2003577 / 100000) (100179 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502907136 :
    ThetaLowerSegment 502907136 502972672 (50287845742517 / 100000) (50294233187437 / 100000) := by
  exact
    packedTile32768 502907136 502972672 13 3188 22425 29 _ _ (200359 / 10000) (2003593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell502972672 :
    ThetaLowerSegment 502972672 503038208 (50294233187437 / 100000) (50300865113367 / 100000) := by
  exact
    packedTile32768 502972672 503038208 13 3310 22427 29 _ _ (2003603 / 100000) (1001803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503038208 :
    ThetaLowerSegment 503038208 503103744 (50300865113367 / 100000) (50307517118487 / 100000) := by
  exact
    packedTile32768 503038208 503103744 13 3320 22428 29 _ _ (62613 / 3125) (2003619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503103744 :
    ThetaLowerSegment 503103744 503169280 (50307517118487 / 100000) (25157103617859 / 50000) := by
  exact
    packedTile32768 503103744 503169280 13 3339 22429 29 _ _ (2003629 / 100000) (125227 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503169280 :
    ThetaLowerSegment 503169280 503234816 (25157103617859 / 50000) (25160363543393 / 50000) := by
  exact
    packedTile32768 503169280 503234816 13 3254 22431 29 _ _ (1001821 / 50000) (400729 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503234816 :
    ThetaLowerSegment 503234816 503300352 (25160363543393 / 50000) (50327236961881 / 100000) := by
  exact
    packedTile32768 503234816 503300352 13 3249 22432 29 _ _ (400731 / 20000) (1001829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503300352 :
    ThetaLowerSegment 503300352 503365888 (50327236961881 / 100000) (10066760997117 / 20000) := by
  exact
    packedTile32768 503300352 503365888 13 3278 22434 29 _ _ (500917 / 25000) (2003671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503365888 :
    ThetaLowerSegment 503365888 503431424 (10066760997117 / 20000) (12585107789663 / 25000) := by
  exact
    packedTile32768 503365888 503431424 13 3307 22435 29 _ _ (2003681 / 100000) (500921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503431424 :
    ThetaLowerSegment 503431424 503496960 (12585107789663 / 25000) (1573340721571 / 3125) := by
  exact
    packedTile32768 503431424 503496960 13 3230 22437 29 _ _ (1001847 / 50000) (2003697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503496960 :
    ThetaLowerSegment 503496960 503562496 (1573340721571 / 3125) (314709019937 / 625) := by
  exact
    packedTile32768 503496960 503562496 13 3264 22438 29 _ _ (2003707 / 100000) (200371 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503562496 :
    ThetaLowerSegment 503562496 503628032 (314709019937 / 625) (251799766381 / 500) := by
  exact
    packedTile32768 503562496 503628032 13 3249 22440 29 _ _ (50093 / 2500) (2003723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503628032 :
    ThetaLowerSegment 503628032 503693568 (251799766381 / 500) (50366583628697 / 100000) := by
  exact
    packedTile32768 503628032 503693568 13 3309 22441 29 _ _ (2003733 / 100000) (250467 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503693568 :
    ThetaLowerSegment 503693568 503759104 (50366583628697 / 100000) (50373256102877 / 100000) := by
  exact
    packedTile32768 503693568 503759104 13 3330 22443 29 _ _ (1001873 / 50000) (2003749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503759104 :
    ThetaLowerSegment 503759104 503824640 (50373256102877 / 100000) (50379900567721 / 100000) := by
  exact
    packedTile32768 503759104 503824640 13 3316 22444 29 _ _ (2003759 / 100000) (1001881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503824640 :
    ThetaLowerSegment 503824640 503890176 (50379900567721 / 100000) (50386354717333 / 100000) := by
  exact
    packedTile32768 503824640 503890176 13 3221 22446 29 _ _ (500943 / 25000) (80151 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503890176 :
    ThetaLowerSegment 503890176 503955712 (50386354717333 / 100000) (25196432507399 / 50000) := by
  exact
    packedTile32768 503890176 503955712 13 3249 22447 29 _ _ (400757 / 20000) (500947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell503955712 :
    ThetaLowerSegment 503955712 504021248 (25196432507399 / 50000) (12599845842423 / 25000) := by
  exact
    packedTile32768 503955712 504021248 13 3253 22448 29 _ _ (1001899 / 50000) (2003801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504021248 :
    ThetaLowerSegment 504021248 504086784 (12599845842423 / 25000) (10081176345753 / 20000) := by
  exact
    packedTile32768 504021248 504086784 13 3243 22450 29 _ _ (2003811 / 100000) (1001907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504086784 :
    ThetaLowerSegment 504086784 504152320 (10081176345753 / 20000) (10082492858121 / 20000) := by
  exact
    packedTile32768 504086784 504152320 13 3285 22451 29 _ _ (125239 / 6250) (2003827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504152320 :
    ThetaLowerSegment 504152320 504217856 (10082492858121 / 20000) (1575594839754 / 3125) := by
  exact
    packedTile32768 504152320 504217856 13 3279 22453 29 _ _ (2003837 / 100000) (12524 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504217856 :
    ThetaLowerSegment 504217856 504283392 (1575594839754 / 3125) (1575801236304 / 3125) := by
  exact
    packedTile32768 504217856 504283392 13 3296 22454 29 _ _ (40077 / 2000) (2003853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504283392 :
    ThetaLowerSegment 504283392 504348928 (1575801236304 / 3125) (12608031015599 / 25000) := by
  exact
    packedTile32768 504283392 504348928 13 3236 22456 29 _ _ (2003863 / 100000) (1001933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504348928 :
    ThetaLowerSegment 504348928 504414464 (12608031015599 / 25000) (1576208334923 / 3125) := by
  exact
    packedTile32768 504348928 504414464 13 3265 22457 29 _ _ (500969 / 25000) (2003879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504414464 :
    ThetaLowerSegment 504414464 504480000 (1576208334923 / 3125) (25222589678393 / 50000) := by
  exact
    packedTile32768 504414464 504480000 13 3250 22459 29 _ _ (2003889 / 100000) (500973 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504480000 :
    ThetaLowerSegment 504480000 504545536 (25222589678393 / 50000) (5045159585099 / 10000) := by
  exact
    packedTile32768 504480000 504545536 13 3202 22460 29 _ _ (1001951 / 50000) (400781 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504545536 :
    ThetaLowerSegment 504545536 504611072 (5045159585099 / 10000) (10091644559579 / 20000) := by
  exact
    packedTile32768 504545536 504611072 13 3307 22462 29 _ _ (400783 / 20000) (1001959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504611072 :
    ThetaLowerSegment 504611072 504676608 (10091644559579 / 20000) (50464849787791 / 100000) := by
  exact
    packedTile32768 504611072 504676608 13 3307 22463 29 _ _ (250491 / 12500) (2003931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504676608 :
    ThetaLowerSegment 504676608 504742144 (50464849787791 / 100000) (25235698331519 / 50000) := by
  exact
    packedTile32768 504676608 504742144 13 3267 22465 29 _ _ (2003941 / 100000) (250493 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504742144 :
    ThetaLowerSegment 504742144 504807680 (25235698331519 / 50000) (25238900650011 / 50000) := by
  exact
    packedTile32768 504742144 504807680 13 3196 22466 29 _ _ (1001977 / 50000) (2003957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504807680 :
    ThetaLowerSegment 504807680 504873216 (25238900650011 / 50000) (25242219219363 / 50000) := by
  exact
    packedTile32768 504807680 504873216 13 3312 22467 29 _ _ (2003967 / 100000) (200397 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504873216 :
    ThetaLowerSegment 504873216 504938752 (25242219219363 / 50000) (25245481698803 / 50000) := by
  exact
    packedTile32768 504873216 504938752 13 3256 22469 29 _ _ (100199 / 5000) (2003983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell504938752 :
    ThetaLowerSegment 504938752 505004288 (25245481698803 / 50000) (12624399153609 / 25000) := by
  exact
    packedTile32768 504938752 505004288 13 3310 22470 29 _ _ (2003993 / 100000) (500999 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505004288 :
    ThetaLowerSegment 505004288 505069824 (12624399153609 / 25000) (25252029766893 / 50000) := by
  exact
    packedTile32768 505004288 505069824 13 3225 22472 29 _ _ (1002003 / 50000) (2004009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505069824 :
    ThetaLowerSegment 505069824 505135360 (25252029766893 / 50000) (50510570591517 / 100000) := by
  exact
    packedTile32768 505069824 505135360 13 3249 22473 29 _ _ (2004019 / 100000) (1002011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505135360 :
    ThetaLowerSegment 505135360 505200896 (50510570591517 / 100000) (50517023574557 / 100000) := by
  exact
    packedTile32768 505135360 505200896 13 3220 22475 29 _ _ (62626 / 3125) (400807 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505200896 :
    ThetaLowerSegment 505200896 505266432 (50517023574557 / 100000) (50523468583277 / 100000) := by
  exact
    packedTile32768 505200896 505266432 13 3216 22476 29 _ _ (400809 / 20000) (125253 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505266432 :
    ThetaLowerSegment 505266432 505331968 (50523468583277 / 100000) (50529981771777 / 100000) := by
  exact
    packedTile32768 505266432 505331968 13 3250 22478 29 _ _ (1002029 / 50000) (2004061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505331968 :
    ThetaLowerSegment 505331968 505397504 (50529981771777 / 100000) (25268284576577 / 50000) := by
  exact
    packedTile32768 505331968 505397504 13 3287 22479 29 _ _ (2004071 / 100000) (1002037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505397504 :
    ThetaLowerSegment 505397504 505463040 (25268284576577 / 50000) (25271619372353 / 50000) := by
  exact
    packedTile32768 505397504 505463040 13 3328 22481 29 _ _ (501021 / 25000) (2004087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505463040 :
    ThetaLowerSegment 505463040 505528576 (25271619372353 / 50000) (25274890058657 / 50000) := by
  exact
    packedTile32768 505463040 505528576 13 3264 22482 29 _ _ (2004097 / 100000) (20041 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505528576 :
    ThetaLowerSegment 505528576 505594112 (25274890058657 / 50000) (25278184815497 / 50000) := by
  exact
    packedTile32768 505528576 505594112 13 3288 22483 29 _ _ (200411 / 10000) (2004113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505594112 :
    ThetaLowerSegment 505594112 505659648 (25278184815497 / 50000) (25281395420543 / 50000) := by
  exact
    packedTile32768 505594112 505659648 13 3204 22485 29 _ _ (2004123 / 100000) (1002063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505659648 :
    ThetaLowerSegment 505659648 505725184 (25281395420543 / 50000) (25284655147747 / 50000) := by
  exact
    packedTile32768 505659648 505725184 13 3253 22486 29 _ _ (250517 / 12500) (2004139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505725184 :
    ThetaLowerSegment 505725184 505790720 (25284655147747 / 50000) (25287909885723 / 50000) := by
  exact
    packedTile32768 505725184 505790720 13 3248 22488 29 _ _ (2004149 / 100000) (250519 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505790720 :
    ThetaLowerSegment 505790720 505856256 (25287909885723 / 50000) (25291176669783 / 50000) := by
  exact
    packedTile32768 505790720 505856256 13 3260 22489 29 _ _ (1002081 / 50000) (400833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505856256 :
    ThetaLowerSegment 505856256 505921792 (25291176669783 / 50000) (25294527650383 / 50000) := by
  exact
    packedTile32768 505856256 505921792 13 3344 22491 29 _ _ (80167 / 4000) (1002089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505921792 :
    ThetaLowerSegment 505921792 505987328 (25294527650383 / 50000) (25297834560583 / 50000) := by
  exact
    packedTile32768 505921792 505987328 13 3300 22492 29 _ _ (501047 / 25000) (2004191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell505987328 :
    ThetaLowerSegment 505987328 506052864 (25297834560583 / 50000) (50602212837431 / 100000) := by
  exact
    packedTile32768 505987328 506052864 13 3265 22494 29 _ _ (2004201 / 100000) (501051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506052864 :
    ThetaLowerSegment 506052864 506118400 (50602212837431 / 100000) (50608800688849 / 100000) := by
  exact
    packedTile32768 506052864 506118400 13 3287 22495 29 _ _ (1002107 / 50000) (2004217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506118400 :
    ThetaLowerSegment 506118400 506183936 (50608800688849 / 100000) (50615362528047 / 100000) := by
  exact
    packedTile32768 506118400 506183936 13 3274 22497 29 _ _ (2004227 / 100000) (200423 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506183936 :
    ThetaLowerSegment 506183936 506249472 (50615362528047 / 100000) (50621956477647 / 100000) := by
  exact
    packedTile32768 506183936 506249472 13 3290 22498 29 _ _ (25053 / 1250) (2004243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506249472 :
    ThetaLowerSegment 506249472 506315008 (50621956477647 / 100000) (50628466291391 / 100000) := by
  exact
    packedTile32768 506249472 506315008 13 3248 22499 29 _ _ (2004253 / 100000) (62633 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506315008 :
    ThetaLowerSegment 506315008 506380544 (50628466291391 / 100000) (6329372268547 / 12500) := by
  exact
    packedTile32768 506315008 506380544 13 3249 22501 29 _ _ (400853 / 20000) (501067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506380544 :
    ThetaLowerSegment 506380544 506446080 (6329372268547 / 12500) 506416083 := by
  exact
    packedTile32768 506380544 506446080 13 3308 22502 29 _ _ (1002139 / 50000) (2004281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506446080 :
    ThetaLowerSegment 506446080 506511616 506416083 (6331020792519 / 12500) := by
  exact
    packedTile32768 506446080 506511616 13 3272 22504 29 _ _ (2004291 / 100000) (1002147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506511616 :
    ThetaLowerSegment 506511616 506577152 (6331020792519 / 12500) (6331849822761 / 12500) := by
  exact
    packedTile32768 506511616 506577152 13 3309 22505 29 _ _ (125269 / 6250) (2004307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506577152 :
    ThetaLowerSegment 506577152 506642688 (6331849822761 / 12500) (50661258495779 / 100000) := by
  exact
    packedTile32768 506577152 506642688 13 3223 22507 29 _ _ (2004317 / 100000) (12527 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506642688 :
    ThetaLowerSegment 506642688 506708224 (50661258495779 / 100000) (50667802633229 / 100000) := by
  exact
    packedTile32768 506642688 506708224 13 3265 22508 29 _ _ (200433 / 10000) (2004333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506708224 :
    ThetaLowerSegment 506708224 506773760 (50667802633229 / 100000) (50674392913013 / 100000) := by
  exact
    packedTile32768 506708224 506773760 13 3288 22510 29 _ _ (2004343 / 100000) (1002173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506773760 :
    ThetaLowerSegment 506773760 506839296 (50674392913013 / 100000) (10136186224457 / 20000) := by
  exact
    packedTile32768 506773760 506839296 13 3262 22511 29 _ _ (501089 / 25000) (2004359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506839296 :
    ThetaLowerSegment 506839296 506904832 (10136186224457 / 20000) (50687541531247 / 100000) := by
  exact
    packedTile32768 506839296 506904832 13 3298 22513 29 _ _ (2004369 / 100000) (501093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506904832 :
    ThetaLowerSegment 506904832 506970368 (50687541531247 / 100000) (50694049759601 / 100000) := by
  exact
    packedTile32768 506904832 506970368 13 3247 22514 29 _ _ (1002191 / 50000) (400877 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell506970368 :
    ThetaLowerSegment 506970368 507035904 (50694049759601 / 100000) (50700535981821 / 100000) := by
  exact
    packedTile32768 506970368 507035904 13 3236 22516 29 _ _ (400879 / 20000) (1002199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507035904 :
    ThetaLowerSegment 507035904 507101440 (50700535981821 / 100000) (50707108435653 / 100000) := by
  exact
    packedTile32768 507035904 507101440 13 3279 22517 29 _ _ (250551 / 12500) (2004411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507101440 :
    ThetaLowerSegment 507101440 507166976 (50707108435653 / 100000) (12678418228607 / 25000) := by
  exact
    packedTile32768 507101440 507166976 13 3275 22518 29 _ _ (2004421 / 100000) (250553 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507166976 :
    ThetaLowerSegment 507166976 507232512 (12678418228607 / 25000) (12680039815713 / 25000) := by
  exact
    packedTile32768 507166976 507232512 13 3236 22520 29 _ _ (1002217 / 50000) (2004437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507232512 :
    ThetaLowerSegment 507232512 507298048 (12680039815713 / 25000) (25363304786649 / 50000) := by
  exact
    packedTile32768 507232512 507298048 13 3218 22521 29 _ _ (2004447 / 100000) (40089 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507298048 :
    ThetaLowerSegment 507298048 507363584 (25363304786649 / 50000) (5073316014531 / 10000) := by
  exact
    packedTile32768 507298048 507363584 13 3268 22523 29 _ _ (2004459 / 100000) (1002231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507363584 :
    ThetaLowerSegment 507363584 507429120 (5073316014531 / 10000) (25369873420151 / 50000) := by
  exact
    packedTile32768 507363584 507429120 13 3286 22524 29 _ _ (250559 / 12500) (80179 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507429120 :
    ThetaLowerSegment 507429120 507494656 (25369873420151 / 50000) (12686559340683 / 25000) := by
  exact
    packedTile32768 507429120 507494656 13 3238 22526 29 _ _ (400897 / 20000) (250561 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507494656 :
    ThetaLowerSegment 507494656 507560192 (12686559340683 / 25000) (3172044994329 / 6250) := by
  exact
    packedTile32768 507494656 507560192 13 3234 22527 29 _ _ (1002249 / 50000) (2004501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507560192 :
    ThetaLowerSegment 507560192 507625728 (3172044994329 / 6250) (50759212520393 / 100000) := by
  exact
    packedTile32768 507560192 507625728 13 3239 22529 29 _ _ (2004511 / 100000) (1002257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507625728 :
    ThetaLowerSegment 507625728 507691264 (50759212520393 / 100000) (10153164688109 / 20000) := by
  exact
    packedTile32768 507625728 507691264 13 3298 22530 29 _ _ (501131 / 25000) (2004527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507691264 :
    ThetaLowerSegment 507691264 507756800 (10153164688109 / 20000) (25386172099703 / 50000) := by
  exact
    packedTile32768 507691264 507756800 13 3253 22532 29 _ _ (2004537 / 100000) (100227 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507756800 :
    ThetaLowerSegment 507756800 507822336 (25386172099703 / 50000) (25389477602653 / 50000) := by
  exact
    packedTile32768 507756800 507822336 13 3298 22533 29 _ _ (40091 / 2000) (2004553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507822336 :
    ThetaLowerSegment 507822336 507887872 (25389477602653 / 50000) (50785608349903 / 100000) := by
  exact
    packedTile32768 507822336 507887872 13 3319 22534 29 _ _ (2004563 / 100000) (1002283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507887872 :
    ThetaLowerSegment 507887872 507953408 (50785608349903 / 100000) (2031688697479 / 4000) := by
  exact
    packedTile32768 507887872 507953408 13 3297 22536 29 _ _ (62643 / 3125) (2004579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell507953408 :
    ThetaLowerSegment 507953408 508018944 (2031688697479 / 4000) (12699698623371 / 25000) := by
  exact
    packedTile32768 507953408 508018944 13 3281 22537 29 _ _ (2004589 / 100000) (125287 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508018944 :
    ThetaLowerSegment 508018944 508084480 (12699698623371 / 25000) (50805283386921 / 100000) := by
  exact
    packedTile32768 508018944 508084480 13 3237 22539 29 _ _ (2004601 / 100000) (501151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508084480 :
    ThetaLowerSegment 508084480 508150016 (50805283386921 / 100000) (10162368095863 / 20000) := by
  exact
    packedTile32768 508084480 508150016 13 3271 22540 29 _ _ (1002307 / 50000) (2004617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508150016 :
    ThetaLowerSegment 508150016 508215552 (10162368095863 / 20000) (25409216848759 / 50000) := by
  exact
    packedTile32768 508150016 508215552 13 3289 22542 29 _ _ (2004627 / 100000) (200463 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508215552 :
    ThetaLowerSegment 508215552 508281088 (25409216848759 / 50000) (25412439307559 / 50000) := by
  exact
    packedTile32768 508215552 508281088 13 3215 22543 29 _ _ (12529 / 625) (2004643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508281088 :
    ThetaLowerSegment 508281088 508346624 (25412439307559 / 50000) (12707854448301 / 25000) := by
  exact
    packedTile32768 508281088 508346624 13 3262 22545 29 _ _ (2004653 / 100000) (125291 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508346624 :
    ThetaLowerSegment 508346624 508412160 (12707854448301 / 25000) (12709482237093 / 25000) := by
  exact
    packedTile32768 508346624 508412160 13 3248 22546 29 _ _ (1002333 / 50000) (2004669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508412160 :
    ThetaLowerSegment 508412160 508477696 (12709482237093 / 25000) (25422238114993 / 50000) := by
  exact
    packedTile32768 508412160 508477696 13 3266 22547 29 _ _ (2004679 / 100000) (1002341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508477696 :
    ThetaLowerSegment 508477696 508543232 (25422238114993 / 50000) (5085113581681 / 10000) := by
  exact
    packedTile32768 508477696 508543232 13 3322 22549 29 _ _ (501173 / 25000) (400939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508543232 :
    ThetaLowerSegment 508543232 508608768 (5085113581681 / 10000) (317860770484 / 625) := by
  exact
    packedTile32768 508543232 508608768 13 3286 22550 29 _ _ (400941 / 20000) (501177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508608768 :
    ThetaLowerSegment 508608768 508674304 (317860770484 / 625) (10172845716821 / 20000) := by
  exact
    packedTile32768 508608768 508674304 13 3245 22552 29 _ _ (2004717 / 100000) (25059 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508674304 :
    ThetaLowerSegment 508674304 508739840 (10172845716821 / 20000) (10174170843351 / 20000) := by
  exact
    packedTile32768 508674304 508739840 13 3305 22553 29 _ _ (200473 / 10000) (2004733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508739840 :
    ThetaLowerSegment 508739840 508805376 (10174170843351 / 20000) (25438727917727 / 50000) := by
  exact
    packedTile32768 508739840 508805376 13 3293 22555 29 _ _ (2004743 / 100000) (1002373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508805376 :
    ThetaLowerSegment 508805376 508870912 (25438727917727 / 50000) (25441990658117 / 50000) := by
  exact
    packedTile32768 508805376 508870912 13 3255 22556 29 _ _ (501189 / 25000) (2004759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508870912 :
    ThetaLowerSegment 508870912 508936448 (25441990658117 / 50000) (50890466743949 / 100000) := by
  exact
    packedTile32768 508870912 508936448 13 3235 22558 29 _ _ (2004769 / 100000) (501193 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell508936448 :
    ThetaLowerSegment 508936448 509001984 (50890466743949 / 100000) (50896932165899 / 100000) := by
  exact
    packedTile32768 508936448 509001984 13 3225 22559 29 _ _ (1002391 / 50000) (400957 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509001984 :
    ThetaLowerSegment 509001984 509067520 (50896932165899 / 100000) (50903556008579 / 100000) := by
  exact
    packedTile32768 509001984 509067520 13 3304 22561 29 _ _ (400959 / 20000) (1002399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509067520 :
    ThetaLowerSegment 509067520 509133056 (50903556008579 / 100000) (50910157841323 / 100000) := by
  exact
    packedTile32768 509067520 509133056 13 3293 22562 29 _ _ (250601 / 12500) (2004811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509133056 :
    ThetaLowerSegment 509133056 509198592 (50910157841323 / 100000) (50916633409923 / 100000) := by
  exact
    packedTile32768 509133056 509198592 13 3230 22563 29 _ _ (100241 / 5000) (2004823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509198592 :
    ThetaLowerSegment 509198592 509264128 (50916633409923 / 100000) (50923353610139 / 100000) := by
  exact
    packedTile32768 509198592 509264128 13 3352 22565 29 _ _ (2004833 / 100000) (501209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509264128 :
    ThetaLowerSegment 509264128 509329664 (50923353610139 / 100000) (50929907451713 / 100000) := by
  exact
    packedTile32768 509264128 509329664 13 3269 22566 29 _ _ (1002423 / 50000) (2004849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509329664 :
    ThetaLowerSegment 509329664 509395200 (50929907451713 / 100000) (12734141397113 / 25000) := by
  exact
    packedTile32768 509329664 509395200 13 3321 22568 29 _ _ (2004859 / 100000) (1002431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509395200 :
    ThetaLowerSegment 509395200 509460736 (12734141397113 / 25000) (12735773864139 / 25000) := by
  exact
    packedTile32768 509395200 509460736 13 3257 22569 29 _ _ (250609 / 12500) (16039 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509460736 :
    ThetaLowerSegment 509460736 509526272 (12735773864139 / 25000) (25474785617553 / 50000) := by
  exact
    packedTile32768 509460736 509526272 13 3230 22571 29 _ _ (400977 / 20000) (250611 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509526272 :
    ThetaLowerSegment 509526272 509591808 (25474785617553 / 50000) (25478107733539 / 50000) := by
  exact
    packedTile32768 509526272 509591808 13 3314 22572 29 _ _ (1002449 / 50000) (2004901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509591808 :
    ThetaLowerSegment 509591808 509657344 (25478107733539 / 50000) (5096269533943 / 10000) := by
  exact
    packedTile32768 509591808 509657344 13 3232 22574 29 _ _ (2004911 / 100000) (1002457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509657344 :
    ThetaLowerSegment 509657344 509722880 (5096269533943 / 10000) (12742274765873 / 25000) := by
  exact
    packedTile32768 509657344 509722880 13 3194 22575 29 _ _ (2004923 / 100000) (1002463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509722880 :
    ThetaLowerSegment 509722880 509788416 (12742274765873 / 25000) (2548788073291 / 5000) := by
  exact
    packedTile32768 509722880 509788416 13 3323 22577 29 _ _ (250617 / 12500) (2004939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509788416 :
    ThetaLowerSegment 509788416 509853952 (2548788073291 / 5000) (50982095099711 / 100000) := by
  exact
    packedTile32768 509788416 509853952 13 3159 22578 29 _ _ (2004949 / 100000) (250619 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509853952 :
    ThetaLowerSegment 509853952 509919488 (50982095099711 / 100000) (10197723047227 / 20000) := by
  exact
    packedTile32768 509853952 509919488 13 3252 22579 29 _ _ (1002481 / 50000) (400993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509919488 :
    ThetaLowerSegment 509919488 509985024 (10197723047227 / 20000) (1274879738729 / 2500) := by
  exact
    packedTile32768 509919488 509985024 13 3279 22581 29 _ _ (80199 / 4000) (1002489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell509985024 :
    ThetaLowerSegment 509985024 510050560 (1274879738729 / 2500) (102003632069 / 200) := by
  exact
    packedTile32768 509985024 510050560 13 3305 22582 29 _ _ (501247 / 25000) (2004991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510050560 :
    ThetaLowerSegment 510050560 510116096 (102003632069 / 200) (25504154113869 / 50000) := by
  exact
    packedTile32768 510050560 510116096 13 3238 22584 29 _ _ (2005001 / 100000) (501251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510116096 :
    ThetaLowerSegment 510116096 510181632 (25504154113869 / 50000) (51014810484897 / 100000) := by
  exact
    packedTile32768 510116096 510181632 13 3243 22585 29 _ _ (2005013 / 100000) (250627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510181632 :
    ThetaLowerSegment 510181632 510247168 (51014810484897 / 100000) (51021336844527 / 100000) := by
  exact
    packedTile32768 510181632 510247168 13 3255 22587 29 _ _ (1002513 / 50000) (2005029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510247168 :
    ThetaLowerSegment 510247168 510312704 (51021336844527 / 100000) (51027941442993 / 100000) := by
  exact
    packedTile32768 510247168 510312704 13 3294 22588 29 _ _ (2005039 / 100000) (1002521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510312704 :
    ThetaLowerSegment 510312704 510378240 (51027941442993 / 100000) (51034536059021 / 100000) := by
  exact
    packedTile32768 510312704 510378240 13 3289 22590 29 _ _ (501263 / 25000) (401011 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510378240 :
    ThetaLowerSegment 510378240 510443776 (51034536059021 / 100000) (12760269646529 / 25000) := by
  exact
    packedTile32768 510378240 510443776 13 3263 22591 29 _ _ (401013 / 20000) (501267 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510443776 :
    ThetaLowerSegment 510443776 510509312 (12760269646529 / 25000) (5104756100329 / 10000) := by
  exact
    packedTile32768 510443776 510509312 13 3233 22593 29 _ _ (1002539 / 50000) (2005081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510509312 :
    ThetaLowerSegment 510509312 510574848 (5104756100329 / 10000) (5105411764759 / 10000) := by
  exact
    packedTile32768 510509312 510574848 13 3270 22594 29 _ _ (200509 / 10000) (2005093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510574848 :
    ThetaLowerSegment 510574848 510640384 (5105411764759 / 10000) (25530355213127 / 50000) := by
  exact
    packedTile32768 510574848 510640384 13 3288 22595 29 _ _ (2005103 / 100000) (1002553 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510640384 :
    ThetaLowerSegment 510640384 510705920 (25530355213127 / 50000) (5106715887931 / 10000) := by
  exact
    packedTile32768 510640384 510705920 13 3216 22597 29 _ _ (501279 / 25000) (2005119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510705920 :
    ThetaLowerSegment 510705920 510771456 (5106715887931 / 10000) (51073641461367 / 100000) := by
  exact
    packedTile32768 510705920 510771456 13 3233 22598 29 _ _ (2005129 / 100000) (501283 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510771456 :
    ThetaLowerSegment 510771456 510836992 (51073641461367 / 100000) (51080164188293 / 100000) := by
  exact
    packedTile32768 510771456 510836992 13 3253 22600 29 _ _ (1002571 / 50000) (401029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510836992 :
    ThetaLowerSegment 510836992 510902528 (51080164188293 / 100000) (51086536570883 / 100000) := by
  exact
    packedTile32768 510836992 510902528 13 3178 22601 29 _ _ (401031 / 20000) (1002579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510902528 :
    ThetaLowerSegment 510902528 510968064 (51086536570883 / 100000) (51093061384301 / 100000) := by
  exact
    packedTile32768 510902528 510968064 13 3254 22603 29 _ _ (2005167 / 100000) (200517 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell510968064 :
    ThetaLowerSegment 510968064 511033600 (51093061384301 / 100000) (51099642385061 / 100000) := by
  exact
    packedTile32768 510968064 511033600 13 3282 22604 29 _ _ (100259 / 5000) (2005183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511033600 :
    ThetaLowerSegment 511033600 511099136 (51099642385061 / 100000) (51106211397329 / 100000) := by
  exact
    packedTile32768 511033600 511099136 13 3276 22606 29 _ _ (2005193 / 100000) (501299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511099136 :
    ThetaLowerSegment 511099136 511164672 (51106211397329 / 100000) (51112654124207 / 100000) := by
  exact
    packedTile32768 511099136 511164672 13 3213 22607 29 _ _ (1002603 / 50000) (2005209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511164672 :
    ThetaLowerSegment 511164672 511230208 (51112654124207 / 100000) (12779783246699 / 25000) := by
  exact
    packedTile32768 511164672 511230208 13 3231 22608 29 _ _ (2005219 / 100000) (1002611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511230208 :
    ThetaLowerSegment 511230208 511295744 (12779783246699 / 25000) (2556284203987 / 5000) := by
  exact
    packedTile32768 511230208 511295744 13 3267 22610 29 _ _ (125327 / 6250) (401047 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511295744 :
    ThetaLowerSegment 511295744 511361280 (2556284203987 / 5000) (2556611058759 / 5000) := by
  exact
    packedTile32768 511295744 511361280 13 3260 22611 29 _ _ (501311 / 25000) (2005247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511361280 :
    ThetaLowerSegment 511361280 511426816 (2556611058759 / 5000) (25569417256383 / 50000) := by
  exact
    packedTile32768 511361280 511426816 13 3298 22613 29 _ _ (2005257 / 100000) (100263 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511426816 :
    ThetaLowerSegment 511426816 511492352 (25569417256383 / 50000) (12786353450909 / 25000) := by
  exact
    packedTile32768 511426816 511492352 13 3281 22614 29 _ _ (200527 / 10000) (2005273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511492352 :
    ThetaLowerSegment 511492352 511557888 (12786353450909 / 25000) (25575881264807 / 50000) := by
  exact
    packedTile32768 511492352 511557888 13 3166 22616 29 _ _ (2005283 / 100000) (1002643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511557888 :
    ThetaLowerSegment 511557888 511623424 (25575881264807 / 50000) (5115845219707 / 10000) := by
  exact
    packedTile32768 511557888 511623424 13 3336 22617 29 _ _ (125331 / 6250) (2005299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511623424 :
    ThetaLowerSegment 511623424 511688960 (5115845219707 / 10000) (25582518814271 / 50000) := by
  exact
    packedTile32768 511623424 511688960 13 3284 22619 29 _ _ (501327 / 25000) (2005311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511688960 :
    ThetaLowerSegment 511688960 511754496 (25582518814271 / 50000) (51171552916471 / 100000) := by
  exact
    packedTile32768 511688960 511754496 13 3249 22620 29 _ _ (2005321 / 100000) (501331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511754496 :
    ThetaLowerSegment 511754496 511820032 (51171552916471 / 100000) (51178150465331 / 100000) := by
  exact
    packedTile32768 511754496 511820032 13 3290 22621 29 _ _ (1002667 / 50000) (2005337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511820032 :
    ThetaLowerSegment 511820032 511885568 (51178150465331 / 100000) (25592437196911 / 50000) := by
  exact
    packedTile32768 511820032 511885568 13 3353 22623 29 _ _ (2005347 / 100000) (40107 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511885568 :
    ThetaLowerSegment 511885568 511951104 (25592437196911 / 50000) (25595713955151 / 50000) := by
  exact
    packedTile32768 511885568 511951104 13 3268 22624 29 _ _ (25067 / 1250) (2005363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell511951104 :
    ThetaLowerSegment 511951104 512016640 (25595713955151 / 50000) (5119808373997 / 10000) := by
  exact
    packedTile32768 511951104 512016640 13 3319 22626 29 _ _ (501343 / 25000) (16043 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512016640 :
    ThetaLowerSegment 512016640 512082176 (5119808373997 / 10000) (1024092746763 / 2000) := by
  exact
    packedTile32768 512016640 512082176 13 3268 22627 29 _ _ (401077 / 20000) (501347 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512082176 :
    ThetaLowerSegment 512082176 512147712 (1024092746763 / 2000) (12802814289237 / 25000) := by
  exact
    packedTile32768 512082176 512147712 13 3301 22629 29 _ _ (1002699 / 50000) (2005401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512147712 :
    ThetaLowerSegment 512147712 512213248 (12802814289237 / 25000) (10243545723649 / 20000) := by
  exact
    packedTile32768 512147712 512213248 13 3227 22630 29 _ _ (2005411 / 100000) (1002707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512213248 :
    ThetaLowerSegment 512213248 512278784 (10243545723649 / 20000) (51224162018437 / 100000) := by
  exact
    packedTile32768 512213248 512278784 13 3208 22632 29 _ _ (125339 / 6250) (2005427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512278784 :
    ThetaLowerSegment 512278784 512344320 (51224162018437 / 100000) (10246153183837 / 20000) := by
  exact
    packedTile32768 512278784 512344320 13 3293 22633 29 _ _ (501359 / 25000) (2005439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512344320 :
    ThetaLowerSegment 512344320 512409856 (10246153183837 / 20000) (51237331759211 / 100000) := by
  exact
    packedTile32768 512344320 512409856 13 3274 22635 29 _ _ (2005449 / 100000) (501363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512409856 :
    ThetaLowerSegment 512409856 512475392 (51237331759211 / 100000) (51243947778349 / 100000) := by
  exact
    packedTile32768 512409856 512475392 13 3299 22636 29 _ _ (1002731 / 50000) (401093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512475392 :
    ThetaLowerSegment 512475392 512540928 (51243947778349 / 100000) (6406309951303 / 12500) := by
  exact
    packedTile32768 512475392 512540928 13 3257 22637 29 _ _ (80219 / 4000) (1002739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512540928 :
    ThetaLowerSegment 512540928 512606464 (6406309951303 / 12500) (6407128190407 / 12500) := by
  exact
    packedTile32768 512540928 512606464 13 3264 22639 29 _ _ (125343 / 6250) (2005491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512606464 :
    ThetaLowerSegment 512606464 512672000 (6407128190407 / 12500) (12815918438939 / 25000) := by
  exact
    packedTile32768 512606464 512672000 13 3315 22640 29 _ _ (4011 / 200) (2005503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512672000 :
    ThetaLowerSegment 512672000 512737536 (12815918438939 / 25000) (51270133513129 / 100000) := by
  exact
    packedTile32768 512672000 512737536 13 3221 22642 29 _ _ (2005513 / 100000) (501379 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512737536 :
    ThetaLowerSegment 512737536 512803072 (51270133513129 / 100000) (51276745732351 / 100000) := by
  exact
    packedTile32768 512737536 512803072 13 3297 22643 29 _ _ (1002763 / 50000) (2005529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512803072 :
    ThetaLowerSegment 512803072 512868608 (51276745732351 / 100000) (10256635098077 / 20000) := by
  exact
    packedTile32768 512803072 512868608 13 3206 22645 29 _ _ (2005539 / 100000) (1002771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512868608 :
    ThetaLowerSegment 512868608 512934144 (10256635098077 / 20000) (51289675484417 / 100000) := by
  exact
    packedTile32768 512868608 512934144 13 3241 22646 29 _ _ (125347 / 6250) (401111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512934144 :
    ThetaLowerSegment 512934144 512999680 (51289675484417 / 100000) (10259259571349 / 20000) := by
  exact
    packedTile32768 512934144 512999680 13 3302 22648 29 _ _ (501391 / 25000) (2005567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell512999680 :
    ThetaLowerSegment 512999680 513065216 (10259259571349 / 20000) (10260591274477 / 20000) := by
  exact
    packedTile32768 512999680 513065216 13 3320 22649 29 _ _ (2005577 / 100000) (100279 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513065216 :
    ThetaLowerSegment 513065216 513130752 (10260591274477 / 20000) (10261883676673 / 20000) := by
  exact
    packedTile32768 513065216 513130752 13 3222 22650 29 _ _ (200559 / 10000) (2005593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513130752 :
    ThetaLowerSegment 513130752 513196288 (10261883676673 / 20000) (51315904503467 / 100000) := by
  exact
    packedTile32768 513130752 513196288 13 3234 22652 29 _ _ (2005603 / 100000) (1002803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513196288 :
    ThetaLowerSegment 513196288 513261824 (51315904503467 / 100000) (51322490943127 / 100000) := by
  exact
    packedTile32768 513196288 513261824 13 3284 22653 29 _ _ (401123 / 20000) (1002809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513261824 :
    ThetaLowerSegment 513261824 513327360 (51322490943127 / 100000) (10265802247951 / 20000) := by
  exact
    packedTile32768 513261824 513327360 13 3251 22655 29 _ _ (501407 / 25000) (2005631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513327360 :
    ThetaLowerSegment 513327360 513392896 (10265802247951 / 20000) (12833881891841 / 25000) := by
  exact
    packedTile32768 513327360 513392896 13 3249 22656 29 _ _ (2005641 / 100000) (501411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513392896 :
    ThetaLowerSegment 513392896 513458432 (12833881891841 / 25000) (5134212416337 / 10000) := by
  exact
    packedTile32768 513392896 513458432 13 3289 22658 29 _ _ (1002827 / 50000) (2005657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513458432 :
    ThetaLowerSegment 513458432 513523968 (5134212416337 / 10000) (25674385470247 / 50000) := by
  exact
    packedTile32768 513458432 513523968 13 3314 22659 29 _ _ (1002833 / 50000) (2005669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513523968 :
    ThetaLowerSegment 513523968 513589504 (25674385470247 / 50000) (5135535759033 / 10000) := by
  exact
    packedTile32768 513523968 513589504 13 3284 22661 29 _ _ (2005679 / 100000) (1002841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513589504 :
    ThetaLowerSegment 513589504 513655040 (5135535759033 / 10000) (25680929019051 / 50000) := by
  exact
    packedTile32768 513589504 513655040 13 3241 22662 29 _ _ (501423 / 25000) (401139 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513655040 :
    ThetaLowerSegment 513655040 513720576 (25680929019051 / 50000) (25684186283971 / 50000) := by
  exact
    packedTile32768 513655040 513720576 13 3248 22663 29 _ _ (401141 / 20000) (501427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513720576 :
    ThetaLowerSegment 513720576 513786112 (25684186283971 / 50000) (5137486307139 / 10000) := by
  exact
    packedTile32768 513720576 513786112 13 3236 22665 29 _ _ (1002859 / 50000) (2005721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513786112 :
    ThetaLowerSegment 513786112 513851648 (5137486307139 / 10000) (2569073998733 / 5000) := by
  exact
    packedTile32768 513786112 513851648 13 3299 22666 29 _ _ (200573 / 10000) (2005733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513851648 :
    ThetaLowerSegment 513851648 513917184 (2569073998733 / 5000) (51388012679611 / 100000) := by
  exact
    packedTile32768 513851648 513917184 13 3257 22668 29 _ _ (2005743 / 100000) (1002873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513917184 :
    ThetaLowerSegment 513917184 513982720 (51388012679611 / 100000) (51394471213931 / 100000) := by
  exact
    packedTile32768 513917184 513982720 13 3220 22669 29 _ _ (501439 / 25000) (2005759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell513982720 :
    ThetaLowerSegment 513982720 514048256 (51394471213931 / 100000) (1028019839379 / 2000) := by
  exact
    packedTile32768 513982720 514048256 13 3251 22671 29 _ _ (2005769 / 100000) (501443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514048256 :
    ThetaLowerSegment 514048256 514113792 (1028019839379 / 2000) (5140749069939 / 10000) := by
  exact
    packedTile32768 514048256 514113792 13 3240 22672 29 _ _ (2005781 / 100000) (250723 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514113792 :
    ThetaLowerSegment 514113792 514179328 (5140749069939 / 10000) (5141400952989 / 10000) := by
  exact
    packedTile32768 514113792 514179328 13 3250 22674 29 _ _ (1002897 / 50000) (2005797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514179328 :
    ThetaLowerSegment 514179328 514244864 (5141400952989 / 10000) (51420522385219 / 100000) := by
  exact
    packedTile32768 514179328 514244864 13 3247 22675 29 _ _ (2005807 / 100000) (200581 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514244864 :
    ThetaLowerSegment 514244864 514310400 (51420522385219 / 100000) (51427113509739 / 100000) := by
  exact
    packedTile32768 514244864 514310400 13 3286 22676 29 _ _ (100291 / 5000) (2005823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514310400 :
    ThetaLowerSegment 514310400 514375936 (51427113509739 / 100000) (51433646504563 / 100000) := by
  exact
    packedTile32768 514310400 514375936 13 3257 22678 29 _ _ (250729 / 12500) (401167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514375936 :
    ThetaLowerSegment 514375936 514441472 (51433646504563 / 100000) (51440125383913 / 100000) := by
  exact
    packedTile32768 514375936 514441472 13 3230 22679 29 _ _ (401169 / 20000) (250731 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514441472 :
    ThetaLowerSegment 514441472 514507008 (51440125383913 / 100000) (51446658463419 / 100000) := by
  exact
    packedTile32768 514441472 514507008 13 3257 22681 29 _ _ (1002929 / 50000) (2005861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514507008 :
    ThetaLowerSegment 514507008 514572544 (51446658463419 / 100000) (51453219664189 / 100000) := by
  exact
    packedTile32768 514507008 514572544 13 3271 22682 29 _ _ (200587 / 10000) (2005873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514572544 :
    ThetaLowerSegment 514572544 514638080 (51453219664189 / 100000) (10291940535609 / 20000) := by
  exact
    packedTile32768 514572544 514638080 13 3232 22684 29 _ _ (2005883 / 100000) (1002943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514638080 :
    ThetaLowerSegment 514638080 514703616 (10291940535609 / 20000) (51466294052301 / 100000) := by
  exact
    packedTile32768 514638080 514703616 13 3286 22685 29 _ _ (250737 / 12500) (2005899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514703616 :
    ThetaLowerSegment 514703616 514769152 (51466294052301 / 100000) (321705346129 / 625) := by
  exact
    packedTile32768 514703616 514769152 13 3271 22687 29 _ _ (2005909 / 100000) (250739 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514769152 :
    ThetaLowerSegment 514769152 514834688 (321705346129 / 625) (51479348546917 / 100000) := by
  exact
    packedTile32768 514769152 514834688 13 3237 22688 29 _ _ (2005921 / 100000) (501481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514834688 :
    ThetaLowerSegment 514834688 514900224 (51479348546917 / 100000) (10297180386659 / 20000) := by
  exact
    packedTile32768 514834688 514900224 13 3267 22689 29 _ _ (1002967 / 50000) (2005937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514900224 :
    ThetaLowerSegment 514900224 514965760 (10297180386659 / 20000) (12873119858377 / 25000) := by
  exact
    packedTile32768 514900224 514965760 13 3279 22691 29 _ _ (2005947 / 100000) (40119 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell514965760 :
    ThetaLowerSegment 514965760 515031296 (12873119858377 / 25000) (12874742178527 / 25000) := by
  exact
    packedTile32768 514965760 515031296 13 3235 22692 29 _ _ (50149 / 2500) (2005963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515031296 :
    ThetaLowerSegment 515031296 515096832 (12874742178527 / 25000) (12876360997931 / 25000) := by
  exact
    packedTile32768 515031296 515096832 13 3228 22694 29 _ _ (501493 / 25000) (80239 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515096832 :
    ThetaLowerSegment 515096832 515162368 (12876360997931 / 25000) (51512029640479 / 100000) := by
  exact
    packedTile32768 515096832 515162368 13 3283 22695 29 _ _ (401197 / 20000) (501497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515162368 :
    ThetaLowerSegment 515162368 515227904 (51512029640479 / 100000) (51518575211953 / 100000) := by
  exact
    packedTile32768 515162368 515227904 13 3263 22697 29 _ _ (1002999 / 50000) (2006001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515227904 :
    ThetaLowerSegment 515227904 515293440 (51518575211953 / 100000) (51525191032933 / 100000) := by
  exact
    packedTile32768 515227904 515293440 13 3298 22698 29 _ _ (200601 / 10000) (2006013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515293440 :
    ThetaLowerSegment 515293440 515358976 (51525191032933 / 100000) (12882939186553 / 25000) := by
  exact
    packedTile32768 515293440 515358976 13 3273 22700 29 _ _ (2006023 / 100000) (1003013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515358976 :
    ThetaLowerSegment 515358976 515424512 (12882939186553 / 25000) (6442281285593 / 12500) := by
  exact
    packedTile32768 515358976 515424512 13 3237 22701 29 _ _ (501509 / 25000) (2006039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515424512 :
    ThetaLowerSegment 515424512 515490048 (6442281285593 / 12500) (51544836143611 / 100000) := by
  exact
    packedTile32768 515424512 515490048 13 3283 22702 29 _ _ (2006049 / 100000) (501513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515490048 :
    ThetaLowerSegment 515490048 515555584 (51544836143611 / 100000) (12887884598353 / 25000) := by
  exact
    packedTile32768 515490048 515555584 13 3341 22704 29 _ _ (2006061 / 100000) (125379 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515555584 :
    ThetaLowerSegment 515555584 515621120 (12887884598353 / 25000) (12889529579033 / 25000) := by
  exact
    packedTile32768 515555584 515621120 13 3280 22705 29 _ _ (1003037 / 50000) (2006077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515621120 :
    ThetaLowerSegment 515621120 515686656 (12889529579033 / 25000) (51564599983229 / 100000) := by
  exact
    packedTile32768 515621120 515686656 13 3231 22707 29 _ _ (2006087 / 100000) (200609 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515686656 :
    ThetaLowerSegment 515686656 515752192 (51564599983229 / 100000) (51571115792781 / 100000) := by
  exact
    packedTile32768 515686656 515752192 13 3248 22708 29 _ _ (2006099 / 100000) (1003051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515752192 :
    ThetaLowerSegment 515752192 515817728 (51571115792781 / 100000) (51577635656781 / 100000) := by
  exact
    packedTile32768 515752192 515817728 13 3250 22710 29 _ _ (62691 / 3125) (401223 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515817728 :
    ThetaLowerSegment 515817728 515883264 (51577635656781 / 100000) (25792092827453 / 50000) := by
  exact
    packedTile32768 515817728 515883264 13 3265 22711 29 _ _ (16049 / 800) (125383 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515883264 :
    ThetaLowerSegment 515883264 515948800 (25792092827453 / 50000) (25795332740323 / 50000) := by
  exact
    packedTile32768 515883264 515948800 13 3230 22713 29 _ _ (1003069 / 50000) (2006141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell515948800 :
    ThetaLowerSegment 515948800 516014336 (25795332740323 / 50000) (12899287840899 / 25000) := by
  exact
    packedTile32768 515948800 516014336 13 3233 22714 29 _ _ (40123 / 2000) (2006153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516014336 :
    ThetaLowerSegment 516014336 516079872 (12899287840899 / 25000) (51603721547421 / 100000) := by
  exact
    packedTile32768 516014336 516079872 13 3275 22715 29 _ _ (2006163 / 100000) (1003083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516079872 :
    ThetaLowerSegment 516079872 516145408 (51603721547421 / 100000) (51610293779997 / 100000) := by
  exact
    packedTile32768 516079872 516145408 13 3276 22717 29 _ _ (62693 / 3125) (2006179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516145408 :
    ThetaLowerSegment 516145408 516210944 (51610293779997 / 100000) (51616958336533 / 100000) := by
  exact
    packedTile32768 516145408 516210944 13 3322 22718 29 _ _ (501547 / 25000) (2006191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516210944 :
    ThetaLowerSegment 516210944 516276480 (51616958336533 / 100000) (51623630961059 / 100000) := by
  exact
    packedTile32768 516210944 516276480 13 3326 22720 29 _ _ (2006201 / 100000) (501551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516276480 :
    ThetaLowerSegment 516276480 516342016 (51623630961059 / 100000) (51630197299481 / 100000) := by
  exact
    packedTile32768 516276480 516342016 13 3273 22721 29 _ _ (1003107 / 50000) (2006217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516342016 :
    ThetaLowerSegment 516342016 516407552 (51630197299481 / 100000) (51636809820377 / 100000) := by
  exact
    packedTile32768 516342016 516407552 13 3296 22723 29 _ _ (1003113 / 50000) (2006229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516407552 :
    ThetaLowerSegment 516407552 516473088 (51636809820377 / 100000) (12910882178697 / 25000) := by
  exact
    packedTile32768 516407552 516473088 13 3349 22724 29 _ _ (2006239 / 100000) (1003121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516473088 :
    ThetaLowerSegment 516473088 516538624 (12910882178697 / 25000) (645625387219 / 1250) := by
  exact
    packedTile32768 516473088 516538624 13 3241 22726 29 _ _ (501563 / 25000) (401251 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516538624 :
    ThetaLowerSegment 516538624 516604160 (645625387219 / 1250) (413253325567 / 800) := by
  exact
    packedTile32768 516538624 516604160 13 3307 22727 29 _ _ (401253 / 20000) (501567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516604160 :
    ThetaLowerSegment 516604160 516669696 (413253325567 / 800) (10332645244333 / 20000) := by
  exact
    packedTile32768 516604160 516669696 13 3270 22728 29 _ _ (2006277 / 100000) (50157 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516669696 :
    ThetaLowerSegment 516669696 516735232 (10332645244333 / 20000) (10333946122769 / 20000) := by
  exact
    packedTile32768 516669696 516735232 13 3242 22730 29 _ _ (200629 / 10000) (2006293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516735232 :
    ThetaLowerSegment 516735232 516800768 (10333946122769 / 20000) (51676275174231 / 100000) := by
  exact
    packedTile32768 516735232 516800768 13 3262 22731 29 _ _ (2006303 / 100000) (1003153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516800768 :
    ThetaLowerSegment 516800768 516866304 (51676275174231 / 100000) (3230173853361 / 6250) := by
  exact
    packedTile32768 516800768 516866304 13 3243 22733 29 _ _ (401263 / 20000) (1003159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516866304 :
    ThetaLowerSegment 516866304 516931840 (3230173853361 / 6250) (3230585652183 / 6250) := by
  exact
    packedTile32768 516866304 516931840 13 3284 22734 29 _ _ (250791 / 12500) (2006331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516931840 :
    ThetaLowerSegment 516931840 516997376 (3230585652183 / 6250) (10339189042877 / 20000) := by
  exact
    packedTile32768 516931840 516997376 13 3277 22736 29 _ _ (2006341 / 100000) (250793 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell516997376 :
    ThetaLowerSegment 516997376 517062912 (10339189042877 / 20000) (25851243965759 / 50000) := by
  exact
    packedTile32768 516997376 517062912 13 3261 22737 29 _ _ (2006353 / 100000) (501589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517062912 :
    ThetaLowerSegment 517062912 517128448 (25851243965759 / 50000) (2585447120547 / 5000) := by
  exact
    packedTile32768 517062912 517128448 13 3217 22739 29 _ _ (1003183 / 50000) (2006369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517128448 :
    ThetaLowerSegment 517128448 517193984 (2585447120547 / 5000) (51715481200101 / 100000) := by
  exact
    packedTile32768 517128448 517193984 13 3259 22740 29 _ _ (2006379 / 100000) (1003191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517193984 :
    ThetaLowerSegment 517193984 517259520 (51715481200101 / 100000) (25861034090877 / 50000) := by
  exact
    packedTile32768 517193984 517259520 13 3283 22741 29 _ _ (2006391 / 100000) (1003197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517259520 :
    ThetaLowerSegment 517259520 517325056 (25861034090877 / 50000) (25864357699103 / 50000) := by
  exact
    packedTile32768 517259520 517325056 13 3313 22743 29 _ _ (501601 / 25000) (2006407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517325056 :
    ThetaLowerSegment 517325056 517390592 (25864357699103 / 50000) (2586759003689 / 5000) := by
  exact
    packedTile32768 517325056 517390592 13 3222 22744 29 _ _ (2006417 / 100000) (100321 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517390592 :
    ThetaLowerSegment 517390592 517456128 (2586759003689 / 5000) (25870946792607 / 50000) := by
  exact
    packedTile32768 517390592 517456128 13 3346 22746 29 _ _ (2006429 / 100000) (62701 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517456128 :
    ThetaLowerSegment 517456128 517521664 (25870946792607 / 50000) (1617136637076 / 3125) := by
  exact
    packedTile32768 517456128 517521664 13 3229 22747 29 _ _ (1003221 / 50000) (401289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517521664 :
    ThetaLowerSegment 517521664 517587200 (1617136637076 / 3125) (25877462734231 / 50000) := by
  exact
    packedTile32768 517521664 517587200 13 3266 22749 29 _ _ (401291 / 20000) (1003229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517587200 :
    ThetaLowerSegment 517587200 517652736 (25877462734231 / 50000) (51761448492679 / 100000) := by
  exact
    packedTile32768 517587200 517652736 13 3251 22750 29 _ _ (2006467 / 100000) (200647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517652736 :
    ThetaLowerSegment 517652736 517718272 (51761448492679 / 100000) (51767977578599 / 100000) := by
  exact
    packedTile32768 517652736 517718272 13 3254 22751 29 _ _ (25081 / 1250) (2006483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517718272 :
    ThetaLowerSegment 517718272 517783808 (51767977578599 / 100000) (1617956783248 / 3125) := by
  exact
    packedTile32768 517718272 517783808 13 3309 22753 29 _ _ (2006493 / 100000) (62703 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517783808 :
    ThetaLowerSegment 517783808 517849344 (1617956783248 / 3125) (25890641336773 / 50000) := by
  exact
    packedTile32768 517783808 517849344 13 3322 22754 29 _ _ (401301 / 20000) (501627 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517849344 :
    ThetaLowerSegment 517849344 517914880 (25890641336773 / 50000) (25893911961113 / 50000) := by
  exact
    packedTile32768 517849344 517914880 13 3260 22756 29 _ _ (1003259 / 50000) (2006521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517914880 :
    ThetaLowerSegment 517914880 517980416 (25893911961113 / 50000) (51794471559429 / 100000) := by
  exact
    packedTile32768 517914880 517980416 13 3313 22757 29 _ _ (2006531 / 100000) (1003267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell517980416 :
    ThetaLowerSegment 517980416 518045952 (51794471559429 / 100000) (25900501428447 / 50000) := by
  exact
    packedTile32768 517980416 518045952 13 3255 22759 29 _ _ (2006543 / 100000) (1003273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518045952 :
    ThetaLowerSegment 518045952 518111488 (25900501428447 / 50000) (25903790173731 / 50000) := by
  exact
    packedTile32768 518045952 518111488 13 3278 22760 29 _ _ (501639 / 25000) (2006559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518111488 :
    ThetaLowerSegment 518111488 518177024 (25903790173731 / 50000) (12953527430747 / 25000) := by
  exact
    packedTile32768 518111488 518177024 13 3254 22762 29 _ _ (2006569 / 100000) (501643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518177024 :
    ThetaLowerSegment 518177024 518242560 (12953527430747 / 25000) (10364129031461 / 20000) := by
  exact
    packedTile32768 518177024 518242560 13 3257 22763 29 _ _ (2006581 / 100000) (250823 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518242560 :
    ThetaLowerSegment 518242560 518308096 (10364129031461 / 20000) (51827172607587 / 100000) := by
  exact
    packedTile32768 518242560 518308096 13 3253 22764 29 _ _ (1003297 / 50000) (2006597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518308096 :
    ThetaLowerSegment 518308096 518373632 (51827172607587 / 100000) (51833734212477 / 100000) := by
  exact
    packedTile32768 518308096 518373632 13 3270 22766 29 _ _ (2006607 / 100000) (200661 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518373632 :
    ThetaLowerSegment 518373632 518439168 (51833734212477 / 100000) (1296008750883 / 2500) := by
  exact
    packedTile32768 518373632 518439168 13 3297 22767 29 _ _ (2006619 / 100000) (1003311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518439168 :
    ThetaLowerSegment 518439168 518504704 (1296008750883 / 2500) (1620213921972 / 3125) := by
  exact
    packedTile32768 518439168 518504704 13 3237 22769 29 _ _ (250829 / 12500) (401327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518504704 :
    ThetaLowerSegment 518504704 518570240 (1620213921972 / 3125) (6481669883691 / 12500) := by
  exact
    packedTile32768 518504704 518570240 13 3246 22770 29 _ _ (501661 / 25000) (2006647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518570240 :
    ThetaLowerSegment 518570240 518635776 (6481669883691 / 12500) (51859946924459 / 100000) := by
  exact
    packedTile32768 518570240 518635776 13 3283 22772 29 _ _ (2006657 / 100000) (100333 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518635776 :
    ThetaLowerSegment 518635776 518701312 (51859946924459 / 100000) (51866572948799 / 100000) := by
  exact
    packedTile32768 518635776 518701312 13 3302 22773 29 _ _ (200667 / 10000) (2006673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518701312 :
    ThetaLowerSegment 518701312 518766848 (51866572948799 / 100000) (10374628163797 / 20000) := by
  exact
    packedTile32768 518701312 518766848 13 3273 22775 29 _ _ (1003341 / 50000) (401337 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518766848 :
    ThetaLowerSegment 518766848 518832384 (10374628163797 / 20000) (5187966458443 / 10000) := by
  exact
    packedTile32768 518766848 518832384 13 3251 22776 29 _ _ (401339 / 20000) (1003349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518832384 :
    ThetaLowerSegment 518832384 518897920 (5187966458443 / 10000) (25943082155821 / 50000) := by
  exact
    packedTile32768 518832384 518897920 13 3239 22777 29 _ _ (501677 / 25000) (2006711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518897920 :
    ThetaLowerSegment 518897920 518963456 (25943082155821 / 50000) (25946391237101 / 50000) := by
  exact
    packedTile32768 518897920 518963456 13 3298 22779 29 _ _ (12542 / 625) (2006723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell518963456 :
    ThetaLowerSegment 518963456 519028992 (25946391237101 / 50000) (25949690306153 / 50000) := by
  exact
    packedTile32768 518963456 519028992 13 3288 22780 29 _ _ (2006733 / 100000) (125421 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519028992 :
    ThetaLowerSegment 519028992 519094528 (25949690306153 / 50000) (25952909126737 / 50000) := by
  exact
    packedTile32768 519028992 519094528 13 3208 22782 29 _ _ (1003373 / 50000) (2006749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519094528 :
    ThetaLowerSegment 519094528 519160064 (25952909126737 / 50000) (2595618716593 / 5000) := by
  exact
    packedTile32768 519094528 519160064 13 3267 22783 29 _ _ (1003379 / 50000) (2006761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519160064 :
    ThetaLowerSegment 519160064 519225600 (2595618716593 / 5000) (5191889633761 / 10000) := by
  exact
    packedTile32768 519160064 519225600 13 3250 22785 29 _ _ (2006771 / 100000) (1003387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519225600 :
    ThetaLowerSegment 519225600 519291136 (5191889633761 / 10000) (25962751333623 / 50000) := by
  exact
    packedTile32768 519225600 519291136 13 3292 22786 29 _ _ (2006783 / 100000) (1003393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519291136 :
    ThetaLowerSegment 519291136 519356672 (25962751333623 / 50000) (25966107699933 / 50000) := by
  exact
    packedTile32768 519291136 519356672 13 3345 22787 29 _ _ (501699 / 25000) (2006799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519356672 :
    ThetaLowerSegment 519356672 519422208 (25966107699933 / 50000) (1298468237547 / 2500) := by
  exact
    packedTile32768 519356672 519422208 13 3246 22789 29 _ _ (2006809 / 100000) (501703 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519422208 :
    ThetaLowerSegment 519422208 519487744 (1298468237547 / 2500) (51945205513247 / 100000) := by
  exact
    packedTile32768 519422208 519487744 13 3227 22790 29 _ _ (2006821 / 100000) (250853 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519487744 :
    ThetaLowerSegment 519487744 519553280 (51945205513247 / 100000) (51951846126953 / 100000) := by
  exact
    packedTile32768 519487744 519553280 13 3309 22792 29 _ _ (1003417 / 50000) (2006837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519553280 :
    ThetaLowerSegment 519553280 519618816 (51951846126953 / 100000) (51958346301147 / 100000) := by
  exact
    packedTile32768 519553280 519618816 13 3239 22793 29 _ _ (1003423 / 50000) (2006849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519618816 :
    ThetaLowerSegment 519618816 519684352 (51958346301147 / 100000) (12991217649939 / 25000) := by
  exact
    packedTile32768 519618816 519684352 13 3251 22795 29 _ _ (2006859 / 100000) (1003431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519684352 :
    ThetaLowerSegment 519684352 519749888 (12991217649939 / 25000) (12992875827929 / 25000) := by
  exact
    packedTile32768 519684352 519749888 13 3305 22796 29 _ _ (250859 / 12500) (3211 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519749888 :
    ThetaLowerSegment 519749888 519815424 (12992875827929 / 25000) (3248633754819 / 6250) := by
  exact
    packedTile32768 519749888 519815424 13 3307 22798 29 _ _ (501721 / 25000) (2006887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519815424 :
    ThetaLowerSegment 519815424 519880960 (3248633754819 / 6250) (1039695979227 / 2000) := by
  exact
    packedTile32768 519815424 519880960 13 3318 22799 29 _ _ (2006897 / 100000) (20069 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519880960 :
    ThetaLowerSegment 519880960 519946496 (1039695979227 / 2000) (5199121304571 / 10000) := by
  exact
    packedTile32768 519880960 519946496 13 3196 22800 29 _ _ (200691 / 10000) (2006913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell519946496 :
    ThetaLowerSegment 519946496 520012032 (5199121304571 / 10000) (12999430373439 / 25000) := by
  exact
    packedTile32768 519946496 520012032 13 3243 22802 29 _ _ (1003461 / 50000) (80277 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520012032 :
    ThetaLowerSegment 520012032 520077568 (12999430373439 / 25000) (26002162154953 / 50000) := by
  exact
    packedTile32768 520012032 520077568 13 3290 22803 29 _ _ (401387 / 20000) (1003469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520077568 :
    ThetaLowerSegment 520077568 520143104 (26002162154953 / 50000) (6501347833169 / 12500) := by
  exact
    packedTile32768 520077568 520143104 13 3218 22805 29 _ _ (2006947 / 100000) (40139 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520143104 :
    ThetaLowerSegment 520143104 520208640 (6501347833169 / 12500) (6502170937639 / 12500) := by
  exact
    packedTile32768 520143104 520208640 13 3281 22806 29 _ _ (25087 / 1250) (2006963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520208640 :
    ThetaLowerSegment 520208640 520274176 (6502170937639 / 12500) (52023823933253 / 100000) := by
  exact
    packedTile32768 520208640 520274176 13 3217 22808 29 _ _ (2006973 / 100000) (62718 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520274176 :
    ThetaLowerSegment 520274176 520339712 (52023823933253 / 100000) (52030294452893 / 100000) := by
  exact
    packedTile32768 520274176 520339712 13 3224 22809 29 _ _ (401397 / 20000) (501747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520339712 :
    ThetaLowerSegment 520339712 520405248 (52030294452893 / 100000) (10407371065871 / 20000) := by
  exact
    packedTile32768 520339712 520405248 13 3269 22810 29 _ _ (1003499 / 50000) (2007001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520405248 :
    ThetaLowerSegment 520405248 520470784 (10407371065871 / 20000) (2081734883633 / 4000) := by
  exact
    packedTile32768 520405248 520470784 13 3247 22812 29 _ _ (200701 / 10000) (2007013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520470784 :
    ThetaLowerSegment 520470784 520536320 (2081734883633 / 4000) (13012475234161 / 25000) := by
  exact
    packedTile32768 520470784 520536320 13 3253 22813 29 _ _ (2007023 / 100000) (1003513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520536320 :
    ThetaLowerSegment 520536320 520601856 (13012475234161 / 25000) (6507066272069 / 12500) := by
  exact
    packedTile32768 520536320 520601856 13 3303 22815 29 _ _ (501759 / 25000) (2007039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520601856 :
    ThetaLowerSegment 520601856 520667392 (6507066272069 / 12500) (6507883642367 / 12500) := by
  exact
    packedTile32768 520601856 520667392 13 3258 22816 29 _ _ (250881 / 12500) (2007051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520667392 :
    ThetaLowerSegment 520667392 520732928 (6507883642367 / 12500) (52069666348443 / 100000) := by
  exact
    packedTile32768 520667392 520732928 13 3287 22818 29 _ _ (2007061 / 100000) (250883 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520732928 :
    ThetaLowerSegment 520732928 520798464 (52069666348443 / 100000) (52076213420569 / 100000) := by
  exact
    packedTile32768 520732928 520798464 13 3262 22819 29 _ _ (2007073 / 100000) (501769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520798464 :
    ThetaLowerSegment 520798464 520864000 (52076213420569 / 100000) (52082636095769 / 100000) := by
  exact
    packedTile32768 520798464 520864000 13 3200 22821 29 _ _ (1003543 / 50000) (2007089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520864000 :
    ThetaLowerSegment 520864000 520929536 (52082636095769 / 100000) (52089245469483 / 100000) := by
  exact
    packedTile32768 520864000 520929536 13 3293 22822 29 _ _ (1003549 / 50000) (2007101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520929536 :
    ThetaLowerSegment 520929536 520995072 (52089245469483 / 100000) (10419158533113 / 20000) := by
  exact
    packedTile32768 520929536 520995072 13 3262 22823 29 _ _ (2007111 / 100000) (1003557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell520995072 :
    ThetaLowerSegment 520995072 521060608 (10419158533113 / 20000) (10420467177961 / 20000) := by
  exact
    packedTile32768 520995072 521060608 13 3260 22825 29 _ _ (501781 / 25000) (2007127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521060608 :
    ThetaLowerSegment 521060608 521126144 (10420467177961 / 20000) (52108826967629 / 100000) := by
  exact
    packedTile32768 521060608 521126144 13 3234 22826 29 _ _ (62723 / 3125) (2007139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521126144 :
    ThetaLowerSegment 521126144 521191680 (52108826967629 / 100000) (52115350201879 / 100000) := by
  exact
    packedTile32768 521126144 521191680 13 3250 22828 29 _ _ (2007149 / 100000) (125447 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521191680 :
    ThetaLowerSegment 521191680 521257216 (52115350201879 / 100000) (13030441773899 / 25000) := by
  exact
    packedTile32768 521191680 521257216 13 3197 22829 29 _ _ (2007161 / 100000) (501791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521257216 :
    ThetaLowerSegment 521257216 521322752 (13030441773899 / 25000) (26064114094351 / 50000) := by
  exact
    packedTile32768 521257216 521322752 13 3219 22831 29 _ _ (1003587 / 50000) (2007177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521322752 :
    ThetaLowerSegment 521322752 521339136 (26064114094351 / 50000) (26064947076541 / 50000) := by
  exact
    packedTile32768 521322752 521339136 11 830 22832 29 _ _ (1003593 / 50000) (2007189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521339136 :
    ThetaLowerSegment 521339136 521341184 (26064947076541 / 50000) (26065051450421 / 50000) := by
  exact
    packedTile32768 521339136 521341184 8 104 22832 29 _ _ (200719 / 10000) (2007193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_489341184_521341184 :
    ThetaLowerSegment 489341184 521341184 (9786377090559 / 20000) (26065051450421 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell489341184 cell489406720)
                    (ThetaLowerSegment.join cell489472256 cell489537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell489603328 cell489668864)
                    (ThetaLowerSegment.join cell489734400 cell489799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell489865472 cell489931008)
                    (ThetaLowerSegment.join cell489996544 cell490062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell490127616 cell490193152)
                    (ThetaLowerSegment.join cell490258688 cell490324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell490389760 cell490455296)
                    (ThetaLowerSegment.join cell490520832 cell490586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell490651904 cell490717440)
                    (ThetaLowerSegment.join cell490782976 cell490848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell490914048 cell490979584)
                    (ThetaLowerSegment.join cell491045120 cell491110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell491176192 cell491241728)
                    (ThetaLowerSegment.join cell491307264 cell491372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell491438336 cell491503872)
                    (ThetaLowerSegment.join cell491569408 cell491634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell491700480 cell491766016)
                    (ThetaLowerSegment.join cell491831552 cell491897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell491962624 cell492028160)
                    (ThetaLowerSegment.join cell492093696 cell492159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell492224768 cell492290304)
                    (ThetaLowerSegment.join cell492355840 cell492421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell492486912 cell492552448)
                    (ThetaLowerSegment.join cell492617984 cell492683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell492749056 cell492814592)
                    (ThetaLowerSegment.join cell492880128 cell492945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell493011200 cell493076736)
                    (ThetaLowerSegment.join cell493142272 cell493207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell493273344 cell493338880)
                    (ThetaLowerSegment.join cell493404416 cell493469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell493535488 cell493601024)
                    (ThetaLowerSegment.join cell493666560 cell493732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell493797632 cell493863168)
                    (ThetaLowerSegment.join cell493928704 cell493994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell494059776 cell494125312)
                    (ThetaLowerSegment.join cell494190848 cell494256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell494321920 cell494387456)
                    (ThetaLowerSegment.join cell494452992 cell494518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell494584064 cell494649600)
                    (ThetaLowerSegment.join cell494715136 cell494780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell494846208 cell494911744)
                    (ThetaLowerSegment.join cell494977280 cell495042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell495108352 cell495173888)
                    (ThetaLowerSegment.join cell495239424 cell495304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell495370496 cell495436032)
                    (ThetaLowerSegment.join cell495501568 cell495567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell495632640 cell495698176)
                    (ThetaLowerSegment.join cell495763712 cell495829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell495894784 cell495960320)
                    (ThetaLowerSegment.join cell496025856 cell496091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell496156928 cell496222464)
                    (ThetaLowerSegment.join cell496288000 cell496353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell496419072 cell496484608)
                    (ThetaLowerSegment.join cell496550144 cell496615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell496681216 cell496746752)
                    (ThetaLowerSegment.join cell496812288 cell496877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell496943360 cell497008896)
                    (ThetaLowerSegment.join cell497074432 cell497139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell497205504 cell497271040)
                    (ThetaLowerSegment.join cell497336576 cell497402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell497467648 cell497533184)
                    (ThetaLowerSegment.join cell497598720 cell497664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell497729792 cell497795328)
                    (ThetaLowerSegment.join cell497860864 cell497926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell497991936 cell498057472)
                    (ThetaLowerSegment.join cell498123008 cell498188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell498254080 cell498319616)
                    (ThetaLowerSegment.join cell498385152 cell498450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell498516224 cell498581760)
                    (ThetaLowerSegment.join cell498647296 cell498712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell498778368 cell498843904)
                    (ThetaLowerSegment.join cell498909440 cell498974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell499040512 cell499106048)
                    (ThetaLowerSegment.join cell499171584 cell499237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell499302656 cell499368192)
                    (ThetaLowerSegment.join cell499433728 cell499499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell499564800 cell499630336)
                    (ThetaLowerSegment.join cell499695872 cell499761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell499826944 cell499892480)
                    (ThetaLowerSegment.join cell499958016 cell500023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell500089088 cell500154624)
                    (ThetaLowerSegment.join cell500220160 cell500285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell500351232 cell500416768)
                    (ThetaLowerSegment.join cell500482304 cell500547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell500613376 cell500678912)
                    (ThetaLowerSegment.join cell500744448 cell500809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell500875520 cell500941056)
                    (ThetaLowerSegment.join cell501006592 cell501072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell501137664 cell501203200)
                    (ThetaLowerSegment.join cell501268736 cell501334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell501399808 cell501465344)
                    (ThetaLowerSegment.join cell501530880 cell501596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell501661952 cell501727488)
                    (ThetaLowerSegment.join cell501793024 cell501858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell501924096 cell501989632)
                    (ThetaLowerSegment.join cell502055168 cell502120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell502186240 cell502251776)
                    (ThetaLowerSegment.join cell502317312 cell502382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell502448384 cell502513920)
                    (ThetaLowerSegment.join cell502579456 cell502644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell502710528 cell502776064)
                    (ThetaLowerSegment.join cell502841600 cell502907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell502972672 cell503038208)
                    (ThetaLowerSegment.join cell503103744 cell503169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell503234816 cell503300352)
                    (ThetaLowerSegment.join cell503365888 cell503431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell503496960 cell503562496)
                    (ThetaLowerSegment.join cell503628032 cell503693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell503759104 cell503824640)
                    (ThetaLowerSegment.join cell503890176 cell503955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell504021248 cell504086784)
                    (ThetaLowerSegment.join cell504152320 cell504217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell504283392 cell504348928)
                    (ThetaLowerSegment.join cell504414464 cell504480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell504545536 cell504611072)
                    (ThetaLowerSegment.join cell504676608 cell504742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell504807680 cell504873216)
                    (ThetaLowerSegment.join cell504938752 cell505004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell505069824 cell505135360)
                    (ThetaLowerSegment.join cell505200896 cell505266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell505331968 cell505397504)
                    (ThetaLowerSegment.join cell505463040 cell505528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell505594112 cell505659648)
                    (ThetaLowerSegment.join cell505725184 cell505790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell505856256 cell505921792)
                    (ThetaLowerSegment.join cell505987328 cell506052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell506118400 cell506183936)
                    (ThetaLowerSegment.join cell506249472 cell506315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell506380544 cell506446080)
                    (ThetaLowerSegment.join cell506511616 cell506577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell506642688 cell506708224)
                    (ThetaLowerSegment.join cell506773760 cell506839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell506904832 cell506970368)
                    (ThetaLowerSegment.join cell507035904 cell507101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell507166976 cell507232512)
                    (ThetaLowerSegment.join cell507298048 cell507363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell507429120 cell507494656)
                    (ThetaLowerSegment.join cell507560192 cell507625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell507691264 cell507756800)
                    (ThetaLowerSegment.join cell507822336 cell507887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell507953408 cell508018944)
                    (ThetaLowerSegment.join cell508084480 cell508150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell508215552 cell508281088)
                    (ThetaLowerSegment.join cell508346624 cell508412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell508477696 cell508543232)
                    (ThetaLowerSegment.join cell508608768 cell508674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell508739840 cell508805376)
                    (ThetaLowerSegment.join cell508870912 cell508936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell509001984 cell509067520)
                    (ThetaLowerSegment.join cell509133056 cell509198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell509264128 cell509329664)
                    (ThetaLowerSegment.join cell509395200 cell509460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell509526272 cell509591808)
                    (ThetaLowerSegment.join cell509657344 cell509722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell509788416 cell509853952)
                    (ThetaLowerSegment.join cell509919488 cell509985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell510050560 cell510116096)
                    (ThetaLowerSegment.join cell510181632 cell510247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell510312704 cell510378240)
                    (ThetaLowerSegment.join cell510443776 cell510509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell510574848 cell510640384)
                    (ThetaLowerSegment.join cell510705920 cell510771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell510836992 cell510902528)
                    (ThetaLowerSegment.join cell510968064 cell511033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell511099136 cell511164672)
                    (ThetaLowerSegment.join cell511230208 cell511295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell511361280 cell511426816)
                    (ThetaLowerSegment.join cell511492352 cell511557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell511623424 cell511688960)
                    (ThetaLowerSegment.join cell511754496 cell511820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell511885568 cell511951104)
                    (ThetaLowerSegment.join cell512016640 cell512082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell512147712 cell512213248)
                    (ThetaLowerSegment.join cell512278784 cell512344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell512409856 cell512475392)
                    (ThetaLowerSegment.join cell512540928 cell512606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell512672000 cell512737536)
                    (ThetaLowerSegment.join cell512803072 cell512868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell512934144 cell512999680)
                    (ThetaLowerSegment.join cell513065216 cell513130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell513196288 cell513261824)
                    (ThetaLowerSegment.join cell513327360 cell513392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell513458432 cell513523968)
                    (ThetaLowerSegment.join cell513589504 cell513655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell513720576 cell513786112)
                    (ThetaLowerSegment.join cell513851648 cell513917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell513982720 cell514048256)
                    (ThetaLowerSegment.join cell514113792 cell514179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell514244864 cell514310400)
                    (ThetaLowerSegment.join cell514375936 cell514441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell514507008 cell514572544)
                    (ThetaLowerSegment.join cell514638080 cell514703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell514769152 cell514834688)
                    (ThetaLowerSegment.join cell514900224 cell514965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell515031296 cell515096832)
                    (ThetaLowerSegment.join cell515162368 cell515227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell515293440 cell515358976)
                    (ThetaLowerSegment.join cell515424512 cell515490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell515555584 cell515621120)
                    (ThetaLowerSegment.join cell515686656 cell515752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell515817728 cell515883264)
                    (ThetaLowerSegment.join cell515948800 cell516014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell516079872 cell516145408)
                    (ThetaLowerSegment.join cell516210944 cell516276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell516342016 cell516407552)
                    (ThetaLowerSegment.join cell516473088 cell516538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell516604160 cell516669696)
                    (ThetaLowerSegment.join cell516735232 cell516800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell516866304 cell516931840)
                    (ThetaLowerSegment.join cell516997376 cell517062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell517128448 cell517193984)
                    (ThetaLowerSegment.join cell517259520 cell517325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell517390592 cell517456128)
                    (ThetaLowerSegment.join cell517521664 cell517587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell517652736 cell517718272)
                    (ThetaLowerSegment.join cell517783808 cell517849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell517914880 cell517980416)
                    (ThetaLowerSegment.join cell518045952 cell518111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell518177024 cell518242560)
                    (ThetaLowerSegment.join cell518308096 cell518373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell518439168 cell518504704)
                    (ThetaLowerSegment.join cell518570240 cell518635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell518701312 cell518766848)
                    (ThetaLowerSegment.join cell518832384 cell518897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell518963456 cell519028992)
                    (ThetaLowerSegment.join cell519094528 cell519160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell519225600 cell519291136)
                    (ThetaLowerSegment.join cell519356672 cell519422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell519487744 cell519553280)
                    (ThetaLowerSegment.join cell519618816 cell519684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell519749888 cell519815424)
                    (ThetaLowerSegment.join cell519880960 cell519946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell520012032 cell520077568)
                    (ThetaLowerSegment.join cell520143104 cell520208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell520274176 cell520339712)
                    (ThetaLowerSegment.join cell520405248 cell520470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell520536320 cell520601856)
                    (ThetaLowerSegment.join cell520667392 cell520732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell520798464 cell520864000)
                  (ThetaLowerSegment.join cell520929536 cell520995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell521060608 cell521126144)
                  (ThetaLowerSegment.join cell521191680 cell521257216)))
              (ThetaLowerSegment.join cell521322752 cell521339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
