/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 937341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell905341184 :
    ThetaLowerSegment 905341184 905406720 (3621155229789 / 4000) (45267716464581 / 50000) := by
  exact
    packedTile32768 905341184 905406720 13 3177 30088 30 _ _ (2062381 / 100000) (128899 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905406720 :
    ThetaLowerSegment 905406720 905472256 (45267716464581 / 50000) (45271009067023 / 50000) := by
  exact
    packedTile32768 905406720 905472256 13 3193 30089 30 _ _ (515597 / 25000) (2062391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905472256 :
    ThetaLowerSegment 905472256 905537792 (45271009067023 / 50000) (5659295572961 / 6250) := by
  exact
    packedTile32768 905472256 905537792 13 3254 30091 30 _ _ (412479 / 20000) (1031199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905537792 :
    ThetaLowerSegment 905537792 905603328 (5659295572961 / 6250) (45277669582893 / 50000) := by
  exact
    packedTile32768 905537792 905603328 13 3205 30092 30 _ _ (1031201 / 50000) (412481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905603328 :
    ThetaLowerSegment 905603328 905668864 (45277669582893 / 50000) (22640433674799 / 25000) := by
  exact
    packedTile32768 905603328 905668864 13 3101 30093 30 _ _ (206241 / 10000) (2062413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905668864 :
    ThetaLowerSegment 905668864 905734400 (22640433674799 / 25000) (45284156904713 / 50000) := by
  exact
    packedTile32768 905668864 905734400 13 3190 30094 30 _ _ (2062417 / 100000) (103121 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905734400 :
    ThetaLowerSegment 905734400 905799936 (45284156904713 / 50000) (45287470188869 / 50000) := by
  exact
    packedTile32768 905734400 905799936 13 3213 30095 30 _ _ (257803 / 12500) (2062427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905799936 :
    ThetaLowerSegment 905799936 905865472 (45287470188869 / 50000) (11322676535777 / 12500) := by
  exact
    packedTile32768 905799936 905865472 13 3138 30096 30 _ _ (2062431 / 100000) (1031217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905865472 :
    ThetaLowerSegment 905865472 905931008 (11322676535777 / 12500) (90588051277357 / 100000) := by
  exact
    packedTile32768 905865472 905931008 13 3219 30097 30 _ _ (2062439 / 100000) (1031221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905931008 :
    ThetaLowerSegment 905931008 905996544 (90588051277357 / 100000) (90594529420243 / 100000) := by
  exact
    packedTile32768 905931008 905996544 13 3141 30098 30 _ _ (1031223 / 50000) (2062449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell905996544 :
    ThetaLowerSegment 905996544 906062080 (90594529420243 / 100000) (45300588353131 / 50000) := by
  exact
    packedTile32768 905996544 906062080 13 3223 30099 30 _ _ (2062453 / 100000) (257807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906062080 :
    ThetaLowerSegment 906062080 906127616 (45300588353131 / 50000) (45303876945601 / 50000) := by
  exact
    packedTile32768 906062080 906127616 13 3189 30100 30 _ _ (103123 / 5000) (2062463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906127616 :
    ThetaLowerSegment 906127616 906193152 (45303876945601 / 50000) (1812284435817 / 2000) := by
  exact
    packedTile32768 906127616 906193152 13 3136 30101 30 _ _ (515617 / 25000) (2062471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906193152 :
    ThetaLowerSegment 906193152 906258688 (1812284435817 / 2000) (3624830475963 / 4000) := by
  exact
    packedTile32768 906193152 906258688 13 3171 30103 30 _ _ (82499 / 4000) (1031239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906258688 :
    ThetaLowerSegment 906258688 906324224 (3624830475963 / 4000) (90627229842627 / 100000) := by
  exact
    packedTile32768 906258688 906324224 13 3136 30104 30 _ _ (1031241 / 50000) (412497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906324224 :
    ThetaLowerSegment 906324224 906389760 (90627229842627 / 100000) (90633714308043 / 100000) := by
  exact
    packedTile32768 906324224 906389760 13 3144 30105 30 _ _ (2062489 / 100000) (515623 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906389760 :
    ThetaLowerSegment 906389760 906455296 (90633714308043 / 100000) (90640363795147 / 100000) := by
  exact
    packedTile32768 906389760 906455296 13 3224 30106 30 _ _ (64453 / 3125) (2062499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906455296 :
    ThetaLowerSegment 906455296 906520832 (90640363795147 / 100000) (18129399774103 / 20000) := by
  exact
    packedTile32768 906455296 906520832 13 3217 30107 30 _ _ (257813 / 12500) (2062507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906520832 :
    ThetaLowerSegment 906520832 906586368 (18129399774103 / 20000) (22663403335823 / 25000) := by
  exact
    packedTile32768 906520832 906586368 13 3207 30108 30 _ _ (2062511 / 100000) (1031257 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906586368 :
    ThetaLowerSegment 906586368 906651904 (22663403335823 / 25000) (45330091231561 / 50000) := by
  exact
    packedTile32768 906586368 906651904 13 3185 30109 30 _ _ (1031259 / 50000) (2062521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906651904 :
    ThetaLowerSegment 906651904 906717440 (45330091231561 / 50000) (90666735105047 / 100000) := by
  exact
    packedTile32768 906651904 906717440 13 3177 30110 30 _ _ (82501 / 4000) (64454 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906717440 :
    ThetaLowerSegment 906717440 906782976 (90666735105047 / 100000) (3626930603381 / 4000) := by
  exact
    packedTile32768 906717440 906782976 13 3166 30111 30 _ _ (2062533 / 100000) (257817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906782976 :
    ThetaLowerSegment 906782976 906848512 (3626930603381 / 4000) (18135984592729 / 20000) := by
  exact
    packedTile32768 906782976 906848512 13 3228 30112 30 _ _ (103127 / 5000) (2062543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906848512 :
    ThetaLowerSegment 906848512 906914048 (18135984592729 / 20000) (90686436487071 / 100000) := by
  exact
    packedTile32768 906848512 906914048 13 3158 30113 30 _ _ (2062547 / 100000) (41251 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906914048 :
    ThetaLowerSegment 906914048 906979584 (90686436487071 / 100000) (90693084098613 / 100000) := by
  exact
    packedTile32768 906914048 906979584 13 3223 30115 30 _ _ (1031277 / 50000) (2062557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell906979584 :
    ThetaLowerSegment 906979584 907045120 (90693084098613 / 100000) (90699653358583 / 100000) := by
  exact
    packedTile32768 906979584 907045120 13 3185 30116 30 _ _ (1031281 / 50000) (412513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907045120 :
    ThetaLowerSegment 907045120 907110656 (90699653358583 / 100000) (18141249890849 / 20000) := by
  exact
    packedTile32768 907045120 907110656 13 3198 30117 30 _ _ (2062569 / 100000) (515643 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907110656 :
    ThetaLowerSegment 907110656 907176192 (18141249890849 / 20000) (18142567876913 / 20000) := by
  exact
    packedTile32768 907110656 907176192 13 3195 30118 30 _ _ (128911 / 6250) (2062579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907176192 :
    ThetaLowerSegment 907176192 907241728 (18142567876913 / 20000) (45359722918957 / 50000) := by
  exact
    packedTile32768 907176192 907241728 13 3203 30119 30 _ _ (2062583 / 100000) (1031293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907241728 :
    ThetaLowerSegment 907241728 907307264 (45359722918957 / 50000) (11340737460253 / 12500) := by
  exact
    packedTile32768 907241728 907307264 13 3129 30120 30 _ _ (206259 / 10000) (2062593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907307264 :
    ThetaLowerSegment 907307264 907372800 (11340737460253 / 12500) (22683121905009 / 25000) := by
  exact
    packedTile32768 907307264 907372800 13 3194 30121 30 _ _ (1031299 / 50000) (2062601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907372800 :
    ThetaLowerSegment 907372800 907438336 (22683121905009 / 25000) (90738995138811 / 100000) := by
  exact
    packedTile32768 907372800 907438336 13 3155 30122 30 _ _ (412521 / 20000) (128913 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907438336 :
    ThetaLowerSegment 907438336 907503872 (90738995138811 / 100000) (18149121987099 / 20000) := by
  exact
    packedTile32768 907438336 907503872 13 3207 30123 30 _ _ (515653 / 25000) (412523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907503872 :
    ThetaLowerSegment 907503872 907569408 (18149121987099 / 20000) (90752202065819 / 100000) := by
  exact
    packedTile32768 907503872 907569408 13 3196 30124 30 _ _ (2062619 / 100000) (1031311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907569408 :
    ThetaLowerSegment 907569408 907634944 (90752202065819 / 100000) (4537936307751 / 5000) := by
  exact
    packedTile32768 907569408 907634944 13 3163 30125 30 _ _ (2062627 / 100000) (206263 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907634944 :
    ThetaLowerSegment 907634944 907700480 (4537936307751 / 5000) (11345681808391 / 12500) := by
  exact
    packedTile32768 907634944 907700480 13 3262 30126 30 _ _ (1031317 / 50000) (2062637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907700480 :
    ThetaLowerSegment 907700480 907766016 (11345681808391 / 12500) (90771990976457 / 100000) := by
  exact
    packedTile32768 907700480 907766016 13 3169 30128 30 _ _ (2062641 / 100000) (515661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907766016 :
    ThetaLowerSegment 907766016 907831552 (90771990976457 / 100000) (90778492442953 / 100000) := by
  exact
    packedTile32768 907766016 907831552 13 3152 30129 30 _ _ (257831 / 12500) (2062651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907831552 :
    ThetaLowerSegment 907831552 907897088 (90778492442953 / 100000) (45392545438149 / 50000) := by
  exact
    packedTile32768 907831552 907897088 13 3199 30130 30 _ _ (412531 / 20000) (1031329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907897088 :
    ThetaLowerSegment 907897088 907962624 (45392545438149 / 50000) (2837237906772 / 3125) := by
  exact
    packedTile32768 907897088 907962624 13 3162 30131 30 _ _ (2062663 / 100000) (1031333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell907962624 :
    ThetaLowerSegment 907962624 908028160 (2837237906772 / 3125) (45399041806247 / 50000) := by
  exact
    packedTile32768 907962624 908028160 13 3137 30132 30 _ _ (206267 / 10000) (2062673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908028160 :
    ThetaLowerSegment 908028160 908093696 (45399041806247 / 50000) (22701178264093 / 25000) := by
  exact
    packedTile32768 908028160 908093696 13 3214 30133 30 _ _ (2062677 / 100000) (51567 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908093696 :
    ThetaLowerSegment 908093696 908159232 (22701178264093 / 25000) (2837849748338 / 3125) := by
  exact
    packedTile32768 908093696 908159232 13 3141 30134 30 _ _ (515671 / 25000) (2062687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908159232 :
    ThetaLowerSegment 908159232 908224768 (2837849748338 / 3125) (2838051376481 / 3125) := by
  exact
    packedTile32768 908159232 908224768 13 3128 30135 30 _ _ (515673 / 25000) (412539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908224768 :
    ThetaLowerSegment 908224768 908290304 (2838051376481 / 3125) (45412070774621 / 50000) := by
  exact
    packedTile32768 908224768 908290304 13 3150 30136 30 _ _ (2062699 / 100000) (1031351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908290304 :
    ThetaLowerSegment 908290304 908355840 (45412070774621 / 50000) (22707673691551 / 25000) := by
  exact
    packedTile32768 908290304 908355840 13 3177 30137 30 _ _ (1031353 / 50000) (2062709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908355840 :
    ThetaLowerSegment 908355840 908421376 (22707673691551 / 25000) (90837326388499 / 100000) := by
  exact
    packedTile32768 908355840 908421376 13 3215 30138 30 _ _ (2062713 / 100000) (515679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908421376 :
    ThetaLowerSegment 908421376 908486912 (90837326388499 / 100000) (90843823956499 / 100000) := by
  exact
    packedTile32768 908421376 908486912 13 3150 30140 30 _ _ (12892 / 625) (2062723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908486912 :
    ThetaLowerSegment 908486912 908552448 (90843823956499 / 100000) (18170087825039 / 20000) := by
  exact
    packedTile32768 908486912 908552448 13 3207 30141 30 _ _ (257841 / 12500) (2062731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908552448 :
    ThetaLowerSegment 908552448 908617984 (18170087825039 / 20000) (18171388173183 / 20000) := by
  exact
    packedTile32768 908552448 908617984 13 3152 30142 30 _ _ (412547 / 20000) (1031369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908617984 :
    ThetaLowerSegment 908617984 908683520 (18171388173183 / 20000) (90863481820797 / 100000) := by
  exact
    packedTile32768 908617984 908683520 13 3171 30143 30 _ _ (1031371 / 50000) (412549 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908683520 :
    ThetaLowerSegment 908683520 908749056 (90863481820797 / 100000) (45435025838181 / 50000) := by
  exact
    packedTile32768 908683520 908749056 13 3185 30144 30 _ _ (2062749 / 100000) (64461 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908749056 :
    ThetaLowerSegment 908749056 908814592 (45435025838181 / 50000) (45438320059513 / 50000) := by
  exact
    packedTile32768 908749056 908814592 13 3194 30145 30 _ _ (515689 / 25000) (2062759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908814592 :
    ThetaLowerSegment 908814592 908880128 (45438320059513 / 50000) (9088305737783 / 10000) := by
  exact
    packedTile32768 908814592 908880128 13 3111 30146 30 _ _ (515691 / 25000) (2062767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908880128 :
    ThetaLowerSegment 908880128 908945664 (9088305737783 / 10000) (90889631429007 / 100000) := by
  exact
    packedTile32768 908880128 908945664 13 3187 30147 30 _ _ (2062771 / 100000) (1031387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell908945664 :
    ThetaLowerSegment 908945664 909011200 (90889631429007 / 100000) (18179253064611 / 20000) := by
  exact
    packedTile32768 908945664 909011200 13 3216 30148 30 _ _ (1031389 / 50000) (2062781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909011200 :
    ThetaLowerSegment 909011200 909076736 (18179253064611 / 20000) (4545140526993 / 5000) := by
  exact
    packedTile32768 909011200 909076736 13 3173 30149 30 _ _ (412557 / 20000) (515697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909076736 :
    ThetaLowerSegment 909076736 909142272 (4545140526993 / 5000) (90909529056661 / 100000) := by
  exact
    packedTile32768 909076736 909142272 13 3257 30150 30 _ _ (2062793 / 100000) (515699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909142272 :
    ThetaLowerSegment 909142272 909207808 (90909529056661 / 100000) (90916105263061 / 100000) := by
  exact
    packedTile32768 909142272 909207808 13 3188 30151 30 _ _ (5157 / 250) (2062803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909207808 :
    ThetaLowerSegment 909207808 909273344 (90916105263061 / 100000) (3636912540457 / 4000) := by
  exact
    packedTile32768 909207808 909273344 13 3252 30153 30 _ _ (2062807 / 100000) (206281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909273344 :
    ThetaLowerSegment 909273344 909338880 (3636912540457 / 4000) (90929369134317 / 100000) := by
  exact
    packedTile32768 909273344 909338880 13 3178 30154 30 _ _ (1031407 / 50000) (2062817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909338880 :
    ThetaLowerSegment 909338880 909404416 (90929369134317 / 100000) (90936019669221 / 100000) := by
  exact
    packedTile32768 909338880 909404416 13 3224 30155 30 _ _ (2062821 / 100000) (257853 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909404416 :
    ThetaLowerSegment 909404416 909469952 (90936019669221 / 100000) (90942608345047 / 100000) := by
  exact
    packedTile32768 909404416 909469952 13 3194 30156 30 _ _ (2062829 / 100000) (128927 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909469952 :
    ThetaLowerSegment 909469952 909535488 (90942608345047 / 100000) (90949095964267 / 100000) := by
  exact
    packedTile32768 909469952 909535488 13 3145 30157 30 _ _ (515709 / 25000) (2062839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909535488 :
    ThetaLowerSegment 909535488 909601024 (90949095964267 / 100000) (90955692936181 / 100000) := by
  exact
    packedTile32768 909535488 909601024 13 3198 30158 30 _ _ (2062843 / 100000) (1031423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909601024 :
    ThetaLowerSegment 909601024 909666560 (90955692936181 / 100000) (90962329124631 / 100000) := by
  exact
    packedTile32768 909601024 909666560 13 3217 30159 30 _ _ (41257 / 2000) (2062853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909666560 :
    ThetaLowerSegment 909666560 909732096 (90962329124631 / 100000) (90968868381321 / 100000) := by
  exact
    packedTile32768 909666560 909732096 13 3170 30160 30 _ _ (2062857 / 100000) (103143 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909732096 :
    ThetaLowerSegment 909732096 909797632 (90968868381321 / 100000) (90975349903151 / 100000) := by
  exact
    packedTile32768 909732096 909797632 13 3142 30161 30 _ _ (412573 / 20000) (515717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909797632 :
    ThetaLowerSegment 909797632 909863168 (90975349903151 / 100000) (90981856201439 / 100000) := by
  exact
    packedTile32768 909797632 909863168 13 3154 30162 30 _ _ (257859 / 12500) (16503 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909863168 :
    ThetaLowerSegment 909863168 909928704 (90981856201439 / 100000) (3639536976327 / 4000) := by
  exact
    packedTile32768 909863168 909928704 13 3184 30163 30 _ _ (2062879 / 100000) (1031441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909928704 :
    ThetaLowerSegment 909928704 909994240 (3639536976327 / 4000) (90995188611369 / 100000) := by
  exact
    packedTile32768 909928704 909994240 13 3279 30165 30 _ _ (1031443 / 50000) (2062889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell909994240 :
    ThetaLowerSegment 909994240 910059776 (90995188611369 / 100000) (91001781617397 / 100000) := by
  exact
    packedTile32768 909994240 910059776 13 3196 30166 30 _ _ (2062893 / 100000) (128931 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910059776 :
    ThetaLowerSegment 910059776 910125312 (91001781617397 / 100000) (3640333500671 / 4000) := by
  exact
    packedTile32768 910059776 910125312 13 3178 30167 30 _ _ (2062901 / 100000) (257863 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910125312 :
    ThetaLowerSegment 910125312 910190848 (3640333500671 / 4000) (91014916130387 / 100000) := by
  exact
    packedTile32768 910125312 910190848 13 3189 30168 30 _ _ (515727 / 25000) (2062911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910190848 :
    ThetaLowerSegment 910190848 910256384 (91014916130387 / 100000) (22755356156803 / 25000) := by
  exact
    packedTile32768 910190848 910256384 13 3155 30169 30 _ _ (412583 / 20000) (1031459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910256384 :
    ThetaLowerSegment 910256384 910321920 (22755356156803 / 25000) (9102785888093 / 10000) := by
  exact
    packedTile32768 910256384 910321920 13 3119 30170 30 _ _ (1031461 / 50000) (82517 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910321920 :
    ThetaLowerSegment 910321920 910387456 (9102785888093 / 10000) (11379300827197 / 12500) := by
  exact
    packedTile32768 910321920 910387456 13 3174 30171 30 _ _ (2062929 / 100000) (515733 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910387456 :
    ThetaLowerSegment 910387456 910452992 (11379300827197 / 12500) (91040989449543 / 100000) := by
  exact
    packedTile32768 910387456 910452992 13 3191 30172 30 _ _ (2062937 / 100000) (103147 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910452992 :
    ThetaLowerSegment 910452992 910518528 (91040989449543 / 100000) (91047654821607 / 100000) := by
  exact
    packedTile32768 910452992 910518528 13 3231 30173 30 _ _ (64467 / 3125) (2062947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910518528 :
    ThetaLowerSegment 910518528 910584064 (91047654821607 / 100000) (45527063149447 / 50000) := by
  exact
    packedTile32768 910518528 910584064 13 3137 30174 30 _ _ (2062951 / 100000) (1031477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910584064 :
    ThetaLowerSegment 910584064 910649600 (45527063149447 / 50000) (9106064937209 / 10000) := by
  exact
    packedTile32768 910584064 910649600 13 3162 30175 30 _ _ (1031479 / 50000) (2062961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910649600 :
    ThetaLowerSegment 910649600 910715136 (9106064937209 / 10000) (9106723435637 / 10000) := by
  exact
    packedTile32768 910649600 910715136 13 3192 30176 30 _ _ (412593 / 20000) (257871 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910715136 :
    ThetaLowerSegment 910715136 910780672 (9106723435637 / 10000) (45536922060931 / 50000) := by
  exact
    packedTile32768 910715136 910780672 13 3204 30178 30 _ _ (2062973 / 100000) (64468 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910780672 :
    ThetaLowerSegment 910780672 910846208 (45536922060931 / 50000) (45540199104661 / 50000) := by
  exact
    packedTile32768 910780672 910846208 13 3177 30179 30 _ _ (103149 / 5000) (2062983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910846208 :
    ThetaLowerSegment 910846208 910911744 (45540199104661 / 50000) (45543446246199 / 50000) := by
  exact
    packedTile32768 910846208 910911744 13 3148 30180 30 _ _ (2062987 / 100000) (206299 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910911744 :
    ThetaLowerSegment 910911744 910977280 (45543446246199 / 50000) (2277340085297 / 2500) := by
  exact
    packedTile32768 910911744 910977280 13 3253 30181 30 _ _ (1031497 / 50000) (2062997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell910977280 :
    ThetaLowerSegment 910977280 911042816 (2277340085297 / 2500) (22775045064767 / 25000) := by
  exact
    packedTile32768 910977280 911042816 13 3188 30182 30 _ _ (2063001 / 100000) (515751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911042816 :
    ThetaLowerSegment 911042816 911108352 (22775045064767 / 25000) (18221341111307 / 20000) := by
  exact
    packedTile32768 911042816 911108352 13 3163 30183 30 _ _ (2063009 / 100000) (515753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911108352 :
    ThetaLowerSegment 911108352 911173888 (18221341111307 / 20000) (18222653189483 / 20000) := by
  exact
    packedTile32768 911108352 911173888 13 3180 30184 30 _ _ (257877 / 12500) (2063019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911173888 :
    ThetaLowerSegment 911173888 911239424 (18222653189483 / 20000) (91119842864739 / 100000) := by
  exact
    packedTile32768 911173888 911239424 13 3188 30185 30 _ _ (2063023 / 100000) (1031513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911239424 :
    ThetaLowerSegment 911239424 911304960 (91119842864739 / 100000) (91126370291659 / 100000) := by
  exact
    packedTile32768 911239424 911304960 13 3164 30186 30 _ _ (206303 / 10000) (2063033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911304960 :
    ThetaLowerSegment 911304960 911370496 (91126370291659 / 100000) (22783224950941 / 25000) := by
  exact
    packedTile32768 911304960 911370496 13 3165 30187 30 _ _ (2063037 / 100000) (12894 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911370496 :
    ThetaLowerSegment 911370496 911436032 (22783224950941 / 25000) (91139553123889 / 100000) := by
  exact
    packedTile32768 911370496 911436032 13 3225 30188 30 _ _ (412609 / 20000) (257881 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911436032 :
    ThetaLowerSegment 911436032 911501568 (91139553123889 / 100000) (91146045548533 / 100000) := by
  exact
    packedTile32768 911436032 911501568 13 3147 30189 30 _ _ (515763 / 25000) (412611 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911501568 :
    ThetaLowerSegment 911501568 911567104 (91146045548533 / 100000) (91152568941091 / 100000) := by
  exact
    packedTile32768 911501568 911567104 13 3162 30191 30 _ _ (2063059 / 100000) (1031531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911567104 :
    ThetaLowerSegment 911567104 911632640 (91152568941091 / 100000) (91159135680169 / 100000) := by
  exact
    packedTile32768 911567104 911632640 13 3183 30192 30 _ _ (1031533 / 50000) (2063069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911632640 :
    ThetaLowerSegment 911632640 911698176 (91159135680169 / 100000) (2848930780139 / 3125) := by
  exact
    packedTile32768 911632640 911698176 13 3223 30193 30 _ _ (2063073 / 100000) (515769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911698176 :
    ThetaLowerSegment 911698176 911763712 (2848930780139 / 3125) (11396538810811 / 12500) := by
  exact
    packedTile32768 911698176 911763712 13 3163 30194 30 _ _ (51577 / 2500) (2063083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911763712 :
    ThetaLowerSegment 911763712 911829248 (11396538810811 / 12500) (11397367914301 / 12500) := by
  exact
    packedTile32768 911763712 911829248 13 3215 30195 30 _ _ (128943 / 6250) (2063091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911829248 :
    ThetaLowerSegment 911829248 911894784 (11397367914301 / 12500) (91185518398173 / 100000) := by
  exact
    packedTile32768 911829248 911894784 13 3187 30196 30 _ _ (412619 / 20000) (1031549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911894784 :
    ThetaLowerSegment 911894784 911960320 (91185518398173 / 100000) (91192147144899 / 100000) := by
  exact
    packedTile32768 911894784 911960320 13 3213 30197 30 _ _ (1031551 / 50000) (412621 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell911960320 :
    ThetaLowerSegment 911960320 912025856 (91192147144899 / 100000) (22799673347439 / 25000) := by
  exact
    packedTile32768 911960320 912025856 13 3173 30198 30 _ _ (2063109 / 100000) (257889 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912025856 :
    ThetaLowerSegment 912025856 912091392 (22799673347439 / 25000) (11400667335799 / 12500) := by
  exact
    packedTile32768 912025856 912091392 13 3221 30199 30 _ _ (515779 / 25000) (2063119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912091392 :
    ThetaLowerSegment 912091392 912156928 (11400667335799 / 12500) (570074655059 / 625) := by
  exact
    packedTile32768 912091392 912156928 13 3202 30200 30 _ _ (515781 / 25000) (2063127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912156928 :
    ThetaLowerSegment 912156928 912222464 (570074655059 / 625) (22804622265243 / 25000) := by
  exact
    packedTile32768 912156928 912222464 13 3172 30201 30 _ _ (2063131 / 100000) (1031567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912222464 :
    ThetaLowerSegment 912222464 912288000 (22804622265243 / 25000) (45612480562439 / 50000) := by
  exact
    packedTile32768 912222464 912288000 13 3137 30203 30 _ _ (1031569 / 50000) (2063141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912288000 :
    ThetaLowerSegment 912288000 912353536 (45612480562439 / 50000) (91231540494283 / 100000) := by
  exact
    packedTile32768 912288000 912353536 13 3189 30204 30 _ _ (412629 / 20000) (515787 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912353536 :
    ThetaLowerSegment 912353536 912419072 (91231540494283 / 100000) (91238047675691 / 100000) := by
  exact
    packedTile32768 912353536 912419072 13 3154 30205 30 _ _ (128947 / 6250) (412631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912419072 :
    ThetaLowerSegment 912419072 912484608 (91238047675691 / 100000) (91244587889721 / 100000) := by
  exact
    packedTile32768 912419072 912484608 13 3170 30206 30 _ _ (2063159 / 100000) (1031581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912484608 :
    ThetaLowerSegment 912484608 912550144 (91244587889721 / 100000) (22812783579653 / 25000) := by
  exact
    packedTile32768 912484608 912550144 13 3173 30207 30 _ _ (2063167 / 100000) (206317 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912550144 :
    ThetaLowerSegment 912550144 912615680 (22812783579653 / 25000) (22814458876941 / 25000) := by
  exact
    packedTile32768 912550144 912615680 13 3248 30208 30 _ _ (1031587 / 50000) (2063177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912615680 :
    ThetaLowerSegment 912615680 912681216 (22814458876941 / 25000) (45632237412111 / 50000) := by
  exact
    packedTile32768 912615680 912681216 13 3218 30209 30 _ _ (2063181 / 100000) (128949 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912681216 :
    ThetaLowerSegment 912681216 912746752 (45632237412111 / 50000) (45635496217557 / 50000) := by
  exact
    packedTile32768 912681216 912746752 13 3159 30210 30 _ _ (515797 / 25000) (2063191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912746752 :
    ThetaLowerSegment 912746752 912812288 (45635496217557 / 50000) (91277596722309 / 100000) := by
  exact
    packedTile32768 912746752 912812288 13 3201 30211 30 _ _ (412639 / 20000) (1031599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912812288 :
    ThetaLowerSegment 912812288 912877824 (91277596722309 / 100000) (18256832366851 / 20000) := by
  exact
    packedTile32768 912812288 912877824 13 3182 30212 30 _ _ (2063203 / 100000) (1031603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912877824 :
    ThetaLowerSegment 912877824 912943360 (18256832366851 / 20000) (3651631967233 / 4000) := by
  exact
    packedTile32768 912877824 912943360 13 3217 30213 30 _ _ (206321 / 10000) (2063213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell912943360 :
    ThetaLowerSegment 912943360 913008896 (3651631967233 / 4000) (5706088494859 / 6250) := by
  exact
    packedTile32768 912943360 913008896 13 3207 30214 30 _ _ (2063217 / 100000) (103161 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913008896 :
    ThetaLowerSegment 913008896 913074432 (5706088494859 / 6250) (11412987063041 / 12500) := by
  exact
    packedTile32768 913008896 913074432 13 3141 30216 30 _ _ (257903 / 12500) (2063227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913074432 :
    ThetaLowerSegment 913074432 913139968 (11412987063041 / 12500) (45655181335141 / 50000) := by
  exact
    packedTile32768 913074432 913139968 13 3134 30217 30 _ _ (2063231 / 100000) (1031617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913139968 :
    ThetaLowerSegment 913139968 913205504 (45655181335141 / 50000) (2853650579437 / 3125) := by
  exact
    packedTile32768 913139968 913205504 13 3129 30218 30 _ _ (1031619 / 50000) (2063241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913205504 :
    ThetaLowerSegment 913205504 913271040 (2853650579437 / 3125) (45661647535589 / 50000) := by
  exact
    packedTile32768 913205504 913271040 13 3139 30219 30 _ _ (1031623 / 50000) (2063249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913271040 :
    ThetaLowerSegment 913271040 913336576 (45661647535589 / 50000) (45664878589787 / 50000) := by
  exact
    packedTile32768 913271040 913336576 13 3132 30220 30 _ _ (2063253 / 100000) (257907 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913336576 :
    ThetaLowerSegment 913336576 913402112 (45664878589787 / 50000) (45668141635477 / 50000) := by
  exact
    packedTile32768 913336576 913402112 13 3163 30221 30 _ _ (103163 / 5000) (2063263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913402112 :
    ThetaLowerSegment 913402112 913467648 (45668141635477 / 50000) (18268545370759 / 20000) := by
  exact
    packedTile32768 913402112 913467648 13 3123 30222 30 _ _ (2063267 / 100000) (206327 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913467648 :
    ThetaLowerSegment 913467648 913533184 (18268545370759 / 20000) (18269886498859 / 20000) := by
  exact
    packedTile32768 913467648 913533184 13 3250 30223 30 _ _ (1031637 / 50000) (2063277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913533184 :
    ThetaLowerSegment 913533184 913598720 (18269886498859 / 20000) (18271190493083 / 20000) := by
  exact
    packedTile32768 913533184 913598720 13 3160 30224 30 _ _ (1031641 / 50000) (412657 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913598720 :
    ThetaLowerSegment 913598720 913664256 (18271190493083 / 20000) (45681259957151 / 50000) := by
  exact
    packedTile32768 913598720 913664256 13 3183 30225 30 _ _ (2063289 / 100000) (515823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913664256 :
    ThetaLowerSegment 913664256 913729792 (45681259957151 / 50000) (45684582895359 / 50000) := by
  exact
    packedTile32768 913664256 913729792 13 3221 30226 30 _ _ (64478 / 3125) (2063299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913729792 :
    ThetaLowerSegment 913729792 913795328 (45684582895359 / 50000) (2855485410743 / 3125) := by
  exact
    packedTile32768 913729792 913795328 13 3086 30227 30 _ _ (2063303 / 100000) (1031653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913795328 :
    ThetaLowerSegment 913795328 913860864 (2855485410743 / 3125) (22845491636089 / 25000) := by
  exact
    packedTile32768 913795328 913860864 13 3118 30229 30 _ _ (206331 / 10000) (2063313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913860864 :
    ThetaLowerSegment 913860864 913926400 (22845491636089 / 25000) (91388600108511 / 100000) := by
  exact
    packedTile32768 913860864 913926400 13 3215 30230 30 _ _ (2063317 / 100000) (51583 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913926400 :
    ThetaLowerSegment 913926400 913991936 (91388600108511 / 100000) (91395128468811 / 100000) := by
  exact
    packedTile32768 913926400 913991936 13 3164 30231 30 _ _ (82533 / 4000) (64479 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell913991936 :
    ThetaLowerSegment 913991936 914057472 (91395128468811 / 100000) (18280342924911 / 20000) := by
  exact
    packedTile32768 913991936 914057472 13 3192 30232 30 _ _ (515833 / 25000) (412667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914057472 :
    ThetaLowerSegment 914057472 914123008 (18280342924911 / 20000) (4570415349633 / 5000) := by
  exact
    packedTile32768 914057472 914123008 13 3195 30233 30 _ _ (2063339 / 100000) (1031671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914123008 :
    ThetaLowerSegment 914123008 914188544 (4570415349633 / 5000) (2856719410017 / 3125) := by
  exact
    packedTile32768 914123008 914188544 13 3254 30234 30 _ _ (1031673 / 50000) (2063349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914188544 :
    ThetaLowerSegment 914188544 914254080 (2856719410017 / 3125) (91421634166909 / 100000) := by
  exact
    packedTile32768 914188544 914254080 13 3205 30235 30 _ _ (2063353 / 100000) (515839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914254080 :
    ThetaLowerSegment 914254080 914319616 (91421634166909 / 100000) (91428032646269 / 100000) := by
  exact
    packedTile32768 914254080 914319616 13 3101 30236 30 _ _ (12896 / 625) (2063363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914319616 :
    ThetaLowerSegment 914319616 914385152 (91428032646269 / 100000) (91434569396093 / 100000) := by
  exact
    packedTile32768 914319616 914385152 13 3168 30237 30 _ _ (257921 / 12500) (2063371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914385152 :
    ThetaLowerSegment 914385152 914450688 (91434569396093 / 100000) (91441201083343 / 100000) := by
  exact
    packedTile32768 914385152 914450688 13 3214 30238 30 _ _ (16507 / 800) (1031689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914450688 :
    ThetaLowerSegment 914450688 914516224 (91441201083343 / 100000) (91447748194429 / 100000) := by
  exact
    packedTile32768 914450688 914516224 13 3173 30239 30 _ _ (1031691 / 50000) (412677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914516224 :
    ThetaLowerSegment 914516224 914581760 (91447748194429 / 100000) (91454412940899 / 100000) := by
  exact
    packedTile32768 914516224 914581760 13 3230 30240 30 _ _ (2063389 / 100000) (64481 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914581760 :
    ThetaLowerSegment 914581760 914647296 (91454412940899 / 100000) (3658441127539 / 4000) := by
  exact
    packedTile32768 914581760 914647296 13 3206 30242 30 _ _ (515849 / 25000) (2063399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914647296 :
    ThetaLowerSegment 914647296 914712832 (3658441127539 / 4000) (91467494893477 / 100000) := by
  exact
    packedTile32768 914647296 914712832 13 3134 30243 30 _ _ (2063403 / 100000) (1031703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914712832 :
    ThetaLowerSegment 914712832 914778368 (91467494893477 / 100000) (45737039618989 / 50000) := by
  exact
    packedTile32768 914712832 914778368 13 3191 30244 30 _ _ (2063411 / 100000) (1031707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914778368 :
    ThetaLowerSegment 914778368 914843904 (45737039618989 / 50000) (9148060789253 / 10000) := by
  exact
    packedTile32768 914778368 914843904 13 3164 30245 30 _ _ (1031709 / 50000) (2063421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914843904 :
    ThetaLowerSegment 914843904 914909440 (9148060789253 / 10000) (9148719434513 / 10000) := by
  exact
    packedTile32768 914843904 914909440 13 3192 30246 30 _ _ (82537 / 4000) (515857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914909440 :
    ThetaLowerSegment 914909440 914974976 (9148719434513 / 10000) (45746885251457 / 50000) := by
  exact
    packedTile32768 914909440 914974976 13 3187 30247 30 _ _ (257929 / 12500) (412687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell914974976 :
    ThetaLowerSegment 914974976 915040512 (45746885251457 / 50000) (45750157865711 / 50000) := by
  exact
    packedTile32768 914974976 915040512 13 3172 30248 30 _ _ (2063439 / 100000) (1031721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915040512 :
    ThetaLowerSegment 915040512 915106048 (45750157865711 / 50000) (45753471759987 / 50000) := by
  exact
    packedTile32768 915040512 915106048 13 3212 30249 30 _ _ (1031723 / 50000) (2063449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915106048 :
    ThetaLowerSegment 915106048 915171584 (45753471759987 / 50000) (5719596015969 / 6250) := by
  exact
    packedTile32768 915106048 915171584 13 3195 30250 30 _ _ (1031727 / 50000) (2063457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915171584 :
    ThetaLowerSegment 915171584 915237120 (5719596015969 / 6250) (45759960301919 / 50000) := by
  exact
    packedTile32768 915171584 915237120 13 3094 30251 30 _ _ (2063461 / 100000) (257933 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915237120 :
    ThetaLowerSegment 915237120 915302656 (45759960301919 / 50000) (45763293834473 / 50000) := by
  exact
    packedTile32768 915237120 915302656 13 3231 30252 30 _ _ (515867 / 25000) (2063471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915302656 :
    ThetaLowerSegment 915302656 915368192 (45763293834473 / 50000) (45766566505823 / 50000) := by
  exact
    packedTile32768 915302656 915368192 13 3172 30253 30 _ _ (82539 / 4000) (1031739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915368192 :
    ThetaLowerSegment 915368192 915433728 (45766566505823 / 50000) (5721228995761 / 6250) := by
  exact
    packedTile32768 915368192 915433728 13 3165 30255 30 _ _ (1031741 / 50000) (412697 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915433728 :
    ThetaLowerSegment 915433728 915499264 (5721228995761 / 6250) (91546236144641 / 100000) := by
  exact
    packedTile32768 915433728 915499264 13 3185 30256 30 _ _ (2063489 / 100000) (515873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915499264 :
    ThetaLowerSegment 915499264 915564800 (91546236144641 / 100000) (91552711398227 / 100000) := by
  exact
    packedTile32768 915499264 915564800 13 3138 30257 30 _ _ (2063497 / 100000) (4127 / 200)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915564800 :
    ThetaLowerSegment 915564800 915630336 (91552711398227 / 100000) (91559430167251 / 100000) := by
  exact
    packedTile32768 915564800 915630336 13 3256 30258 30 _ _ (128969 / 6250) (2063507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915630336 :
    ThetaLowerSegment 915630336 915695872 (91559430167251 / 100000) (18313187696189 / 20000) := by
  exact
    packedTile32768 915630336 915695872 13 3154 30259 30 _ _ (2063511 / 100000) (1031757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915695872 :
    ThetaLowerSegment 915695872 915761408 (18313187696189 / 20000) (91572494277631 / 100000) := by
  exact
    packedTile32768 915695872 915761408 13 3177 30260 30 _ _ (1031759 / 50000) (2063521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915761408 :
    ThetaLowerSegment 915761408 915826944 (91572494277631 / 100000) (91579081049431 / 100000) := by
  exact
    packedTile32768 915761408 915826944 13 3192 30261 30 _ _ (82541 / 4000) (257941 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915826944 :
    ThetaLowerSegment 915826944 915892480 (91579081049431 / 100000) (91585630699999 / 100000) := by
  exact
    packedTile32768 915826944 915892480 13 3174 30262 30 _ _ (515883 / 25000) (412707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915892480 :
    ThetaLowerSegment 915892480 915958016 (91585630699999 / 100000) (22898045609081 / 25000) := by
  exact
    packedTile32768 915892480 915958016 13 3175 30263 30 _ _ (2063539 / 100000) (1031771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell915958016 :
    ThetaLowerSegment 915958016 916023552 (22898045609081 / 25000) (2289966962057 / 2500) := by
  exact
    packedTile32768 915958016 916023552 13 3148 30264 30 _ _ (2063547 / 100000) (41271 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916023552 :
    ThetaLowerSegment 916023552 916089088 (2289966962057 / 2500) (45802662594857 / 50000) := by
  exact
    packedTile32768 916023552 916089088 13 3221 30265 30 _ _ (1031777 / 50000) (2063557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916089088 :
    ThetaLowerSegment 916089088 916154624 (45802662594857 / 50000) (91611980173939 / 100000) := by
  exact
    packedTile32768 916089088 916154624 13 3225 30266 30 _ _ (2063561 / 100000) (515891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916154624 :
    ThetaLowerSegment 916154624 916220160 (91611980173939 / 100000) (91618612481491 / 100000) := by
  exact
    packedTile32768 916154624 916220160 13 3214 30268 30 _ _ (128973 / 6250) (2063571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916220160 :
    ThetaLowerSegment 916220160 916285696 (91618612481491 / 100000) (91625224175791 / 100000) := by
  exact
    packedTile32768 916220160 916285696 13 3204 30269 30 _ _ (82543 / 4000) (1031789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916285696 :
    ThetaLowerSegment 916285696 916351232 (91625224175791 / 100000) (91631761603567 / 100000) := by
  exact
    packedTile32768 916285696 916351232 13 3168 30270 30 _ _ (1031791 / 50000) (412717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916351232 :
    ThetaLowerSegment 916351232 916416768 (91631761603567 / 100000) (91638332074127 / 100000) := by
  exact
    packedTile32768 916351232 916416768 13 3184 30271 30 _ _ (206359 / 10000) (2063593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916416768 :
    ThetaLowerSegment 916416768 916482304 (91638332074127 / 100000) (11455591411053 / 12500) := by
  exact
    packedTile32768 916416768 916482304 13 3101 30272 30 _ _ (2063597 / 100000) (5159 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916482304 :
    ThetaLowerSegment 916482304 916547840 (11455591411053 / 12500) (22912854857247 / 25000) := by
  exact
    packedTile32768 916482304 916547840 13 3241 30273 30 _ _ (515901 / 25000) (2063607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916547840 :
    ThetaLowerSegment 916547840 916613376 (22912854857247 / 25000) (22914464473827 / 25000) := by
  exact
    packedTile32768 916547840 916613376 13 3120 30274 30 _ _ (2063611 / 100000) (1031807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916613376 :
    ThetaLowerSegment 916613376 916678912 (22914464473827 / 25000) (22916094732047 / 25000) := by
  exact
    packedTile32768 916613376 916678912 13 3160 30275 30 _ _ (1031809 / 50000) (2063621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916678912 :
    ThetaLowerSegment 916678912 916744448 (22916094732047 / 25000) (45835505709469 / 50000) := by
  exact
    packedTile32768 916678912 916744448 13 3214 30276 30 _ _ (16509 / 800) (515907 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916744448 :
    ThetaLowerSegment 916744448 916809984 (45835505709469 / 50000) (45838806488853 / 50000) := by
  exact
    packedTile32768 916744448 916809984 13 3199 30277 30 _ _ (128977 / 6250) (412727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916809984 :
    ThetaLowerSegment 916809984 916875520 (45838806488853 / 50000) (45842020608153 / 50000) := by
  exact
    packedTile32768 916809984 916875520 13 3115 30278 30 _ _ (51591 / 2500) (2063643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916875520 :
    ThetaLowerSegment 916875520 916941056 (45842020608153 / 50000) (11461337317691 / 12500) := by
  exact
    packedTile32768 916875520 916941056 13 3226 30279 30 _ _ (2063647 / 100000) (41273 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell916941056 :
    ThetaLowerSegment 916941056 917006592 (11461337317691 / 12500) (45848584048409 / 50000) := by
  exact
    packedTile32768 916941056 917006592 13 3135 30281 30 _ _ (1031827 / 50000) (2063657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917006592 :
    ThetaLowerSegment 917006592 917072128 (45848584048409 / 50000) (91703691329239 / 100000) := by
  exact
    packedTile32768 917006592 917072128 13 3161 30282 30 _ _ (2063661 / 100000) (128979 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917072128 :
    ThetaLowerSegment 917072128 917137664 (91703691329239 / 100000) (91710212520119 / 100000) := by
  exact
    packedTile32768 917072128 917137664 13 3160 30283 30 _ _ (515917 / 25000) (2063671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917137664 :
    ThetaLowerSegment 917137664 917203200 (91710212520119 / 100000) (5732300372609 / 6250) := by
  exact
    packedTile32768 917137664 917203200 13 3195 30284 30 _ _ (82547 / 4000) (1031839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917203200 :
    ThetaLowerSegment 917203200 917268736 (5732300372609 / 6250) (9172341593519 / 10000) := by
  exact
    packedTile32768 917203200 917268736 13 3203 30285 30 _ _ (1031841 / 50000) (412737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917268736 :
    ThetaLowerSegment 917268736 917334272 (9172341593519 / 10000) (9172994957773 / 10000) := by
  exact
    packedTile32768 917268736 917334272 13 3166 30286 30 _ _ (206369 / 10000) (2063693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917334272 :
    ThetaLowerSegment 917334272 917399808 (9172994957773 / 10000) (91736415140431 / 100000) := by
  exact
    packedTile32768 917334272 917399808 13 3133 30287 30 _ _ (2063697 / 100000) (20637 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917399808 :
    ThetaLowerSegment 917399808 917465344 (91736415140431 / 100000) (91742973591743 / 100000) := by
  exact
    packedTile32768 917399808 917465344 13 3178 30288 30 _ _ (257963 / 12500) (2063707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917465344 :
    ThetaLowerSegment 917465344 917530880 (91742973591743 / 100000) (11468670097161 / 12500) := by
  exact
    packedTile32768 917465344 917530880 13 3095 30289 30 _ _ (2063711 / 100000) (1031857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917530880 :
    ThetaLowerSegment 917530880 917596416 (11468670097161 / 12500) (1146950693481 / 1250) := by
  exact
    packedTile32768 917530880 917596416 13 3244 30290 30 _ _ (1031859 / 50000) (2063721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917596416 :
    ThetaLowerSegment 917596416 917661952 (1146950693481 / 1250) (18352522386561 / 20000) := by
  exact
    packedTile32768 917596416 917661952 13 3177 30291 30 _ _ (82549 / 4000) (128983 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917661952 :
    ThetaLowerSegment 917661952 917727488 (18352522386561 / 20000) (91769151899513 / 100000) := by
  exact
    packedTile32768 917661952 917727488 13 3169 30292 30 _ _ (515933 / 25000) (412747 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917727488 :
    ThetaLowerSegment 917727488 917793024 (91769151899513 / 100000) (91775464880173 / 100000) := by
  exact
    packedTile32768 917727488 917793024 13 3059 30294 30 _ _ (103187 / 5000) (2063743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917793024 :
    ThetaLowerSegment 917793024 917858560 (91775464880173 / 100000) (45891037530907 / 50000) := by
  exact
    packedTile32768 917793024 917858560 13 3203 30295 30 _ _ (2063747 / 100000) (1651 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917858560 :
    ThetaLowerSegment 917858560 917924096 (45891037530907 / 50000) (11473565536633 / 12500) := by
  exact
    packedTile32768 917858560 917924096 13 3125 30296 30 _ _ (1031877 / 50000) (2063757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917924096 :
    ThetaLowerSegment 917924096 917989632 (11473565536633 / 12500) (9179501688517 / 10000) := by
  exact
    packedTile32768 917924096 917989632 13 3146 30297 30 _ _ (2063761 / 100000) (515941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell917989632 :
    ThetaLowerSegment 917989632 918055168 (9179501688517 / 10000) (45900776419213 / 50000) := by
  exact
    packedTile32768 917989632 918055168 13 3167 30298 30 _ _ (257971 / 12500) (2063771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918055168 :
    ThetaLowerSegment 918055168 918120704 (45900776419213 / 50000) (2869004516743 / 3125) := by
  exact
    packedTile32768 918055168 918120704 13 3194 30299 30 _ _ (82551 / 4000) (1031889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918120704 :
    ThetaLowerSegment 918120704 918186240 (2869004516743 / 3125) (45907296927263 / 50000) := by
  exact
    packedTile32768 918120704 918186240 13 3125 30300 30 _ _ (1031891 / 50000) (412757 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918186240 :
    ThetaLowerSegment 918186240 918251776 (45907296927263 / 50000) (11477654649317 / 12500) := by
  exact
    packedTile32768 918186240 918251776 13 3219 30301 30 _ _ (206379 / 10000) (2063793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918251776 :
    ThetaLowerSegment 918251776 918317312 (11477654649317 / 12500) (45913877332731 / 50000) := by
  exact
    packedTile32768 918251776 918317312 13 3158 30302 30 _ _ (2063797 / 100000) (10319 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918317312 :
    ThetaLowerSegment 918317312 918382848 (45913877332731 / 50000) (45917147430169 / 50000) := by
  exact
    packedTile32768 918317312 918382848 13 3169 30303 30 _ _ (515951 / 25000) (2063807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918382848 :
    ThetaLowerSegment 918382848 918448384 (45917147430169 / 50000) (45920499059233 / 50000) := by
  exact
    packedTile32768 918382848 918448384 13 3248 30304 30 _ _ (2063811 / 100000) (1031907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918448384 :
    ThetaLowerSegment 918448384 918513920 (45920499059233 / 50000) (11480947970213 / 12500) := by
  exact
    packedTile32768 918448384 918513920 13 3191 30305 30 _ _ (1031909 / 50000) (2063821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918513920 :
    ThetaLowerSegment 918513920 918579456 (11480947970213 / 12500) (91854115767829 / 100000) := by
  exact
    packedTile32768 918513920 918579456 13 3165 30306 30 _ _ (82553 / 4000) (515957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918579456 :
    ThetaLowerSegment 918579456 918644992 (91854115767829 / 100000) (91860635413117 / 100000) := by
  exact
    packedTile32768 918579456 918644992 13 3159 30308 30 _ _ (257979 / 12500) (412767 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918644992 :
    ThetaLowerSegment 918644992 918710528 (91860635413117 / 100000) (91867204615837 / 100000) := by
  exact
    packedTile32768 918644992 918710528 13 3183 30309 30 _ _ (12899 / 625) (2063843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918710528 :
    ThetaLowerSegment 918710528 918776064 (91867204615837 / 100000) (91873759393909 / 100000) := by
  exact
    packedTile32768 918710528 918776064 13 3176 30310 30 _ _ (2063847 / 100000) (41277 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918776064 :
    ThetaLowerSegment 918776064 918841600 (91873759393909 / 100000) (91880328641191 / 100000) := by
  exact
    packedTile32768 918776064 918841600 13 3183 30311 30 _ _ (1031927 / 50000) (2063857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918841600 :
    ThetaLowerSegment 918841600 918907136 (91880328641191 / 100000) (18377392378089 / 20000) := by
  exact
    packedTile32768 918841600 918907136 13 3214 30312 30 _ _ (2063861 / 100000) (257983 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918907136 :
    ThetaLowerSegment 918907136 918972672 (18377392378089 / 20000) (91893661205973 / 100000) := by
  exact
    packedTile32768 918907136 918972672 13 3246 30313 30 _ _ (515967 / 25000) (2063871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell918972672 :
    ThetaLowerSegment 918972672 919038208 (91893661205973 / 100000) (91900154156723 / 100000) := by
  exact
    packedTile32768 918972672 919038208 13 3146 30314 30 _ _ (16511 / 800) (1031939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919038208 :
    ThetaLowerSegment 919038208 919103744 (91900154156723 / 100000) (91906723493129 / 100000) := by
  exact
    packedTile32768 919038208 919103744 13 3183 30315 30 _ _ (1031941 / 50000) (412777 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919103744 :
    ThetaLowerSegment 919103744 919169280 (91906723493129 / 100000) (91913237126813 / 100000) := by
  exact
    packedTile32768 919103744 919169280 13 3156 30316 30 _ _ (2063889 / 100000) (515973 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919169280 :
    ThetaLowerSegment 919169280 919234816 (91913237126813 / 100000) (22979964011123 / 25000) := by
  exact
    packedTile32768 919169280 919234816 13 3207 30317 30 _ _ (2063897 / 100000) (20639 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919234816 :
    ThetaLowerSegment 919234816 919300352 (22979964011123 / 25000) (22981591915403 / 25000) := by
  exact
    packedTile32768 919234816 919300352 13 3155 30318 30 _ _ (64497 / 3125) (2063907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919300352 :
    ThetaLowerSegment 919300352 919365888 (22981591915403 / 25000) (91932932962503 / 100000) := by
  exact
    packedTile32768 919300352 919365888 13 3181 30319 30 _ _ (2063911 / 100000) (1031957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919365888 :
    ThetaLowerSegment 919365888 919431424 (91932932962503 / 100000) (91939378578417 / 100000) := by
  exact
    packedTile32768 919365888 919431424 13 3123 30321 30 _ _ (1031959 / 50000) (2063921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919431424 :
    ThetaLowerSegment 919431424 919496960 (91939378578417 / 100000) (91946016161217 / 100000) := by
  exact
    packedTile32768 919431424 919496960 13 3216 30322 30 _ _ (82557 / 4000) (257991 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919496960 :
    ThetaLowerSegment 919496960 919562496 (91946016161217 / 100000) (91952521674881 / 100000) := by
  exact
    packedTile32768 919496960 919562496 13 3152 30323 30 _ _ (515983 / 25000) (412787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919562496 :
    ThetaLowerSegment 919562496 919628032 (91952521674881 / 100000) (22989794469539 / 25000) := by
  exact
    packedTile32768 919562496 919628032 13 3225 30324 30 _ _ (2063939 / 100000) (1031971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919628032 :
    ThetaLowerSegment 919628032 919693568 (22989794469539 / 25000) (45982902604381 / 50000) := by
  exact
    packedTile32768 919628032 919693568 13 3211 30325 30 _ _ (1031973 / 50000) (2063949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919693568 :
    ThetaLowerSegment 919693568 919759104 (45982902604381 / 50000) (22993092661609 / 25000) := by
  exact
    packedTile32768 919693568 919759104 13 3181 30326 30 _ _ (1031977 / 50000) (2063957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919759104 :
    ThetaLowerSegment 919759104 919824640 (22993092661609 / 25000) (91978940234299 / 100000) := by
  exact
    packedTile32768 919759104 919824640 13 3183 30327 30 _ _ (2063961 / 100000) (515991 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919824640 :
    ThetaLowerSegment 919824640 919890176 (91978940234299 / 100000) (91985540803963 / 100000) := by
  exact
    packedTile32768 919824640 919890176 13 3198 30328 30 _ _ (64499 / 3125) (2063971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919890176 :
    ThetaLowerSegment 919890176 919955712 (91985540803963 / 100000) (45996106817569 / 50000) := by
  exact
    packedTile32768 919890176 919955712 13 3233 30329 30 _ _ (82559 / 4000) (1031989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell919955712 :
    ThetaLowerSegment 919955712 920021248 (45996106817569 / 50000) (45999365845147 / 50000) := by
  exact
    packedTile32768 919955712 920021248 13 3158 30330 30 _ _ (1031991 / 50000) (412797 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920021248 :
    ThetaLowerSegment 920021248 920086784 (45999365845147 / 50000) (4600264139569 / 5000) := by
  exact
    packedTile32768 920021248 920086784 13 3174 30331 30 _ _ (2063989 / 100000) (257999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920086784 :
    ThetaLowerSegment 920086784 920152320 (4600264139569 / 5000) (23002970862647 / 25000) := by
  exact
    packedTile32768 920086784 920152320 13 3198 30332 30 _ _ (515999 / 25000) (2063999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920152320 :
    ThetaLowerSegment 920152320 920217856 (23002970862647 / 25000) (92018411892077 / 100000) := by
  exact
    packedTile32768 920152320 920217856 13 3163 30334 30 _ _ (2064003 / 100000) (1032003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920217856 :
    ThetaLowerSegment 920217856 920283392 (92018411892077 / 100000) (92024855734419 / 100000) := by
  exact
    packedTile32768 920217856 920283392 13 3122 30335 30 _ _ (2064011 / 100000) (1032007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920283392 :
    ThetaLowerSegment 920283392 920348928 (92024855734419 / 100000) (92031522512559 / 100000) := by
  exact
    packedTile32768 920283392 920348928 13 3230 30336 30 _ _ (1032009 / 50000) (2064021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920348928 :
    ThetaLowerSegment 920348928 920414464 (92031522512559 / 100000) (92038218209659 / 100000) := by
  exact
    packedTile32768 920348928 920414464 13 3244 30337 30 _ _ (82561 / 4000) (516007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920414464 :
    ThetaLowerSegment 920414464 920480000 (92038218209659 / 100000) (92044691014011 / 100000) := by
  exact
    packedTile32768 920414464 920480000 13 3136 30338 30 _ _ (64501 / 3125) (412807 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920480000 :
    ThetaLowerSegment 920480000 920545536 (92044691014011 / 100000) (92051312451123 / 100000) := by
  exact
    packedTile32768 920480000 920545536 13 3208 30339 30 _ _ (2064039 / 100000) (1032021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920545536 :
    ThetaLowerSegment 920545536 920611072 (92051312451123 / 100000) (92057770851057 / 100000) := by
  exact
    packedTile32768 920545536 920611072 13 3129 30340 30 _ _ (1032023 / 50000) (2064049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920611072 :
    ThetaLowerSegment 920611072 920676608 (92057770851057 / 100000) (23016076926727 / 25000) := by
  exact
    packedTile32768 920611072 920676608 13 3167 30341 30 _ _ (2064053 / 100000) (258007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920676608 :
    ThetaLowerSegment 920676608 920742144 (23016076926727 / 25000) (23017720950517 / 25000) := by
  exact
    packedTile32768 920676608 920742144 13 3186 30342 30 _ _ (103203 / 5000) (2064063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920742144 :
    ThetaLowerSegment 920742144 920807680 (23017720950517 / 25000) (2877421719121 / 3125) := by
  exact
    packedTile32768 920742144 920807680 13 3203 30343 30 _ _ (516017 / 25000) (2064071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920807680 :
    ThetaLowerSegment 920807680 920873216 (2877421719121 / 3125) (92084147525597 / 100000) := by
  exact
    packedTile32768 920807680 920873216 13 3223 30344 30 _ _ (82563 / 4000) (1032039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920873216 :
    ThetaLowerSegment 920873216 920938752 (92084147525597 / 100000) (92090746395751 / 100000) := by
  exact
    packedTile32768 920873216 920938752 13 3197 30345 30 _ _ (1032041 / 50000) (412817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell920938752 :
    ThetaLowerSegment 920938752 921004288 (92090746395751 / 100000) (73677866323 / 80) := by
  exact
    packedTile32768 920938752 921004288 13 3191 30346 30 _ _ (2064089 / 100000) (516023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921004288 :
    ThetaLowerSegment 921004288 921069824 (73677866323 / 80) (46051976229811 / 50000) := by
  exact
    packedTile32768 921004288 921069824 13 3207 30348 30 _ _ (64503 / 3125) (2064099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921069824 :
    ThetaLowerSegment 921069824 921135360 (46051976229811 / 50000) (2302762185243 / 2500) := by
  exact
    packedTile32768 921069824 921135360 13 3166 30349 30 _ _ (2064103 / 100000) (1032053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921135360 :
    ThetaLowerSegment 921135360 921200896 (2302762185243 / 2500) (4605851119099 / 5000) := by
  exact
    packedTile32768 921135360 921200896 13 3166 30350 30 _ _ (206411 / 10000) (2064113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921200896 :
    ThetaLowerSegment 921200896 921266432 (4605851119099 / 5000) (46061716764691 / 50000) := by
  exact
    packedTile32768 921200896 921266432 13 3106 30351 30 _ _ (2064117 / 100000) (51603 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921266432 :
    ThetaLowerSegment 921266432 921331968 (46061716764691 / 50000) (46064981176797 / 50000) := by
  exact
    packedTile32768 921266432 921331968 13 3163 30352 30 _ _ (516031 / 25000) (2064127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921331968 :
    ThetaLowerSegment 921331968 921397504 (46064981176797 / 50000) (46068228056433 / 50000) := by
  exact
    packedTile32768 921331968 921397504 13 3146 30353 30 _ _ (516033 / 25000) (412827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921397504 :
    ThetaLowerSegment 921397504 921463040 (46068228056433 / 50000) (92142972599689 / 100000) := by
  exact
    packedTile32768 921397504 921463040 13 3157 30354 30 _ _ (2064139 / 100000) (1032071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921463040 :
    ThetaLowerSegment 921463040 921528576 (92142972599689 / 100000) (18429909793769 / 20000) := by
  exact
    packedTile32768 921463040 921528576 13 3186 30355 30 _ _ (1032073 / 50000) (2064149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921528576 :
    ThetaLowerSegment 921528576 921594112 (18429909793769 / 20000) (46078036878239 / 50000) := by
  exact
    packedTile32768 921528576 921594112 13 3161 30356 30 _ _ (2064153 / 100000) (516039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921594112 :
    ThetaLowerSegment 921594112 921659648 (46078036878239 / 50000) (46081323020959 / 50000) := by
  exact
    packedTile32768 921594112 921659648 13 3184 30357 30 _ _ (12901 / 625) (2064163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921659648 :
    ThetaLowerSegment 921659648 921725184 (46081323020959 / 50000) (92169286467157 / 100000) := by
  exact
    packedTile32768 921659648 921725184 13 3217 30358 30 _ _ (2064167 / 100000) (206417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921725184 :
    ThetaLowerSegment 921725184 921790720 (92169286467157 / 100000) (18435168869591 / 20000) := by
  exact
    packedTile32768 921725184 921790720 13 3177 30359 30 _ _ (1032087 / 50000) (2064177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921790720 :
    ThetaLowerSegment 921790720 921856256 (18435168869591 / 20000) (230455840493 / 250) := by
  exact
    packedTile32768 921790720 921856256 13 3145 30361 30 _ _ (2064181 / 100000) (258023 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921856256 :
    ThetaLowerSegment 921856256 921921792 (230455840493 / 250) (2880904682986 / 3125) := by
  exact
    packedTile32768 921856256 921921792 13 3204 30362 30 _ _ (516047 / 25000) (2064191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921921792 :
    ThetaLowerSegment 921921792 921987328 (2880904682986 / 3125) (23048856309601 / 25000) := by
  exact
    packedTile32768 921921792 921987328 13 3137 30363 30 _ _ (516049 / 25000) (2064199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell921987328 :
    ThetaLowerSegment 921987328 922052864 (23048856309601 / 25000) (92201979082929 / 100000) := by
  exact
    packedTile32768 921987328 922052864 13 3175 30364 30 _ _ (2064203 / 100000) (1032103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922052864 :
    ThetaLowerSegment 922052864 922118400 (92201979082929 / 100000) (92208481344429 / 100000) := by
  exact
    packedTile32768 922052864 922118400 13 3150 30365 30 _ _ (206421 / 10000) (2064213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922118400 :
    ThetaLowerSegment 922118400 922183936 (92208481344429 / 100000) (92215029040753 / 100000) := by
  exact
    packedTile32768 922118400 922183936 13 3172 30366 30 _ _ (2064217 / 100000) (103211 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922183936 :
    ThetaLowerSegment 922183936 922249472 (92215029040753 / 100000) (92221601529969 / 100000) := by
  exact
    packedTile32768 922183936 922249472 13 3184 30367 30 _ _ (64507 / 3125) (2064227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922249472 :
    ThetaLowerSegment 922249472 922315008 (92221601529969 / 100000) (92228194683783 / 100000) := by
  exact
    packedTile32768 922249472 922315008 13 3194 30368 30 _ _ (2064231 / 100000) (1032117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922315008 :
    ThetaLowerSegment 922315008 922380544 (92228194683783 / 100000) (737877724893 / 800) := by
  exact
    packedTile32768 922315008 922380544 13 3159 30369 30 _ _ (1032119 / 50000) (2064241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922380544 :
    ThetaLowerSegment 922380544 922446080 (737877724893 / 800) (2306029881917 / 2500) := by
  exact
    packedTile32768 922380544 922446080 13 3139 30370 30 _ _ (412849 / 20000) (258031 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922446080 :
    ThetaLowerSegment 922446080 922511616 (2306029881917 / 2500) (11530966853377 / 12500) := by
  exact
    packedTile32768 922446080 922511616 13 3168 30371 30 _ _ (516063 / 25000) (412851 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922511616 :
    ThetaLowerSegment 922511616 922577152 (11530966853377 / 12500) (2882944913938 / 3125) := by
  exact
    packedTile32768 922511616 922577152 13 3150 30372 30 _ _ (103213 / 5000) (2064263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922577152 :
    ThetaLowerSegment 922577152 922642688 (2882944913938 / 3125) (23065188018167 / 25000) := by
  exact
    packedTile32768 922577152 922642688 13 3156 30373 30 _ _ (2064267 / 100000) (206427 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922642688 :
    ThetaLowerSegment 922642688 922708224 (23065188018167 / 25000) (11533402688423 / 12500) := by
  exact
    packedTile32768 922642688 922708224 13 3134 30375 30 _ _ (1032137 / 50000) (2064277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922708224 :
    ThetaLowerSegment 922708224 922773760 (11533402688423 / 12500) (92273858170799 / 100000) := by
  exact
    packedTile32768 922708224 922773760 13 3215 30376 30 _ _ (2064281 / 100000) (516071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922773760 :
    ThetaLowerSegment 922773760 922839296 (92273858170799 / 100000) (92280350356559 / 100000) := by
  exact
    packedTile32768 922773760 922839296 13 3145 30377 30 _ _ (64509 / 3125) (2064291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922839296 :
    ThetaLowerSegment 922839296 922904832 (92280350356559 / 100000) (23071748830541 / 25000) := by
  exact
    packedTile32768 922839296 922904832 13 3219 30378 30 _ _ (412859 / 20000) (1032149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922904832 :
    ThetaLowerSegment 922904832 922970368 (23071748830541 / 25000) (9229350406637 / 10000) := by
  exact
    packedTile32768 922904832 922970368 13 3153 30379 30 _ _ (1032151 / 50000) (412861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell922970368 :
    ThetaLowerSegment 922970368 923035904 (9229350406637 / 10000) (92300091276389 / 100000) := by
  exact
    packedTile32768 922970368 923035904 13 3191 30380 30 _ _ (2064309 / 100000) (258039 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923035904 :
    ThetaLowerSegment 923035904 923101440 (92300091276389 / 100000) (92306666122849 / 100000) := by
  exact
    packedTile32768 923035904 923101440 13 3185 30381 30 _ _ (516079 / 25000) (2064319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923101440 :
    ThetaLowerSegment 923101440 923166976 (92306666122849 / 100000) (5769571885087 / 6250) := by
  exact
    packedTile32768 923101440 923166976 13 3141 30382 30 _ _ (2064323 / 100000) (1032163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923166976 :
    ThetaLowerSegment 923166976 923232512 (5769571885087 / 6250) (92319650739711 / 100000) := by
  exact
    packedTile32768 923166976 923232512 13 3149 30383 30 _ _ (2064331 / 100000) (1032167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923232512 :
    ThetaLowerSegment 923232512 923298048 (92319650739711 / 100000) (92326287586381 / 100000) := by
  exact
    packedTile32768 923232512 923298048 13 3215 30384 30 _ _ (1032169 / 50000) (2064341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923298048 :
    ThetaLowerSegment 923298048 923363584 (92326287586381 / 100000) (11541604203047 / 12500) := by
  exact
    packedTile32768 923298048 923363584 13 3171 30385 30 _ _ (412869 / 20000) (516087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923363584 :
    ThetaLowerSegment 923363584 923429120 (11541604203047 / 12500) (11542411880767 / 12500) := by
  exact
    packedTile32768 923363584 923429120 13 3130 30386 30 _ _ (64511 / 3125) (412871 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923429120 :
    ThetaLowerSegment 923429120 923494656 (11542411880767 / 12500) (23086477313093 / 25000) := by
  exact
    packedTile32768 923429120 923494656 13 3204 30387 30 _ _ (2064359 / 100000) (1032181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923494656 :
    ThetaLowerSegment 923494656 923560192 (23086477313093 / 25000) (46176120331447 / 50000) := by
  exact
    packedTile32768 923494656 923560192 13 3067 30389 30 _ _ (1032183 / 50000) (2064369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923560192 :
    ThetaLowerSegment 923560192 923625728 (46176120331447 / 50000) (92358972583247 / 100000) := by
  exact
    packedTile32768 923560192 923625728 13 3261 30390 30 _ _ (2064373 / 100000) (258047 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923625728 :
    ThetaLowerSegment 923625728 923691264 (92358972583247 / 100000) (92365512539087 / 100000) := by
  exact
    packedTile32768 923625728 923691264 13 3168 30391 30 _ _ (103219 / 5000) (2064383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923691264 :
    ThetaLowerSegment 923691264 923756800 (92365512539087 / 100000) (92372015358137 / 100000) := by
  exact
    packedTile32768 923691264 923756800 13 3150 30392 30 _ _ (2064387 / 100000) (206439 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923756800 :
    ThetaLowerSegment 923756800 923822336 (92372015358137 / 100000) (3695140893121 / 4000) := by
  exact
    packedTile32768 923756800 923822336 13 3152 30393 30 _ _ (1032197 / 50000) (2064397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923822336 :
    ThetaLowerSegment 923822336 923887872 (3695140893121 / 4000) (92385116028013 / 100000) := by
  exact
    packedTile32768 923822336 923887872 13 3194 30394 30 _ _ (1032201 / 50000) (412881 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923887872 :
    ThetaLowerSegment 923887872 923953408 (92385116028013 / 100000) (92391590014637 / 100000) := by
  exact
    packedTile32768 923887872 923953408 13 3136 30395 30 _ _ (2064409 / 100000) (516103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell923953408 :
    ThetaLowerSegment 923953408 924018944 (92391590014637 / 100000) (3695927267797 / 4000) := by
  exact
    packedTile32768 923953408 924018944 13 3193 30396 30 _ _ (64513 / 3125) (2064419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924018944 :
    ThetaLowerSegment 924018944 924084480 (3695927267797 / 4000) (46202372247821 / 50000) := by
  exact
    packedTile32768 924018944 924084480 13 3179 30397 30 _ _ (2064423 / 100000) (1032213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924084480 :
    ThetaLowerSegment 924084480 924150016 (46202372247821 / 50000) (46205638176081 / 50000) := by
  exact
    packedTile32768 924084480 924150016 13 3164 30398 30 _ _ (206443 / 10000) (2064433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924150016 :
    ThetaLowerSegment 924150016 924215552 (46205638176081 / 50000) (46208953661903 / 50000) := by
  exact
    packedTile32768 924150016 924215552 13 3212 30399 30 _ _ (2064437 / 100000) (51611 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924215552 :
    ThetaLowerSegment 924215552 924281088 (46208953661903 / 50000) (9242442270907 / 10000) := by
  exact
    packedTile32768 924215552 924281088 13 3156 30400 30 _ _ (516111 / 25000) (2064447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924281088 :
    ThetaLowerSegment 924281088 924346624 (9242442270907 / 10000) (46215518605037 / 50000) := by
  exact
    packedTile32768 924281088 924346624 13 3204 30401 30 _ _ (2064451 / 100000) (1032227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924346624 :
    ThetaLowerSegment 924346624 924412160 (46215518605037 / 50000) (4621875670741 / 5000) := by
  exact
    packedTile32768 924346624 924412160 13 3137 30403 30 _ _ (1032229 / 50000) (2064461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924412160 :
    ThetaLowerSegment 924412160 924477696 (4621875670741 / 5000) (462220309489 / 500) := by
  exact
    packedTile32768 924412160 924477696 13 3172 30404 30 _ _ (412893 / 20000) (516117 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924477696 :
    ThetaLowerSegment 924477696 924543232 (462220309489 / 500) (11556338171087 / 12500) := by
  exact
    packedTile32768 924477696 924543232 13 3218 30405 30 _ _ (258059 / 12500) (82579 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924543232 :
    ThetaLowerSegment 924543232 924608768 (11556338171087 / 12500) (11557156995467 / 12500) := by
  exact
    packedTile32768 924543232 924608768 13 3173 30406 30 _ _ (12903 / 625) (2064483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924608768 :
    ThetaLowerSegment 924608768 924674304 (11557156995467 / 12500) (46231883677867 / 50000) := by
  exact
    packedTile32768 924608768 924674304 13 3154 30407 30 _ _ (2064487 / 100000) (206449 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924674304 :
    ThetaLowerSegment 924674304 924739840 (46231883677867 / 50000) (46235157965351 / 50000) := by
  exact
    packedTile32768 924674304 924739840 13 3172 30408 30 _ _ (1032247 / 50000) (2064497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924739840 :
    ThetaLowerSegment 924739840 924805376 (46235157965351 / 50000) (5779802742679 / 6250) := by
  exact
    packedTile32768 924739840 924805376 13 3162 30409 30 _ _ (2064501 / 100000) (258063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924805376 :
    ThetaLowerSegment 924805376 924870912 (5779802742679 / 6250) (23120838319147 / 25000) := by
  exact
    packedTile32768 924805376 924870912 13 3153 30410 30 _ _ (516127 / 25000) (2064511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924870912 :
    ThetaLowerSegment 924870912 924936448 (23120838319147 / 25000) (92489858563353 / 100000) := by
  exact
    packedTile32768 924870912 924936448 13 3151 30411 30 _ _ (412903 / 20000) (1032259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell924936448 :
    ThetaLowerSegment 924936448 925001984 (92489858563353 / 100000) (92496473291841 / 100000) := by
  exact
    packedTile32768 924936448 925001984 13 3204 30412 30 _ _ (1032261 / 50000) (82581 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925001984 :
    ThetaLowerSegment 925001984 925067520 (92496473291841 / 100000) (92503100429931 / 100000) := by
  exact
    packedTile32768 925001984 925067520 13 3210 30413 30 _ _ (2064529 / 100000) (516133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925067520 :
    ThetaLowerSegment 925067520 925133056 (92503100429931 / 100000) (92509702816059 / 100000) := by
  exact
    packedTile32768 925067520 925133056 13 3198 30414 30 _ _ (258067 / 12500) (2064539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925133056 :
    ThetaLowerSegment 925133056 925198592 (92509702816059 / 100000) (18503258567463 / 20000) := by
  exact
    packedTile32768 925133056 925198592 13 3192 30416 30 _ _ (2064543 / 100000) (1032273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925198592 :
    ThetaLowerSegment 925198592 925264128 (18503258567463 / 20000) (18504555104863 / 20000) := by
  exact
    packedTile32768 925198592 925264128 13 3140 30417 30 _ _ (41291 / 2000) (2064553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925264128 :
    ThetaLowerSegment 925264128 925329664 (18504555104863 / 20000) (46264648729939 / 50000) := by
  exact
    packedTile32768 925264128 925329664 13 3159 30418 30 _ _ (2064557 / 100000) (25807 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925329664 :
    ThetaLowerSegment 925329664 925395200 (46264648729939 / 50000) (23133979113817 / 25000) := by
  exact
    packedTile32768 925329664 925395200 13 3206 30419 30 _ _ (412913 / 20000) (258071 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925395200 :
    ThetaLowerSegment 925395200 925460736 (23133979113817 / 25000) (925423290159 / 1000) := by
  exact
    packedTile32768 925395200 925460736 13 3106 30420 30 _ _ (516143 / 25000) (82583 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925460736 :
    ThetaLowerSegment 925460736 925526272 (925423290159 / 1000) (18509764423371 / 20000) := by
  exact
    packedTile32768 925460736 925526272 13 3145 30421 30 _ _ (2064579 / 100000) (1032291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925526272 :
    ThetaLowerSegment 925526272 925591808 (18509764423371 / 20000) (92555437050399 / 100000) := by
  exact
    packedTile32768 925526272 925591808 13 3204 30422 30 _ _ (1032293 / 50000) (2064589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925591808 :
    ThetaLowerSegment 925591808 925657344 (92555437050399 / 100000) (46281020841703 / 50000) := by
  exact
    packedTile32768 925591808 925657344 13 3199 30423 30 _ _ (2064593 / 100000) (516149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925657344 :
    ThetaLowerSegment 925657344 925722880 (46281020841703 / 50000) (46284327298603 / 50000) := by
  exact
    packedTile32768 925657344 925722880 13 3203 30424 30 _ _ (10323 / 500) (2064603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925722880 :
    ThetaLowerSegment 925722880 925788416 (46284327298603 / 50000) (46287614152947 / 50000) := by
  exact
    packedTile32768 925722880 925788416 13 3184 30425 30 _ _ (2064607 / 100000) (206461 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925788416 :
    ThetaLowerSegment 925788416 925853952 (46287614152947 / 50000) (46290934052259 / 50000) := by
  exact
    packedTile32768 925788416 925853952 13 3216 30426 30 _ _ (1032307 / 50000) (2064617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925853952 :
    ThetaLowerSegment 925853952 925919488 (46290934052259 / 50000) (46294204411923 / 50000) := by
  exact
    packedTile32768 925853952 925919488 13 3168 30427 30 _ _ (2064621 / 100000) (129039 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925919488 :
    ThetaLowerSegment 925919488 925985024 (46294204411923 / 50000) (46297435554743 / 50000) := by
  exact
    packedTile32768 925919488 925985024 13 3130 30428 30 _ _ (516157 / 25000) (2064631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell925985024 :
    ThetaLowerSegment 925985024 926050560 (46297435554743 / 50000) (92601475876851 / 100000) := by
  exact
    packedTile32768 925985024 926050560 13 3199 30430 30 _ _ (412927 / 20000) (1032319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926050560 :
    ThetaLowerSegment 926050560 926116096 (92601475876851 / 100000) (18521609113539 / 20000) := by
  exact
    packedTile32768 926050560 926116096 13 3182 30431 30 _ _ (1032321 / 50000) (412929 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926116096 :
    ThetaLowerSegment 926116096 926181632 (18521609113539 / 20000) (18522904474949 / 20000) := by
  exact
    packedTile32768 926116096 926181632 13 3137 30432 30 _ _ (41293 / 2000) (2064653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926181632 :
    ThetaLowerSegment 926181632 926247168 (18522904474949 / 20000) (9262118089357 / 10000) := by
  exact
    packedTile32768 926181632 926247168 13 3225 30433 30 _ _ (2064657 / 100000) (103233 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926247168 :
    ThetaLowerSegment 926247168 926312704 (9262118089357 / 10000) (46313933137801 / 50000) := by
  exact
    packedTile32768 926247168 926312704 13 3238 30434 30 _ _ (258083 / 12500) (2064667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926312704 :
    ThetaLowerSegment 926312704 926378240 (46313933137801 / 50000) (92634388571291 / 100000) := by
  exact
    packedTile32768 926312704 926378240 13 3159 30435 30 _ _ (2064671 / 100000) (1032337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926378240 :
    ThetaLowerSegment 926378240 926443776 (92634388571291 / 100000) (92640925341839 / 100000) := by
  exact
    packedTile32768 926378240 926443776 13 3166 30436 30 _ _ (1032339 / 50000) (2064681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926443776 :
    ThetaLowerSegment 926443776 926509312 (92640925341839 / 100000) (92647532333839 / 100000) := by
  exact
    packedTile32768 926443776 926509312 13 3200 30437 30 _ _ (412937 / 20000) (129043 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926509312 :
    ThetaLowerSegment 926509312 926574848 (92647532333839 / 100000) (18530796073391 / 20000) := by
  exact
    packedTile32768 926509312 926574848 13 3123 30438 30 _ _ (516173 / 25000) (412939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926574848 :
    ThetaLowerSegment 926574848 926640384 (18530796073391 / 20000) (92660612180143 / 100000) := by
  exact
    packedTile32768 926574848 926640384 13 3212 30439 30 _ _ (2064699 / 100000) (1032351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926640384 :
    ThetaLowerSegment 926640384 926705920 (92660612180143 / 100000) (92667064386393 / 100000) := by
  exact
    packedTile32768 926640384 926705920 13 3125 30440 30 _ _ (1032353 / 50000) (2064709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926705920 :
    ThetaLowerSegment 926705920 926771456 (92667064386393 / 100000) (92673522808657 / 100000) := by
  exact
    packedTile32768 926705920 926771456 13 3128 30441 30 _ _ (2064713 / 100000) (516179 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926771456 :
    ThetaLowerSegment 926771456 926836992 (92673522808657 / 100000) (92680148495137 / 100000) := by
  exact
    packedTile32768 926771456 926836992 13 3209 30442 30 _ _ (25809 / 1250) (2064723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926836992 :
    ThetaLowerSegment 926836992 926902528 (92680148495137 / 100000) (18537340387727 / 20000) := by
  exact
    packedTile32768 926836992 926902528 13 3174 30443 30 _ _ (2064727 / 100000) (206473 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926902528 :
    ThetaLowerSegment 926902528 926968064 (18537340387727 / 20000) (92693313216903 / 100000) := by
  exact
    packedTile32768 926902528 926968064 13 3202 30445 30 _ _ (1032367 / 50000) (2064737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell926968064 :
    ThetaLowerSegment 926968064 927033600 (92693313216903 / 100000) (92699804762607 / 100000) := by
  exact
    packedTile32768 926968064 927033600 13 3144 30446 30 _ _ (2064741 / 100000) (258093 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927033600 :
    ThetaLowerSegment 927033600 927099136 (92699804762607 / 100000) (46353163652349 / 50000) := by
  exact
    packedTile32768 927033600 927099136 13 3159 30447 30 _ _ (2064749 / 100000) (129047 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927099136 :
    ThetaLowerSegment 927099136 927164672 (46353163652349 / 50000) (9271284573939 / 10000) := by
  exact
    packedTile32768 927099136 927164672 13 3157 30448 30 _ _ (516189 / 25000) (2064759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927164672 :
    ThetaLowerSegment 927164672 927230208 (9271284573939 / 10000) (46359734749547 / 50000) := by
  exact
    packedTile32768 927164672 927230208 13 3208 30449 30 _ _ (2064763 / 100000) (1032383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927230208 :
    ThetaLowerSegment 927230208 927295744 (46359734749547 / 50000) (23181512480271 / 25000) := by
  exact
    packedTile32768 927230208 927295744 13 3187 30450 30 _ _ (206477 / 10000) (2064773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927295744 :
    ThetaLowerSegment 927295744 927361280 (23181512480271 / 25000) (46366276984317 / 50000) := by
  exact
    packedTile32768 927295744 927361280 13 3150 30451 30 _ _ (2064777 / 100000) (103239 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927361280 :
    ThetaLowerSegment 927361280 927426816 (46366276984317 / 50000) (9273906629737 / 10000) := by
  exact
    packedTile32768 927361280 927426816 13 3154 30452 30 _ _ (129049 / 6250) (2064787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927426816 :
    ThetaLowerSegment 927426816 927492352 (9273906629737 / 10000) (46372807907211 / 50000) := by
  exact
    packedTile32768 927426816 927492352 13 3172 30453 30 _ _ (2064791 / 100000) (1032397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927492352 :
    ThetaLowerSegment 927492352 927557888 (46372807907211 / 50000) (2898501489381 / 3125) := by
  exact
    packedTile32768 927492352 927557888 13 3115 30454 30 _ _ (1032399 / 50000) (2064801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927557888 :
    ThetaLowerSegment 927557888 927623424 (2898501489381 / 3125) (92758512564647 / 100000) := by
  exact
    packedTile32768 927557888 927623424 13 3131 30455 30 _ _ (412961 / 20000) (258101 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927623424 :
    ThetaLowerSegment 927623424 927688960 (92758512564647 / 100000) (92765070407559 / 100000) := by
  exact
    packedTile32768 927623424 927688960 13 3176 30456 30 _ _ (516203 / 25000) (412963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927688960 :
    ThetaLowerSegment 927688960 927754496 (92765070407559 / 100000) (92771620013427 / 100000) := by
  exact
    packedTile32768 927688960 927754496 13 3172 30457 30 _ _ (2064819 / 100000) (1032411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927754496 :
    ThetaLowerSegment 927754496 927820032 (92771620013427 / 100000) (92778023038853 / 100000) := by
  exact
    packedTile32768 927754496 927820032 13 3101 30459 30 _ _ (1032413 / 50000) (2064829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927820032 :
    ThetaLowerSegment 927820032 927885568 (92778023038853 / 100000) (2899521445467 / 3125) := by
  exact
    packedTile32768 927820032 927885568 13 3227 30460 30 _ _ (2064833 / 100000) (516209 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927885568 :
    ThetaLowerSegment 927885568 927951104 (2899521445467 / 3125) (2899723541682 / 3125) := by
  exact
    packedTile32768 927885568 927951104 13 3132 30461 30 _ _ (51621 / 2500) (2064843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell927951104 :
    ThetaLowerSegment 927951104 928016640 (2899723541682 / 3125) (5799857987917 / 6250) := by
  exact
    packedTile32768 927951104 928016640 13 3184 30462 30 _ _ (2064847 / 100000) (41297 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928016640 :
    ThetaLowerSegment 928016640 928082176 (5799857987917 / 6250) (92804337407527 / 100000) := by
  exact
    packedTile32768 928016640 928082176 13 3201 30463 30 _ _ (412971 / 20000) (1032429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928082176 :
    ThetaLowerSegment 928082176 928147712 (92804337407527 / 100000) (18562174126179 / 20000) := by
  exact
    packedTile32768 928082176 928147712 13 3164 30464 30 _ _ (1032431 / 50000) (412973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928147712 :
    ThetaLowerSegment 928147712 928213248 (18562174126179 / 20000) (9281738529259 / 10000) := by
  exact
    packedTile32768 928147712 928213248 13 3155 30465 30 _ _ (2064869 / 100000) (258109 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928213248 :
    ThetaLowerSegment 928213248 928278784 (9281738529259 / 10000) (9282392062513 / 10000) := by
  exact
    packedTile32768 928213248 928278784 13 3165 30466 30 _ _ (516219 / 25000) (2064879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928278784 :
    ThetaLowerSegment 928278784 928344320 (9282392062513 / 10000) (46415255865833 / 50000) := by
  exact
    packedTile32768 928278784 928344320 13 3192 30467 30 _ _ (2064883 / 100000) (1032443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928344320 :
    ThetaLowerSegment 928344320 928409856 (46415255865833 / 50000) (46418543170713 / 50000) := by
  exact
    packedTile32768 928344320 928409856 13 3184 30468 30 _ _ (206489 / 10000) (2064893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928409856 :
    ThetaLowerSegment 928409856 928475392 (46418543170713 / 50000) (92843737374663 / 100000) := by
  exact
    packedTile32768 928409856 928475392 13 3221 30469 30 _ _ (2064897 / 100000) (20649 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928475392 :
    ThetaLowerSegment 928475392 928540928 (92843737374663 / 100000) (92850190199663 / 100000) := by
  exact
    packedTile32768 928475392 928540928 13 3125 30470 30 _ _ (258113 / 12500) (2064907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928540928 :
    ThetaLowerSegment 928540928 928606464 (92850190199663 / 100000) (46428383470599 / 50000) := by
  exact
    packedTile32768 928540928 928606464 13 3185 30471 30 _ _ (2064911 / 100000) (1032457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928606464 :
    ThetaLowerSegment 928606464 928672000 (46428383470599 / 50000) (46431668755137 / 50000) := by
  exact
    packedTile32768 928606464 928672000 13 3182 30473 30 _ _ (1032459 / 50000) (2064921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928672000 :
    ThetaLowerSegment 928672000 928737536 (46431668755137 / 50000) (46434914817237 / 50000) := by
  exact
    packedTile32768 928672000 928737536 13 3144 30474 30 _ _ (82597 / 4000) (64529 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928737536 :
    ThetaLowerSegment 928737536 928803072 (46434914817237 / 50000) (46438133013759 / 50000) := by
  exact
    packedTile32768 928737536 928803072 13 3117 30475 30 _ _ (516233 / 25000) (412987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928803072 :
    ThetaLowerSegment 928803072 928868608 (46438133013759 / 50000) (92882863507623 / 100000) := by
  exact
    packedTile32768 928803072 928868608 13 3195 30476 30 _ _ (2064939 / 100000) (1032471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928868608 :
    ThetaLowerSegment 928868608 928934144 (92882863507623 / 100000) (18577851729077 / 20000) := by
  exact
    packedTile32768 928868608 928934144 13 3097 30477 30 _ _ (1032473 / 50000) (2064949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928934144 :
    ThetaLowerSegment 928934144 928999680 (18577851729077 / 20000) (92895841715549 / 100000) := by
  exact
    packedTile32768 928934144 928999680 13 3188 30478 30 _ _ (2064953 / 100000) (516239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell928999680 :
    ThetaLowerSegment 928999680 929065216 (92895841715549 / 100000) (92902247221469 / 100000) := by
  exact
    packedTile32768 928999680 929065216 13 3102 30479 30 _ _ (12906 / 625) (2064963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929065216 :
    ThetaLowerSegment 929065216 929130752 (92902247221469 / 100000) (23227164736001 / 25000) := by
  exact
    packedTile32768 929065216 929130752 13 3105 30480 30 _ _ (2064967 / 100000) (206497 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929130752 :
    ThetaLowerSegment 929130752 929196288 (23227164736001 / 25000) (92915161550279 / 100000) := by
  exact
    packedTile32768 929130752 929196288 13 3149 30481 30 _ _ (82599 / 4000) (1032489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929196288 :
    ThetaLowerSegment 929196288 929261824 (92915161550279 / 100000) (92921695153327 / 100000) := by
  exact
    packedTile32768 929196288 929261824 13 3164 30482 30 _ _ (1032491 / 50000) (412997 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929261824 :
    ThetaLowerSegment 929261824 929327360 (92921695153327 / 100000) (23232055645889 / 25000) := by
  exact
    packedTile32768 929261824 929327360 13 3161 30483 30 _ _ (2064989 / 100000) (64531 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929327360 :
    ThetaLowerSegment 929327360 929392896 (23232055645889 / 25000) (23233679765243 / 25000) := by
  exact
    packedTile32768 929327360 929392896 13 3146 30484 30 _ _ (516249 / 25000) (2064999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929392896 :
    ThetaLowerSegment 929392896 929458432 (23233679765243 / 25000) (92941333265581 / 100000) := by
  exact
    packedTile32768 929392896 929458432 13 3203 30485 30 _ _ (2065003 / 100000) (1032503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929458432 :
    ThetaLowerSegment 929458432 929523968 (92941333265581 / 100000) (92948046613091 / 100000) := by
  exact
    packedTile32768 929458432 929523968 13 3251 30487 30 _ _ (206501 / 10000) (2065013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929523968 :
    ThetaLowerSegment 929523968 929589504 (92948046613091 / 100000) (92954634017321 / 100000) := by
  exact
    packedTile32768 929523968 929589504 13 3190 30488 30 _ _ (2065017 / 100000) (103251 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929589504 :
    ThetaLowerSegment 929589504 929655040 (92954634017321 / 100000) (18592238506709 / 20000) := by
  exact
    packedTile32768 929589504 929655040 13 3176 30489 30 _ _ (64532 / 3125) (2065027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929655040 :
    ThetaLowerSegment 929655040 929720576 (18592238506709 / 20000) (23241903178731 / 25000) := by
  exact
    packedTile32768 929655040 929720576 13 3109 30490 30 _ _ (2065031 / 100000) (1032517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929720576 :
    ThetaLowerSegment 929720576 929786112 (23241903178731 / 25000) (23243534558751 / 25000) := by
  exact
    packedTile32768 929720576 929786112 13 3160 30491 30 _ _ (1032519 / 50000) (2065041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929786112 :
    ThetaLowerSegment 929786112 929851648 (23243534558751 / 25000) (92980628671439 / 100000) := by
  exact
    packedTile32768 929786112 929851648 13 3143 30492 30 _ _ (413009 / 20000) (258131 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929851648 :
    ThetaLowerSegment 929851648 929917184 (92980628671439 / 100000) (92987288464139 / 100000) := by
  exact
    packedTile32768 929851648 929917184 13 3225 30493 30 _ _ (516263 / 25000) (413011 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929917184 :
    ThetaLowerSegment 929917184 929982720 (92987288464139 / 100000) (9299383263611 / 10000) := by
  exact
    packedTile32768 929917184 929982720 13 3169 30494 30 _ _ (2065059 / 100000) (1032531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell929982720 :
    ThetaLowerSegment 929982720 930048256 (9299383263611 / 10000) (23250111760627 / 25000) := by
  exact
    packedTile32768 929982720 930048256 13 3203 30495 30 _ _ (1032533 / 50000) (2065069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930048256 :
    ThetaLowerSegment 930048256 930113792 (23250111760627 / 25000) (4650355241893 / 5000) := by
  exact
    packedTile32768 930048256 930113792 13 3224 30496 30 _ _ (2065073 / 100000) (516269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930113792 :
    ThetaLowerSegment 930113792 930179328 (4650355241893 / 5000) (4650679872469 / 5000) := by
  exact
    packedTile32768 930113792 930179328 13 3144 30497 30 _ _ (51627 / 2500) (2065083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930179328 :
    ThetaLowerSegment 930179328 930244864 (4650679872469 / 5000) (4651002026041 / 5000) := by
  exact
    packedTile32768 930179328 930244864 13 3120 30498 30 _ _ (2065087 / 100000) (206509 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930244864 :
    ThetaLowerSegment 930244864 930310400 (4651002026041 / 5000) (11628324391147 / 12500) := by
  exact
    packedTile32768 930244864 930310400 13 3174 30499 30 _ _ (1032547 / 50000) (2065097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930310400 :
    ThetaLowerSegment 930310400 930375936 (11628324391147 / 12500) (93033213777881 / 100000) := by
  exact
    packedTile32768 930310400 930375936 13 3205 30500 30 _ _ (2065101 / 100000) (129069 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930375936 :
    ThetaLowerSegment 930375936 930441472 (93033213777881 / 100000) (93039760170241 / 100000) := by
  exact
    packedTile32768 930375936 930441472 13 3170 30502 30 _ _ (516277 / 25000) (2065111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930441472 :
    ThetaLowerSegment 930441472 930507008 (93039760170241 / 100000) (93046356147551 / 100000) := by
  exact
    packedTile32768 930441472 930507008 13 3194 30503 30 _ _ (413023 / 20000) (1032559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930507008 :
    ThetaLowerSegment 930507008 930572544 (93046356147551 / 100000) (18610579691443 / 20000) := by
  exact
    packedTile32768 930507008 930572544 13 3168 30504 30 _ _ (2065123 / 100000) (1032563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930572544 :
    ThetaLowerSegment 930572544 930638080 (18610579691443 / 20000) (18611901374643 / 20000) := by
  exact
    packedTile32768 930572544 930638080 13 3200 30505 30 _ _ (206513 / 10000) (2065133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930638080 :
    ThetaLowerSegment 930638080 930703616 (18611901374643 / 20000) (46532986408581 / 50000) := by
  exact
    packedTile32768 930638080 930703616 13 3131 30506 30 _ _ (2065137 / 100000) (103257 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930703616 :
    ThetaLowerSegment 930703616 930769152 (46532986408581 / 50000) (46536259661821 / 50000) := by
  exact
    packedTile32768 930703616 930769152 13 3170 30507 30 _ _ (258143 / 12500) (2065147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930769152 :
    ThetaLowerSegment 930769152 930834688 (46536259661821 / 50000) (93079150523503 / 100000) := by
  exact
    packedTile32768 930769152 930834688 13 3211 30508 30 _ _ (2065151 / 100000) (1032577 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930834688 :
    ThetaLowerSegment 930834688 930900224 (93079150523503 / 100000) (93085721856259 / 100000) := by
  exact
    packedTile32768 930834688 930900224 13 3182 30509 30 _ _ (1032579 / 50000) (2065161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930900224 :
    ThetaLowerSegment 930900224 930965760 (93085721856259 / 100000) (93092338644919 / 100000) := by
  exact
    packedTile32768 930900224 930965760 13 3204 30510 30 _ _ (413033 / 20000) (129073 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell930965760 :
    ThetaLowerSegment 930965760 931031296 (93092338644919 / 100000) (93098794372591 / 100000) := by
  exact
    packedTile32768 930965760 931031296 13 3126 30511 30 _ _ (516293 / 25000) (82607 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931031296 :
    ThetaLowerSegment 931031296 931096832 (93098794372591 / 100000) (18621066545861 / 20000) := by
  exact
    packedTile32768 931031296 931096832 13 3166 30512 30 _ _ (2065179 / 100000) (1032591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931096832 :
    ThetaLowerSegment 931096832 931162368 (18621066545861 / 20000) (93111738936277 / 100000) := by
  exact
    packedTile32768 931096832 931162368 13 3102 30513 30 _ _ (1032593 / 50000) (2065189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931162368 :
    ThetaLowerSegment 931162368 931227904 (93111738936277 / 100000) (46559191331079 / 50000) := by
  exact
    packedTile32768 931162368 931227904 13 3217 30514 30 _ _ (2065193 / 100000) (516299 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931227904 :
    ThetaLowerSegment 931227904 931293440 (46559191331079 / 50000) (46562448151479 / 50000) := by
  exact
    packedTile32768 931227904 931293440 13 3154 30516 30 _ _ (5163 / 250) (2065203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931293440 :
    ThetaLowerSegment 931293440 931358976 (46562448151479 / 50000) (93131597899673 / 100000) := by
  exact
    packedTile32768 931293440 931358976 13 3245 30517 30 _ _ (2065207 / 100000) (206521 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931358976 :
    ThetaLowerSegment 931358976 931424512 (93131597899673 / 100000) (93138134301983 / 100000) := by
  exact
    packedTile32768 931358976 931424512 13 3165 30518 30 _ _ (1032607 / 50000) (2065217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931424512 :
    ThetaLowerSegment 931424512 931490048 (93138134301983 / 100000) (18628945297483 / 20000) := by
  exact
    packedTile32768 931424512 931490048 13 3192 30519 30 _ _ (2065221 / 100000) (258153 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931490048 :
    ThetaLowerSegment 931490048 931555584 (18628945297483 / 20000) (93151258803579 / 100000) := by
  exact
    packedTile32768 931490048 931555584 13 3163 30520 30 _ _ (516307 / 25000) (2065231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931555584 :
    ThetaLowerSegment 931555584 931621120 (93151258803579 / 100000) (93157842772759 / 100000) := by
  exact
    packedTile32768 931555584 931621120 13 3188 30521 30 _ _ (413047 / 20000) (1032619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931621120 :
    ThetaLowerSegment 931621120 931686656 (93157842772759 / 100000) (18632875026641 / 20000) := by
  exact
    packedTile32768 931621120 931686656 13 3163 30522 30 _ _ (1032621 / 50000) (413049 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931686656 :
    ThetaLowerSegment 931686656 931752192 (18632875026641 / 20000) (46585451692647 / 50000) := by
  exact
    packedTile32768 931686656 931752192 13 3161 30523 30 _ _ (2065249 / 100000) (516313 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931752192 :
    ThetaLowerSegment 931752192 931817728 (46585451692647 / 50000) (9317747296463 / 10000) := by
  exact
    packedTile32768 931752192 931817728 13 3181 30524 30 _ _ (258157 / 12500) (2065259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931817728 :
    ThetaLowerSegment 931817728 931883264 (9317747296463 / 10000) (93184034305181 / 100000) := by
  exact
    packedTile32768 931817728 931883264 13 3177 30525 30 _ _ (2065263 / 100000) (1032633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931883264 :
    ThetaLowerSegment 931883264 931948800 (93184034305181 / 100000) (93190562623651 / 100000) := by
  exact
    packedTile32768 931883264 931948800 13 3161 30526 30 _ _ (206527 / 10000) (2065273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell931948800 :
    ThetaLowerSegment 931948800 932014336 (93190562623651 / 100000) (2912409608952 / 3125) := by
  exact
    packedTile32768 931948800 932014336 13 3169 30527 30 _ _ (2065277 / 100000) (12908 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932014336 :
    ThetaLowerSegment 932014336 932079872 (2912409608952 / 3125) (2330087436879 / 2500) := by
  exact
    packedTile32768 932014336 932079872 13 3094 30528 30 _ _ (516321 / 25000) (2065287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932079872 :
    ThetaLowerSegment 932079872 932145408 (2330087436879 / 2500) (46605038746143 / 50000) := by
  exact
    packedTile32768 932079872 932145408 13 3186 30529 30 _ _ (2065291 / 100000) (1032647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932145408 :
    ThetaLowerSegment 932145408 932210944 (46605038746143 / 50000) (11652087096547 / 12500) := by
  exact
    packedTile32768 932145408 932210944 13 3205 30531 30 _ _ (1032649 / 50000) (2065301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932210944 :
    ThetaLowerSegment 932210944 932276480 (11652087096547 / 12500) (46611605372173 / 50000) := by
  exact
    packedTile32768 932210944 932276480 13 3154 30532 30 _ _ (413061 / 20000) (516327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932276480 :
    ThetaLowerSegment 932276480 932342016 (46611605372173 / 50000) (46614912969341 / 50000) := by
  exact
    packedTile32768 932276480 932342016 13 3203 30533 30 _ _ (64541 / 3125) (413063 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932342016 :
    ThetaLowerSegment 932342016 932407552 (46614912969341 / 50000) (46618187534201 / 50000) := by
  exact
    packedTile32768 932342016 932407552 13 3171 30534 30 _ _ (51633 / 2500) (2065323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932407552 :
    ThetaLowerSegment 932407552 932473088 (46618187534201 / 50000) (46621479665439 / 50000) := by
  exact
    packedTile32768 932407552 932473088 13 3188 30535 30 _ _ (2065327 / 100000) (206533 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932473088 :
    ThetaLowerSegment 932473088 932538624 (46621479665439 / 50000) (23312369897579 / 25000) := by
  exact
    packedTile32768 932473088 932538624 13 3157 30536 30 _ _ (1032667 / 50000) (2065337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932538624 :
    ThetaLowerSegment 932538624 932604160 (23312369897579 / 25000) (93255995741171 / 100000) := by
  exact
    packedTile32768 932538624 932604160 13 3155 30537 30 _ _ (2065341 / 100000) (64542 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932604160 :
    ThetaLowerSegment 932604160 932669696 (93255995741171 / 100000) (93262530502243 / 100000) := by
  exact
    packedTile32768 932604160 932669696 13 3164 30538 30 _ _ (516337 / 25000) (2065351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932669696 :
    ThetaLowerSegment 932669696 932735232 (93262530502243 / 100000) (46634500629729 / 50000) := by
  exact
    packedTile32768 932669696 932735232 13 3133 30539 30 _ _ (413071 / 20000) (1032679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932735232 :
    ThetaLowerSegment 932735232 932800768 (46634500629729 / 50000) (46637827927911 / 50000) := by
  exact
    packedTile32768 932735232 932800768 13 3222 30540 30 _ _ (1032681 / 50000) (413073 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932800768 :
    ThetaLowerSegment 932800768 932866304 (46637827927911 / 50000) (2915072976849 / 3125) := by
  exact
    packedTile32768 932800768 932866304 13 3234 30541 30 _ _ (2065369 / 100000) (516343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932866304 :
    ThetaLowerSegment 932866304 932931840 (2915072976849 / 3125) (2915273641036 / 3125) := by
  exact
    packedTile32768 932866304 932931840 13 3109 30542 30 _ _ (64543 / 3125) (2065379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932931840 :
    ThetaLowerSegment 932931840 932997376 (2915273641036 / 3125) (93295400850263 / 100000) := by
  exact
    packedTile32768 932931840 932997376 13 3217 30543 30 _ _ (2065383 / 100000) (1032693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell932997376 :
    ThetaLowerSegment 932997376 933062912 (93295400850263 / 100000) (93302026621383 / 100000) := by
  exact
    packedTile32768 932997376 933062912 13 3208 30545 30 _ _ (206539 / 10000) (2065393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933062912 :
    ThetaLowerSegment 933062912 933128448 (93302026621383 / 100000) (9330857599527 / 10000) := by
  exact
    packedTile32768 933062912 933128448 13 3171 30546 30 _ _ (2065397 / 100000) (10327 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933128448 :
    ThetaLowerSegment 933128448 933193984 (9330857599527 / 10000) (46657579218909 / 50000) := by
  exact
    packedTile32768 933128448 933193984 13 3187 30547 30 _ _ (516351 / 25000) (2065407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933193984 :
    ThetaLowerSegment 933193984 933259520 (46657579218909 / 50000) (93321811126649 / 100000) := by
  exact
    packedTile32768 933193984 933259520 13 3221 30548 30 _ _ (2065411 / 100000) (1032707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933259520 :
    ThetaLowerSegment 933259520 933325056 (93321811126649 / 100000) (18665660134001 / 20000) := by
  exact
    packedTile32768 933259520 933325056 13 3142 30549 30 _ _ (1032709 / 50000) (2065421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933325056 :
    ThetaLowerSegment 933325056 933390592 (18665660134001 / 20000) (18666966308771 / 20000) := by
  exact
    packedTile32768 933325056 933390592 13 3162 30550 30 _ _ (82617 / 4000) (516357 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933390592 :
    ThetaLowerSegment 933390592 933456128 (18666966308771 / 20000) (93341412010207 / 100000) := by
  exact
    packedTile32768 933390592 933456128 13 3186 30551 30 _ _ (258179 / 12500) (413087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933456128 :
    ThetaLowerSegment 933456128 933521664 (93341412010207 / 100000) (18669584454787 / 20000) := by
  exact
    packedTile32768 933456128 933521664 13 3152 30552 30 _ _ (2065439 / 100000) (1032721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933521664 :
    ThetaLowerSegment 933521664 933587200 (18669584454787 / 20000) (93354473868647 / 100000) := by
  exact
    packedTile32768 933521664 933587200 13 3172 30553 30 _ _ (1032723 / 50000) (2065449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933587200 :
    ThetaLowerSegment 933587200 933652736 (93354473868647 / 100000) (46680536495491 / 50000) := by
  exact
    packedTile32768 933587200 933652736 13 3195 30554 30 _ _ (2065453 / 100000) (129091 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933652736 :
    ThetaLowerSegment 933652736 933718272 (46680536495491 / 50000) (46683807151401 / 50000) := by
  exact
    packedTile32768 933652736 933718272 13 3167 30555 30 _ _ (103273 / 5000) (2065463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933718272 :
    ThetaLowerSegment 933718272 933783808 (46683807151401 / 50000) (46687120160469 / 50000) := by
  exact
    packedTile32768 933718272 933783808 13 3208 30556 30 _ _ (2065467 / 100000) (206547 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933783808 :
    ThetaLowerSegment 933783808 933849344 (46687120160469 / 50000) (2918150201962 / 3125) := by
  exact
    packedTile32768 933783808 933849344 13 3179 30557 30 _ _ (1032737 / 50000) (2065477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933849344 :
    ThetaLowerSegment 933849344 933914880 (2918150201962 / 3125) (23346897375597 / 25000) := by
  exact
    packedTile32768 933849344 933914880 13 3284 30558 30 _ _ (2065481 / 100000) (516371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933914880 :
    ThetaLowerSegment 933914880 933980416 (23346897375597 / 25000) (4669705202577 / 5000) := by
  exact
    packedTile32768 933914880 933980416 13 3154 30560 30 _ _ (129093 / 6250) (2065491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell933980416 :
    ThetaLowerSegment 933980416 934045952 (4669705202577 / 5000) (18680092742129 / 20000) := by
  exact
    packedTile32768 933980416 934045952 13 3079 30561 30 _ _ (413099 / 20000) (1032749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934045952 :
    ThetaLowerSegment 934045952 934111488 (18680092742129 / 20000) (93406848177327 / 100000) := by
  exact
    packedTile32768 934045952 934111488 13 3091 30562 30 _ _ (1032751 / 50000) (413101 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934111488 :
    ThetaLowerSegment 934111488 934177024 (93406848177327 / 100000) (93413515640379 / 100000) := by
  exact
    packedTile32768 934111488 934177024 13 3228 30563 30 _ _ (2065509 / 100000) (258189 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934177024 :
    ThetaLowerSegment 934177024 934242560 (93413515640379 / 100000) (18684008947291 / 20000) := by
  exact
    packedTile32768 934177024 934242560 13 3161 30564 30 _ _ (516379 / 25000) (2065519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934242560 :
    ThetaLowerSegment 934242560 934308096 (18684008947291 / 20000) (3737065350193 / 4000) := by
  exact
    packedTile32768 934242560 934308096 13 3190 30565 30 _ _ (2065523 / 100000) (1032763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934308096 :
    ThetaLowerSegment 934308096 934373632 (3737065350193 / 4000) (18686604074717 / 20000) := by
  exact
    packedTile32768 934308096 934373632 13 3092 30566 30 _ _ (206553 / 10000) (2065533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934373632 :
    ThetaLowerSegment 934373632 934439168 (18686604074717 / 20000) (18687917756249 / 20000) := by
  exact
    packedTile32768 934373632 934439168 13 3180 30567 30 _ _ (2065537 / 100000) (103277 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934439168 :
    ThetaLowerSegment 934439168 934504704 (18687917756249 / 20000) (93446277012717 / 100000) := by
  exact
    packedTile32768 934439168 934504704 13 3238 30568 30 _ _ (258193 / 12500) (2065547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934504704 :
    ThetaLowerSegment 934504704 934570240 (93446277012717 / 100000) (46726442355183 / 50000) := by
  exact
    packedTile32768 934504704 934570240 13 3199 30569 30 _ _ (2065551 / 100000) (1032777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934570240 :
    ThetaLowerSegment 934570240 934635776 (46726442355183 / 50000) (2336486484537 / 2500) := by
  exact
    packedTile32768 934570240 934635776 13 3183 30570 30 _ _ (1032779 / 50000) (2065561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934635776 :
    ThetaLowerSegment 934635776 934701312 (2336486484537 / 2500) (9346599069801 / 10000) := by
  exact
    packedTile32768 934635776 934701312 13 3162 30571 30 _ _ (413113 / 20000) (64549 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934701312 :
    ThetaLowerSegment 934701312 934766848 (9346599069801 / 10000) (9347251790553 / 10000) := by
  exact
    packedTile32768 934701312 934766848 13 3160 30572 30 _ _ (516393 / 25000) (82623 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934766848 :
    ThetaLowerSegment 934766848 934832384 (9347251790553 / 10000) (23369780906793 / 25000) := by
  exact
    packedTile32768 934766848 934832384 13 3198 30573 30 _ _ (2065579 / 100000) (1032791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934832384 :
    ThetaLowerSegment 934832384 934897920 (23369780906793 / 25000) (23371429244421 / 25000) := by
  exact
    packedTile32768 934832384 934897920 13 3192 30575 30 _ _ (1032793 / 50000) (2065589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934897920 :
    ThetaLowerSegment 934897920 934963456 (23371429244421 / 25000) (93492250448343 / 100000) := by
  exact
    packedTile32768 934897920 934963456 13 3163 30576 30 _ _ (2065593 / 100000) (516399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell934963456 :
    ThetaLowerSegment 934963456 935028992 (93492250448343 / 100000) (93498680661143 / 100000) := by
  exact
    packedTile32768 934963456 935028992 13 3113 30577 30 _ _ (2582 / 125) (2065603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935028992 :
    ThetaLowerSegment 935028992 935094528 (93498680661143 / 100000) (18701077124293 / 20000) := by
  exact
    packedTile32768 935028992 935094528 13 3246 30578 30 _ _ (2065607 / 100000) (206561 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935094528 :
    ThetaLowerSegment 935094528 935160064 (18701077124293 / 20000) (93511896436793 / 100000) := by
  exact
    packedTile32768 935094528 935160064 13 3152 30579 30 _ _ (1032807 / 50000) (2065617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935160064 :
    ThetaLowerSegment 935160064 935225600 (93511896436793 / 100000) (93518514686477 / 100000) := by
  exact
    packedTile32768 935160064 935225600 13 3204 30580 30 _ _ (2065621 / 100000) (258203 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935225600 :
    ThetaLowerSegment 935225600 935291136 (93518514686477 / 100000) (93525097842913 / 100000) := by
  exact
    packedTile32768 935225600 935291136 13 3187 30581 30 _ _ (516407 / 25000) (2065631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935291136 :
    ThetaLowerSegment 935291136 935356672 (93525097842913 / 100000) (93531712006183 / 100000) := by
  exact
    packedTile32768 935291136 935356672 13 3202 30582 30 _ _ (413127 / 20000) (1032819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935356672 :
    ThetaLowerSegment 935356672 935422208 (93531712006183 / 100000) (3741530899407 / 4000) := by
  exact
    packedTile32768 935356672 935422208 13 3176 30583 30 _ _ (1032821 / 50000) (413129 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935422208 :
    ThetaLowerSegment 935422208 935487744 (3741530899407 / 4000) (93544857774187 / 100000) := by
  exact
    packedTile32768 935422208 935487744 13 3188 30584 30 _ _ (2065649 / 100000) (516413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935487744 :
    ThetaLowerSegment 935487744 935553280 (93544857774187 / 100000) (93551500923883 / 100000) := by
  exact
    packedTile32768 935487744 935553280 13 3216 30585 30 _ _ (258207 / 12500) (2065659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935553280 :
    ThetaLowerSegment 935553280 935618816 (93551500923883 / 100000) (93557970580399 / 100000) := by
  exact
    packedTile32768 935553280 935618816 13 3132 30586 30 _ _ (2065663 / 100000) (1032833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935618816 :
    ThetaLowerSegment 935618816 935684352 (93557970580399 / 100000) (93564624103469 / 100000) := by
  exact
    packedTile32768 935618816 935684352 13 3221 30587 30 _ _ (206567 / 10000) (2065673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935684352 :
    ThetaLowerSegment 935684352 935749888 (93564624103469 / 100000) (23392781197247 / 25000) := by
  exact
    packedTile32768 935684352 935749888 13 3147 30588 30 _ _ (2065677 / 100000) (25821 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935749888 :
    ThetaLowerSegment 935749888 935815424 (23392781197247 / 25000) (23394436842973 / 25000) := by
  exact
    packedTile32768 935749888 935815424 13 3206 30590 30 _ _ (516421 / 25000) (2065687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935815424 :
    ThetaLowerSegment 935815424 935880960 (23394436842973 / 25000) (93584347254637 / 100000) := by
  exact
    packedTile32768 935815424 935880960 13 3195 30591 30 _ _ (2065691 / 100000) (1032847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935880960 :
    ThetaLowerSegment 935880960 935946496 (93584347254637 / 100000) (93590883123109 / 100000) := by
  exact
    packedTile32768 935880960 935946496 13 3164 30592 30 _ _ (1032849 / 50000) (2065701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell935946496 :
    ThetaLowerSegment 935946496 936012032 (93590883123109 / 100000) (93597390093859 / 100000) := by
  exact
    packedTile32768 935946496 936012032 13 3150 30593 30 _ _ (413141 / 20000) (516427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936012032 :
    ThetaLowerSegment 936012032 936077568 (93597390093859 / 100000) (93603884692387 / 100000) := by
  exact
    packedTile32768 936012032 936077568 13 3144 30594 30 _ _ (129107 / 6250) (413143 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936077568 :
    ThetaLowerSegment 936077568 936143104 (93603884692387 / 100000) (46805298106709 / 50000) := by
  exact
    packedTile32768 936077568 936143104 13 3249 30595 30 _ _ (2065719 / 100000) (1032861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936143104 :
    ThetaLowerSegment 936143104 936208640 (46805298106709 / 50000) (23404237080217 / 25000) := by
  exact
    packedTile32768 936143104 936208640 13 3075 30596 30 _ _ (1032863 / 50000) (2065729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936208640 :
    ThetaLowerSegment 936208640 936274176 (23404237080217 / 25000) (46811781398967 / 50000) := by
  exact
    packedTile32768 936208640 936274176 13 3202 30597 30 _ _ (2065733 / 100000) (258217 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936274176 :
    ThetaLowerSegment 936274176 936339712 (46811781398967 / 50000) (46815116536197 / 50000) := by
  exact
    packedTile32768 936274176 936339712 13 3229 30598 30 _ _ (103287 / 5000) (2065743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936339712 :
    ThetaLowerSegment 936339712 936405248 (46815116536197 / 50000) (46818372153469 / 50000) := by
  exact
    packedTile32768 936339712 936405248 13 3152 30599 30 _ _ (2065747 / 100000) (8263 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936405248 :
    ThetaLowerSegment 936405248 936470784 (46818372153469 / 50000) (46821580269431 / 50000) := by
  exact
    packedTile32768 936405248 936470784 13 3106 30600 30 _ _ (1032877 / 50000) (2065757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936470784 :
    ThetaLowerSegment 936470784 936536320 (46821580269431 / 50000) (93649624305031 / 100000) := by
  exact
    packedTile32768 936470784 936536320 13 3129 30601 30 _ _ (2065761 / 100000) (516441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936536320 :
    ThetaLowerSegment 936536320 936601856 (93649624305031 / 100000) (93656139737303 / 100000) := by
  exact
    packedTile32768 936536320 936601856 13 3154 30602 30 _ _ (258221 / 12500) (2065771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936601856 :
    ThetaLowerSegment 936601856 936667392 (93656139737303 / 100000) (11707839387391 / 12500) := by
  exact
    packedTile32768 936601856 936667392 13 3183 30603 30 _ _ (82631 / 4000) (1032889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936667392 :
    ThetaLowerSegment 936667392 936732928 (11707839387391 / 12500) (11708663634409 / 12500) := by
  exact
    packedTile32768 936667392 936732928 13 3192 30605 30 _ _ (1032891 / 50000) (413157 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936732928 :
    ThetaLowerSegment 936732928 936798464 (11708663634409 / 12500) (23418977834229 / 25000) := by
  exact
    packedTile32768 936732928 936798464 13 3196 30606 30 _ _ (2065789 / 100000) (64556 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936798464 :
    ThetaLowerSegment 936798464 936864000 (23418977834229 / 25000) (11710293802881 / 12500) := by
  exact
    packedTile32768 936798464 936864000 13 3117 30607 30 _ _ (516449 / 25000) (2065799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936864000 :
    ThetaLowerSegment 936864000 936929536 (11710293802881 / 12500) (93688851505089 / 100000) := by
  exact
    packedTile32768 936864000 936929536 13 3147 30608 30 _ _ (2065803 / 100000) (1032903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936929536 :
    ThetaLowerSegment 936929536 936995072 (93688851505089 / 100000) (93695340214299 / 100000) := by
  exact
    packedTile32768 936929536 936995072 13 3141 30609 30 _ _ (206581 / 10000) (2065813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell936995072 :
    ThetaLowerSegment 936995072 937060608 (93695340214299 / 100000) (23425467565459 / 25000) := by
  exact
    packedTile32768 936995072 937060608 13 3161 30610 30 _ _ (2065817 / 100000) (103291 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937060608 :
    ThetaLowerSegment 937060608 937126144 (23425467565459 / 25000) (23427120224659 / 25000) := by
  exact
    packedTile32768 937060608 937126144 13 3200 30611 30 _ _ (64557 / 3125) (2065827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937126144 :
    ThetaLowerSegment 937126144 937191680 (23427120224659 / 25000) (93714969673807 / 100000) := by
  exact
    packedTile32768 937126144 937191680 13 3141 30612 30 _ _ (2065831 / 100000) (1032917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937191680 :
    ThetaLowerSegment 937191680 937257216 (93714969673807 / 100000) (93721470865993 / 100000) := by
  exact
    packedTile32768 937191680 937257216 13 3147 30613 30 _ _ (1032919 / 50000) (2065841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937257216 :
    ThetaLowerSegment 937257216 937322752 (93721470865993 / 100000) (23432003349277 / 25000) := by
  exact
    packedTile32768 937257216 937322752 13 3167 30614 30 _ _ (413169 / 20000) (258231 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937322752 :
    ThetaLowerSegment 937322752 937339136 (23432003349277 / 25000) (23432438211123 / 25000) := by
  exact
    packedTile32768 937322752 937339136 11 842 30615 30 _ _ (516463 / 25000) (413171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell937339136 :
    ThetaLowerSegment 937339136 937341184 (23432438211123 / 25000) (46864982813727 / 50000) := by
  exact
    packedTile32768 937339136 937341184 8 103 30615 30 _ _ (1032927 / 50000) (2065857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_905341184_937341184 :
    ThetaLowerSegment 905341184 937341184 (3621155229789 / 4000) (46864982813727 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell905341184 cell905406720)
                    (ThetaLowerSegment.join cell905472256 cell905537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell905603328 cell905668864)
                    (ThetaLowerSegment.join cell905734400 cell905799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell905865472 cell905931008)
                    (ThetaLowerSegment.join cell905996544 cell906062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell906127616 cell906193152)
                    (ThetaLowerSegment.join cell906258688 cell906324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell906389760 cell906455296)
                    (ThetaLowerSegment.join cell906520832 cell906586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell906651904 cell906717440)
                    (ThetaLowerSegment.join cell906782976 cell906848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell906914048 cell906979584)
                    (ThetaLowerSegment.join cell907045120 cell907110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell907176192 cell907241728)
                    (ThetaLowerSegment.join cell907307264 cell907372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell907438336 cell907503872)
                    (ThetaLowerSegment.join cell907569408 cell907634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell907700480 cell907766016)
                    (ThetaLowerSegment.join cell907831552 cell907897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell907962624 cell908028160)
                    (ThetaLowerSegment.join cell908093696 cell908159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell908224768 cell908290304)
                    (ThetaLowerSegment.join cell908355840 cell908421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell908486912 cell908552448)
                    (ThetaLowerSegment.join cell908617984 cell908683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell908749056 cell908814592)
                    (ThetaLowerSegment.join cell908880128 cell908945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell909011200 cell909076736)
                    (ThetaLowerSegment.join cell909142272 cell909207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell909273344 cell909338880)
                    (ThetaLowerSegment.join cell909404416 cell909469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell909535488 cell909601024)
                    (ThetaLowerSegment.join cell909666560 cell909732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell909797632 cell909863168)
                    (ThetaLowerSegment.join cell909928704 cell909994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell910059776 cell910125312)
                    (ThetaLowerSegment.join cell910190848 cell910256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell910321920 cell910387456)
                    (ThetaLowerSegment.join cell910452992 cell910518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell910584064 cell910649600)
                    (ThetaLowerSegment.join cell910715136 cell910780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell910846208 cell910911744)
                    (ThetaLowerSegment.join cell910977280 cell911042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell911108352 cell911173888)
                    (ThetaLowerSegment.join cell911239424 cell911304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell911370496 cell911436032)
                    (ThetaLowerSegment.join cell911501568 cell911567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell911632640 cell911698176)
                    (ThetaLowerSegment.join cell911763712 cell911829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell911894784 cell911960320)
                    (ThetaLowerSegment.join cell912025856 cell912091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell912156928 cell912222464)
                    (ThetaLowerSegment.join cell912288000 cell912353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell912419072 cell912484608)
                    (ThetaLowerSegment.join cell912550144 cell912615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell912681216 cell912746752)
                    (ThetaLowerSegment.join cell912812288 cell912877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell912943360 cell913008896)
                    (ThetaLowerSegment.join cell913074432 cell913139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell913205504 cell913271040)
                    (ThetaLowerSegment.join cell913336576 cell913402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell913467648 cell913533184)
                    (ThetaLowerSegment.join cell913598720 cell913664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell913729792 cell913795328)
                    (ThetaLowerSegment.join cell913860864 cell913926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell913991936 cell914057472)
                    (ThetaLowerSegment.join cell914123008 cell914188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell914254080 cell914319616)
                    (ThetaLowerSegment.join cell914385152 cell914450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell914516224 cell914581760)
                    (ThetaLowerSegment.join cell914647296 cell914712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell914778368 cell914843904)
                    (ThetaLowerSegment.join cell914909440 cell914974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell915040512 cell915106048)
                    (ThetaLowerSegment.join cell915171584 cell915237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell915302656 cell915368192)
                    (ThetaLowerSegment.join cell915433728 cell915499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell915564800 cell915630336)
                    (ThetaLowerSegment.join cell915695872 cell915761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell915826944 cell915892480)
                    (ThetaLowerSegment.join cell915958016 cell916023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell916089088 cell916154624)
                    (ThetaLowerSegment.join cell916220160 cell916285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell916351232 cell916416768)
                    (ThetaLowerSegment.join cell916482304 cell916547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell916613376 cell916678912)
                    (ThetaLowerSegment.join cell916744448 cell916809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell916875520 cell916941056)
                    (ThetaLowerSegment.join cell917006592 cell917072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell917137664 cell917203200)
                    (ThetaLowerSegment.join cell917268736 cell917334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell917399808 cell917465344)
                    (ThetaLowerSegment.join cell917530880 cell917596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell917661952 cell917727488)
                    (ThetaLowerSegment.join cell917793024 cell917858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell917924096 cell917989632)
                    (ThetaLowerSegment.join cell918055168 cell918120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell918186240 cell918251776)
                    (ThetaLowerSegment.join cell918317312 cell918382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell918448384 cell918513920)
                    (ThetaLowerSegment.join cell918579456 cell918644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell918710528 cell918776064)
                    (ThetaLowerSegment.join cell918841600 cell918907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell918972672 cell919038208)
                    (ThetaLowerSegment.join cell919103744 cell919169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell919234816 cell919300352)
                    (ThetaLowerSegment.join cell919365888 cell919431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell919496960 cell919562496)
                    (ThetaLowerSegment.join cell919628032 cell919693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell919759104 cell919824640)
                    (ThetaLowerSegment.join cell919890176 cell919955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell920021248 cell920086784)
                    (ThetaLowerSegment.join cell920152320 cell920217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell920283392 cell920348928)
                    (ThetaLowerSegment.join cell920414464 cell920480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell920545536 cell920611072)
                    (ThetaLowerSegment.join cell920676608 cell920742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell920807680 cell920873216)
                    (ThetaLowerSegment.join cell920938752 cell921004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell921069824 cell921135360)
                    (ThetaLowerSegment.join cell921200896 cell921266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell921331968 cell921397504)
                    (ThetaLowerSegment.join cell921463040 cell921528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell921594112 cell921659648)
                    (ThetaLowerSegment.join cell921725184 cell921790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell921856256 cell921921792)
                    (ThetaLowerSegment.join cell921987328 cell922052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell922118400 cell922183936)
                    (ThetaLowerSegment.join cell922249472 cell922315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell922380544 cell922446080)
                    (ThetaLowerSegment.join cell922511616 cell922577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell922642688 cell922708224)
                    (ThetaLowerSegment.join cell922773760 cell922839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell922904832 cell922970368)
                    (ThetaLowerSegment.join cell923035904 cell923101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell923166976 cell923232512)
                    (ThetaLowerSegment.join cell923298048 cell923363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell923429120 cell923494656)
                    (ThetaLowerSegment.join cell923560192 cell923625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell923691264 cell923756800)
                    (ThetaLowerSegment.join cell923822336 cell923887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell923953408 cell924018944)
                    (ThetaLowerSegment.join cell924084480 cell924150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell924215552 cell924281088)
                    (ThetaLowerSegment.join cell924346624 cell924412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell924477696 cell924543232)
                    (ThetaLowerSegment.join cell924608768 cell924674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell924739840 cell924805376)
                    (ThetaLowerSegment.join cell924870912 cell924936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell925001984 cell925067520)
                    (ThetaLowerSegment.join cell925133056 cell925198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell925264128 cell925329664)
                    (ThetaLowerSegment.join cell925395200 cell925460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell925526272 cell925591808)
                    (ThetaLowerSegment.join cell925657344 cell925722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell925788416 cell925853952)
                    (ThetaLowerSegment.join cell925919488 cell925985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell926050560 cell926116096)
                    (ThetaLowerSegment.join cell926181632 cell926247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell926312704 cell926378240)
                    (ThetaLowerSegment.join cell926443776 cell926509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell926574848 cell926640384)
                    (ThetaLowerSegment.join cell926705920 cell926771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell926836992 cell926902528)
                    (ThetaLowerSegment.join cell926968064 cell927033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell927099136 cell927164672)
                    (ThetaLowerSegment.join cell927230208 cell927295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell927361280 cell927426816)
                    (ThetaLowerSegment.join cell927492352 cell927557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell927623424 cell927688960)
                    (ThetaLowerSegment.join cell927754496 cell927820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell927885568 cell927951104)
                    (ThetaLowerSegment.join cell928016640 cell928082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell928147712 cell928213248)
                    (ThetaLowerSegment.join cell928278784 cell928344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell928409856 cell928475392)
                    (ThetaLowerSegment.join cell928540928 cell928606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell928672000 cell928737536)
                    (ThetaLowerSegment.join cell928803072 cell928868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell928934144 cell928999680)
                    (ThetaLowerSegment.join cell929065216 cell929130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell929196288 cell929261824)
                    (ThetaLowerSegment.join cell929327360 cell929392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell929458432 cell929523968)
                    (ThetaLowerSegment.join cell929589504 cell929655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell929720576 cell929786112)
                    (ThetaLowerSegment.join cell929851648 cell929917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell929982720 cell930048256)
                    (ThetaLowerSegment.join cell930113792 cell930179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell930244864 cell930310400)
                    (ThetaLowerSegment.join cell930375936 cell930441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell930507008 cell930572544)
                    (ThetaLowerSegment.join cell930638080 cell930703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell930769152 cell930834688)
                    (ThetaLowerSegment.join cell930900224 cell930965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell931031296 cell931096832)
                    (ThetaLowerSegment.join cell931162368 cell931227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell931293440 cell931358976)
                    (ThetaLowerSegment.join cell931424512 cell931490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell931555584 cell931621120)
                    (ThetaLowerSegment.join cell931686656 cell931752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell931817728 cell931883264)
                    (ThetaLowerSegment.join cell931948800 cell932014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell932079872 cell932145408)
                    (ThetaLowerSegment.join cell932210944 cell932276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell932342016 cell932407552)
                    (ThetaLowerSegment.join cell932473088 cell932538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell932604160 cell932669696)
                    (ThetaLowerSegment.join cell932735232 cell932800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell932866304 cell932931840)
                    (ThetaLowerSegment.join cell932997376 cell933062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell933128448 cell933193984)
                    (ThetaLowerSegment.join cell933259520 cell933325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell933390592 cell933456128)
                    (ThetaLowerSegment.join cell933521664 cell933587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell933652736 cell933718272)
                    (ThetaLowerSegment.join cell933783808 cell933849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell933914880 cell933980416)
                    (ThetaLowerSegment.join cell934045952 cell934111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell934177024 cell934242560)
                    (ThetaLowerSegment.join cell934308096 cell934373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell934439168 cell934504704)
                    (ThetaLowerSegment.join cell934570240 cell934635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell934701312 cell934766848)
                    (ThetaLowerSegment.join cell934832384 cell934897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell934963456 cell935028992)
                    (ThetaLowerSegment.join cell935094528 cell935160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell935225600 cell935291136)
                    (ThetaLowerSegment.join cell935356672 cell935422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell935487744 cell935553280)
                    (ThetaLowerSegment.join cell935618816 cell935684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell935749888 cell935815424)
                    (ThetaLowerSegment.join cell935880960 cell935946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell936012032 cell936077568)
                    (ThetaLowerSegment.join cell936143104 cell936208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell936274176 cell936339712)
                    (ThetaLowerSegment.join cell936405248 cell936470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell936536320 cell936601856)
                    (ThetaLowerSegment.join cell936667392 cell936732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell936798464 cell936864000)
                  (ThetaLowerSegment.join cell936929536 cell936995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell937060608 cell937126144)
                  (ThetaLowerSegment.join cell937191680 cell937257216)))
              (ThetaLowerSegment.join cell937322752 cell937339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
