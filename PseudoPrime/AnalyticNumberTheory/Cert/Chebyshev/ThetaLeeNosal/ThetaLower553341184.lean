/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 553341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell521341184 :
    ThetaLowerSegment 521341184 521406720 (26065051450421 / 50000) (13034195205493 / 25000) := by
  exact
    packedTile32768 521341184 521406720 13 3327 22832 29 _ _ (200719 / 10000) (2007193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521406720 :
    ThetaLowerSegment 521406720 521472256 (13034195205493 / 25000) (26071680216703 / 50000) := by
  exact
    packedTile32768 521406720 521472256 13 3278 22834 29 _ _ (2007203 / 100000) (1003603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521472256 :
    ThetaLowerSegment 521472256 521537792 (26071680216703 / 50000) (26074951977153 / 50000) := by
  exact
    packedTile32768 521472256 521537792 13 3260 22835 29 _ _ (401443 / 20000) (1003609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521537792 :
    ThetaLowerSegment 521537792 521603328 (26074951977153 / 50000) (26078263903353 / 50000) := by
  exact
    packedTile32768 521537792 521603328 13 3300 22837 29 _ _ (501807 / 25000) (2007231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521603328 :
    ThetaLowerSegment 521603328 521668864 (26078263903353 / 50000) (26081508606813 / 50000) := by
  exact
    packedTile32768 521603328 521668864 13 3233 22838 29 _ _ (50181 / 2500) (2007243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521668864 :
    ThetaLowerSegment 521668864 521734400 (26081508606813 / 50000) (6521201630873 / 12500) := by
  exact
    packedTile32768 521668864 521734400 13 3286 22840 29 _ _ (2007253 / 100000) (250907 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521734400 :
    ThetaLowerSegment 521734400 521799936 (6521201630873 / 12500) (13044059255371 / 25000) := by
  exact
    packedTile32768 521734400 521799936 13 3300 22841 29 _ _ (401453 / 20000) (501817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521799936 :
    ThetaLowerSegment 521799936 521865472 (13044059255371 / 25000) (13045719274277 / 25000) := by
  exact
    packedTile32768 521799936 521865472 13 3308 22842 29 _ _ (1003639 / 50000) (2007281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521865472 :
    ThetaLowerSegment 521865472 521931008 (13045719274277 / 25000) (52189418858477 / 100000) := by
  exact
    packedTile32768 521865472 521931008 13 3259 22844 29 _ _ (2007291 / 100000) (1003647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521931008 :
    ThetaLowerSegment 521931008 521996544 (52189418858477 / 100000) (52195930549409 / 100000) := by
  exact
    packedTile32768 521931008 521996544 13 3244 22845 29 _ _ (2007303 / 100000) (1003653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell521996544 :
    ThetaLowerSegment 521996544 522062080 (52195930549409 / 100000) (52202390092297 / 100000) := by
  exact
    packedTile32768 521996544 522062080 13 3218 22847 29 _ _ (501829 / 25000) (2007319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522062080 :
    ThetaLowerSegment 522062080 522127616 (52202390092297 / 100000) (10441795227093 / 20000) := by
  exact
    packedTile32768 522062080 522127616 13 3281 22848 29 _ _ (62729 / 3125) (2007331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522127616 :
    ThetaLowerSegment 522127616 522193152 (10441795227093 / 20000) (6526931728109 / 12500) := by
  exact
    packedTile32768 522127616 522193152 13 3227 22850 29 _ _ (2007341 / 100000) (125459 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522193152 :
    ThetaLowerSegment 522193152 522258688 (6526931728109 / 12500) (26110936669883 / 50000) := by
  exact
    packedTile32768 522193152 522258688 13 3198 22851 29 _ _ (2007353 / 100000) (501839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522258688 :
    ThetaLowerSegment 522258688 522324224 (26110936669883 / 50000) (26114196632267 / 50000) := by
  exact
    packedTile32768 522258688 522324224 13 3248 22852 29 _ _ (1003683 / 50000) (2007369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522324224 :
    ThetaLowerSegment 522324224 522389760 (26114196632267 / 50000) (13058719775713 / 25000) := by
  exact
    packedTile32768 522324224 522389760 13 3231 22854 29 _ _ (1003689 / 50000) (2007381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522389760 :
    ThetaLowerSegment 522389760 522455296 (13058719775713 / 25000) (52241453308377 / 100000) := by
  exact
    packedTile32768 522389760 522455296 13 3275 22855 29 _ _ (2007391 / 100000) (1003697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522455296 :
    ThetaLowerSegment 522455296 522520832 (52241453308377 / 100000) (52248222271293 / 100000) := by
  exact
    packedTile32768 522455296 522520832 13 3372 22857 29 _ _ (2007403 / 100000) (1003703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522520832 :
    ThetaLowerSegment 522520832 522586368 (52248222271293 / 100000) (52254766447453 / 100000) := by
  exact
    packedTile32768 522520832 522586368 13 3260 22858 29 _ _ (250927 / 12500) (2007419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522586368 :
    ThetaLowerSegment 522586368 522651904 (52254766447453 / 100000) (6532660571177 / 12500) := by
  exact
    packedTile32768 522586368 522651904 13 3247 22860 29 _ _ (2007429 / 100000) (250929 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522651904 :
    ThetaLowerSegment 522651904 522717440 (6532660571177 / 12500) (52267931206567 / 100000) := by
  exact
    packedTile32768 522651904 522717440 13 3311 22861 29 _ _ (2007441 / 100000) (501861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522717440 :
    ThetaLowerSegment 522717440 522782976 (52267931206567 / 100000) (52274483536423 / 100000) := by
  exact
    packedTile32768 522717440 522782976 13 3264 22863 29 _ _ (1003727 / 50000) (2007457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522782976 :
    ThetaLowerSegment 522782976 522848512 (52274483536423 / 100000) (52281080069699 / 100000) := by
  exact
    packedTile32768 522782976 522848512 13 3286 22864 29 _ _ (1003733 / 50000) (2007469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522848512 :
    ThetaLowerSegment 522848512 522914048 (52281080069699 / 100000) (13071899588503 / 25000) := by
  exact
    packedTile32768 522848512 522914048 13 3247 22865 29 _ _ (2007479 / 100000) (1003741 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522914048 :
    ThetaLowerSegment 522914048 522979584 (13071899588503 / 25000) (26147053319917 / 50000) := by
  exact
    packedTile32768 522914048 522979584 13 3242 22867 29 _ _ (2007491 / 100000) (1003747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell522979584 :
    ThetaLowerSegment 522979584 523045120 (26147053319917 / 50000) (26150356667749 / 50000) := by
  exact
    packedTile32768 522979584 523045120 13 3291 22868 29 _ _ (125469 / 6250) (2007507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523045120 :
    ThetaLowerSegment 523045120 523110656 (26150356667749 / 50000) (5230737226607 / 10000) := by
  exact
    packedTile32768 523045120 523110656 13 3317 22870 29 _ _ (501879 / 25000) (2007519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523110656 :
    ThetaLowerSegment 523110656 523176192 (5230737226607 / 10000) (52313934878371 / 100000) := by
  exact
    packedTile32768 523110656 523176192 13 3269 22871 29 _ _ (2007529 / 100000) (501883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523176192 :
    ThetaLowerSegment 523176192 523241728 (52313934878371 / 100000) (52320563778753 / 100000) := by
  exact
    packedTile32768 523176192 523241728 13 3302 22873 29 _ _ (2007541 / 100000) (250943 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523241728 :
    ThetaLowerSegment 523241728 523307264 (52320563778753 / 100000) (52327200752277 / 100000) := by
  exact
    packedTile32768 523241728 523307264 13 3306 22874 29 _ _ (1003777 / 50000) (2007557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523307264 :
    ThetaLowerSegment 523307264 523372800 (52327200752277 / 100000) (52333805644417 / 100000) := by
  exact
    packedTile32768 523307264 523372800 13 3290 22875 29 _ _ (1003783 / 50000) (2007569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523372800 :
    ThetaLowerSegment 523372800 523438336 (52333805644417 / 100000) (52340362397431 / 100000) := by
  exact
    packedTile32768 523372800 523438336 13 3266 22877 29 _ _ (2007579 / 100000) (1003791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523438336 :
    ThetaLowerSegment 523438336 523503872 (52340362397431 / 100000) (1635840032669 / 3125) := by
  exact
    packedTile32768 523438336 523503872 13 3247 22878 29 _ _ (2007591 / 100000) (1003797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523503872 :
    ThetaLowerSegment 523503872 523569408 (1635840032669 / 3125) (1308833537877 / 2500) := by
  exact
    packedTile32768 523503872 523569408 13 3218 22880 29 _ _ (501901 / 25000) (2007607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523569408 :
    ThetaLowerSegment 523569408 523634944 (1308833537877 / 2500) (13089983632327 / 25000) := by
  exact
    packedTile32768 523569408 523634944 13 3284 22881 29 _ _ (2007617 / 100000) (100381 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523634944 :
    ThetaLowerSegment 523634944 523700480 (13089983632327 / 25000) (52366328827673 / 100000) := by
  exact
    packedTile32768 523634944 523700480 13 3185 22883 29 _ _ (2007629 / 100000) (125477 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523700480 :
    ThetaLowerSegment 523700480 523766016 (52366328827673 / 100000) (52372839610679 / 100000) := by
  exact
    packedTile32768 523700480 523766016 13 3243 22884 29 _ _ (1003821 / 50000) (401529 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523766016 :
    ThetaLowerSegment 523766016 523831552 (52372839610679 / 100000) (10475850411511 / 20000) := by
  exact
    packedTile32768 523766016 523831552 13 3194 22885 29 _ _ (1003827 / 50000) (2007657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523831552 :
    ThetaLowerSegment 523831552 523897088 (10475850411511 / 20000) (26192967790499 / 50000) := by
  exact
    packedTile32768 523831552 523897088 13 3329 22887 29 _ _ (2007667 / 100000) (200767 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523897088 :
    ThetaLowerSegment 523897088 523962624 (26192967790499 / 50000) (6549068609453 / 12500) := by
  exact
    packedTile32768 523897088 523962624 13 3294 22888 29 _ _ (2007679 / 100000) (1003841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell523962624 :
    ThetaLowerSegment 523962624 524028160 (6549068609453 / 12500) (3274947638317 / 6250) := by
  exact
    packedTile32768 523962624 524028160 13 3294 22890 29 _ _ (501923 / 25000) (401539 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524028160 :
    ThetaLowerSegment 524028160 524093696 (3274947638317 / 6250) (6550715674681 / 12500) := by
  exact
    packedTile32768 524028160 524093696 13 3269 22891 29 _ _ (250963 / 12500) (2007707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524093696 :
    ThetaLowerSegment 524093696 524159232 (6550715674681 / 12500) (52412320747793 / 100000) := by
  exact
    packedTile32768 524093696 524159232 13 3285 22893 29 _ _ (2007717 / 100000) (50193 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524159232 :
    ThetaLowerSegment 524159232 524224768 (52412320747793 / 100000) (13104675829571 / 25000) := by
  exact
    packedTile32768 524159232 524224768 13 3179 22894 29 _ _ (2007729 / 100000) (501933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524224768 :
    ThetaLowerSegment 524224768 524290304 (13104675829571 / 25000) (1638289644832 / 3125) := by
  exact
    packedTile32768 524224768 524290304 13 3270 22895 29 _ _ (1003871 / 50000) (401549 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524290304 :
    ThetaLowerSegment 524290304 524355840 (1638289644832 / 3125) (26215863789621 / 50000) := by
  exact
    packedTile32768 524290304 524355840 13 3217 22897 29 _ _ (1003877 / 50000) (2007757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524355840 :
    ThetaLowerSegment 524355840 524421376 (26215863789621 / 50000) (52438303016167 / 100000) := by
  exact
    packedTile32768 524355840 524421376 13 3275 22898 29 _ _ (2007767 / 100000) (200777 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524421376 :
    ThetaLowerSegment 524421376 524486912 (52438303016167 / 100000) (26222525580693 / 50000) := by
  exact
    packedTile32768 524421376 524486912 13 3361 22900 29 _ _ (2007779 / 100000) (1003891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524486912 :
    ThetaLowerSegment 524486912 524552448 (26222525580693 / 50000) (26225777199837 / 50000) := by
  exact
    packedTile32768 524486912 524552448 13 3239 22901 29 _ _ (125487 / 6250) (401559 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524552448 :
    ThetaLowerSegment 524552448 524617984 (26225777199837 / 50000) (1049163362121 / 2000) := by
  exact
    packedTile32768 524552448 524617984 13 3294 22903 29 _ _ (501951 / 25000) (2007807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524617984 :
    ThetaLowerSegment 524617984 524683520 (1049163362121 / 2000) (26232300575859 / 50000) := by
  exact
    packedTile32768 524617984 524683520 13 3204 22904 29 _ _ (2007817 / 100000) (100391 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524683520 :
    ThetaLowerSegment 524683520 524749056 (26232300575859 / 50000) (52471249073537 / 100000) := by
  exact
    packedTile32768 524683520 524749056 13 3311 22905 29 _ _ (2007829 / 100000) (250979 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524749056 :
    ThetaLowerSegment 524749056 524814592 (52471249073537 / 100000) (2099110098951 / 4000) := by
  exact
    packedTile32768 524749056 524814592 13 3239 22907 29 _ _ (1003921 / 50000) (401569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524814592 :
    ThetaLowerSegment 524814592 524880128 (2099110098951 / 4000) (52484263944297 / 100000) := by
  exact
    packedTile32768 524814592 524880128 13 3243 22908 29 _ _ (1003927 / 50000) (2007857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524880128 :
    ThetaLowerSegment 524880128 524945664 (52484263944297 / 100000) (26245391744223 / 50000) := by
  exact
    packedTile32768 524880128 524945664 13 3247 22910 29 _ _ (2007867 / 100000) (200787 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell524945664 :
    ThetaLowerSegment 524945664 525011200 (26245391744223 / 50000) (52497375355203 / 100000) := by
  exact
    packedTile32768 524945664 525011200 13 3283 22911 29 _ _ (2007879 / 100000) (1003941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525011200 :
    ThetaLowerSegment 525011200 525076736 (52497375355203 / 100000) (52503955217287 / 100000) := by
  exact
    packedTile32768 525011200 525076736 13 3277 22913 29 _ _ (501973 / 25000) (401579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525076736 :
    ThetaLowerSegment 525076736 525142272 (52503955217287 / 100000) (52510571260967 / 100000) := by
  exact
    packedTile32768 525076736 525142272 13 3295 22914 29 _ _ (62747 / 3125) (2007907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525142272 :
    ThetaLowerSegment 525142272 525207808 (52510571260967 / 100000) (420136984727 / 800) := by
  exact
    packedTile32768 525142272 525207808 13 3263 22915 29 _ _ (501979 / 25000) (2007919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525207808 :
    ThetaLowerSegment 525207808 525273344 (420136984727 / 800) (420189190881 / 800) := by
  exact
    packedTile32768 525207808 525273344 13 3250 22917 29 _ _ (2007929 / 100000) (501983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525273344 :
    ThetaLowerSegment 525273344 525338880 (420189190881 / 800) (52530222858959 / 100000) := by
  exact
    packedTile32768 525273344 525338880 13 3274 22918 29 _ _ (2007941 / 100000) (250993 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525338880 :
    ThetaLowerSegment 525338880 525404416 (52530222858959 / 100000) (52536863162837 / 100000) := by
  exact
    packedTile32768 525338880 525404416 13 3307 22920 29 _ _ (1003977 / 50000) (2007957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525404416 :
    ThetaLowerSegment 525404416 525469952 (52536863162837 / 100000) (52543429211657 / 100000) := by
  exact
    packedTile32768 525404416 525469952 13 3270 22921 29 _ _ (1003983 / 50000) (2007969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525469952 :
    ThetaLowerSegment 525469952 525535488 (52543429211657 / 100000) (26274918336323 / 50000) := by
  exact
    packedTile32768 525469952 525535488 13 3191 22923 29 _ _ (2007979 / 100000) (1003991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525535488 :
    ThetaLowerSegment 525535488 525601024 (26274918336323 / 50000) (656952625451 / 1250) := by
  exact
    packedTile32768 525535488 525601024 13 3174 22924 29 _ _ (2007991 / 100000) (1003997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525601024 :
    ThetaLowerSegment 525601024 525666560 (656952625451 / 1250) (2628135296451 / 5000) := by
  exact
    packedTile32768 525601024 525666560 13 3235 22925 29 _ _ (502001 / 25000) (2008007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525666560 :
    ThetaLowerSegment 525666560 525732096 (2628135296451 / 5000) (13142306991247 / 25000) := by
  exact
    packedTile32768 525666560 525732096 13 3248 22927 29 _ _ (125501 / 6250) (2008019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525732096 :
    ThetaLowerSegment 525732096 525797632 (13142306991247 / 25000) (1642994447882 / 3125) := by
  exact
    packedTile32768 525732096 525797632 13 3284 22928 29 _ _ (2008029 / 100000) (62751 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525797632 :
    ThetaLowerSegment 525797632 525863168 (1642994447882 / 3125) (52582386618253 / 100000) := by
  exact
    packedTile32768 525797632 525863168 13 3269 22930 29 _ _ (2008041 / 100000) (502011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525863168 :
    ThetaLowerSegment 525863168 525928704 (52582386618253 / 100000) (52588886689051 / 100000) := by
  exact
    packedTile32768 525863168 525928704 13 3237 22931 29 _ _ (1004027 / 50000) (2008057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525928704 :
    ThetaLowerSegment 525928704 525994240 (52588886689051 / 100000) (52595485193927 / 100000) := by
  exact
    packedTile32768 525928704 525994240 13 3286 22933 29 _ _ (1004033 / 50000) (2008069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell525994240 :
    ThetaLowerSegment 525994240 526059776 (52595485193927 / 100000) (13150503364689 / 25000) := by
  exact
    packedTile32768 525994240 526059776 13 3251 22934 29 _ _ (2008079 / 100000) (1004041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526059776 :
    ThetaLowerSegment 526059776 526125312 (13150503364689 / 25000) (1644014984743 / 3125) := by
  exact
    packedTile32768 526059776 526125312 13 3220 22935 29 _ _ (2008091 / 100000) (1004047 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526125312 :
    ThetaLowerSegment 526125312 526190848 (1644014984743 / 3125) (52615176535281 / 100000) := by
  exact
    packedTile32768 526125312 526190848 13 3335 22937 29 _ _ (2008103 / 100000) (1004053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526190848 :
    ThetaLowerSegment 526190848 526256384 (52615176535281 / 100000) (52621706928513 / 100000) := by
  exact
    packedTile32768 526190848 526256384 13 3252 22938 29 _ _ (502029 / 25000) (2008119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526256384 :
    ThetaLowerSegment 526256384 526321920 (52621706928513 / 100000) (10525654299789 / 20000) := by
  exact
    packedTile32768 526256384 526321920 13 3269 22940 29 _ _ (62754 / 3125) (2008131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526321920 :
    ThetaLowerSegment 526321920 526387456 (10525654299789 / 20000) (13158718064603 / 25000) := by
  exact
    packedTile32768 526321920 526387456 13 3287 22941 29 _ _ (2008141 / 100000) (125509 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526387456 :
    ThetaLowerSegment 526387456 526452992 (13158718064603 / 25000) (26320703394137 / 50000) := by
  exact
    packedTile32768 526387456 526452992 13 3254 22943 29 _ _ (2008153 / 100000) (502039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526452992 :
    ThetaLowerSegment 526452992 526518528 (26320703394137 / 50000) (13162001907479 / 25000) := by
  exact
    packedTile32768 526452992 526518528 13 3287 22944 29 _ _ (1004083 / 50000) (2008169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526518528 :
    ThetaLowerSegment 526518528 526584064 (13162001907479 / 25000) (13163630539837 / 25000) := by
  exact
    packedTile32768 526518528 526584064 13 3244 22945 29 _ _ (1004089 / 50000) (2008181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526584064 :
    ThetaLowerSegment 526584064 526649600 (13163630539837 / 25000) (26330600701307 / 50000) := by
  exact
    packedTile32768 526584064 526649600 13 3326 22947 29 _ _ (2008191 / 100000) (1004097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526649600 :
    ThetaLowerSegment 526649600 526715136 (26330600701307 / 50000) (52667794333063 / 100000) := by
  exact
    packedTile32768 526649600 526715136 13 3283 22948 29 _ _ (2008203 / 100000) (1004103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526715136 :
    ThetaLowerSegment 526715136 526780672 (52667794333063 / 100000) (52674383289759 / 100000) := by
  exact
    packedTile32768 526715136 526780672 13 3281 22950 29 _ _ (251027 / 12500) (2008219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526780672 :
    ThetaLowerSegment 526780672 526846208 (52674383289759 / 100000) (52680908022531 / 100000) := by
  exact
    packedTile32768 526780672 526846208 13 3249 22951 29 _ _ (502057 / 25000) (2008231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526846208 :
    ThetaLowerSegment 526846208 526911744 (52680908022531 / 100000) (52687493041491 / 100000) := by
  exact
    packedTile32768 526846208 526911744 13 3279 22953 29 _ _ (25103 / 1250) (2008243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526911744 :
    ThetaLowerSegment 526911744 526977280 (52687493041491 / 100000) (26346994869973 / 50000) := by
  exact
    packedTile32768 526911744 526977280 13 3235 22954 29 _ _ (2008253 / 100000) (62758 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell526977280 :
    ThetaLowerSegment 526977280 527042816 (26346994869973 / 50000) (52700478444161 / 100000) := by
  exact
    packedTile32768 526977280 527042816 13 3231 22955 29 _ _ (401653 / 20000) (502067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527042816 :
    ThetaLowerSegment 527042816 527108352 (52700478444161 / 100000) (52707023422163 / 100000) := by
  exact
    packedTile32768 527042816 527108352 13 3259 22957 29 _ _ (1004139 / 50000) (2008281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527108352 :
    ThetaLowerSegment 527108352 527173888 (52707023422163 / 100000) (52713516223733 / 100000) := by
  exact
    packedTile32768 527108352 527173888 13 3233 22958 29 _ _ (200829 / 10000) (2008293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527173888 :
    ThetaLowerSegment 527173888 527239424 (52713516223733 / 100000) (52720087391149 / 100000) := by
  exact
    packedTile32768 527173888 527239424 13 3272 22960 29 _ _ (2008303 / 100000) (1004153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527239424 :
    ThetaLowerSegment 527239424 527304960 (52720087391149 / 100000) (52726638514679 / 100000) := by
  exact
    packedTile32768 527239424 527304960 13 3262 22961 29 _ _ (401663 / 20000) (1004159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527304960 :
    ThetaLowerSegment 527304960 527370496 (52726638514679 / 100000) (52733314193627 / 100000) := by
  exact
    packedTile32768 527304960 527370496 13 3324 22963 29 _ _ (2008327 / 100000) (200833 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527370496 :
    ThetaLowerSegment 527370496 527436032 (52733314193627 / 100000) (52739937698947 / 100000) := by
  exact
    packedTile32768 527370496 527436032 13 3298 22964 29 _ _ (100417 / 5000) (2008343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527436032 :
    ThetaLowerSegment 527436032 527501568 (52739937698947 / 100000) (52746505009987 / 100000) := by
  exact
    packedTile32768 527436032 527501568 13 3270 22965 29 _ _ (62761 / 3125) (401671 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527501568 :
    ThetaLowerSegment 527501568 527567104 (52746505009987 / 100000) (52752871527037 / 100000) := by
  exact
    packedTile32768 527501568 527567104 13 3170 22967 29 _ _ (401673 / 20000) (125523 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527567104 :
    ThetaLowerSegment 527567104 527632640 (52752871527037 / 100000) (52759563439201 / 100000) := by
  exact
    packedTile32768 527567104 527632640 13 3332 22968 29 _ _ (2008377 / 100000) (100419 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527632640 :
    ThetaLowerSegment 527632640 527698176 (52759563439201 / 100000) (52766092715091 / 100000) := by
  exact
    packedTile32768 527632640 527698176 13 3251 22970 29 _ _ (200839 / 10000) (2008393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527698176 :
    ThetaLowerSegment 527698176 527763712 (52766092715091 / 100000) (52772736508907 / 100000) := by
  exact
    packedTile32768 527698176 527763712 13 3308 22971 29 _ _ (1004201 / 50000) (401681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527763712 :
    ThetaLowerSegment 527763712 527829248 (52772736508907 / 100000) (10555881692043 / 20000) := by
  exact
    packedTile32768 527763712 527829248 13 3322 22973 29 _ _ (1004207 / 50000) (2008417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527829248 :
    ThetaLowerSegment 527829248 527894784 (10555881692043 / 20000) (659824825733 / 1250) := by
  exact
    packedTile32768 527829248 527894784 13 3275 22974 29 _ _ (2008427 / 100000) (200843 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527894784 :
    ThetaLowerSegment 527894784 527960320 (659824825733 / 1250) (26396220590793 / 50000) := by
  exact
    packedTile32768 527894784 527960320 13 3214 22975 29 _ _ (2008439 / 100000) (1004221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell527960320 :
    ThetaLowerSegment 527960320 528025856 (26396220590793 / 50000) (26399563659147 / 50000) := by
  exact
    packedTile32768 527960320 528025856 13 3329 22977 29 _ _ (502113 / 25000) (401691 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528025856 :
    ThetaLowerSegment 528025856 528091392 (26399563659147 / 50000) (26402803311579 / 50000) := by
  exact
    packedTile32768 528025856 528091392 13 3226 22978 29 _ _ (125529 / 6250) (2008467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528091392 :
    ThetaLowerSegment 528091392 528156928 (26402803311579 / 50000) (26406082148649 / 50000) := by
  exact
    packedTile32768 528091392 528156928 13 3265 22980 29 _ _ (502119 / 25000) (2008479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528156928 :
    ThetaLowerSegment 528156928 528222464 (26406082148649 / 50000) (6602345524019 / 12500) := by
  exact
    packedTile32768 528156928 528222464 13 3286 22981 29 _ _ (2008489 / 100000) (502123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528222464 :
    ThetaLowerSegment 528222464 528288000 (6602345524019 / 12500) (52825229556871 / 100000) := by
  exact
    packedTile32768 528222464 528288000 13 3219 22983 29 _ _ (2008501 / 100000) (251063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528288000 :
    ThetaLowerSegment 528288000 528353536 (52825229556871 / 100000) (52831787355081 / 100000) := by
  exact
    packedTile32768 528288000 528353536 13 3265 22984 29 _ _ (1004257 / 50000) (2008517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528353536 :
    ThetaLowerSegment 528353536 528419072 (52831787355081 / 100000) (10567682696471 / 20000) := by
  exact
    packedTile32768 528353536 528419072 13 3299 22985 29 _ _ (1004263 / 50000) (2008529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528419072 :
    ThetaLowerSegment 528419072 528484608 (10567682696471 / 20000) (26422501749407 / 50000) := by
  exact
    packedTile32768 528419072 528484608 13 3281 22987 29 _ _ (2008539 / 100000) (1004271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528484608 :
    ThetaLowerSegment 528484608 528550144 (26422501749407 / 50000) (52851589537543 / 100000) := by
  exact
    packedTile32768 528484608 528550144 13 3279 22988 29 _ _ (2008551 / 100000) (1004277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528550144 :
    ThetaLowerSegment 528550144 528615680 (52851589537543 / 100000) (2114325819487 / 4000) := by
  exact
    packedTile32768 528550144 528615680 13 3264 22990 29 _ _ (2008563 / 100000) (1004283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528615680 :
    ThetaLowerSegment 528615680 528681216 (2114325819487 / 4000) (52864580964679 / 100000) := by
  exact
    packedTile32768 528615680 528681216 13 3204 22991 29 _ _ (62768 / 3125) (2008579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528681216 :
    ThetaLowerSegment 528681216 528746752 (52864580964679 / 100000) (10574214544219 / 20000) := by
  exact
    packedTile32768 528681216 528746752 13 3232 22993 29 _ _ (502147 / 25000) (2008591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528746752 :
    ThetaLowerSegment 528746752 528812288 (10574214544219 / 20000) (26438789289867 / 50000) := by
  exact
    packedTile32768 528746752 528812288 13 3239 22994 29 _ _ (2008601 / 100000) (502151 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528812288 :
    ThetaLowerSegment 528812288 528877824 (26438789289867 / 50000) (5288419093373 / 10000) := by
  exact
    packedTile32768 528812288 528877824 13 3292 22995 29 _ _ (2008613 / 100000) (251077 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528877824 :
    ThetaLowerSegment 528877824 528943360 (5288419093373 / 10000) (10578153032671 / 20000) := by
  exact
    packedTile32768 528877824 528943360 13 3273 22997 29 _ _ (16069 / 800) (502157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell528943360 :
    ThetaLowerSegment 528943360 529008896 (10578153032671 / 20000) (52897411746497 / 100000) := by
  exact
    packedTile32768 528943360 529008896 13 3309 22998 29 _ _ (1004319 / 50000) (2008641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529008896 :
    ThetaLowerSegment 529008896 529074432 (52897411746497 / 100000) (52903933833047 / 100000) := by
  exact
    packedTile32768 529008896 529074432 13 3247 23000 29 _ _ (40173 / 2000) (2008653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529074432 :
    ThetaLowerSegment 529074432 529139968 (52903933833047 / 100000) (52910518227083 / 100000) := by
  exact
    packedTile32768 529074432 529139968 13 3278 23001 29 _ _ (1004331 / 50000) (401733 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529139968 :
    ThetaLowerSegment 529139968 529205504 (52910518227083 / 100000) (26458482032579 / 50000) := by
  exact
    packedTile32768 529139968 529205504 13 3209 23003 29 _ _ (80347 / 4000) (1004339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529205504 :
    ThetaLowerSegment 529205504 529271040 (26458482032579 / 50000) (6615439550269 / 12500) := by
  exact
    packedTile32768 529205504 529271040 13 3262 23004 29 _ _ (2008687 / 100000) (200869 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529271040 :
    ThetaLowerSegment 529271040 529336576 (6615439550269 / 12500) (6616263117269 / 12500) := by
  exact
    packedTile32768 529271040 529336576 13 3280 23005 29 _ _ (20087 / 1000) (2008703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529336576 :
    ThetaLowerSegment 529336576 529402112 (6616263117269 / 12500) (6617079658697 / 12500) := by
  exact
    packedTile32768 529336576 529402112 13 3252 23007 29 _ _ (251089 / 12500) (401743 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529402112 :
    ThetaLowerSegment 529402112 529467648 (6617079658697 / 12500) (661789972027 / 1250) := by
  exact
    packedTile32768 529402112 529467648 13 3266 23008 29 _ _ (502181 / 25000) (2008727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529467648 :
    ThetaLowerSegment 529467648 529533184 (661789972027 / 1250) (13237428526247 / 25000) := by
  exact
    packedTile32768 529467648 529533184 13 3244 23010 29 _ _ (2008737 / 100000) (100437 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529533184 :
    ThetaLowerSegment 529533184 529598720 (13237428526247 / 25000) (26478177514591 / 50000) := by
  exact
    packedTile32768 529533184 529598720 13 3306 23011 29 _ _ (2008749 / 100000) (125547 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529598720 :
    ThetaLowerSegment 529598720 529664256 (26478177514591 / 50000) (331018260451 / 625) := by
  exact
    packedTile32768 529598720 529664256 13 3269 23013 29 _ _ (1004381 / 50000) (401753 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529664256 :
    ThetaLowerSegment 529664256 529729792 (331018260451 / 625) (2648476526931 / 5000) := by
  exact
    packedTile32768 529664256 529729792 13 3290 23014 29 _ _ (1004387 / 50000) (2008777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529729792 :
    ThetaLowerSegment 529729792 529795328 (2648476526931 / 5000) (26488068717887 / 50000) := by
  exact
    packedTile32768 529729792 529795328 13 3289 23015 29 _ _ (1004393 / 50000) (2008789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529795328 :
    ThetaLowerSegment 529795328 529860864 (26488068717887 / 50000) (2649131694587 / 5000) := by
  exact
    packedTile32768 529795328 529860864 13 3234 23017 29 _ _ (2008799 / 100000) (1004401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529860864 :
    ThetaLowerSegment 529860864 529926400 (2649131694587 / 5000) (13247297662711 / 25000) := by
  exact
    packedTile32768 529860864 529926400 13 3264 23018 29 _ _ (2008811 / 100000) (1004407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529926400 :
    ThetaLowerSegment 529926400 529991936 (13247297662711 / 25000) (26497847609859 / 50000) := by
  exact
    packedTile32768 529926400 529991936 13 3238 23020 29 _ _ (2008823 / 100000) (1004413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell529991936 :
    ThetaLowerSegment 529991936 530057472 (26497847609859 / 50000) (26501238525027 / 50000) := by
  exact
    packedTile32768 529991936 530057472 13 3376 23021 29 _ _ (502209 / 25000) (2008839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530057472 :
    ThetaLowerSegment 530057472 530123008 (26501238525027 / 50000) (5300907008919 / 10000) := by
  exact
    packedTile32768 530057472 530123008 13 3282 23022 29 _ _ (125553 / 6250) (2008851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530123008 :
    ThetaLowerSegment 530123008 530188544 (5300907008919 / 10000) (1060311214317 / 2000) := by
  exact
    packedTile32768 530123008 530188544 13 3231 23024 29 _ _ (100443 / 5000) (2008863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530188544 :
    ThetaLowerSegment 530188544 530254080 (1060311214317 / 2000) (26511042767677 / 50000) := by
  exact
    packedTile32768 530188544 530254080 13 3248 23025 29 _ _ (2008873 / 100000) (502219 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530254080 :
    ThetaLowerSegment 530254080 530319616 (26511042767677 / 50000) (26514285108067 / 50000) := by
  exact
    packedTile32768 530254080 530319616 13 3228 23027 29 _ _ (401777 / 20000) (251111 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530319616 :
    ThetaLowerSegment 530319616 530385152 (26514285108067 / 50000) (1657347538516 / 3125) := by
  exact
    packedTile32768 530319616 530385152 13 3261 23028 29 _ _ (1004449 / 50000) (2008901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530385152 :
    ThetaLowerSegment 530385152 530450688 (1657347538516 / 3125) (26520848197471 / 50000) := by
  exact
    packedTile32768 530385152 530450688 13 3273 23030 29 _ _ (200891 / 10000) (2008913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530450688 :
    ThetaLowerSegment 530450688 530516224 (26520848197471 / 50000) (5304819324869 / 10000) := by
  exact
    packedTile32768 530450688 530516224 13 3234 23031 29 _ _ (1004461 / 50000) (80357 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530516224 :
    ThetaLowerSegment 530516224 530581760 (5304819324869 / 10000) (10610950484293 / 20000) := by
  exact
    packedTile32768 530516224 530581760 13 3265 23032 29 _ _ (401787 / 20000) (1004469 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530581760 :
    ThetaLowerSegment 530581760 530647296 (10610950484293 / 20000) (53061297570791 / 100000) := by
  exact
    packedTile32768 530581760 530647296 13 3258 23034 29 _ _ (2008947 / 100000) (40179 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530647296 :
    ThetaLowerSegment 530647296 530712832 (53061297570791 / 100000) (53067726239591 / 100000) := by
  exact
    packedTile32768 530647296 530712832 13 3200 23035 29 _ _ (2008959 / 100000) (1004481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530712832 :
    ThetaLowerSegment 530712832 530778368 (53067726239591 / 100000) (53074315667751 / 100000) := by
  exact
    packedTile32768 530712832 530778368 13 3280 23037 29 _ _ (502243 / 25000) (80359 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530778368 :
    ThetaLowerSegment 530778368 530843904 (53074315667751 / 100000) (10616145267139 / 20000) := by
  exact
    packedTile32768 530778368 530843904 13 3191 23038 29 _ _ (251123 / 12500) (2008987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530843904 :
    ThetaLowerSegment 530843904 530909440 (10616145267139 / 20000) (53087410265387 / 100000) := by
  exact
    packedTile32768 530843904 530909440 13 3327 23040 29 _ _ (502249 / 25000) (2008999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530909440 :
    ThetaLowerSegment 530909440 530974976 (53087410265387 / 100000) (26546930596643 / 50000) := by
  exact
    packedTile32768 530909440 530974976 13 3211 23041 29 _ _ (2009009 / 100000) (502253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell530974976 :
    ThetaLowerSegment 530974976 531040512 (26546930596643 / 50000) (53100392520557 / 100000) := by
  exact
    packedTile32768 530974976 531040512 13 3251 23042 29 _ _ (2009021 / 100000) (62782 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531040512 :
    ThetaLowerSegment 531040512 531106048 (53100392520557 / 100000) (53106962058467 / 100000) := by
  exact
    packedTile32768 531040512 531106048 13 3270 23044 29 _ _ (2009033 / 100000) (502259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531106048 :
    ThetaLowerSegment 531106048 531171584 (53106962058467 / 100000) (53113429177541 / 100000) := by
  exact
    packedTile32768 531106048 531171584 13 3219 23045 29 _ _ (1004523 / 50000) (2009049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531171584 :
    ThetaLowerSegment 531171584 531237120 (53113429177541 / 100000) (10624027082629 / 20000) := by
  exact
    packedTile32768 531171584 531237120 13 3338 23047 29 _ _ (1004529 / 50000) (2009061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531237120 :
    ThetaLowerSegment 531237120 531302656 (10624027082629 / 20000) (10625333781757 / 20000) := by
  exact
    packedTile32768 531237120 531302656 13 3252 23048 29 _ _ (200907 / 10000) (2009073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531302656 :
    ThetaLowerSegment 531302656 531368192 (10625333781757 / 20000) (26566596200643 / 50000) := by
  exact
    packedTile32768 531302656 531368192 13 3247 23050 29 _ _ (2009083 / 100000) (1004543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531368192 :
    ThetaLowerSegment 531368192 531433728 (26566596200643 / 50000) (53139667714471 / 100000) := by
  exact
    packedTile32768 531368192 531433728 13 3223 23051 29 _ _ (401819 / 20000) (1004549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531433728 :
    ThetaLowerSegment 531433728 531499264 (53139667714471 / 100000) (10629244284301 / 20000) := by
  exact
    packedTile32768 531433728 531499264 13 3262 23052 29 _ _ (2009107 / 100000) (200911 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531499264 :
    ThetaLowerSegment 531499264 531564800 (10629244284301 / 20000) (10630573116269 / 20000) := by
  exact
    packedTile32768 531499264 531564800 13 3307 23054 29 _ _ (12557 / 625) (2009123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531564800 :
    ThetaLowerSegment 531564800 531630336 (10630573116269 / 20000) (10631881061201 / 20000) := by
  exact
    packedTile32768 531564800 531630336 13 3255 23055 29 _ _ (502283 / 25000) (401827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531630336 :
    ThetaLowerSegment 531630336 531695872 (10631881061201 / 20000) (53165961142877 / 100000) := by
  exact
    packedTile32768 531630336 531695872 13 3263 23057 29 _ _ (251143 / 12500) (2009147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531695872 :
    ThetaLowerSegment 531695872 531761408 (53165961142877 / 100000) (10634487733009 / 20000) := by
  exact
    packedTile32768 531695872 531761408 13 3224 23058 29 _ _ (2009157 / 100000) (50229 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531761408 :
    ThetaLowerSegment 531761408 531826944 (10634487733009 / 20000) (10635785656183 / 20000) := by
  exact
    packedTile32768 531761408 531826944 13 3230 23059 29 _ _ (2009169 / 100000) (502293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531826944 :
    ThetaLowerSegment 531826944 531892480 (10635785656183 / 20000) (53185590725111 / 100000) := by
  exact
    packedTile32768 531826944 531892480 13 3316 23061 29 _ _ (2009181 / 100000) (62787 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531892480 :
    ThetaLowerSegment 531892480 531958016 (53185590725111 / 100000) (53192134669969 / 100000) := by
  exact
    packedTile32768 531892480 531958016 13 3257 23062 29 _ _ (1004597 / 50000) (2009197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell531958016 :
    ThetaLowerSegment 531958016 532023552 (53192134669969 / 100000) (53198702764383 / 100000) := by
  exact
    packedTile32768 531958016 532023552 13 3269 23064 29 _ _ (1004603 / 50000) (2009209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532023552 :
    ThetaLowerSegment 532023552 532089088 (53198702764383 / 100000) (10641068244131 / 20000) := by
  exact
    packedTile32768 532023552 532089088 13 3304 23065 29 _ _ (1004609 / 50000) (2009221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532089088 :
    ThetaLowerSegment 532089088 532154624 (10641068244131 / 20000) (13302976344583 / 25000) := by
  exact
    packedTile32768 532089088 532154624 13 3267 23067 29 _ _ (2009231 / 100000) (1004617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532154624 :
    ThetaLowerSegment 532154624 532220160 (13302976344583 / 25000) (53218473593699 / 100000) := by
  exact
    packedTile32768 532154624 532220160 13 3269 23068 29 _ _ (2009243 / 100000) (1004623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532220160 :
    ThetaLowerSegment 532220160 532285696 (53218473593699 / 100000) (26612452609477 / 50000) := by
  exact
    packedTile32768 532220160 532285696 13 3201 23069 29 _ _ (401851 / 20000) (1004629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532285696 :
    ThetaLowerSegment 532285696 532351232 (26612452609477 / 50000) (26615713651441 / 50000) := by
  exact
    packedTile32768 532285696 532351232 13 3246 23071 29 _ _ (502317 / 25000) (2009271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532351232 :
    ThetaLowerSegment 532351232 532416768 (26615713651441 / 50000) (26619000833521 / 50000) := by
  exact
    packedTile32768 532351232 532416768 13 3272 23072 29 _ _ (12558 / 625) (2009283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532416768 :
    ThetaLowerSegment 532416768 532482304 (26619000833521 / 50000) (1064889592489 / 2000) := by
  exact
    packedTile32768 532416768 532482304 13 3224 23074 29 _ _ (502323 / 25000) (401859 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532482304 :
    ThetaLowerSegment 532482304 532547840 (1064889592489 / 2000) (665638728439 / 1250) := by
  exact
    packedTile32768 532482304 532547840 13 3294 23075 29 _ _ (401861 / 20000) (502327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532547840 :
    ThetaLowerSegment 532547840 532613376 (665638728439 / 1250) (53257674769661 / 100000) := by
  exact
    packedTile32768 532547840 532613376 13 3273 23076 29 _ _ (2009317 / 100000) (50233 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532613376 :
    ThetaLowerSegment 532613376 532678912 (53257674769661 / 100000) (6658031915267 / 12500) := by
  exact
    packedTile32768 532613376 532678912 13 3275 23078 29 _ _ (2009329 / 100000) (502333 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532678912 :
    ThetaLowerSegment 532678912 532744448 (6658031915267 / 12500) (53270847969957 / 100000) := by
  exact
    packedTile32768 532678912 532744448 13 3281 23079 29 _ _ (2009341 / 100000) (62792 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532744448 :
    ThetaLowerSegment 532744448 532809984 (53270847969957 / 100000) (53277424585599 / 100000) := by
  exact
    packedTile32768 532744448 532809984 13 3273 23081 29 _ _ (1004677 / 50000) (2009357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532809984 :
    ThetaLowerSegment 532809984 532875520 (53277424585599 / 100000) (10656799444357 / 20000) := by
  exact
    packedTile32768 532809984 532875520 13 3271 23082 29 _ _ (1004683 / 50000) (2009369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532875520 :
    ThetaLowerSegment 532875520 532941056 (10656799444357 / 20000) (53290481484591 / 100000) := by
  exact
    packedTile32768 532875520 532941056 13 3227 23084 29 _ _ (1004689 / 50000) (2009381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell532941056 :
    ThetaLowerSegment 532941056 533006592 (53290481484591 / 100000) (53297108456109 / 100000) := by
  exact
    packedTile32768 532941056 533006592 13 3298 23085 29 _ _ (2009391 / 100000) (1004697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533006592 :
    ThetaLowerSegment 533006592 533072128 (53297108456109 / 100000) (5330371336377 / 10000) := by
  exact
    packedTile32768 533006592 533072128 13 3287 23086 29 _ _ (2009403 / 100000) (1004703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533072128 :
    ThetaLowerSegment 533072128 533137664 (5330371336377 / 10000) (10662033119067 / 20000) := by
  exact
    packedTile32768 533072128 533137664 13 3211 23088 29 _ _ (401883 / 20000) (1004709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533137664 :
    ThetaLowerSegment 533137664 533203200 (10662033119067 / 20000) (53316750490891 / 100000) := by
  exact
    packedTile32768 533137664 533203200 13 3277 23089 29 _ _ (502357 / 25000) (2009431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533203200 :
    ThetaLowerSegment 533203200 533268736 (53316750490891 / 100000) (53323267104811 / 100000) := by
  exact
    packedTile32768 533203200 533268736 13 3243 23091 29 _ _ (12559 / 625) (2009443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533268736 :
    ThetaLowerSegment 533268736 533334272 (53323267104811 / 100000) (53329918390931 / 100000) := by
  exact
    packedTile32768 533268736 533334272 13 3310 23092 29 _ _ (502363 / 25000) (401891 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533334272 :
    ThetaLowerSegment 533334272 533399808 (53329918390931 / 100000) (10667286212751 / 20000) := by
  exact
    packedTile32768 533334272 533399808 13 3241 23094 29 _ _ (251183 / 12500) (2009467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533399808 :
    ThetaLowerSegment 533399808 533465344 (10667286212751 / 20000) (53343094489487 / 100000) := by
  exact
    packedTile32768 533399808 533465344 13 3316 23095 29 _ _ (2009477 / 100000) (50237 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533465344 :
    ThetaLowerSegment 533465344 533530880 (53343094489487 / 100000) (53349496721441 / 100000) := by
  exact
    packedTile32768 533465344 533530880 13 3186 23096 29 _ _ (2009489 / 100000) (502373 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533530880 :
    ThetaLowerSegment 533530880 533596416 (53349496721441 / 100000) (26678065042121 / 50000) := by
  exact
    packedTile32768 533530880 533596416 13 3301 23098 29 _ _ (2009501 / 100000) (62797 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533596416 :
    ThetaLowerSegment 533596416 533661952 (26678065042121 / 50000) (266813274881 / 500) := by
  exact
    packedTile32768 533596416 533661952 13 3247 23099 29 _ _ (1004757 / 50000) (2009517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533661952 :
    ThetaLowerSegment 533661952 533727488 (266813274881 / 500) (667113065861 / 1250) := by
  exact
    packedTile32768 533661952 533727488 13 3180 23101 29 _ _ (1004763 / 50000) (2009529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533727488 :
    ThetaLowerSegment 533727488 533793024 (667113065861 / 1250) (6671961602573 / 12500) := by
  exact
    packedTile32768 533727488 533793024 13 3308 23102 29 _ _ (1004769 / 50000) (2009541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533793024 :
    ThetaLowerSegment 533793024 533858560 (6671961602573 / 12500) (13345551945421 / 25000) := by
  exact
    packedTile32768 533793024 533858560 13 3242 23103 29 _ _ (40191 / 2000) (2009553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533858560 :
    ThetaLowerSegment 533858560 533924096 (13345551945421 / 25000) (53388760966627 / 100000) := by
  exact
    packedTile32768 533858560 533924096 13 3261 23105 29 _ _ (2009563 / 100000) (1004783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533924096 :
    ThetaLowerSegment 533924096 533989632 (53388760966627 / 100000) (53395396583277 / 100000) := by
  exact
    packedTile32768 533924096 533989632 13 3302 23106 29 _ _ (80383 / 4000) (1004789 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell533989632 :
    ThetaLowerSegment 533989632 534055168 (53395396583277 / 100000) (26700964875307 / 50000) := by
  exact
    packedTile32768 533989632 534055168 13 3251 23108 29 _ _ (2009587 / 100000) (200959 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534055168 :
    ThetaLowerSegment 534055168 534120704 (26700964875307 / 50000) (53408454918567 / 100000) := by
  exact
    packedTile32768 534055168 534120704 13 3247 23109 29 _ _ (2009599 / 100000) (1004801 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534120704 :
    ThetaLowerSegment 534120704 534186240 (53408454918567 / 100000) (53415006253687 / 100000) := by
  exact
    packedTile32768 534120704 534186240 13 3260 23111 29 _ _ (502403 / 25000) (401923 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534186240 :
    ThetaLowerSegment 534186240 534251776 (53415006253687 / 100000) (53421497339207 / 100000) := by
  exact
    packedTile32768 534186240 534251776 13 3230 23112 29 _ _ (251203 / 12500) (2009627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534251776 :
    ThetaLowerSegment 534251776 534317312 (53421497339207 / 100000) (53428062820019 / 100000) := by
  exact
    packedTile32768 534251776 534317312 13 3267 23113 29 _ _ (502409 / 25000) (2009639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534317312 :
    ThetaLowerSegment 534317312 534382848 (53428062820019 / 100000) (53434570063481 / 100000) := by
  exact
    packedTile32768 534317312 534382848 13 3238 23115 29 _ _ (2009649 / 100000) (502413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534382848 :
    ThetaLowerSegment 534382848 534448384 (53434570063481 / 100000) (10688233958041 / 20000) := by
  exact
    packedTile32768 534382848 534448384 13 3284 23116 29 _ _ (2009661 / 100000) (62802 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534448384 :
    ThetaLowerSegment 534448384 534513920 (10688233958041 / 20000) (53447628879227 / 100000) := by
  exact
    packedTile32768 534448384 534513920 13 3214 23118 29 _ _ (2009673 / 100000) (502419 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534513920 :
    ThetaLowerSegment 534513920 534579456 (53447628879227 / 100000) (13363533557393 / 25000) := by
  exact
    packedTile32768 534513920 534579456 13 3237 23119 29 _ _ (401937 / 20000) (251211 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534579456 :
    ThetaLowerSegment 534579456 534644992 (13363533557393 / 25000) (5346074814569 / 10000) := by
  exact
    packedTile32768 534579456 534644992 13 3291 23120 29 _ _ (1004849 / 50000) (2009701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534644992 :
    ThetaLowerSegment 534644992 534710528 (5346074814569 / 10000) (2673367703123 / 5000) := by
  exact
    packedTile32768 534644992 534710528 13 3287 23122 29 _ _ (200971 / 10000) (2009713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534710528 :
    ThetaLowerSegment 534710528 534776064 (2673367703123 / 5000) (26736971970449 / 50000) := by
  exact
    packedTile32768 534710528 534776064 13 3279 23123 29 _ _ (1004861 / 50000) (80389 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534776064 :
    ThetaLowerSegment 534776064 534841600 (26736971970449 / 50000) (26740229749263 / 50000) := by
  exact
    packedTile32768 534776064 534841600 13 3242 23125 29 _ _ (1004867 / 50000) (2009737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534841600 :
    ThetaLowerSegment 534841600 534907136 (26740229749263 / 50000) (53486957010577 / 100000) := by
  exact
    packedTile32768 534841600 534907136 13 3233 23126 29 _ _ (2009747 / 100000) (8039 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534907136 :
    ThetaLowerSegment 534907136 534972672 (53486957010577 / 100000) (13373401825777 / 25000) := by
  exact
    packedTile32768 534907136 534972672 13 3309 23128 29 _ _ (2009759 / 100000) (1004881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell534972672 :
    ThetaLowerSegment 534972672 535038208 (13373401825777 / 25000) (1671881480971 / 3125) := by
  exact
    packedTile32768 534972672 535038208 13 3284 23129 29 _ _ (2009771 / 100000) (1004887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535038208 :
    ThetaLowerSegment 535038208 535103744 (1671881480971 / 3125) (53506893939113 / 100000) := by
  exact
    packedTile32768 535038208 535103744 13 3327 23130 29 _ _ (2009783 / 100000) (1004893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535103744 :
    ThetaLowerSegment 535103744 535169280 (53506893939113 / 100000) (53513494109177 / 100000) := by
  exact
    packedTile32768 535103744 535169280 13 3284 23132 29 _ _ (502449 / 25000) (2009799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535169280 :
    ThetaLowerSegment 535169280 535234816 (53513494109177 / 100000) (53520166671737 / 100000) := by
  exact
    packedTile32768 535169280 535234816 13 3320 23133 29 _ _ (125613 / 6250) (2009811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535234816 :
    ThetaLowerSegment 535234816 535300352 (53520166671737 / 100000) (53526684517997 / 100000) := by
  exact
    packedTile32768 535234816 535300352 13 3243 23135 29 _ _ (100491 / 5000) (2009823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535300352 :
    ThetaLowerSegment 535300352 535365888 (53526684517997 / 100000) (53533377258557 / 100000) := by
  exact
    packedTile32768 535300352 535365888 13 3330 23136 29 _ _ (251229 / 12500) (401967 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535365888 :
    ThetaLowerSegment 535365888 535431424 (53533377258557 / 100000) (6692487903159 / 12500) := by
  exact
    packedTile32768 535365888 535431424 13 3247 23137 29 _ _ (401969 / 20000) (251231 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535431424 :
    ThetaLowerSegment 535431424 535496960 (6692487903159 / 12500) (53546517664659 / 100000) := by
  exact
    packedTile32768 535431424 535496960 13 3291 23139 29 _ _ (2009857 / 100000) (100493 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535496960 :
    ThetaLowerSegment 535496960 535562496 (53546517664659 / 100000) (267765640619 / 500) := by
  exact
    packedTile32768 535496960 535562496 13 3289 23140 29 _ _ (2009869 / 100000) (125617 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535562496 :
    ThetaLowerSegment 535562496 535628032 (267765640619 / 500) (53559694405027 / 100000) := by
  exact
    packedTile32768 535562496 535628032 13 3267 23142 29 _ _ (2009881 / 100000) (502471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535628032 :
    ThetaLowerSegment 535628032 535693568 (53559694405027 / 100000) (53566071798689 / 100000) := by
  exact
    packedTile32768 535628032 535693568 13 3173 23143 29 _ _ (1004947 / 50000) (2009897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535693568 :
    ThetaLowerSegment 535693568 535759104 (53566071798689 / 100000) (53572461289863 / 100000) := by
  exact
    packedTile32768 535693568 535759104 13 3179 23145 29 _ _ (1004953 / 50000) (2009909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535759104 :
    ThetaLowerSegment 535759104 535824640 (53572461289863 / 100000) (53579005582871 / 100000) := by
  exact
    packedTile32768 535759104 535824640 13 3256 23146 29 _ _ (1004959 / 50000) (2009921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535824640 :
    ThetaLowerSegment 535824640 535890176 (53579005582871 / 100000) (53585463487961 / 100000) := by
  exact
    packedTile32768 535824640 535890176 13 3213 23147 29 _ _ (200993 / 10000) (2009933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535890176 :
    ThetaLowerSegment 535890176 535955712 (53585463487961 / 100000) (53592108356213 / 100000) := by
  exact
    packedTile32768 535890176 535955712 13 3306 23149 29 _ _ (1004971 / 50000) (401989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell535955712 :
    ThetaLowerSegment 535955712 536021248 (53592108356213 / 100000) (13399685804417 / 25000) := by
  exact
    packedTile32768 535955712 536021248 13 3301 23150 29 _ _ (401991 / 20000) (1004979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536021248 :
    ThetaLowerSegment 536021248 536086784 (13399685804417 / 25000) (26802637805209 / 50000) := by
  exact
    packedTile32768 536021248 536086784 13 3250 23152 29 _ _ (2009967 / 100000) (200997 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536086784 :
    ThetaLowerSegment 536086784 536152320 (26802637805209 / 50000) (53611910551097 / 100000) := by
  exact
    packedTile32768 536086784 536152320 13 3301 23153 29 _ _ (2009979 / 100000) (1004991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536152320 :
    ThetaLowerSegment 536152320 536217856 (53611910551097 / 100000) (10723687800373 / 20000) := by
  exact
    packedTile32768 536152320 536217856 13 3248 23154 29 _ _ (2009991 / 100000) (1004997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536217856 :
    ThetaLowerSegment 536217856 536283392 (10723687800373 / 20000) (53624993624909 / 100000) := by
  exact
    packedTile32768 536217856 536283392 13 3261 23156 29 _ _ (502501 / 25000) (2010007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536283392 :
    ThetaLowerSegment 536283392 536348928 (53624993624909 / 100000) (53631680948141 / 100000) := by
  exact
    packedTile32768 536283392 536348928 13 3327 23157 29 _ _ (62813 / 3125) (2010019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536348928 :
    ThetaLowerSegment 536348928 536414464 (53631680948141 / 100000) (53638157258357 / 100000) := by
  exact
    packedTile32768 536348928 536414464 13 3222 23159 29 _ _ (502507 / 25000) (2010031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536414464 :
    ThetaLowerSegment 536414464 536480000 (53638157258357 / 100000) (53644808480717 / 100000) := by
  exact
    packedTile32768 536414464 536480000 13 3309 23160 29 _ _ (50251 / 2500) (2010043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536480000 :
    ThetaLowerSegment 536480000 536545536 (53644808480717 / 100000) (53651341149717 / 100000) := by
  exact
    packedTile32768 536480000 536545536 13 3250 23162 29 _ _ (502513 / 25000) (402011 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536545536 :
    ThetaLowerSegment 536545536 536611072 (53651341149717 / 100000) (13414466957693 / 25000) := by
  exact
    packedTile32768 536545536 536611072 13 3247 23163 29 _ _ (402013 / 20000) (502517 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536611072 :
    ThetaLowerSegment 536611072 536676608 (13414466957693 / 25000) (26832208330819 / 50000) := by
  exact
    packedTile32768 536611072 536676608 13 3258 23164 29 _ _ (2010077 / 100000) (12563 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536676608 :
    ThetaLowerSegment 536676608 536742144 (26832208330819 / 50000) (13417755453523 / 25000) := by
  exact
    packedTile32768 536676608 536742144 13 3286 23166 29 _ _ (2010089 / 100000) (502523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536742144 :
    ThetaLowerSegment 536742144 536807680 (13417755453523 / 25000) (5367749031911 / 10000) := by
  exact
    packedTile32768 536742144 536807680 13 3218 23167 29 _ _ (2010101 / 100000) (251263 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536807680 :
    ThetaLowerSegment 536807680 536873216 (5367749031911 / 10000) (26842049786971 / 50000) := by
  exact
    packedTile32768 536807680 536873216 13 3288 23169 29 _ _ (1005057 / 50000) (2010117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536873216 :
    ThetaLowerSegment 536873216 536938752 (26842049786971 / 50000) (26845350413863 / 50000) := by
  exact
    packedTile32768 536873216 536938752 13 3284 23170 29 _ _ (1005063 / 50000) (2010129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell536938752 :
    ThetaLowerSegment 536938752 537004288 (26845350413863 / 50000) (5369706894491 / 10000) := by
  exact
    packedTile32768 536938752 537004288 13 3168 23171 29 _ _ (1005069 / 50000) (2010141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537004288 :
    ThetaLowerSegment 537004288 537069824 (5369706894491 / 10000) (2685183212353 / 5000) := by
  exact
    packedTile32768 537004288 537069824 13 3281 23173 29 _ _ (40203 / 2000) (2010153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537069824 :
    ThetaLowerSegment 537069824 537135360 (2685183212353 / 5000) (13427568414929 / 25000) := by
  exact
    packedTile32768 537069824 537135360 13 3288 23174 29 _ _ (1005081 / 50000) (402033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537135360 :
    ThetaLowerSegment 537135360 537200896 (13427568414929 / 25000) (53716800697941 / 100000) := by
  exact
    packedTile32768 537135360 537200896 13 3247 23176 29 _ _ (80407 / 4000) (1005089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537200896 :
    ThetaLowerSegment 537200896 537266432 (53716800697941 / 100000) (10744671585587 / 20000) := by
  exact
    packedTile32768 537200896 537266432 13 3262 23177 29 _ _ (2010187 / 100000) (201019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537266432 :
    ThetaLowerSegment 537266432 537331968 (10744671585587 / 20000) (26865012879009 / 50000) := by
  exact
    packedTile32768 537266432 537331968 13 3317 23179 29 _ _ (2010199 / 100000) (1005101 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537331968 :
    ThetaLowerSegment 537331968 537397504 (26865012879009 / 50000) (1343411561341 / 2500) := by
  exact
    packedTile32768 537331968 537397504 13 3202 23180 29 _ _ (2010211 / 100000) (1005107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537397504 :
    ThetaLowerSegment 537397504 537463040 (1343411561341 / 2500) (3358929942841 / 6250) := by
  exact
    packedTile32768 537397504 537463040 13 3192 23181 29 _ _ (2010223 / 100000) (1005113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537463040 :
    ThetaLowerSegment 537463040 537528576 (3358929942841 / 6250) (13437365652089 / 25000) := by
  exact
    packedTile32768 537463040 537528576 13 3275 23183 29 _ _ (502559 / 25000) (2010239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537528576 :
    ThetaLowerSegment 537528576 537594112 (13437365652089 / 25000) (13438991440159 / 25000) := by
  exact
    packedTile32768 537528576 537594112 13 3235 23184 29 _ _ (251281 / 12500) (2010251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537594112 :
    ThetaLowerSegment 537594112 537659648 (13438991440159 / 25000) (1680081803468 / 3125) := by
  exact
    packedTile32768 537594112 537659648 13 3309 23186 29 _ _ (100513 / 5000) (2010263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537659648 :
    ThetaLowerSegment 537659648 537725184 (1680081803468 / 3125) (1680286223002 / 3125) := by
  exact
    packedTile32768 537659648 537725184 13 3254 23187 29 _ _ (62821 / 3125) (80411 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537725184 :
    ThetaLowerSegment 537725184 537790720 (1680286223002 / 3125) (6721963580167 / 12500) := by
  exact
    packedTile32768 537725184 537790720 13 3258 23188 29 _ _ (502571 / 25000) (2010287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537790720 :
    ThetaLowerSegment 537790720 537856256 (6721963580167 / 12500) (13445585655359 / 25000) := by
  exact
    packedTile32768 537790720 537856256 13 3300 23190 29 _ _ (2010297 / 100000) (20103 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537856256 :
    ThetaLowerSegment 537856256 537921792 (13445585655359 / 25000) (5378902890917 / 10000) := by
  exact
    packedTile32768 537856256 537921792 13 3326 23191 29 _ _ (2010309 / 100000) (251289 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537921792 :
    ThetaLowerSegment 537921792 537987328 (5378902890917 / 10000) (13448874530537 / 25000) := by
  exact
    packedTile32768 537921792 537987328 13 3218 23193 29 _ _ (2010321 / 100000) (502581 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell537987328 :
    ThetaLowerSegment 537987328 538052864 (13448874530537 / 25000) (1345052501393 / 2500) := by
  exact
    packedTile32768 537987328 538052864 13 3284 23194 29 _ _ (2010333 / 100000) (62823 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538052864 :
    ThetaLowerSegment 538052864 538118400 (1345052501393 / 2500) (1076172834367 / 2000) := by
  exact
    packedTile32768 538052864 538118400 13 3254 23195 29 _ _ (402069 / 20000) (502587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538118400 :
    ThetaLowerSegment 538118400 538183936 (1076172834367 / 2000) (10763033065363 / 20000) := by
  exact
    packedTile32768 538118400 538183936 13 3245 23197 29 _ _ (2010357 / 100000) (50259 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538183936 :
    ThetaLowerSegment 538183936 538249472 (10763033065363 / 20000) (2152870212787 / 4000) := by
  exact
    packedTile32768 538183936 538249472 13 3278 23198 29 _ _ (201037 / 10000) (2010373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538249472 :
    ThetaLowerSegment 538249472 538315008 (2152870212787 / 4000) (10765673895291 / 20000) := by
  exact
    packedTile32768 538249472 538315008 13 3290 23200 29 _ _ (1005191 / 50000) (402077 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538315008 :
    ThetaLowerSegment 538315008 538380544 (10765673895291 / 20000) (53834796706073 / 100000) := by
  exact
    packedTile32768 538315008 538380544 13 3197 23201 29 _ _ (1005197 / 50000) (2010397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538380544 :
    ThetaLowerSegment 538380544 538446080 (53834796706073 / 100000) (53841248098927 / 100000) := by
  exact
    packedTile32768 538380544 538446080 13 3209 23203 29 _ _ (1005203 / 50000) (2010409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538446080 :
    ThetaLowerSegment 538446080 538511616 (53841248098927 / 100000) (53847785978263 / 100000) := by
  exact
    packedTile32768 538446080 538511616 13 3252 23204 29 _ _ (1005209 / 50000) (2010421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538511616 :
    ThetaLowerSegment 538511616 538577152 (53847785978263 / 100000) (53854301781893 / 100000) := by
  exact
    packedTile32768 538511616 538577152 13 3241 23205 29 _ _ (201043 / 10000) (2010433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538577152 :
    ThetaLowerSegment 538577152 538642688 (53854301781893 / 100000) (13465246626217 / 25000) := by
  exact
    packedTile32768 538577152 538642688 13 3325 23207 29 _ _ (2010443 / 100000) (1005223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538642688 :
    ThetaLowerSegment 538642688 538708224 (13465246626217 / 25000) (6733446594431 / 12500) := by
  exact
    packedTile32768 538642688 538708224 13 3276 23208 29 _ _ (402091 / 20000) (1005229 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538708224 :
    ThetaLowerSegment 538708224 538773760 (6733446594431 / 12500) (3367134437717 / 6250) := by
  exact
    packedTile32768 538708224 538773760 13 3272 23210 29 _ _ (2010467 / 100000) (201047 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538773760 :
    ThetaLowerSegment 538773760 538839296 (3367134437717 / 6250) (10776111680009 / 20000) := by
  exact
    packedTile32768 538773760 538839296 13 3187 23211 29 _ _ (2010479 / 100000) (1005241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538839296 :
    ThetaLowerSegment 538839296 538904832 (10776111680009 / 20000) (53887201062309 / 100000) := by
  exact
    packedTile32768 538839296 538904832 13 3304 23212 29 _ _ (2010491 / 100000) (1005247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538904832 :
    ThetaLowerSegment 538904832 538970368 (53887201062309 / 100000) (53893626629897 / 100000) := by
  exact
    packedTile32768 538904832 538970368 13 3196 23214 29 _ _ (2010503 / 100000) (1005253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell538970368 :
    ThetaLowerSegment 538970368 539035904 (53893626629897 / 100000) (2156007075641 / 4000) := by
  exact
    packedTile32768 538970368 539035904 13 3258 23215 29 _ _ (502629 / 25000) (2010519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539035904 :
    ThetaLowerSegment 539035904 539101440 (2156007075641 / 4000) (53906674917521 / 100000) := by
  exact
    packedTile32768 539035904 539101440 13 3232 23217 29 _ _ (62829 / 3125) (2010531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539101440 :
    ThetaLowerSegment 539101440 539166976 (53906674917521 / 100000) (53913315731141 / 100000) := by
  exact
    packedTile32768 539101440 539166976 13 3303 23218 29 _ _ (100527 / 5000) (2010543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539166976 :
    ThetaLowerSegment 539166976 539232512 (53913315731141 / 100000) (10783994935873 / 20000) := by
  exact
    packedTile32768 539166976 539232512 13 3312 23219 29 _ _ (251319 / 12500) (402111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539232512 :
    ThetaLowerSegment 539232512 539298048 (10783994935873 / 20000) (53926607530001 / 100000) := by
  exact
    packedTile32768 539232512 539298048 13 3299 23221 29 _ _ (502641 / 25000) (2010567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539298048 :
    ThetaLowerSegment 539298048 539363584 (53926607530001 / 100000) (53933194176977 / 100000) := by
  exact
    packedTile32768 539298048 539363584 13 3276 23222 29 _ _ (125661 / 6250) (2010579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539363584 :
    ThetaLowerSegment 539363584 539429120 (53933194176977 / 100000) (53939780866541 / 100000) := by
  exact
    packedTile32768 539363584 539429120 13 3276 23224 29 _ _ (2010589 / 100000) (62831 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539429120 :
    ThetaLowerSegment 539429120 539494656 (53939780866541 / 100000) (26973164696999 / 50000) := by
  exact
    packedTile32768 539429120 539494656 13 3257 23225 29 _ _ (2010601 / 100000) (502651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539494656 :
    ThetaLowerSegment 539494656 539560192 (26973164696999 / 50000) (431622573307 / 800) := by
  exact
    packedTile32768 539494656 539560192 13 3229 23227 29 _ _ (2010613 / 100000) (251327 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539560192 :
    ThetaLowerSegment 539560192 539625728 (431622573307 / 800) (431675911167 / 800) := by
  exact
    packedTile32768 539560192 539625728 13 3316 23228 29 _ _ (3217 / 160) (502657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539625728 :
    ThetaLowerSegment 539625728 539691264 (431675911167 / 800) (13491519438331 / 25000) := by
  exact
    packedTile32768 539625728 539691264 13 3277 23229 29 _ _ (2010637 / 100000) (25133 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539691264 :
    ThetaLowerSegment 539691264 539756800 (13491519438331 / 25000) (13493148064021 / 25000) := by
  exact
    packedTile32768 539691264 539756800 13 3240 23231 29 _ _ (2010649 / 100000) (502663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539756800 :
    ThetaLowerSegment 539756800 539822336 (13493148064021 / 25000) (53979112829707 / 100000) := by
  exact
    packedTile32768 539756800 539822336 13 3243 23232 29 _ _ (2010661 / 100000) (251333 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539822336 :
    ThetaLowerSegment 539822336 539887872 (53979112829707 / 100000) (10797120254941 / 20000) := by
  exact
    packedTile32768 539822336 539887872 13 3227 23234 29 _ _ (1005337 / 50000) (2010677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539887872 :
    ThetaLowerSegment 539887872 539953408 (10797120254941 / 20000) (10798429211527 / 20000) := by
  exact
    packedTile32768 539887872 539953408 13 3255 23235 29 _ _ (1005343 / 50000) (2010689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell539953408 :
    ThetaLowerSegment 539953408 540018944 (10798429211527 / 20000) (10799716058247 / 20000) := by
  exact
    packedTile32768 539953408 540018944 13 3200 23236 29 _ _ (1005349 / 50000) (2010701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540018944 :
    ThetaLowerSegment 540018944 540084480 (10799716058247 / 20000) (10801035486149 / 20000) := by
  exact
    packedTile32768 540018944 540084480 13 3281 23238 29 _ _ (201071 / 10000) (2010713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540084480 :
    ThetaLowerSegment 540084480 540150016 (10801035486149 / 20000) (54011744448797 / 100000) := by
  exact
    packedTile32768 540084480 540150016 13 3266 23239 29 _ _ (1005361 / 50000) (80429 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540150016 :
    ThetaLowerSegment 540150016 540215552 (54011744448797 / 100000) (54018184829799 / 100000) := by
  exact
    packedTile32768 540150016 540215552 13 3203 23241 29 _ _ (1005367 / 50000) (2010737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540215552 :
    ThetaLowerSegment 540215552 540281088 (54018184829799 / 100000) (10804948374501 / 20000) := by
  exact
    packedTile32768 540215552 540281088 13 3261 23242 29 _ _ (1005373 / 50000) (2010749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540281088 :
    ThetaLowerSegment 540281088 540346624 (10804948374501 / 20000) (54031313032917 / 100000) := by
  exact
    packedTile32768 540281088 540346624 13 3268 23243 29 _ _ (2010759 / 100000) (1005381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540346624 :
    ThetaLowerSegment 540346624 540412160 (54031313032917 / 100000) (54037815866331 / 100000) := by
  exact
    packedTile32768 540346624 540412160 13 3234 23245 29 _ _ (2010771 / 100000) (1005387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540412160 :
    ThetaLowerSegment 540412160 540477696 (54037815866331 / 100000) (13511122413777 / 25000) := by
  exact
    packedTile32768 540412160 540477696 13 3319 23246 29 _ _ (2010783 / 100000) (1005393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540477696 :
    ThetaLowerSegment 540477696 540543232 (13511122413777 / 25000) (54051030771243 / 100000) := by
  exact
    packedTile32768 540477696 540543232 13 3253 23248 29 _ _ (402159 / 20000) (1005399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540543232 :
    ThetaLowerSegment 540543232 540608768 (54051030771243 / 100000) (27028802049663 / 50000) := by
  exact
    packedTile32768 540543232 540608768 13 3269 23249 29 _ _ (2010807 / 100000) (201081 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540608768 :
    ThetaLowerSegment 540608768 540674304 (27028802049663 / 50000) (54064278007587 / 100000) := by
  exact
    packedTile32768 540608768 540674304 13 3319 23250 29 _ _ (2010819 / 100000) (1005411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540674304 :
    ThetaLowerSegment 540674304 540739840 (54064278007587 / 100000) (2703541967457 / 5000) := by
  exact
    packedTile32768 540674304 540739840 13 3263 23252 29 _ _ (2010831 / 100000) (1005417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540739840 :
    ThetaLowerSegment 540739840 540805376 (2703541967457 / 5000) (2163094581387 / 4000) := by
  exact
    packedTile32768 540739840 540805376 13 3245 23253 29 _ _ (2010843 / 100000) (1005423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540805376 :
    ThetaLowerSegment 540805376 540870912 (2163094581387 / 4000) (54083891773251 / 100000) := by
  exact
    packedTile32768 540805376 540870912 13 3246 23255 29 _ _ (251357 / 12500) (2010859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540870912 :
    ThetaLowerSegment 540870912 540936448 (54083891773251 / 100000) (54090398942099 / 100000) := by
  exact
    packedTile32768 540870912 540936448 13 3236 23256 29 _ _ (502717 / 25000) (2010871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell540936448 :
    ThetaLowerSegment 540936448 541001984 (54090398942099 / 100000) (54096970497939 / 100000) := by
  exact
    packedTile32768 540936448 541001984 13 3268 23258 29 _ _ (12568 / 625) (2010883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541001984 :
    ThetaLowerSegment 541001984 541067520 (54096970497939 / 100000) (54103554158347 / 100000) := by
  exact
    packedTile32768 541001984 541067520 13 3274 23259 29 _ _ (502723 / 25000) (402179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541067520 :
    ThetaLowerSegment 541067520 541133056 (54103554158347 / 100000) (54110097639963 / 100000) := by
  exact
    packedTile32768 541067520 541133056 13 3254 23260 29 _ _ (251363 / 12500) (2010907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541133056 :
    ThetaLowerSegment 541133056 541198592 (54110097639963 / 100000) (54116639149711 / 100000) := by
  exact
    packedTile32768 541133056 541198592 13 3253 23262 29 _ _ (502729 / 25000) (2010919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541198592 :
    ThetaLowerSegment 541198592 541264128 (54116639149711 / 100000) (54123275212111 / 100000) := by
  exact
    packedTile32768 541198592 541264128 13 3300 23263 29 _ _ (125683 / 6250) (2010931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541264128 :
    ThetaLowerSegment 541264128 541329664 (54123275212111 / 100000) (54129712231051 / 100000) := by
  exact
    packedTile32768 541264128 541329664 13 3201 23265 29 _ _ (100547 / 5000) (2010943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541329664 :
    ThetaLowerSegment 541329664 541395200 (54129712231051 / 100000) (54136370493123 / 100000) := by
  exact
    packedTile32768 541329664 541395200 13 3311 23266 29 _ _ (251369 / 12500) (402191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541395200 :
    ThetaLowerSegment 541395200 541460736 (54136370493123 / 100000) (27071385697359 / 50000) := by
  exact
    packedTile32768 541395200 541460736 13 3183 23267 29 _ _ (402193 / 20000) (251371 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541460736 :
    ThetaLowerSegment 541460736 541526272 (27071385697359 / 50000) (10829865838143 / 20000) := by
  exact
    packedTile32768 541460736 541526272 13 3261 23269 29 _ _ (2010977 / 100000) (100549 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541526272 :
    ThetaLowerSegment 541526272 541591808 (10829865838143 / 20000) (54155872948921 / 100000) := by
  exact
    packedTile32768 541526272 541591808 13 3254 23270 29 _ _ (2010989 / 100000) (125687 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541591808 :
    ThetaLowerSegment 541591808 541657344 (54155872948921 / 100000) (3385146144821 / 6250) := by
  exact
    packedTile32768 541591808 541657344 13 3215 23272 29 _ _ (2011001 / 100000) (502751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541657344 :
    ThetaLowerSegment 541657344 541722880 (3385146144821 / 6250) (54168948516867 / 100000) := by
  exact
    packedTile32768 541657344 541722880 13 3287 23273 29 _ _ (2011013 / 100000) (251377 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541722880 :
    ThetaLowerSegment 541722880 541788416 (54168948516867 / 100000) (54175480326067 / 100000) := by
  exact
    packedTile32768 541722880 541788416 13 3248 23274 29 _ _ (80441 / 4000) (502757 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541788416 :
    ThetaLowerSegment 541788416 541853952 (54175480326067 / 100000) (54182012174243 / 100000) := by
  exact
    packedTile32768 541788416 541853952 13 3248 23276 29 _ _ (2011037 / 100000) (12569 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541853952 :
    ThetaLowerSegment 541853952 541919488 (54182012174243 / 100000) (10837704790181 / 20000) := by
  exact
    packedTile32768 541853952 541919488 13 3238 23277 29 _ _ (2011049 / 100000) (502763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541919488 :
    ThetaLowerSegment 541919488 541985024 (10837704790181 / 20000) (54195132297351 / 100000) := by
  exact
    packedTile32768 541919488 541985024 13 3286 23279 29 _ _ (2011061 / 100000) (251383 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell541985024 :
    ThetaLowerSegment 541985024 542050560 (54195132297351 / 100000) (2710083715891 / 5000) := by
  exact
    packedTile32768 541985024 542050560 13 3253 23280 29 _ _ (2011073 / 100000) (502769 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542050560 :
    ThetaLowerSegment 542050560 542116096 (2710083715891 / 5000) (10841629600087 / 20000) := by
  exact
    packedTile32768 542050560 542116096 13 3219 23281 29 _ _ (402217 / 20000) (125693 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542116096 :
    ThetaLowerSegment 542116096 542181632 (10841629600087 / 20000) (54214712224307 / 100000) := by
  exact
    packedTile32768 542116096 542181632 13 3264 23283 29 _ _ (1005549 / 50000) (2011101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542181632 :
    ThetaLowerSegment 542181632 542247168 (54214712224307 / 100000) (54221286542897 / 100000) := by
  exact
    packedTile32768 542181632 542247168 13 3269 23284 29 _ _ (201111 / 10000) (2011113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542247168 :
    ThetaLowerSegment 542247168 542312704 (54221286542897 / 100000) (10845546035557 / 20000) := by
  exact
    packedTile32768 542247168 542312704 13 3204 23286 29 _ _ (1005561 / 50000) (16089 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542312704 :
    ThetaLowerSegment 542312704 542378240 (10845546035557 / 20000) (54234364908851 / 100000) := by
  exact
    packedTile32768 542312704 542378240 13 3299 23287 29 _ _ (1005567 / 50000) (2011137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542378240 :
    ThetaLowerSegment 542378240 542443776 (54234364908851 / 100000) (54240971523461 / 100000) := by
  exact
    packedTile32768 542378240 542443776 13 3285 23289 29 _ _ (1005573 / 50000) (2011149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542443776 :
    ThetaLowerSegment 542443776 542509312 (54240971523461 / 100000) (54247511809277 / 100000) := by
  exact
    packedTile32768 542443776 542509312 13 3252 23290 29 _ _ (1005579 / 50000) (2011161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542509312 :
    ThetaLowerSegment 542509312 542574848 (54247511809277 / 100000) (54253971687317 / 100000) := by
  exact
    packedTile32768 542509312 542574848 13 3212 23291 29 _ _ (201117 / 10000) (2011173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542574848 :
    ThetaLowerSegment 542574848 542640384 (54253971687317 / 100000) (54260443670993 / 100000) := by
  exact
    packedTile32768 542574848 542640384 13 3218 23293 29 _ _ (1005591 / 50000) (402237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542640384 :
    ThetaLowerSegment 542640384 542705920 (54260443670993 / 100000) (54267040387313 / 100000) := by
  exact
    packedTile32768 542640384 542705920 13 3280 23294 29 _ _ (1005597 / 50000) (2011197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542705920 :
    ThetaLowerSegment 542705920 542771456 (54267040387313 / 100000) (54273552672341 / 100000) := by
  exact
    packedTile32768 542705920 542771456 13 3238 23296 29 _ _ (1005603 / 50000) (2011209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542771456 :
    ThetaLowerSegment 542771456 542836992 (54273552672341 / 100000) (54280137400073 / 100000) := by
  exact
    packedTile32768 542771456 542836992 13 3274 23297 29 _ _ (1005609 / 50000) (2011221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542836992 :
    ThetaLowerSegment 542836992 542902528 (54280137400073 / 100000) (54286653785273 / 100000) := by
  exact
    packedTile32768 542836992 542902528 13 3240 23298 29 _ _ (201123 / 10000) (2011233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542902528 :
    ThetaLowerSegment 542902528 542968064 (54286653785273 / 100000) (10858659786429 / 20000) := by
  exact
    packedTile32768 542902528 542968064 13 3304 23300 29 _ _ (2011243 / 100000) (1005623 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell542968064 :
    ThetaLowerSegment 542968064 543033600 (10858659786429 / 20000) (678746510867 / 1250) := by
  exact
    packedTile32768 542968064 543033600 13 3193 23301 29 _ _ (402251 / 20000) (1005629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543033600 :
    ThetaLowerSegment 543033600 543099136 (678746510867 / 1250) (6788283694339 / 12500) := by
  exact
    packedTile32768 543033600 543099136 13 3256 23303 29 _ _ (2011267 / 100000) (201127 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543099136 :
    ThetaLowerSegment 543099136 543164672 (6788283694339 / 12500) (54312876606227 / 100000) := by
  exact
    packedTile32768 543099136 543164672 13 3285 23304 29 _ _ (2011279 / 100000) (1005641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543164672 :
    ThetaLowerSegment 543164672 543230208 (54312876606227 / 100000) (54319260443861 / 100000) := by
  exact
    packedTile32768 543164672 543230208 13 3174 23305 29 _ _ (2011291 / 100000) (1005647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543230208 :
    ThetaLowerSegment 543230208 543295744 (54319260443861 / 100000) (1697679841914 / 3125) := by
  exact
    packedTile32768 543230208 543295744 13 3229 23307 29 _ _ (2011303 / 100000) (1005653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543295744 :
    ThetaLowerSegment 543295744 543361280 (1697679841914 / 3125) (6791541995491 / 12500) := by
  exact
    packedTile32768 543295744 543361280 13 3272 23308 29 _ _ (402263 / 20000) (1005659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543361280 :
    ThetaLowerSegment 543361280 543426816 (6791541995491 / 12500) (27169440410993 / 50000) := by
  exact
    packedTile32768 543361280 543426816 13 3254 23310 29 _ _ (2011327 / 100000) (201133 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543426816 :
    ThetaLowerSegment 543426816 543492352 (27169440410993 / 50000) (27172698780173 / 50000) := by
  exact
    packedTile32768 543426816 543492352 13 3240 23311 29 _ _ (2011339 / 100000) (1005671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543492352 :
    ThetaLowerSegment 543492352 543557888 (27172698780173 / 50000) (54352069211613 / 100000) := by
  exact
    packedTile32768 543492352 543557888 13 3317 23312 29 _ _ (2011351 / 100000) (1005677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543557888 :
    ThetaLowerSegment 543557888 543623424 (54352069211613 / 100000) (10871706746459 / 20000) := by
  exact
    packedTile32768 543557888 543623424 13 3214 23314 29 _ _ (2011363 / 100000) (1005683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543623424 :
    ThetaLowerSegment 543623424 543688960 (10871706746459 / 20000) (339782157012 / 625) := by
  exact
    packedTile32768 543623424 543688960 13 3287 23315 29 _ _ (16091 / 800) (1005689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543688960 :
    ThetaLowerSegment 543688960 543754496 (339782157012 / 625) (6796441660879 / 12500) := by
  exact
    packedTile32768 543688960 543754496 13 3176 23317 29 _ _ (2011387 / 100000) (201139 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543754496 :
    ThetaLowerSegment 543754496 543820032 (6796441660879 / 12500) (54378092459171 / 100000) := by
  exact
    packedTile32768 543754496 543820032 13 3261 23318 29 _ _ (2011399 / 100000) (1005701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543820032 :
    ThetaLowerSegment 543820032 543885568 (54378092459171 / 100000) (54384665750319 / 100000) := by
  exact
    packedTile32768 543820032 543885568 13 3268 23319 29 _ _ (2011411 / 100000) (1005707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543885568 :
    ThetaLowerSegment 543885568 543951104 (54384665750319 / 100000) (27195612500361 / 50000) := by
  exact
    packedTile32768 543885568 543951104 13 3261 23321 29 _ _ (2011423 / 100000) (1005713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell543951104 :
    ThetaLowerSegment 543951104 544016640 (27195612500361 / 50000) (54397804404607 / 100000) := by
  exact
    packedTile32768 543951104 544016640 13 3271 23322 29 _ _ (402287 / 20000) (1005719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544016640 :
    ThetaLowerSegment 544016640 544082176 (54397804404607 / 100000) (2176176963199 / 4000) := by
  exact
    packedTile32768 544016640 544082176 13 3291 23324 29 _ _ (251431 / 12500) (2011451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544082176 :
    ThetaLowerSegment 544082176 544147712 (2176176963199 / 4000) (10882183012279 / 20000) := by
  exact
    packedTile32768 544082176 544147712 13 3227 23325 29 _ _ (100573 / 5000) (2011463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544147712 :
    ThetaLowerSegment 544147712 544213248 (10882183012279 / 20000) (54417558953411 / 100000) := by
  exact
    packedTile32768 544147712 544213248 13 3303 23326 29 _ _ (125717 / 6250) (80459 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544213248 :
    ThetaLowerSegment 544213248 544278784 (54417558953411 / 100000) (54424023862987 / 100000) := by
  exact
    packedTile32768 544213248 544278784 13 3214 23328 29 _ _ (502871 / 25000) (2011487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544278784 :
    ThetaLowerSegment 544278784 544344320 (54424023862987 / 100000) (54430551167507 / 100000) := by
  exact
    packedTile32768 544278784 544344320 13 3245 23329 29 _ _ (251437 / 12500) (2011499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544344320 :
    ThetaLowerSegment 544344320 544409856 (54430551167507 / 100000) (54436971901043 / 100000) := by
  exact
    packedTile32768 544344320 544409856 13 3192 23331 29 _ _ (502877 / 25000) (2011511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544409856 :
    ThetaLowerSegment 544409856 544475392 (54436971901043 / 100000) (54443589801843 / 100000) := by
  exact
    packedTile32768 544409856 544475392 13 3290 23332 29 _ _ (12572 / 625) (2011523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544475392 :
    ThetaLowerSegment 544475392 544540928 (54443589801843 / 100000) (54450091073267 / 100000) := by
  exact
    packedTile32768 544475392 544540928 13 3232 23333 29 _ _ (502883 / 25000) (402307 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544540928 :
    ThetaLowerSegment 544540928 544606464 (54450091073267 / 100000) (10891324511327 / 20000) := by
  exact
    packedTile32768 544540928 544606464 13 3247 23335 29 _ _ (251443 / 12500) (2011547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544606464 :
    ThetaLowerSegment 544606464 544672000 (10891324511327 / 20000) (10892646103619 / 20000) := by
  exact
    packedTile32768 544606464 544672000 13 3285 23336 29 _ _ (502889 / 25000) (2011559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544672000 :
    ThetaLowerSegment 544672000 544737536 (10892646103619 / 20000) (54469766102527 / 100000) := by
  exact
    packedTile32768 544672000 544737536 13 3249 23338 29 _ _ (125723 / 6250) (2011571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544737536 :
    ThetaLowerSegment 544737536 544803072 (54469766102527 / 100000) (54476390235467 / 100000) := by
  exact
    packedTile32768 544737536 544803072 13 3293 23339 29 _ _ (100579 / 5000) (2011583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544803072 :
    ThetaLowerSegment 544803072 544868608 (54476390235467 / 100000) (54482937967427 / 100000) := by
  exact
    packedTile32768 544803072 544868608 13 3255 23341 29 _ _ (251449 / 12500) (402319 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544868608 :
    ThetaLowerSegment 544868608 544934144 (54482937967427 / 100000) (54489493784863 / 100000) := by
  exact
    packedTile32768 544868608 544934144 13 3259 23342 29 _ _ (502901 / 25000) (2011607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544934144 :
    ThetaLowerSegment 544934144 544999680 (54489493784863 / 100000) (54496013432319 / 100000) := by
  exact
    packedTile32768 544934144 544999680 13 3241 23343 29 _ _ (62863 / 3125) (2011619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell544999680 :
    ThetaLowerSegment 544999680 545065216 (54496013432319 / 100000) (54502627665183 / 100000) := by
  exact
    packedTile32768 544999680 545065216 13 3288 23345 29 _ _ (502907 / 25000) (2011631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545065216 :
    ThetaLowerSegment 545065216 545130752 (54502627665183 / 100000) (54509235902583 / 100000) := by
  exact
    packedTile32768 545065216 545130752 13 3285 23346 29 _ _ (50291 / 2500) (2011643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545130752 :
    ThetaLowerSegment 545130752 545196288 (54509235902583 / 100000) (54515789864799 / 100000) := by
  exact
    packedTile32768 545130752 545196288 13 3258 23348 29 _ _ (502913 / 25000) (402331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545196288 :
    ThetaLowerSegment 545196288 545261824 (54515789864799 / 100000) (54522307656159 / 100000) := by
  exact
    packedTile32768 545196288 545261824 13 3240 23349 29 _ _ (125729 / 6250) (2011667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545261824 :
    ThetaLowerSegment 545261824 545327360 (54522307656159 / 100000) (54528871754947 / 100000) := by
  exact
    packedTile32768 545261824 545327360 13 3263 23350 29 _ _ (502919 / 25000) (2011679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545327360 :
    ThetaLowerSegment 545327360 545392896 (54528871754947 / 100000) (54535419799387 / 100000) := by
  exact
    packedTile32768 545327360 545392896 13 3255 23352 29 _ _ (251461 / 12500) (2011691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545392896 :
    ThetaLowerSegment 545392896 545458432 (54535419799387 / 100000) (54541925637187 / 100000) := by
  exact
    packedTile32768 545392896 545458432 13 3234 23353 29 _ _ (20117 / 1000) (2011703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545458432 :
    ThetaLowerSegment 545458432 545523968 (54541925637187 / 100000) (10909690326183 / 20000) := by
  exact
    packedTile32768 545458432 545523968 13 3244 23355 29 _ _ (62866 / 3125) (402343 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545523968 :
    ThetaLowerSegment 545523968 545589504 (10909690326183 / 20000) (54555076238047 / 100000) := by
  exact
    packedTile32768 545523968 545589504 13 3293 23356 29 _ _ (502931 / 25000) (2011727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545589504 :
    ThetaLowerSegment 545589504 545655040 (54555076238047 / 100000) (2182470449471 / 4000) := by
  exact
    packedTile32768 545589504 545655040 13 3323 23357 29 _ _ (251467 / 12500) (2011739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545655040 :
    ThetaLowerSegment 545655040 545720576 (2182470449471 / 4000) (54568293382531 / 100000) := by
  exact
    packedTile32768 545655040 545720576 13 3247 23359 29 _ _ (502937 / 25000) (2011751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545720576 :
    ThetaLowerSegment 545720576 545786112 (54568293382531 / 100000) (54574811484931 / 100000) := by
  exact
    packedTile32768 545720576 545786112 13 3240 23360 29 _ _ (25147 / 1250) (2011763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545786112 :
    ThetaLowerSegment 545786112 545851648 (54574811484931 / 100000) (54581281343683 / 100000) := by
  exact
    packedTile32768 545786112 545851648 13 3216 23362 29 _ _ (502943 / 25000) (80471 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545851648 :
    ThetaLowerSegment 545851648 545917184 (54581281343683 / 100000) (54587882006987 / 100000) := by
  exact
    packedTile32768 545851648 545917184 13 3281 23363 29 _ _ (251473 / 12500) (2011787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545917184 :
    ThetaLowerSegment 545917184 545982720 (54587882006987 / 100000) (54594462591703 / 100000) := by
  exact
    packedTile32768 545917184 545982720 13 3271 23364 29 _ _ (502949 / 25000) (2011799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell545982720 :
    ThetaLowerSegment 545982720 546048256 (54594462591703 / 100000) (54601013038551 / 100000) := by
  exact
    packedTile32768 545982720 546048256 13 3256 23366 29 _ _ (62869 / 3125) (2011811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546048256 :
    ThetaLowerSegment 546048256 546113792 (54601013038551 / 100000) (54607664115471 / 100000) := by
  exact
    packedTile32768 546048256 546113792 13 3306 23367 29 _ _ (100591 / 5000) (2011823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546113792 :
    ThetaLowerSegment 546113792 546179328 (54607664115471 / 100000) (54614101977871 / 100000) := by
  exact
    packedTile32768 546113792 546179328 13 3200 23369 29 _ _ (251479 / 12500) (402367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546179328 :
    ThetaLowerSegment 546179328 546244864 (54614101977871 / 100000) (54620559997111 / 100000) := by
  exact
    packedTile32768 546179328 546244864 13 3210 23370 29 _ _ (502961 / 25000) (2011847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546244864 :
    ThetaLowerSegment 546244864 546310400 (54620559997111 / 100000) (54627140778087 / 100000) := by
  exact
    packedTile32768 546244864 546310400 13 3271 23371 29 _ _ (125741 / 6250) (2011859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546310400 :
    ThetaLowerSegment 546310400 546375936 (54627140778087 / 100000) (54633697455899 / 100000) := by
  exact
    packedTile32768 546310400 546375936 13 3259 23373 29 _ _ (502967 / 25000) (2011871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546375936 :
    ThetaLowerSegment 546375936 546441472 (54633697455899 / 100000) (54640292398539 / 100000) := by
  exact
    packedTile32768 546375936 546441472 13 3278 23374 29 _ _ (50297 / 2500) (2011883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546441472 :
    ThetaLowerSegment 546441472 546507008 (54640292398539 / 100000) (54646718381587 / 100000) := by
  exact
    packedTile32768 546441472 546507008 13 3194 23376 29 _ _ (502973 / 25000) (402379 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546507008 :
    ThetaLowerSegment 546507008 546572544 (54646718381587 / 100000) (54653265117203 / 100000) := by
  exact
    packedTile32768 546507008 546572544 13 3254 23377 29 _ _ (62872 / 3125) (2011907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546572544 :
    ThetaLowerSegment 546572544 546638080 (54653265117203 / 100000) (54659900416171 / 100000) := by
  exact
    packedTile32768 546572544 546638080 13 3298 23378 29 _ _ (502979 / 25000) (2011919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546638080 :
    ThetaLowerSegment 546638080 546703616 (54659900416171 / 100000) (10933276972023 / 20000) := by
  exact
    packedTile32768 546638080 546703616 13 3223 23380 29 _ _ (251491 / 12500) (2011931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546703616 :
    ThetaLowerSegment 546703616 546769152 (10933276972023 / 20000) (10934566625563 / 20000) := by
  exact
    packedTile32768 546703616 546769152 13 3205 23381 29 _ _ (100597 / 5000) (2011943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546769152 :
    ThetaLowerSegment 546769152 546834688 (10934566625563 / 20000) (54679345816439 / 100000) := by
  exact
    packedTile32768 546769152 546834688 13 3237 23383 29 _ _ (125747 / 6250) (402391 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546834688 :
    ThetaLowerSegment 546834688 546900224 (54679345816439 / 100000) (54685894759259 / 100000) := by
  exact
    packedTile32768 546834688 546900224 13 3255 23384 29 _ _ (502991 / 25000) (2011967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546900224 :
    ThetaLowerSegment 546900224 546965760 (54685894759259 / 100000) (54692562447723 / 100000) := by
  exact
    packedTile32768 546900224 546965760 13 3314 23385 29 _ _ (251497 / 12500) (2011979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell546965760 :
    ThetaLowerSegment 546965760 547031296 (54692562447723 / 100000) (10939823903323 / 20000) := by
  exact
    packedTile32768 546965760 547031296 13 3259 23387 29 _ _ (502997 / 25000) (2011991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547031296 :
    ThetaLowerSegment 547031296 547096832 (10939823903323 / 20000) (10941161883323 / 20000) := by
  exact
    packedTile32768 547031296 547096832 13 3325 23388 29 _ _ (503 / 25) (2012003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547096832 :
    ThetaLowerSegment 547096832 547162368 (10941161883323 / 20000) (54712396743903 / 100000) := by
  exact
    packedTile32768 547096832 547162368 13 3274 23390 29 _ _ (503003 / 25000) (402403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547162368 :
    ThetaLowerSegment 547162368 547227904 (54712396743903 / 100000) (54719034411079 / 100000) := by
  exact
    packedTile32768 547162368 547227904 13 3299 23391 29 _ _ (251503 / 12500) (2012027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547227904 :
    ThetaLowerSegment 547227904 547293440 (54719034411079 / 100000) (54725583588259 / 100000) := by
  exact
    packedTile32768 547227904 547293440 13 3255 23392 29 _ _ (503009 / 25000) (2012039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547293440 :
    ThetaLowerSegment 547293440 547358976 (54725583588259 / 100000) (54732164997267 / 100000) := by
  exact
    packedTile32768 547293440 547358976 13 3271 23394 29 _ _ (125753 / 6250) (2012051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547358976 :
    ThetaLowerSegment 547358976 547424512 (54732164997267 / 100000) (54738766566127 / 100000) := by
  exact
    packedTile32768 547358976 547424512 13 3281 23395 29 _ _ (100603 / 5000) (2012063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547424512 :
    ThetaLowerSegment 547424512 547490048 (54738766566127 / 100000) (54745408415799 / 100000) := by
  exact
    packedTile32768 547424512 547490048 13 3301 23397 29 _ _ (251509 / 12500) (80483 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547490048 :
    ThetaLowerSegment 547490048 547555584 (54745408415799 / 100000) (54751889338363 / 100000) := by
  exact
    packedTile32768 547490048 547555584 13 3221 23398 29 _ _ (503021 / 25000) (2012087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547555584 :
    ThetaLowerSegment 547555584 547621120 (54751889338363 / 100000) (10951690559103 / 20000) := by
  exact
    packedTile32768 547555584 547621120 13 3262 23399 29 _ _ (62878 / 3125) (2012099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547621120 :
    ThetaLowerSegment 547621120 547686656 (10951690559103 / 20000) (10952998429303 / 20000) := by
  exact
    packedTile32768 547621120 547686656 13 3250 23401 29 _ _ (503027 / 25000) (2012111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547686656 :
    ThetaLowerSegment 547686656 547752192 (10952998429303 / 20000) (10954302685487 / 20000) := by
  exact
    packedTile32768 547686656 547752192 13 3241 23402 29 _ _ (50303 / 2500) (2012123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547752192 :
    ThetaLowerSegment 547752192 547817728 (10954302685487 / 20000) (54778056880699 / 100000) := by
  exact
    packedTile32768 547752192 547817728 13 3252 23404 29 _ _ (503033 / 25000) (402427 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547817728 :
    ThetaLowerSegment 547817728 547883264 (54778056880699 / 100000) (54784562142251 / 100000) := by
  exact
    packedTile32768 547817728 547883264 13 3233 23405 29 _ _ (125759 / 6250) (2012147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547883264 :
    ThetaLowerSegment 547883264 547948800 (54784562142251 / 100000) (54791091588471 / 100000) := by
  exact
    packedTile32768 547883264 547948800 13 3245 23406 29 _ _ (503039 / 25000) (2012159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell547948800 :
    ThetaLowerSegment 547948800 548014336 (54791091588471 / 100000) (10959551580211 / 20000) := by
  exact
    packedTile32768 547948800 548014336 13 3313 23408 29 _ _ (251521 / 12500) (2012171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548014336 :
    ThetaLowerSegment 548014336 548079872 (10959551580211 / 20000) (10960859899647 / 20000) := by
  exact
    packedTile32768 548014336 548079872 13 3251 23409 29 _ _ (100609 / 5000) (2012183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548079872 :
    ThetaLowerSegment 548079872 548145408 (10960859899647 / 20000) (54810865280731 / 100000) := by
  exact
    packedTile32768 548079872 548145408 13 3263 23411 29 _ _ (62881 / 3125) (402439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548145408 :
    ThetaLowerSegment 548145408 548210944 (54810865280731 / 100000) (54817384821691 / 100000) := by
  exact
    packedTile32768 548145408 548210944 13 3240 23412 29 _ _ (503051 / 25000) (2012207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548210944 :
    ThetaLowerSegment 548210944 548276480 (54817384821691 / 100000) (54824069403243 / 100000) := by
  exact
    packedTile32768 548210944 548276480 13 3322 23413 29 _ _ (251527 / 12500) (2012219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548276480 :
    ThetaLowerSegment 548276480 548342016 (54824069403243 / 100000) (10966125450859 / 20000) := by
  exact
    packedTile32768 548276480 548342016 13 3259 23415 29 _ _ (503057 / 25000) (2012231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548342016 :
    ThetaLowerSegment 548342016 548407552 (10966125450859 / 20000) (10967413283819 / 20000) := by
  exact
    packedTile32768 548342016 548407552 13 3200 23416 29 _ _ (2012239 / 100000) (1006121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548407552 :
    ThetaLowerSegment 548407552 548473088 (10967413283819 / 20000) (13710928221037 / 25000) := by
  exact
    packedTile32768 548407552 548473088 13 3303 23418 29 _ _ (2012251 / 100000) (1006127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548473088 :
    ThetaLowerSegment 548473088 548538624 (13710928221037 / 25000) (6856276058639 / 12500) := by
  exact
    packedTile32768 548473088 548538624 13 3228 23419 29 _ _ (2012263 / 100000) (1006133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548538624 :
    ThetaLowerSegment 548538624 548604160 (6856276058639 / 12500) (54856810743387 / 100000) := by
  exact
    packedTile32768 548538624 548604160 13 3281 23420 29 _ _ (80491 / 4000) (1006139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548604160 :
    ThetaLowerSegment 548604160 548669696 (54856810743387 / 100000) (54863374823581 / 100000) := by
  exact
    packedTile32768 548604160 548669696 13 3262 23422 29 _ _ (2012287 / 100000) (201229 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548669696 :
    ThetaLowerSegment 548669696 548735232 (54863374823581 / 100000) (54869922844527 / 100000) := by
  exact
    packedTile32768 548669696 548735232 13 3254 23423 29 _ _ (2012299 / 100000) (1006151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548735232 :
    ThetaLowerSegment 548735232 548800768 (54869922844527 / 100000) (5487646889221 / 10000) := by
  exact
    packedTile32768 548735232 548800768 13 3253 23425 29 _ _ (2012311 / 100000) (1006157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548800768 :
    ThetaLowerSegment 548800768 548866304 (5487646889221 / 10000) (13720754247813 / 25000) := by
  exact
    packedTile32768 548800768 548866304 13 3254 23426 29 _ _ (2012323 / 100000) (1006163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548866304 :
    ThetaLowerSegment 548866304 548931840 (13720754247813 / 25000) (54889502746957 / 100000) := by
  exact
    packedTile32768 548866304 548931840 13 3223 23427 29 _ _ (402467 / 20000) (1006169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548931840 :
    ThetaLowerSegment 548931840 548997376 (54889502746957 / 100000) (27448034517609 / 50000) := by
  exact
    packedTile32768 548931840 548997376 13 3263 23429 29 _ _ (2012347 / 100000) (40247 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell548997376 :
    ThetaLowerSegment 548997376 549062912 (27448034517609 / 50000) (2196106219449 / 4000) := by
  exact
    packedTile32768 548997376 549062912 13 3273 23430 29 _ _ (2012359 / 100000) (1006181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549062912 :
    ThetaLowerSegment 549062912 549128448 (2196106219449 / 4000) (54909203741459 / 100000) := by
  exact
    packedTile32768 549062912 549128448 13 3254 23432 29 _ _ (2012371 / 100000) (1006187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549128448 :
    ThetaLowerSegment 549128448 549193984 (54909203741459 / 100000) (27457810615423 / 50000) := by
  exact
    packedTile32768 549128448 549193984 13 3189 23433 29 _ _ (2012383 / 100000) (1006193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549193984 :
    ThetaLowerSegment 549193984 549259520 (27457810615423 / 50000) (54922163526991 / 100000) := by
  exact
    packedTile32768 549193984 549259520 13 3251 23434 29 _ _ (402479 / 20000) (1006199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549259520 :
    ThetaLowerSegment 549259520 549325056 (54922163526991 / 100000) (54928792395649 / 100000) := by
  exact
    packedTile32768 549259520 549325056 13 3294 23436 29 _ _ (2012407 / 100000) (201241 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549325056 :
    ThetaLowerSegment 549325056 549390592 (54928792395649 / 100000) (54935393129969 / 100000) := by
  exact
    packedTile32768 549325056 549390592 13 3280 23437 29 _ _ (2012419 / 100000) (1006211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549390592 :
    ThetaLowerSegment 549390592 549456128 (54935393129969 / 100000) (6867743452217 / 12500) := by
  exact
    packedTile32768 549390592 549456128 13 3257 23439 29 _ _ (2012431 / 100000) (1006217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549456128 :
    ThetaLowerSegment 549456128 549521664 (6867743452217 / 12500) (13737130063327 / 25000) := by
  exact
    packedTile32768 549456128 549521664 13 3266 23440 29 _ _ (1006221 / 50000) (402489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549521664 :
    ThetaLowerSegment 549521664 549587200 (13737130063327 / 25000) (6869388628463 / 12500) := by
  exact
    packedTile32768 549521664 549587200 13 3274 23441 29 _ _ (1006227 / 50000) (2012457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549587200 :
    ThetaLowerSegment 549587200 549652736 (6869388628463 / 12500) (2748084087083 / 5000) := by
  exact
    packedTile32768 549587200 549652736 13 3266 23443 29 _ _ (1006233 / 50000) (2012469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549652736 :
    ThetaLowerSegment 549652736 549718272 (2748084087083 / 5000) (27484162465769 / 50000) := by
  exact
    packedTile32768 549652736 549718272 13 3301 23444 29 _ _ (1006239 / 50000) (2012481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549718272 :
    ThetaLowerSegment 549718272 549783808 (27484162465769 / 50000) (27487462949369 / 50000) := by
  exact
    packedTile32768 549718272 549783808 13 3280 23446 29 _ _ (201249 / 10000) (2012493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549783808 :
    ThetaLowerSegment 549783808 549849344 (27487462949369 / 50000) (13745342985661 / 25000) := by
  exact
    packedTile32768 549783808 549849344 13 3203 23447 29 _ _ (1006251 / 50000) (402501 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549849344 :
    ThetaLowerSegment 549849344 549914880 (13745342985661 / 25000) (2749399051931 / 5000) := by
  exact
    packedTile32768 549849344 549914880 13 3284 23448 29 _ _ (1006257 / 50000) (2012517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549914880 :
    ThetaLowerSegment 549914880 549980416 (2749399051931 / 5000) (13748627418241 / 25000) := by
  exact
    packedTile32768 549914880 549980416 13 3244 23450 29 _ _ (1006263 / 50000) (2012529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell549980416 :
    ThetaLowerSegment 549980416 550045952 (13748627418241 / 25000) (1718782070969 / 3125) := by
  exact
    packedTile32768 549980416 550045952 13 3238 23451 29 _ _ (1006269 / 50000) (2012541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550045952 :
    ThetaLowerSegment 550045952 550111488 (1718782070969 / 3125) (13751923965427 / 25000) := by
  exact
    packedTile32768 550045952 550111488 13 3314 23453 29 _ _ (40251 / 2000) (2012553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550111488 :
    ThetaLowerSegment 550111488 550177024 (13751923965427 / 25000) (13753574266267 / 25000) := by
  exact
    packedTile32768 550111488 550177024 13 3280 23454 29 _ _ (1006281 / 50000) (402513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550177024 :
    ThetaLowerSegment 550177024 550242560 (13753574266267 / 25000) (5502088421977 / 10000) := by
  exact
    packedTile32768 550177024 550242560 13 3273 23455 29 _ _ (1006287 / 50000) (2012577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550242560 :
    ThetaLowerSegment 550242560 550308096 (5502088421977 / 10000) (5502754990129 / 10000) := by
  exact
    packedTile32768 550242560 550308096 13 3312 23457 29 _ _ (402517 / 20000) (503147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550308096 :
    ThetaLowerSegment 550308096 550373632 (5502754990129 / 10000) (27517023282203 / 50000) := by
  exact
    packedTile32768 550308096 550373632 13 3228 23458 29 _ _ (2012597 / 100000) (10063 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550373632 :
    ThetaLowerSegment 550373632 550439168 (27517023282203 / 50000) (11008121936471 / 20000) := by
  exact
    packedTile32768 550373632 550439168 13 3261 23460 29 _ _ (2012609 / 100000) (503153 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550439168 :
    ThetaLowerSegment 550439168 550504704 (11008121936471 / 20000) (27523564280887 / 50000) := by
  exact
    packedTile32768 550439168 550504704 13 3239 23461 29 _ _ (2012621 / 100000) (125789 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550504704 :
    ThetaLowerSegment 550504704 550570240 (27523564280887 / 50000) (13763427467921 / 25000) := by
  exact
    packedTile32768 550504704 550570240 13 3270 23462 29 _ _ (2012633 / 100000) (503159 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550570240 :
    ThetaLowerSegment 550570240 550635776 (13763427467921 / 25000) (55060188575939 / 100000) := by
  exact
    packedTile32768 550570240 550635776 13 3219 23464 29 _ _ (402529 / 20000) (251581 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550635776 :
    ThetaLowerSegment 550635776 550701312 (55060188575939 / 100000) (55066733736503 / 100000) := by
  exact
    packedTile32768 550635776 550701312 13 3252 23465 29 _ _ (2012657 / 100000) (100633 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550701312 :
    ThetaLowerSegment 550701312 550766848 (55066733736503 / 100000) (27536706892457 / 50000) := by
  exact
    packedTile32768 550701312 550766848 13 3319 23467 29 _ _ (2012669 / 100000) (62896 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550766848 :
    ThetaLowerSegment 550766848 550832384 (27536706892457 / 50000) (55080009340551 / 100000) := by
  exact
    packedTile32768 550766848 550832384 13 3277 23468 29 _ _ (2012681 / 100000) (503171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550832384 :
    ThetaLowerSegment 550832384 550897920 (55080009340551 / 100000) (55086643176679 / 100000) := by
  exact
    packedTile32768 550832384 550897920 13 3296 23469 29 _ _ (2012693 / 100000) (251587 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550897920 :
    ThetaLowerSegment 550897920 550963456 (55086643176679 / 100000) (55093164340879 / 100000) := by
  exact
    packedTile32768 550897920 550963456 13 3240 23471 29 _ _ (402541 / 20000) (503177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell550963456 :
    ThetaLowerSegment 550963456 551028992 (55093164340879 / 100000) (55099751960347 / 100000) := by
  exact
    packedTile32768 550963456 551028992 13 3273 23472 29 _ _ (503179 / 25000) (2012719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551028992 :
    ThetaLowerSegment 551028992 551094528 (55099751960347 / 100000) (2204251813563 / 4000) := by
  exact
    packedTile32768 551028992 551094528 13 3251 23474 29 _ _ (251591 / 12500) (2012731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551094528 :
    ThetaLowerSegment 551094528 551160064 (2204251813563 / 4000) (11022582243091 / 20000) := by
  exact
    packedTile32768 551094528 551160064 13 3287 23475 29 _ _ (100637 / 5000) (2012743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551160064 :
    ThetaLowerSegment 551160064 551225600 (11022582243091 / 20000) (2204776898727 / 4000) := by
  exact
    packedTile32768 551160064 551225600 13 3235 23476 29 _ _ (125797 / 6250) (402551 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551225600 :
    ThetaLowerSegment 551225600 551291136 (2204776898727 / 4000) (11025174675359 / 20000) := by
  exact
    packedTile32768 551225600 551291136 13 3205 23478 29 _ _ (503191 / 25000) (2012767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551291136 :
    ThetaLowerSegment 551291136 551356672 (11025174675359 / 20000) (55132352502739 / 100000) := by
  exact
    packedTile32768 551291136 551356672 13 3219 23479 29 _ _ (251597 / 12500) (2012779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551356672 :
    ThetaLowerSegment 551356672 551422208 (55132352502739 / 100000) (11027799745743 / 20000) := by
  exact
    packedTile32768 551356672 551422208 13 3302 23480 29 _ _ (503197 / 25000) (2012791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551422208 :
    ThetaLowerSegment 551422208 551487744 (11027799745743 / 20000) (11029119739983 / 20000) := by
  exact
    packedTile32768 551422208 551487744 13 3279 23482 29 _ _ (2516 / 125) (2012803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551487744 :
    ThetaLowerSegment 551487744 551553280 (11029119739983 / 20000) (2206084003307 / 4000) := by
  exact
    packedTile32768 551487744 551553280 13 3230 23483 29 _ _ (503203 / 25000) (402563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551553280 :
    ThetaLowerSegment 551553280 551618816 (2206084003307 / 4000) (55158617603549 / 100000) := by
  exact
    packedTile32768 551553280 551618816 13 3238 23485 29 _ _ (2012823 / 100000) (1006413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551618816 :
    ThetaLowerSegment 551618816 551684352 (55158617603549 / 100000) (55165175419979 / 100000) := by
  exact
    packedTile32768 551618816 551684352 13 3258 23486 29 _ _ (402567 / 20000) (1006419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551684352 :
    ThetaLowerSegment 551684352 551749888 (55165175419979 / 100000) (11034358732183 / 20000) := by
  exact
    packedTile32768 551684352 551749888 13 3288 23487 29 _ _ (2012847 / 100000) (40257 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551749888 :
    ThetaLowerSegment 551749888 551815424 (11034358732183 / 20000) (27589166719903 / 50000) := by
  exact
    packedTile32768 551749888 551815424 13 3249 23489 29 _ _ (2012859 / 100000) (1006431 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551815424 :
    ThetaLowerSegment 551815424 551880960 (27589166719903 / 50000) (1379622083051 / 2500) := by
  exact
    packedTile32768 551815424 551880960 13 3254 23490 29 _ _ (2012871 / 100000) (1006437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551880960 :
    ThetaLowerSegment 551880960 551946496 (1379622083051 / 2500) (55191564080717 / 100000) := by
  exact
    packedTile32768 551880960 551946496 13 3319 23492 29 _ _ (2012883 / 100000) (1006443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell551946496 :
    ThetaLowerSegment 551946496 552012032 (55191564080717 / 100000) (55198134169997 / 100000) := by
  exact
    packedTile32768 551946496 552012032 13 3264 23493 29 _ _ (402579 / 20000) (1006449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552012032 :
    ThetaLowerSegment 552012032 552077568 (55198134169997 / 100000) (55204672091933 / 100000) := by
  exact
    packedTile32768 552012032 552077568 13 3248 23494 29 _ _ (2012907 / 100000) (201291 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552077568 :
    ThetaLowerSegment 552077568 552143104 (55204672091933 / 100000) (55211244269203 / 100000) := by
  exact
    packedTile32768 552077568 552143104 13 3265 23496 29 _ _ (1006459 / 50000) (2012921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552143104 :
    ThetaLowerSegment 552143104 552208640 (55211244269203 / 100000) (55217917132153 / 100000) := by
  exact
    packedTile32768 552143104 552208640 13 3315 23497 29 _ _ (201293 / 10000) (2012933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552208640 :
    ThetaLowerSegment 552208640 552274176 (55217917132153 / 100000) (55224465232479 / 100000) := by
  exact
    packedTile32768 552208640 552274176 13 3253 23499 29 _ _ (1006471 / 50000) (402589 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552274176 :
    ThetaLowerSegment 552274176 552339712 (55224465232479 / 100000) (55230977138669 / 100000) := by
  exact
    packedTile32768 552274176 552339712 13 3235 23500 29 _ _ (1006477 / 50000) (2012957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552339712 :
    ThetaLowerSegment 552339712 552405248 (55230977138669 / 100000) (55237472979951 / 100000) := by
  exact
    packedTile32768 552339712 552405248 13 3227 23501 29 _ _ (1006483 / 50000) (2012969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552405248 :
    ThetaLowerSegment 552405248 552470784 (55237472979951 / 100000) (55243984963781 / 100000) := by
  exact
    packedTile32768 552405248 552470784 13 3235 23503 29 _ _ (1006489 / 50000) (2012981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552470784 :
    ThetaLowerSegment 552470784 552536320 (55243984963781 / 100000) (55250609713871 / 100000) := by
  exact
    packedTile32768 552470784 552536320 13 3291 23504 29 _ _ (201299 / 10000) (2012993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552536320 :
    ThetaLowerSegment 552536320 552601856 (55250609713871 / 100000) (11051440055829 / 20000) := by
  exact
    packedTile32768 552536320 552601856 13 3274 23506 29 _ _ (2013001 / 100000) (503251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552601856 :
    ThetaLowerSegment 552601856 552667392 (11051440055829 / 20000) (11052724358123 / 20000) := by
  exact
    packedTile32768 552601856 552667392 13 3190 23507 29 _ _ (2013013 / 100000) (251627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552667392 :
    ThetaLowerSegment 552667392 552732928 (11052724358123 / 20000) (11054040071263 / 20000) := by
  exact
    packedTile32768 552667392 552732928 13 3268 23508 29 _ _ (80521 / 4000) (503257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552732928 :
    ThetaLowerSegment 552732928 552798464 (11054040071263 / 20000) (27638444839133 / 50000) := by
  exact
    packedTile32768 552732928 552798464 13 3323 23510 29 _ _ (2013037 / 100000) (25163 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552798464 :
    ThetaLowerSegment 552798464 552864000 (27638444839133 / 50000) (27641726109003 / 50000) := by
  exact
    packedTile32768 552798464 552864000 13 3260 23511 29 _ _ (2013049 / 100000) (503263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552864000 :
    ThetaLowerSegment 552864000 552929536 (27641726109003 / 50000) (55289964470341 / 100000) := by
  exact
    packedTile32768 552864000 552929536 13 3235 23513 29 _ _ (2013061 / 100000) (251633 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552929536 :
    ThetaLowerSegment 552929536 552995072 (55289964470341 / 100000) (55296700212599 / 100000) := by
  exact
    packedTile32768 552929536 552995072 13 3346 23514 29 _ _ (2013073 / 100000) (503269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell552995072 :
    ThetaLowerSegment 552995072 553060608 (55296700212599 / 100000) (55303216565507 / 100000) := by
  exact
    packedTile32768 552995072 553060608 13 3237 23515 29 _ _ (503271 / 25000) (2013087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553060608 :
    ThetaLowerSegment 553060608 553126144 (55303216565507 / 100000) (55309839651347 / 100000) := by
  exact
    packedTile32768 553060608 553126144 13 3290 23517 29 _ _ (251637 / 12500) (2013099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553126144 :
    ThetaLowerSegment 553126144 553191680 (55309839651347 / 100000) (11063274839983 / 20000) := by
  exact
    packedTile32768 553126144 553191680 13 3246 23518 29 _ _ (503277 / 25000) (2013111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553191680 :
    ThetaLowerSegment 553191680 553257216 (11063274839983 / 20000) (11064589809967 / 20000) := by
  exact
    packedTile32768 553191680 553257216 13 3266 23520 29 _ _ (12582 / 625) (2013123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553257216 :
    ThetaLowerSegment 553257216 553322752 (11064589809967 / 20000) (55329624595547 / 100000) := by
  exact
    packedTile32768 553257216 553322752 13 3316 23521 29 _ _ (503283 / 25000) (402627 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553322752 :
    ThetaLowerSegment 553322752 553339136 (55329624595547 / 100000) (2213250370739 / 4000) := by
  exact
    packedTile32768 553322752 553339136 11 812 23522 29 _ _ (251643 / 12500) (2013147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell553339136 :
    ThetaLowerSegment 553339136 553341184 (2213250370739 / 4000) (55331452530587 / 100000) := by
  exact
    packedTile32768 553339136 553341184 8 96 23523 29 _ _ (2013147 / 100000) (40263 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_521341184_553341184 :
    ThetaLowerSegment 521341184 553341184 (26065051450421 / 50000) (55331452530587 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell521341184 cell521406720)
                    (ThetaLowerSegment.join cell521472256 cell521537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell521603328 cell521668864)
                    (ThetaLowerSegment.join cell521734400 cell521799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell521865472 cell521931008)
                    (ThetaLowerSegment.join cell521996544 cell522062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell522127616 cell522193152)
                    (ThetaLowerSegment.join cell522258688 cell522324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell522389760 cell522455296)
                    (ThetaLowerSegment.join cell522520832 cell522586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell522651904 cell522717440)
                    (ThetaLowerSegment.join cell522782976 cell522848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell522914048 cell522979584)
                    (ThetaLowerSegment.join cell523045120 cell523110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell523176192 cell523241728)
                    (ThetaLowerSegment.join cell523307264 cell523372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell523438336 cell523503872)
                    (ThetaLowerSegment.join cell523569408 cell523634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell523700480 cell523766016)
                    (ThetaLowerSegment.join cell523831552 cell523897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell523962624 cell524028160)
                    (ThetaLowerSegment.join cell524093696 cell524159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell524224768 cell524290304)
                    (ThetaLowerSegment.join cell524355840 cell524421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell524486912 cell524552448)
                    (ThetaLowerSegment.join cell524617984 cell524683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell524749056 cell524814592)
                    (ThetaLowerSegment.join cell524880128 cell524945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell525011200 cell525076736)
                    (ThetaLowerSegment.join cell525142272 cell525207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell525273344 cell525338880)
                    (ThetaLowerSegment.join cell525404416 cell525469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell525535488 cell525601024)
                    (ThetaLowerSegment.join cell525666560 cell525732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell525797632 cell525863168)
                    (ThetaLowerSegment.join cell525928704 cell525994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell526059776 cell526125312)
                    (ThetaLowerSegment.join cell526190848 cell526256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell526321920 cell526387456)
                    (ThetaLowerSegment.join cell526452992 cell526518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell526584064 cell526649600)
                    (ThetaLowerSegment.join cell526715136 cell526780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell526846208 cell526911744)
                    (ThetaLowerSegment.join cell526977280 cell527042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell527108352 cell527173888)
                    (ThetaLowerSegment.join cell527239424 cell527304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell527370496 cell527436032)
                    (ThetaLowerSegment.join cell527501568 cell527567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell527632640 cell527698176)
                    (ThetaLowerSegment.join cell527763712 cell527829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell527894784 cell527960320)
                    (ThetaLowerSegment.join cell528025856 cell528091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell528156928 cell528222464)
                    (ThetaLowerSegment.join cell528288000 cell528353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell528419072 cell528484608)
                    (ThetaLowerSegment.join cell528550144 cell528615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell528681216 cell528746752)
                    (ThetaLowerSegment.join cell528812288 cell528877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell528943360 cell529008896)
                    (ThetaLowerSegment.join cell529074432 cell529139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell529205504 cell529271040)
                    (ThetaLowerSegment.join cell529336576 cell529402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell529467648 cell529533184)
                    (ThetaLowerSegment.join cell529598720 cell529664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell529729792 cell529795328)
                    (ThetaLowerSegment.join cell529860864 cell529926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell529991936 cell530057472)
                    (ThetaLowerSegment.join cell530123008 cell530188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell530254080 cell530319616)
                    (ThetaLowerSegment.join cell530385152 cell530450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell530516224 cell530581760)
                    (ThetaLowerSegment.join cell530647296 cell530712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell530778368 cell530843904)
                    (ThetaLowerSegment.join cell530909440 cell530974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell531040512 cell531106048)
                    (ThetaLowerSegment.join cell531171584 cell531237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell531302656 cell531368192)
                    (ThetaLowerSegment.join cell531433728 cell531499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell531564800 cell531630336)
                    (ThetaLowerSegment.join cell531695872 cell531761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell531826944 cell531892480)
                    (ThetaLowerSegment.join cell531958016 cell532023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell532089088 cell532154624)
                    (ThetaLowerSegment.join cell532220160 cell532285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell532351232 cell532416768)
                    (ThetaLowerSegment.join cell532482304 cell532547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell532613376 cell532678912)
                    (ThetaLowerSegment.join cell532744448 cell532809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell532875520 cell532941056)
                    (ThetaLowerSegment.join cell533006592 cell533072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell533137664 cell533203200)
                    (ThetaLowerSegment.join cell533268736 cell533334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell533399808 cell533465344)
                    (ThetaLowerSegment.join cell533530880 cell533596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell533661952 cell533727488)
                    (ThetaLowerSegment.join cell533793024 cell533858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell533924096 cell533989632)
                    (ThetaLowerSegment.join cell534055168 cell534120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell534186240 cell534251776)
                    (ThetaLowerSegment.join cell534317312 cell534382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell534448384 cell534513920)
                    (ThetaLowerSegment.join cell534579456 cell534644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell534710528 cell534776064)
                    (ThetaLowerSegment.join cell534841600 cell534907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell534972672 cell535038208)
                    (ThetaLowerSegment.join cell535103744 cell535169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell535234816 cell535300352)
                    (ThetaLowerSegment.join cell535365888 cell535431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell535496960 cell535562496)
                    (ThetaLowerSegment.join cell535628032 cell535693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell535759104 cell535824640)
                    (ThetaLowerSegment.join cell535890176 cell535955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell536021248 cell536086784)
                    (ThetaLowerSegment.join cell536152320 cell536217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell536283392 cell536348928)
                    (ThetaLowerSegment.join cell536414464 cell536480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell536545536 cell536611072)
                    (ThetaLowerSegment.join cell536676608 cell536742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell536807680 cell536873216)
                    (ThetaLowerSegment.join cell536938752 cell537004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell537069824 cell537135360)
                    (ThetaLowerSegment.join cell537200896 cell537266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell537331968 cell537397504)
                    (ThetaLowerSegment.join cell537463040 cell537528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell537594112 cell537659648)
                    (ThetaLowerSegment.join cell537725184 cell537790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell537856256 cell537921792)
                    (ThetaLowerSegment.join cell537987328 cell538052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell538118400 cell538183936)
                    (ThetaLowerSegment.join cell538249472 cell538315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell538380544 cell538446080)
                    (ThetaLowerSegment.join cell538511616 cell538577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell538642688 cell538708224)
                    (ThetaLowerSegment.join cell538773760 cell538839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell538904832 cell538970368)
                    (ThetaLowerSegment.join cell539035904 cell539101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell539166976 cell539232512)
                    (ThetaLowerSegment.join cell539298048 cell539363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell539429120 cell539494656)
                    (ThetaLowerSegment.join cell539560192 cell539625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell539691264 cell539756800)
                    (ThetaLowerSegment.join cell539822336 cell539887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell539953408 cell540018944)
                    (ThetaLowerSegment.join cell540084480 cell540150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell540215552 cell540281088)
                    (ThetaLowerSegment.join cell540346624 cell540412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell540477696 cell540543232)
                    (ThetaLowerSegment.join cell540608768 cell540674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell540739840 cell540805376)
                    (ThetaLowerSegment.join cell540870912 cell540936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell541001984 cell541067520)
                    (ThetaLowerSegment.join cell541133056 cell541198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell541264128 cell541329664)
                    (ThetaLowerSegment.join cell541395200 cell541460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell541526272 cell541591808)
                    (ThetaLowerSegment.join cell541657344 cell541722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell541788416 cell541853952)
                    (ThetaLowerSegment.join cell541919488 cell541985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell542050560 cell542116096)
                    (ThetaLowerSegment.join cell542181632 cell542247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell542312704 cell542378240)
                    (ThetaLowerSegment.join cell542443776 cell542509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell542574848 cell542640384)
                    (ThetaLowerSegment.join cell542705920 cell542771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell542836992 cell542902528)
                    (ThetaLowerSegment.join cell542968064 cell543033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell543099136 cell543164672)
                    (ThetaLowerSegment.join cell543230208 cell543295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell543361280 cell543426816)
                    (ThetaLowerSegment.join cell543492352 cell543557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell543623424 cell543688960)
                    (ThetaLowerSegment.join cell543754496 cell543820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell543885568 cell543951104)
                    (ThetaLowerSegment.join cell544016640 cell544082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell544147712 cell544213248)
                    (ThetaLowerSegment.join cell544278784 cell544344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell544409856 cell544475392)
                    (ThetaLowerSegment.join cell544540928 cell544606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell544672000 cell544737536)
                    (ThetaLowerSegment.join cell544803072 cell544868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell544934144 cell544999680)
                    (ThetaLowerSegment.join cell545065216 cell545130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell545196288 cell545261824)
                    (ThetaLowerSegment.join cell545327360 cell545392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell545458432 cell545523968)
                    (ThetaLowerSegment.join cell545589504 cell545655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell545720576 cell545786112)
                    (ThetaLowerSegment.join cell545851648 cell545917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell545982720 cell546048256)
                    (ThetaLowerSegment.join cell546113792 cell546179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell546244864 cell546310400)
                    (ThetaLowerSegment.join cell546375936 cell546441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell546507008 cell546572544)
                    (ThetaLowerSegment.join cell546638080 cell546703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell546769152 cell546834688)
                    (ThetaLowerSegment.join cell546900224 cell546965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell547031296 cell547096832)
                    (ThetaLowerSegment.join cell547162368 cell547227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell547293440 cell547358976)
                    (ThetaLowerSegment.join cell547424512 cell547490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell547555584 cell547621120)
                    (ThetaLowerSegment.join cell547686656 cell547752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell547817728 cell547883264)
                    (ThetaLowerSegment.join cell547948800 cell548014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell548079872 cell548145408)
                    (ThetaLowerSegment.join cell548210944 cell548276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell548342016 cell548407552)
                    (ThetaLowerSegment.join cell548473088 cell548538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell548604160 cell548669696)
                    (ThetaLowerSegment.join cell548735232 cell548800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell548866304 cell548931840)
                    (ThetaLowerSegment.join cell548997376 cell549062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell549128448 cell549193984)
                    (ThetaLowerSegment.join cell549259520 cell549325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell549390592 cell549456128)
                    (ThetaLowerSegment.join cell549521664 cell549587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell549652736 cell549718272)
                    (ThetaLowerSegment.join cell549783808 cell549849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell549914880 cell549980416)
                    (ThetaLowerSegment.join cell550045952 cell550111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell550177024 cell550242560)
                    (ThetaLowerSegment.join cell550308096 cell550373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell550439168 cell550504704)
                    (ThetaLowerSegment.join cell550570240 cell550635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell550701312 cell550766848)
                    (ThetaLowerSegment.join cell550832384 cell550897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell550963456 cell551028992)
                    (ThetaLowerSegment.join cell551094528 cell551160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell551225600 cell551291136)
                    (ThetaLowerSegment.join cell551356672 cell551422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell551487744 cell551553280)
                    (ThetaLowerSegment.join cell551618816 cell551684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell551749888 cell551815424)
                    (ThetaLowerSegment.join cell551880960 cell551946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell552012032 cell552077568)
                    (ThetaLowerSegment.join cell552143104 cell552208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell552274176 cell552339712)
                    (ThetaLowerSegment.join cell552405248 cell552470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell552536320 cell552601856)
                    (ThetaLowerSegment.join cell552667392 cell552732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell552798464 cell552864000)
                  (ThetaLowerSegment.join cell552929536 cell552995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell553060608 cell553126144)
                  (ThetaLowerSegment.join cell553191680 cell553257216)))
              (ThetaLowerSegment.join cell553322752 cell553339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
